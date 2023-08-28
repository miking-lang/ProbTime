include "argparse.mc"
include "ast.mc"
include "compile.mc"
include "pprint.mc"
include "priority.mc"
include "validate.mc"

include "json.mc"
include "mexpr/shallow-patterns.mc"
include "mexpr/type-check.mc"
include "ocaml/mcore.mc"
include "tuning/hole-cfa.mc"

include "coreppl::dppl-arg.mc"
include "coreppl::infer-method.mc"
include "coreppl::parser.mc"
include "coreppl::coreppl-to-mexpr/compile.mc"
include "coreppl::coreppl-to-mexpr/runtimes.mc"

let _rts = lam.
  use LoadRuntime in
  let _bpf = BPF {particles = int_ 1} in
  let _bpfRtEntry = loadRuntimeEntry _bpf "smc-bpf/runtime.mc" in
  let _defaultRuntimes = mapFromSeq cmpInferMethod [(_bpf, _bpfRtEntry)] in
  combineRuntimes default _defaultRuntimes

lang RtpplJson = RtpplAst
  type RtpplNames = {
    sensors : [Name],
    actuators : [Name],
    tasks : [Name]
  }

  sem optJoinPath : String -> String -> String
  sem optJoinPath path =
  | file ->
    if null path then file
    else join [path, "/", file]

  sem collectSensorOrActuatorName : RtpplNames -> RtpplExt -> RtpplNames
  sem collectSensorOrActuatorName acc =
  | SensorRtpplExt {id = {v = id}} ->
    {acc with sensors = cons id acc.sensors}
  | ActuatorRtpplExt {id = {v = id}} ->
    {acc with actuators = cons id acc.actuators}
  | _ -> acc

  sem collectTaskName : RtpplNames -> RtpplTask -> RtpplNames
  sem collectTaskName acc =
  | TaskRtpplTask {id = {v = id}} ->
    {acc with tasks = cons id acc.tasks}

  sem connectionToJsonObject : RtpplConnection -> JsonValue
  sem connectionToJsonObject =
  | ConnectionRtpplConnection {from = from, to = to} ->
    let portSpecToJsonString = lam ps.
      match ps with PortSpecRtpplPortSpec {port = {v = pid}, id = id} in
      let s =
        match id with Some {v = chid} then
          join [nameGetStr pid, "-", chid]
        else nameGetStr pid
      in
      JsonString s
    in
    let mappings = [
      ("from", portSpecToJsonString from),
      ("to", portSpecToJsonString to)
    ] in
    JsonObject (mapFromSeq cmpString mappings)

  sem makeJsonSpecification : RtpplNames -> [RtpplConnection] -> JsonValue
  sem makeJsonSpecification names =
  | connections ->
    let nameToJsonString = lam id. JsonString (nameGetStr id) in
    let topMappings = [
      ("sensors", JsonArray (map nameToJsonString names.sensors)),
      ("actuators", JsonArray (map nameToJsonString names.actuators)),
      ("tasks", JsonArray (map nameToJsonString names.tasks)),
      ("connections", JsonArray (map connectionToJsonObject connections))
    ] in
    JsonObject (mapFromSeq cmpString topMappings)

  sem generateJsonNetworkSpecification : RtpplOptions -> RtpplProgram -> ()
  sem generateJsonNetworkSpecification options =
  | ProgramRtpplProgram {
      main = MainRtpplMain {ext = ext, tasks = tasks, connections = connections}
    } ->
    let names = {sensors = [], actuators = [], tasks = []} in
    let names = foldl collectSensorOrActuatorName names ext in
    let names = foldl collectTaskName names tasks in
    let json = makeJsonSpecification names connections in
    let path = optJoinPath options.outputPath "network.json" in
    writeFile path (json2string json)
end

lang Rtppl =
  RtpplCompile + RtpplValidate + RtpplTaskAlloc + RtpplPrettyPrint + RtpplJson +
  MExprCompile + DPPLParser +
  MExprLowerNestedPatterns + MExprTypeCheck + MCoreCompileLang

  sem createPipe : RtpplOptions -> String -> ()
  sem createPipe options =
  | name ->
    let path = optJoinPath options.outputPath name in
    let ifPipeExists = join ["[ -p ", path, " ]"] in
    let mkfifo = concat "touch " path in
    match sysRunCommand [ifPipeExists, "||", mkfifo] "" "."
    with {stderr = stderr, returncode = rc} in
    if eqi rc 0 then ()
    else
      let msg = join ["Could not create pipe for port ", path, ": ", stderr] in
      error msg

  sem buildTaskMExpr : RtpplOptions -> String -> Expr -> ()
  sem buildTaskMExpr options filepath =
  | ast ->
    -- TODO(larshum, 2023-04-12): This code is essentially duplicated from the
    -- current compilation approach in mi. It should be directly available in a
    -- library.
    let compileOCaml = lam libs. lam clibs. lam prog.
      let opts = {optimize = true, libraries = libs, cLibraries = clibs} in
      let p = ocamlCompileWithConfig opts prog in
      sysMoveFile p.binaryPath filepath;
      sysChmodWriteAccessFile filepath;
      p.cleanup ()
    in
    -- NOTE(larshum, 2023-04-18): If enabled, writes the MExpr AST of the task
    -- to a file using the filepath with a '.mc' suffix.
    (if options.debugCompileMExpr then
      writeFile (concat filepath ".mc") (concat "mexpr\n" (expr2str ast))
    else ());
    let ast = typeCheck ast in
    let ast = lowerAll ast in
    compileMCore ast (mkEmptyHooks compileOCaml)

  sem buildTaskDppl : RtpplOptions -> String -> Expr -> ()
  sem buildTaskDppl options filepath =
  | ast ->
    let runtimeData = _rts () in
    let dpplOpts = default in
    let ast = mexprCompile dpplOpts runtimeData ast in
    buildTaskMExpr options filepath ast

  -- TODO(larshum, 2023-04-12): For now, we just use the mi compiler
  -- directly. When a task makes use of PPL constructs, we should use the
  -- CorePPL compiler instead.
  sem buildTaskExecutable : RtpplOptions -> Name -> Expr -> ()
  sem buildTaskExecutable options taskId =
  | taskAst ->
    let path = optJoinPath options.outputPath (nameGetStr taskId) in
    buildTaskDppl options path taskAst

  sem buildRtppl : RtpplOptions -> RtpplProgram -> CompileResult -> ()
  sem buildRtppl options program =
  | {tasks = tasks, ports = ports} ->
    iter (createPipe options) ports;
    generateJsonNetworkSpecification options program;
    mapFoldWithKey (lam. lam k. lam v. buildTaskExecutable options k v) () tasks
end

mexpr

use Rtppl in

let options = parseOptions () in
let content = readFile options.file in
let program = parseRtpplExn options.file content in
(if options.debugParse then
  printLn (pprintRtpplProgram program)
else ());
validateRtpplProgram program;
let alloc = computeTaskAllocations program in
mapMapWithKey
  (lam taskId. lam taskPeriod.
    printLn (join ["Task ", nameGetStr taskId, " was allocated a period of ", int2string taskPeriod]))
  alloc;
exit 1;
let result = compileRtpplProgram options program in
(if options.debugCompileDppl then
  mapMapWithKey
    (lam id. lam ast.
      printLn (join ["Task ", nameGetStr id, ":"]);
      printLn (expr2str ast))
    result.tasks;
  ()
else ());
buildRtppl options program result
