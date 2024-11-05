include "argparse.mc"
include "ast.mc"
include "pprint.mc"
include "lowered/ast.mc"
include "lowered/codegen.mc"
include "lowered/compile.mc"
include "lowered/json.mc"
include "lowered/pprint.mc"
include "lowered/validate.mc"

include "stdlib::json.mc"
include "stdlib::mexpr/shallow-patterns.mc"
include "stdlib::mexpr/type-check.mc"
include "stdlib::ocaml/mcore.mc"
include "stdlib::tuning/hole-cfa.mc"

include "coreppl::dppl-arg.mc"
include "coreppl::infer-method.mc"
include "coreppl::parser.mc"
include "coreppl::coreppl-to-mexpr/compile.mc"
include "coreppl::coreppl-to-mexpr/runtimes.mc"

let _rts = lam.
  use LoadRuntime in
  let _bpf = BPF {particles = int_ 1} in
  let _bpfRtEntry = loadRuntimeEntry _bpf "smc-bpf/runtime.mc" in
  combineInferRuntimes default (mapFromSeq cmpInferMethod [(_bpf, _bpfRtEntry)])

lang ProbTimeCompileLang =
  ProbTimeLower + ProbTimeSym + ProbTimePrettyPrint +
  ProbTimeValidate + ProbTimeCodegen + RtpplPrettyPrint + ProbTimeJson +

  DPPLParser + MExprLowerNestedPatterns + MExprTypeCheck + MCoreCompileLang

  sem buildProbTime : RtpplOptions -> PTProgram -> CompileResult -> ()
  sem buildProbTime options program =
  | tasks ->
    generateJsonSpecification options program;
    mapFoldWithKey (lam. lam k. lam v. buildTaskExecutable options k v) () tasks

  sem buildTaskExecutable : RtpplOptions -> Name -> Expr -> ()
  sem buildTaskExecutable options taskId =
  | taskAst ->
    let path = optJoinPath (nameGetStr taskId) options.outputPath in
    buildTaskDppl options path taskAst

  sem buildTaskDppl : RtpplOptions -> String -> Expr -> ()
  sem buildTaskDppl options path =
  | taskAst ->
    let runtimeData = _rts () in
    let dpplOpts = {default with extractSimplification = "inline"} in
    let taskAst = mexprCompile dpplOpts runtimeData taskAst in
    buildTaskMExpr options path taskAst

  sem buildTaskMExpr : RtpplOptions -> String -> Expr -> ()
  sem buildTaskMExpr options path =
  | taskAst ->
    -- TODO(larshum, 2023-04-12): This code is essentially duplicated from the
    -- current compilation approach in mi. It should be directly available in a
    -- library.
    let compileOCaml = lam libs. lam clibs. lam prog.
      let opts = {optimize = true, libraries = libs, cLibraries = clibs} in
      let p = ocamlCompileWithConfig opts prog in
      sysMoveFile p.binaryPath path;
      sysChmodWriteAccessFile path;
      p.cleanup()
    in
    writeIntermediateMExprIf path taskAst options.debugCompileMExpr;
    let taskAst = typeCheck taskAst in
    let taskAst = lowerAll taskAst in
    compileMCore taskAst (mkEmptyHooks compileOCaml)

  -- NOTE(larshum, 2024-11-05): If the provided boolean value is true, we write
  -- the pretty-printed AST of a task to the provided path.
  sem writeIntermediateMExprIf : String -> Expr -> Bool -> ()
  sem writeIntermediateMExprIf path ast =
  | true -> writeFile (concat path ".mc") (concat "mexpr\n" (expr2str ast))
  | false -> ()

  -- NOTE(larshum, 2024-11-05): Conditionally print the value produced by the
  -- provided pretty-print function based on the provided boolean value.
  sem condPrint : all a. (a -> String) -> a -> Bool -> ()
  sem condPrint pprint v =
  | true -> printLn (pprint v)
  | false -> ()
end

mexpr

use ProbTimeCompileLang in

let options = parseOptions () in
let content = readFile options.file in
let program = parseRtpplExn options.file content in
condPrint pprintRtpplProgram program options.debugParse;
let program = lowerRtpplProgram program in
condPrint pprintPTProgram program options.debugLowered;
validateProbTimeProgram program;
let result = compileProbTimeProgram options program in
(if options.debugCompileDppl then
  mapMapWithKey
    (lam id. lam ast.
      printLn (join ["Task ", nameGetStr id, ":"]);
      printLn (expr2str ast))
    result;
  ()
else ());
buildProbTime options program result
