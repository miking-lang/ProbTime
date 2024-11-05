include "../src-loc.mc"
include "codegen-base.mc"

include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utils.mc"

include "coreppl::parser.mc"

let ptRuntimeRef = ref (None ())
let ptRuntimeIdsRef = ref (None ())

lang ProbTimeRuntime =
  ProbTimeCodegenBase + MExprAst + MExprFindSym + BootParser + MExprSym

  type RuntimeIds = Map String Name

  sem loadProbTimeRuntime : () -> Expr
  sem loadProbTimeRuntime =
  | _ ->
    match deref ptRuntimeRef with Some rt then rt
    else
      let runtimePath = concat rtpplSrcLoc "runtime/probtime.mc" in
      let parseOpts =
        {defaultBootParserParseMCoreFileArg with keepUtests = false,
                                                 eliminateDeadCode = false}
      in
      let runtime = symbolize (parseMCoreFile parseOpts runtimePath) in
      modref ptRuntimeRef (Some runtime);
      runtime

  sem getProbTimeRuntimeIds : () -> RuntimeIds
  sem getProbTimeRuntimeIds =
  | _ ->
    match deref ptRuntimeIdsRef with Some ids then ids
    else
      let strs = [
        "sdelay", "openFileDescriptor", "closeFileDescriptor", "rtpplReadInt",
        "rtpplReadFloat", "rtpplReadIntRecord", "rtpplReadFloatRecord",
        "rtpplReadDistFloat", "rtpplReadDistFloatRecord", "rtpplWriteInts",
        "rtpplWriteFloats", "rtpplWriteIntRecords", "rtpplWriteFloatRecords",
        "rtpplWriteDistFloats", "rtpplWriteDistFloatRecords", "tsv",
        "probTimeInferRunner", "rtpplRuntimeInit"
      ] in
      let rt = loadProbTimeRuntime () in
      match optionMapM identity (findNamesOfStrings strs rt)
      with Some ids then
        let result = mapFromSeq cmpString (zip strs ids) in
        modref ptRuntimeIdsRef (Some result);
        result
      else
        error "Failed to find required identifiers in the ProbTime runtime"

  -- Performs a lookup of the name in the runtime AST corresponding to the
  -- given string identifier, and reports an error if this fails.
  sem lookupRuntimeId : String -> Name
  sem lookupRuntimeId =
  | str ->
    match lookupRuntimeIdHelper str with Some id then id
    else error (concat "Error in lookupRuntimeId: failed to find name corresponding to " str)

  sem lookupRuntimeIdHelper : String -> Option Name
  sem lookupRuntimeIdHelper =
  | str ->
    let ids = getProbTimeRuntimeIds () in
    mapLookup str ids
end

let fileDescriptorsId = nameSym "fileDescriptors"
let closeFileDescriptorsId = nameSym "closeFileDescriptors"
let inputSeqsId = nameSym "inputSeqs"
let updateInputsId = nameSym "updateInputs"
let outputSeqsId = nameSym "outputSeqs"
let flushOutputsId = nameSym "flushOutputs"

lang ProbTimePortIORuntime = ProbTimeAst + ProbTimeRuntime + DPPLParser
  sem isIntType : PTType -> Bool
  sem isIntType =
  | PTTInt _ -> true
  | _ -> false

  sem isFloatType : PTType -> Bool
  sem isFloatType =
  | PTTFloat _ -> true
  | _ -> false

  sem probTimeReadExprType : Expr -> PTType -> Expr
  sem probTimeReadExprType fdExpr =
  | PTTInt {info = info} ->
    let readInt = nvar_ (lookupRuntimeId "rtpplReadInt") in
    withInfoRec info (app_ readInt fdExpr)
  | PTTFloat {info = info} ->
    let readFloat = nvar_ (lookupRuntimeId "rtpplReadFloat") in
    withInfoRec info (app_ readFloat fdExpr)
  | PTTRecord {fields = fields, info = info} ->
    let readExpr =
      if mapAll isIntType fields then
        nvar_ (lookupRuntimeId "rtpplReadIntRecord")
      else if mapAll isFloatType fields then
        nvar_ (lookupRuntimeId "rtpplReadFloatRecord")
      else
        errorSingle [info] "Compiler only supports reading records of (exclusively) integers or floats"
    in
    let fieldsLength = int_ (mapSize fields) in
    withInfoRec info (appf2_ readExpr fdExpr fieldsLength)
  | PTTDist {ty = PTTFloat _, info = info} ->
    let transformExpr = decodeDistribution () in
    let readDistFloat = nvar_ (lookupRuntimeId "rtpplReadDistFloat") in
    withInfoRec info (map_ transformExpr (app_ readDistFloat fdExpr))
  | PTTDist {ty = PTTRecord {fields = fields}, info = info} ->
    if mapAll isFloatType fields then
      let transformExpr = decodeDistribution () in
      let readDistFloatRecord = nvar_ (lookupRuntimeId "rtpplReadDistFloatRecord") in
      let lengthExpr = int_ (mapSize fields) in
      withInfoRec info (map_ transformExpr (appf2_ readDistFloatRecord fdExpr lengthExpr))
    else
      errorSingle [info] "Compiler only supports reading distributions of float-only records"
  | ty ->
    errorSingle [ptTypeInfo ty] "Reading from ports of this type is not supported"

  -- NOTE(larshum, 2024-11-04): When receiving an encoded distribution,
  -- represented as a sequence of weight/sample tuples, we decode this as an
  -- empirical distribution.
  sem decodeDistribution : () -> Expr
  sem decodeDistribution =
  | () ->
    let distExpr = TmDist {
      dist = DEmpirical {samples = var_ "v"},
      ty = tyunknown_, info = NoInfo ()
    } in
    ulam_ "tsv"
      (match_ (var_ "tsv")
        (prec_ [("0", pvar_ "ts"), ("1", pvar_ "v")])
        (urecord_ [("0", var_ "ts"), ("1", distExpr)])
        never_)

  -- Produces an expression for writing to a port of the given type.
  sem probTimeWriteExprType : Expr -> Expr -> PTType -> Expr
  sem probTimeWriteExprType fdExpr msgsExpr =
  | PTTInt {info = info} ->
    let writeInts = nvar_ (lookupRuntimeId "rtpplWriteInts") in
    withInfoRec info (appf2_ writeInts fdExpr msgsExpr)
  | PTTFloat {info = info} ->
    let writeFloats = nvar_ (lookupRuntimeId "rtpplWriteFloats") in
    withInfoRec info (appf2_ writeFloats fdExpr msgsExpr)
  | PTTRecord {fields = fields, info = info} ->
    let writeFun =
      if mapAll isIntType fields then
        nvar_ (lookupRuntimeId "rtpplWriteIntRecords")
      else if mapAll isFloatType fields then
        nvar_ (lookupRuntimeId "rtpplWriteFloatRecords")
      else
        errorSingle [info] "Compiler only supports writing records of (exclusively) integers or floats"
    in
    let fieldsLength = int_ (mapSize fields) in
    withInfoRec info (appf3_ writeFun fdExpr fieldsLength (unsafeCoerce_ msgsExpr))
  | PTTDist {ty = PTTFloat _, info = info} ->
    let writeDistFloat = nvar_ (lookupRuntimeId "rtpplWriteDistFloats") in
    let transformExpr = encodeDistribution () in
    withInfoRec info (appf2_ writeDistFloat fdExpr (map_ transformExpr msgsExpr))
  | PTTDist {ty = PTTRecord {fields = fields}, info = info} ->
    if mapAll isFloatType fields then
      let writeDistFloatRecord = nvar_ (lookupRuntimeId "rtpplWriteDistFloatRecords") in
      let transformExpr = map_ (encodeDistribution ()) msgsExpr in
      let fieldsLength = int_ (mapSize fields) in
      withInfoRec info (appf3_ writeDistFloatRecord fdExpr fieldsLength transformExpr)
    else
      errorSingle [info] "Compiler only supports writing distributions of float-only records"
  | ty ->
    errorSingle [ptTypeInfo ty] "Writing to ports of this type is not supported"

  -- NOTE(larshum, 2024-11-04): Before we send a distribution, we encode it as
  -- a tuple of samples and weights.
  sem encodeDistribution : () -> Expr
  sem encodeDistribution =
  | () ->
    let samplesExpr = app_ (uconst_ (CDistEmpiricalSamples ())) (var_ "v") in
    ulam_ "tsv"
      (match_ (var_ "tsv")
        (prec_ [("0", pvar_ "ts"), ("1", pvar_ "v")])
        (urecord_ [("0", var_ "ts"), ("1", unsafeCoerce_ samplesExpr)])
        never_)
end

lang ProbTimeGenerateRuntime =
  ProbTimeAst + ProbTimeRuntime + ProbTimePortIORuntime

  type PortData = {dstLabel : String, ty : PTType}

  sem generateTaskSpecificRuntime : PTCompileEnv -> PTNode -> Expr
  sem generateTaskSpecificRuntime env =
  | PTNTask {id = id, template = template, inputs = inputs, outputs = outputs,
             info = info} ->
    let insertPortData = lam srcPortLabel. lam ty. lam acc. lam p.
      mapInsertWith concat srcPortLabel [{dstLabel = ptPortName p, ty = ty}] acc
    in
    let addPortEntry = lam connectedPorts. lam acc. lam port.
      match mapLookup port.label connectedPorts with Some ports then
        let ty = resolveTypeAlias env.aliases port.ty in
        foldl (insertPortData port.label ty) acc ports
      else errorSingle [info] (join ["Could not find port ", port.label, " of task ", nameGetStr id])
    in
    match mapLookup template env.templates with Some t then
      let inputs = foldl (addPortEntry inputs) (mapEmpty cmpString) t.inputs in
      let outputs = foldl (addPortEntry outputs) (mapEmpty cmpString) t.outputs in
      bindall_ [
        generateFileDescriptorCode env.options info id inputs outputs,
        generateBufferInitializationCode inputSeqsId info inputs,
        generateBufferInitializationCode outputSeqsId info outputs,
        generateInputUpdateCode info id inputs,
        generateOutputFlushCode id info outputs ]
    else
      errorSingle [info] (join ["Task ", nameGetStr id, " refers to unknown template ",
                                nameGetStr template])
  | _ -> unit_

  sem generateFileDescriptorCode : RtpplOptions -> Info -> Name
                                -> Map String [PortData]
                                -> Map String [PortData] -> Expr
  sem generateFileDescriptorCode options info taskId inputs =
  | outputs ->
    let openFile = nvar_ (lookupRuntimeId "openFileDescriptor") in
    let closeFile = nvar_ (lookupRuntimeId "closeFileDescriptor") in
    let openFileDescField = lam p.
      (p, appf2_ openFile (str_ p) (int_ options.bufferSize))
    in
    let closeFileDescField = lam p.
      let bindId = nameNoSym (concat "close_" p) in
      nulet_ bindId (app_ closeFile (recordproj_ p (nvar_ fileDescriptorsId)))
    in
    let fdports =
      concat
        (mapFoldWithKey
          (lam acc. lam label. lam ports.
            let inputPortLabel = join [nameGetStr taskId, ".", label] in
            foldl (lam acc. lam p. snoc acc inputPortLabel) acc ports)
          [] inputs)
        (mapFoldWithKey
          (lam acc. lam label. lam ports.
            foldl (lam acc. lam p. snoc acc p.dstLabel) acc ports)
          [] outputs)
    in
    let openFilesExpr = urecord_ (map openFileDescField fdports) in
    let closeFilesExpr = ulam_ "" (bindall_ (map closeFileDescField fdports)) in
    withInfoRec info
      (bindall_ [
        nulet_ fileDescriptorsId openFilesExpr,
        nulet_ closeFileDescriptorsId closeFilesExpr ])

  sem generateBufferInitializationCode : Name -> Info -> Map String [PortData] -> Expr
  sem generateBufferInitializationCode bufferId info =
  | ports ->
    let initEmptySeq = lam acc. lam label. lam. snoc acc (label, seq_ []) in
    let bufferInit = urecord_ (mapFoldWithKey initEmptySeq [] ports) in
    withInfoRec info (nulet_ bufferId (ref_ bufferInit))

  sem generateInputUpdateCode : Info -> Name -> Map String [PortData] -> Expr
  sem generateInputUpdateCode info taskId =
  | inputs ->
    let fdId = nvar_ fileDescriptorsId in
    let updatePortData = lam acc. lam label. lam ports.
      match ports with [p] then
        let taskPortLabel = join [nameGetStr taskId, ".", label] in
        let fdExpr = recordproj_ taskPortLabel fdId in
        snoc acc (label, probTimeReadExprType fdExpr p.ty)
      else
        errorSingle [info]
          (join ["Input port ", label, " of task ", nameGetStr taskId,
                 " is not connected to exactly one output port."])
    in
    let updateExpr = urecord_ (mapFoldWithKey updatePortData [] inputs) in
    withInfoRec info
      (nulet_ updateInputsId (ulam_ "" (modref_ (nvar_ inputSeqsId) updateExpr)))

  sem generateOutputFlushCode : Name -> Info -> Map String [PortData] -> Expr
  sem generateOutputFlushCode taskId info =
  | outputs ->
    let flushPortData = lam srcLabel. lam dstPorts.
      let msgsExpr = recordproj_ srcLabel (deref_ (nvar_ outputSeqsId)) in
      foldl
        (lam acc. lam p.
          let fdExpr = recordproj_ p.dstLabel (nvar_ fileDescriptorsId) in
          -- NOTE(larshum, 2024-11-01): Use a distinct identifier for each port
          -- so that the duplicate code elimination does not remove it.
          let id = nameNoSym (join ["w_", nameGetStr taskId, "_", p.dstLabel]) in
          bind_ (nulet_ id (probTimeWriteExprType fdExpr msgsExpr p.ty)) acc)
        unit_ dstPorts
    in
    let clearPortData = lam acc. lam label. lam. snoc acc (label, seq_ []) in
    let clearExpr =
      ulet_ "" (modref_ (nvar_ outputSeqsId)
        (urecord_ (mapFoldWithKey clearPortData [] outputs)))
    in
    let flushExprs =
      bindall_ (snoc (mapValues (mapMapWithKey flushPortData outputs)) clearExpr)
    in
    withInfoRec info (nulet_ flushOutputsId (ulam_ "" flushExprs))
end
