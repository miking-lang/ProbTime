include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utils.mc"

let ptRuntimeRef = ref (None ())
let ptRuntimeIdsRef = ref (None ())

lang ProbTimeRuntime = MExprAst + MExprFindSym + BootParser + MExprSym
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
  -- given string identifier.
  sem lookupRuntimeId : String -> Option Name
  sem lookupRuntimeId =
  | str ->
    let ids = getProbTimeRuntimeIds () in
    match mapLookup str ids with Some id then id
    else error (concat "Error in lookupRuntimeId: failed to find name corresponding to " str)
end
