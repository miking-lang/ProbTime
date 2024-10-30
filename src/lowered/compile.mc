-- Lowering of the parse AST to a specialized AST designed to be significantly
-- easier to work with than the automatically generated AST from the parser.

include "../ast.mc"
include "ast.mc"
include "stdlib::digraph.mc"
include "stdlib::tuple.mc"

lang ProbTimeLowerBase = RtpplAst
end

lang ProbTimeLowerConst = ProbTimeLowerBase + ProbTimeConstAst
  sem lowerRtpplConst : RtpplConst -> PTConst
  sem lowerRtpplConst =
  | LitIntRtpplConst {value = v} -> PTCInt {value = v.v}
  | LitFloatRtpplConst {value = v} -> PTCFloat {value = v.v}
  | LitBoolRtpplConst {value = v} -> PTCBool {value = v.v}
  | LitStringRtpplConst {value = v} -> PTCString {value = v.v}
end

lang ProbTimeLowerExpr = ProbTimeLowerConst + ProbTimeExprAst
  sem lowerRtpplExpr : RtpplExpr -> PTExpr
  sem lowerRtpplExpr =
  | DistSamplesRtpplExpr t ->
    PTEDistSamples {e = lowerRtpplExpr t.e, info = t.info}
  | GaussianDistRtpplExpr t ->
    PTEGaussianDist {
      mu = lowerRtpplExpr t.mu, sigma = lowerRtpplExpr t.sigma, info = t.info }
  | UniformDistRtpplExpr t ->
    PTEUniformDist {
      lo = lowerRtpplExpr t.lo, hi = lowerRtpplExpr t.hi, info = t.info }
  | BernoulliDistRtpplExpr t ->
    PTEBernoulliDist {p = lowerRtpplExpr t.p, info = t.info}
  | GammaDistRtpplExpr t ->
    PTEGammaDist {
      k = lowerRtpplExpr t.k, theta = lowerRtpplExpr t.theta, info = t.info }
  | IdentPlusExprRtpplExpr (t & {next = VariableRtpplExprNoIdent _}) ->
    PTEVar {id = t.id.v, info = t.info}
  | IdentPlusExprRtpplExpr (t & {next = FunctionCallERtpplExprNoIdent {args = args}}) ->
    PTEFunctionCall {id = t.id.v, args = map lowerRtpplExpr args, info = t.info}
  | IdentPlusExprRtpplExpr (t & {next = ProjectionRtpplExprNoIdent {id = id}}) ->
    PTEProjection {id = t.id.v, proj = id.v, info = t.info}
  | ArrayLitRtpplExpr t ->
    PTEArrayLiteral {elems = map lowerRtpplExpr t.elems, info = t.info}
  | ArrayAccessRtpplExpr t ->
    PTEArrayAccess {e = lowerRtpplExpr t.e, idx = lowerRtpplExpr t.idx, info = t.info}
  | RecordLitRtpplExpr t ->
    let addField = lam acc. lam field.
      match field with {id = {v = id}, e = e} in
      mapInsert id (lowerRtpplExpr e) acc
    in
    let fields = foldl addField (mapEmpty cmpString) t.fields in
    PTERecordLiteral {fields = fields, info = t.info}
  | LiteralRtpplExpr t ->
    PTELiteral {const = lowerRtpplConst t.const, info = t.info}
  | LengthRtpplExpr t ->
    PTELength {e = lowerRtpplExpr t.e, info = t.info}
  | AddRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBAdd (), info = t.info}
  | SubRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBSub (), info = t.info}
  | MulRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBMul (), info = t.info}
  | DivRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBDiv (), info = t.info}
  | EqRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBEq (), info = t.info}
  | NeqRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBNeq (), info = t.info}
  | LtRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBLt (), info = t.info}
  | GtRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBGt (), info = t.info}
  | LeqRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBLeq (), info = t.info}
  | GeqRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBGeq (), info = t.info}
  | AndRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBAnd (), info = t.info}
  | OrRtpplExpr t ->
    PTEBinOp {lhs = lowerRtpplExpr t.left, rhs = lowerRtpplExpr t.right, op = PTBOr (), info = t.info}
end

lang ProbTimeLowerType = ProbTimeLowerBase + ProbTimeTypeAst
  sem lowerRtpplType : RtpplType -> PTType
  sem lowerRtpplType =
  | IntRtpplType t -> PTTInt {info = t.info}
  | FloatRtpplType t -> PTTFloat {info = t.info}
  | BoolRtpplType t -> PTTBool {info = t.info}
  | StringRtpplType t -> PTTString {info = t.info}
  | UnitRtpplType t -> PTTUnit {info = t.info}
  | SeqRtpplType t -> PTTSeq {ty = lowerRtpplType t.ty, info = t.info}
  | DistRtpplType t -> PTTDist {ty = lowerRtpplType t.ty, info = t.info}
  | RecordRtpplType t ->
    let addField = lam acc. lam field.
      match field with {id = {v = id}, ty = ty} in
      mapInsert id (lowerRtpplType ty) acc
    in
    PTTRecord {fields = foldl addField (mapEmpty cmpString) t.fields, info = t.info}
  | FunctionRtpplType t ->
    PTTFunction {from = lowerRtpplType t.from, to = lowerRtpplType t.to, info = t.info}
  | AliasRtpplType (t & {next = DirectRtpplTypeNoIdent _}) ->
    PTTAlias {id = t.id.v, args = [], info = t.info}
  | AliasRtpplType (t & {next = ApplicationRtpplTypeNoIdent {args = args}}) ->
    PTTAlias {id = t.id.v, args = map lowerRtpplType args, info = t.info}
end

lang ProbTimeLowerStmt =
  ProbTimeLowerExpr + ProbTimeLowerType + ProbTimeStmtAst

  sem lowerRtpplStmt : RtpplStmt -> PTStmt
  sem lowerRtpplStmt =
  | ObserveRtpplStmt t ->
    PTSObserve {e = lowerRtpplExpr t.e, dist = lowerRtpplExpr t.d, info = t.info}
  | AssumeRtpplStmt t ->
    PTSAssume {id = t.id.v, dist = lowerRtpplExpr t.d, info = t.info}
  | InferRtpplStmt t ->
    PTSInfer {id = t.id.v, model = lowerRtpplExpr t.model,
              particles = optionMap lowerRtpplExpr t.p, info = t.info}
  | DegenerateRtpplStmt t -> PTSDegenerate {info = t.info}
  | ResampleRtpplStmt t -> PTSResample {info = t.info}
  | ReadRtpplStmt t ->
    PTSRead {port = t.port.v, dst = t.dst.v, info = t.info}
  | WriteRtpplStmt t ->
    PTSWrite {
      src = lowerRtpplExpr t.src, port = t.port.v,
      delay = optionMap lowerRtpplExpr t.delay, info = t.info }
  | DelayRtpplStmt t -> PTSDelay {ns = lowerRtpplExpr t.ns, info = t.info}
  | BindingRtpplStmt t ->
    PTSBinding {
      id = t.id.v, ty = optionMap lowerRtpplType t.ty, e = lowerRtpplExpr t.e,
      info = t.info }
  | ConditionRtpplStmt t ->
    let updVar = getUpdateVarIdentifier t.id in
    PTSCondition {
      cond = lowerRtpplExpr t.cond, upd = updVar, thn = map lowerRtpplStmt t.thn,
      els = map lowerRtpplStmt t.els, info = t.info }
  | ForLoopRtpplStmt t ->
    let updVar = getUpdateVarIdentifier t.upd in
    PTSForLoop {
      id = t.id.v, e = lowerRtpplExpr t.e, upd = updVar,
      body = map lowerRtpplStmt t.body, info = t.info }
  | WhileLoopRtpplStmt t ->
    let updVar = getUpdateVarIdentifier t.upd in
    PTSWhileLoop {
      cond = lowerRtpplExpr t.cond, upd = updVar,
      body = map lowerRtpplStmt t.body, info = t.info }
  | IdentPlusStmtRtpplStmt (t & {next = ReassignRtpplStmtNoIdent {proj = None _, e = e}}) ->
    let target = PTEVar {id = t.id.v, info = t.id.i} in
    PTSAssign {target = target, e = lowerRtpplExpr e, info = t.info}
  | IdentPlusStmtRtpplStmt (t & {next = ReassignRtpplStmtNoIdent {proj = Some proj, e = e}}) ->
    let target = PTEProjection {
      id = t.id.v, proj = proj.v, info = mergeInfo t.id.i proj.i
    } in
    PTSAssign {target = target, e = lowerRtpplExpr e, info = t.info}
  | IdentPlusStmtRtpplStmt (t & {next = FunctionCallSRtpplStmtNoIdent {args = args}}) ->
    PTSFunctionCall {id = t.id.v, args = map lowerRtpplExpr args, info = t.info}

  sem getUpdateVarIdentifier : Option {v : Name, i : Info} -> Option Name
  sem getUpdateVarIdentifier =
  | Some {v = id} -> Some id
  | None _ -> None ()
end

lang ProbTimeLowerTop =
  ProbTimeLowerStmt + ProbTimeLowerType + ProbTimeLowerExpr + ProbTimeTopAst

  sem lowerRtpplTop : RtpplTop -> PTTop
  sem lowerRtpplTop =
  | ConstantRtpplTop t ->
    PTTConstant { id = t.id.v, ty = lowerRtpplType t.ty,
                  e = lowerRtpplExpr t.e, info = t.info }
  | TypeAliasRtpplTop t ->
    PTTTypeAlias { id = t.id.v, ty = lowerRtpplType t.ty, info = t.info }
  | FunctionDefRtpplTop t ->
    let body = constructLoweredBody t.body.stmts t.body.ret in
    PTTFunDef {
      id = t.id.v, params = lowerRtpplParams t.params,
      ty = lowerRtpplType t.ty, body = body, funKind = PTKFunction (),
      info = t.info }
  | ModelDefRtpplTop t ->
    let body = constructLoweredBody t.body.stmts t.body.ret in
    PTTFunDef {
      id = t.id.v, params = lowerRtpplParams t.params,
      ty = lowerRtpplType t.ty, body = body, funKind = PTKProbModel (),
      info = t.info }
  | TemplateDefRtpplTop t ->
    let body = concat (map lowerRtpplPort t.body.ports) (map lowerRtpplStmt t.body.body) in
    PTTFunDef {
      id = t.id.v, params = lowerRtpplParams t.params,
      ty = PTTUnit {info = t.info}, body = body, funKind = PTKTemplate (),
      info = t.info }

  sem lowerRtpplParams : RtpplTopParams -> [PTParam]
  sem lowerRtpplParams =
  | ParamsRtpplTopParams {params = params} ->
    let lowerRtpplParam = lam param.
      match param with {id = {v = id, i = info}, ty = ty} in
      {id = id, ty = lowerRtpplType ty, info = info}
    in
    map lowerRtpplParam params

  sem lowerRtpplPort : RtpplPort -> PTStmt
  sem lowerRtpplPort =
  | InputRtpplPort t ->
    PTSPortDecl {
      id = t.id.v, ty = lowerRtpplType t.ty, output = false, info = t.info }
  | OutputRtpplPort t ->
    PTSPortDecl {
      id = t.id.v, ty = lowerRtpplType t.ty, output = true, info = t.info }

  sem constructLoweredBody : [RtpplStmt] -> Option RtpplExpr -> [PTStmt]
  sem constructLoweredBody stmts =
  | Some e ->
    let stmts = map lowerRtpplStmt stmts in
    let e = lowerRtpplExpr e in
    snoc stmts (PTSReturn {e = e, info = ptExprInfo e})
  | None _ ->
    map lowerRtpplStmt stmts
end

lang ProbTimeConnectionGraph
  type ConnectionLabel = (Option String, Option String)

  sem eqConnectionLabel : ConnectionLabel -> ConnectionLabel -> Bool
  sem eqConnectionLabel lhs =
  | rhs -> eqi (cmpConnectionLabel lhs rhs) 0

  sem cmpConnectionLabel : ConnectionLabel -> ConnectionLabel -> Int
  sem cmpConnectionLabel lhs =
  | rhs -> tupleCmp2 cmpLabel cmpLabel lhs rhs

  sem cmpLabel : Option String -> Option String -> Int
  sem cmpLabel lhs =
  | rhs -> cmpLabelH (lhs, rhs)

  sem cmpLabelH : (Option String, Option String) -> Int
  sem cmpLabelH =
  | (None _, None _) -> 0
  | (Some _, None _) -> 1
  | (None _, Some _) -> -1
  | (Some l, Some r) -> cmpString l r

  type ConnectionGraph = Digraph Name ConnectionLabel
end

lang ProbTimeLowerMain =
  ProbTimeLowerStmt + ProbTimeLowerType + ProbTimeMainAst + ProbTimeConnectionGraph

  sem lowerRtpplMain : RtpplMain -> [PTNode]
  sem lowerRtpplMain =
  | MainRtpplMain {ext = ext, tasks = tasks, connections = connections} ->
    let graph = constructSystemGraph ext tasks connections in
    join [map (extToNode graph) ext, map (taskToNode graph) tasks]

  sem constructSystemGraph : [RtpplExt] -> [RtpplTask] -> [RtpplConnection]
                          -> ConnectionGraph
  sem constructSystemGraph exts tasks =
  | connections ->
    let graph = digraphEmpty nameCmp eqConnectionLabel in
    let vertexNames = concat (map extName exts) (map taskName tasks) in
    let graph = digraphAddVertices vertexNames graph in
    foldl addConnectionEdge graph connections

  sem extName : RtpplExt -> Name
  sem extName =
  | SensorRtpplExt t -> t.id.v
  | ActuatorRtpplExt t -> t.id.v

  sem taskName : RtpplTask -> Name
  sem taskName =
  | TaskRtpplTask t -> t.id.v

  sem addConnectionEdge : ConnectionGraph -> RtpplConnection -> ConnectionGraph
  sem addConnectionEdge g =
  | ConnectionRtpplConnection {from = from, to = to} ->
    match from with PortSpecRtpplPortSpec {port = {v = srcId}, id = fromPortLabel} in
    match to with PortSpecRtpplPortSpec {port = {v = dstId}, id = toPortLabel} in
    let fromLabel = optionMap (lam x. x.v) fromPortLabel in
    let toLabel = optionMap (lam x. x.v) toPortLabel in
    digraphAddEdge srcId dstId (fromLabel, toLabel) g

  sem extToNode : ConnectionGraph -> RtpplExt -> PTNode
  sem extToNode g =
  | SensorRtpplExt t ->
    let id = t.id.v in
    let ty = lowerRtpplType t.ty in
    let outputs = digraphSuccessors id g in
    PTNSensor {
      id = id, ty = ty, rate = lowerRtpplExpr t.r, outputs = outputs,
      info = t.info }
  | ActuatorRtpplExt t ->
    let id = t.id.v in
    let ty = lowerRtpplType t.ty in
    let inputs = digraphPredeccessors id g in
    PTNActuator {
      id = id, ty = ty, rate = lowerRtpplExpr t.r, inputs = inputs,
      info = t.info }

  sem taskToNode : ConnectionGraph -> RtpplTask -> PTNode
  sem taskToNode g =
  | TaskRtpplTask t ->
    let id = t.id.v in
    let outputs =
      mapFromSeq cmpString
        (map
          (lam edge.
            match edge with (_, dst, (Some label, _)) in
            (label, dst))
          (digraphEdgesFrom id g))
    in
    let inputs =
      mapFromSeq cmpString
        (map
          (lam edge.
            match edge with (src, _, (_, Some label)) in
            (label, src))
          (digraphEdgesTo id g))
    in
    let args = map lowerRtpplExpr t.args in
    match extractRequiredTaskKeyValuePairs t.info (zip t.key t.value)
    with [importance, minDelay, maxDelay] in
    PTNTask {
      id = id, template = t.templateId.v, args = args, inputs = inputs,
      outputs = outputs, importance = importance, minDelay = minDelay,
      maxDelay = maxDelay, info = t.info
    }

  type KeyValuePairs = [({i : Info, v : String}, {i : Info, v : Int})]

  sem extractRequiredTaskKeyValuePairs : Info -> KeyValuePairs -> [Int]
  sem extractRequiredTaskKeyValuePairs info =
  | kvs ->
    let m = extractTaskKeyValuePairs (mapEmpty cmpString) kvs in
    let requiredKeys = ["importance", "minDelay", "maxDelay"] in
    lookupRequiredKeys info m requiredKeys

  sem extractTaskKeyValuePairs
    : Map String Int -> [({i : Info, v : String}, {i : Info, v : Int})]
   -> Map String Int
  sem extractTaskKeyValuePairs acc =
  | [({v = key}, {v = value})] ++ kvs ->
    extractTaskKeyValuePairs (mapInsert key value acc) kvs
  | [] -> acc

  sem lookupRequiredKeys : Info -> Map String Int -> [String] -> [Int]
  sem lookupRequiredKeys info m =
  | [requiredKey] ++ keys ->
    match mapLookup requiredKey m with Some v then
      cons v (lookupRequiredKeys info m keys)
    else errorSingle [info] (join ["Missing required task parameter: ", requiredKey])
  | [] -> []
end

lang ProbTimeLower = ProbTimeAst + ProbTimeLowerMain + ProbTimeLowerTop
  sem lowerRtpplProgram : RtpplProgram -> PTProgram
  sem lowerRtpplProgram =
  | ProgramRtpplProgram p ->
    {tops = map lowerRtpplTop p.tops, system = lowerRtpplMain p.main}
end
