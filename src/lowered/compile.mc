-- Lowering of the parse AST to a specialized AST designed to be significantly
-- easier to work with than the automatically generated AST from the parser.

include "../ast.mc"
include "ast.mc"

include "digraph.mc"
include "tuple.mc"

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

  sem lowerRtpplStmt : Map String PTType -> RtpplStmt -> PTStmt
  sem lowerRtpplStmt inputPortTypes =
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
    let port = t.port.v in
    match mapLookup port inputPortTypes with Some ty then
      PTSRead {port = port, dst = t.dst.v, ty = ty, info = t.info}
    else
      errorSingle [t.info] (concat "Read refers to unknown input port " port)
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
      cond = lowerRtpplExpr t.cond, upd = updVar,
      thn = map (lowerRtpplStmt inputPortTypes) t.thn,
      els = map (lowerRtpplStmt inputPortTypes) t.els, info = t.info }
  | ForLoopRtpplStmt t ->
    let updVar = getUpdateVarIdentifier t.upd in
    PTSForLoop {
      id = t.id.v, e = lowerRtpplExpr t.e, upd = updVar,
      body = map (lowerRtpplStmt inputPortTypes) t.body, info = t.info }
  | WhileLoopRtpplStmt t ->
    let updVar = getUpdateVarIdentifier t.upd in
    PTSWhileLoop {
      cond = lowerRtpplExpr t.cond, upd = updVar,
      body = map (lowerRtpplStmt inputPortTypes) t.body, info = t.info }
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

  sem getUpdateVarIdentifier : Option {v : Name, i : Info} -> UpdateEntry
  sem getUpdateVarIdentifier =
  | Some {v = id} ->
    Some {preId = id, bodyParamId = id, bodyResultIds = [], postId = id}
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
    let body = map (lowerRtpplStmt (mapEmpty cmpString)) t.body.stmts in
    let return = optionMap lowerRtpplExpr t.body.ret in
    PTTFunDef {
      id = t.id.v, params = lowerRtpplParams t.params,
      ty = lowerRtpplType t.ty, body = body, return = return,
      funKind = PTKFunction (), info = t.info }
  | ModelDefRtpplTop t ->
    let body = map (lowerRtpplStmt (mapEmpty cmpString)) t.body.stmts in
    let return = optionMap lowerRtpplExpr t.body.ret in
    PTTFunDef {
      id = t.id.v, params = lowerRtpplParams t.params,
      ty = lowerRtpplType t.ty, body = body, return = return,
      funKind = PTKProbModel (),
      info = t.info }
  | TemplateDefRtpplTop t ->
    match partition (lam p. match p with InputRtpplPort _ then true else false) t.body.ports
    with (inputPorts, outputPorts) in
    let inputs = map lowerRtpplPort inputPorts in
    let outputs = map lowerRtpplPort outputPorts in
    let inputTypes = mapFromSeq cmpString (map (lam i. (i.label, i.ty)) inputs) in
    let body = map (lowerRtpplStmt inputTypes) t.body.body in
    PTTFunDef {
      id = t.id.v, params = lowerRtpplParams t.params,
      ty = PTTUnit {info = t.info}, body = body, return = None (),
      funKind = PTKTemplate {inputs = inputs, outputs = outputs}, info = t.info }

  sem lowerRtpplParams : RtpplTopParams -> [PTParam]
  sem lowerRtpplParams =
  | ParamsRtpplTopParams {params = params} ->
    let lowerRtpplParam = lam param.
      match param with {id = {v = id, i = info}, ty = ty} in
      {id = id, ty = lowerRtpplType ty, info = info}
    in
    map lowerRtpplParam params

  sem lowerRtpplPort : RtpplPort -> PTPortDecl
  sem lowerRtpplPort =
  | InputRtpplPort t ->
    {label = t.id.v, ty = lowerRtpplType t.ty, info = t.info}
  | OutputRtpplPort t ->
    {label = t.id.v, ty = lowerRtpplType t.ty, info = t.info}
end

lang ProbTimeConnectionGraph = ProbTimeMainAst
  type Connection = (PTPort, PTPort)

  sem eqConnection : Connection -> Connection -> Bool
  sem eqConnection lhs =
  | rhs -> eqi (cmpConnection lhs rhs) 0

  sem cmpConnection : Connection -> Connection -> Int
  sem cmpConnection lhs =
  | rhs -> tupleCmp2 cmpPort cmpPort lhs rhs

  sem cmpPort : PTPort -> PTPort -> Int
  sem cmpPort lhs =
  | rhs -> cmpPortH (lhs, rhs)

  sem cmpPortH : (PTPort, PTPort) -> Int
  sem cmpPortH =
  | (Sensor l, Sensor r) -> nameCmp l.id r.id
  | (Actuator l, Actuator r) -> nameCmp l.id r.id
  | (Task l, Task r) ->
    let c = nameCmp l.id r.id in
    if eqi c 0 then cmpString l.label r.label
    else c

  type ConnectionGraph = Digraph Name Connection
end

lang ProbTimeLowerMain =
  ProbTimeLowerStmt + ProbTimeLowerType + ProbTimeMainAst + ProbTimeConnectionGraph

  type PortTypeEnv = {
    taskPorts : Map Name (Map String PTType),
    extPorts : Map Name PTType
  }

  sem lowerRtpplMain : [RtpplTop] -> RtpplMain -> [PTNode]
  sem lowerRtpplMain tops =
  | MainRtpplMain {ext = ext, tasks = tasks, connections = connections} ->
    -- NOTE(larshum, 2024-11-05): Collect the ports of all templates, so that
    -- we can find a mapping from port label to its type. We do this here so
    -- that we can encode this information directly in the lowered AST.
    let templatePorts = foldl findTemplatePorts (mapEmpty nameCmp) tops in
    let env = {
      taskPorts = foldl (addTaskPorts templatePorts) (mapEmpty nameCmp) tasks,
      extPorts = mapFromSeq nameCmp (map extNameToType ext)
    } in
    let graph = constructSystemGraph env ext tasks connections in
    join [map (extToNode graph) ext, map (taskToNode env graph) tasks]

  sem extNameToType : RtpplExt -> (Name, PTType)
  sem extNameToType =
  | SensorRtpplExt t -> (t.id.v, lowerRtpplType t.ty)
  | ActuatorRtpplExt t -> (t.id.v, lowerRtpplType t.ty)

  sem findTemplatePorts : Map Name (Map String PTType) -> RtpplTop
                       -> Map Name (Map String PTType)
  sem findTemplatePorts templatePorts =
  | TemplateDefRtpplTop {id = {v = id}, body = {ports = ports}} ->
    let toPortEntry = lam p.
      match p with InputRtpplPort {id = {v = id}, ty = ty} then
        (id, lowerRtpplType ty)
      else match p with OutputRtpplPort {id = {v = id}, ty = ty} then
        (id, lowerRtpplType ty)
      else never
    in
    let v = mapFromSeq cmpString (map toPortEntry ports) in
    mapInsert id v templatePorts
  | _ -> templatePorts

  sem addTaskPorts : Map Name (Map String PTType) -> Map Name (Map String PTType)
                  -> RtpplTask -> Map Name (Map String PTType)
  sem addTaskPorts templateMap taskMap =
  | TaskRtpplTask {id = {v = id}, templateId = {v = templateId}, info = info} ->
    match mapLookup templateId templateMap with Some templatePorts then
      mapInsert id templatePorts taskMap
    else
      errorSingle [info]
        (join ["Task ", nameGetStr id, " refers to unknown template ",
               nameGetStr templateId])

  sem constructSystemGraph : PortTypeEnv -> [RtpplExt] -> [RtpplTask]
                          -> [RtpplConnection] -> ConnectionGraph
  sem constructSystemGraph portTypeEnv exts tasks =
  | connections ->
    let graph = digraphEmpty nameCmp eqConnection in
    let vertexNames = concat (map extName exts) (map taskName tasks) in
    let graph = digraphAddVertices vertexNames graph in
    foldl (addConnectionEdge portTypeEnv) graph connections

  sem extName : RtpplExt -> Name
  sem extName =
  | SensorRtpplExt t -> t.id.v
  | ActuatorRtpplExt t -> t.id.v

  sem taskName : RtpplTask -> Name
  sem taskName =
  | TaskRtpplTask t -> t.id.v

  sem addConnectionEdge : PortTypeEnv -> ConnectionGraph -> RtpplConnection
                       -> ConnectionGraph
  sem addConnectionEdge portTypeEnv g =
  | ConnectionRtpplConnection {from = from, to = to} ->
    match from with PortSpecRtpplPortSpec {port = {v = srcId}, id = fromPortLabel, info = i1} in
    match to with PortSpecRtpplPortSpec {port = {v = dstId}, id = toPortLabel, info = i2} in
    let from =
      match fromPortLabel with Some label then
        let ty = findTaskPortType portTypeEnv i1 srcId label.v in
        Task {id = srcId, label = label.v, isOutput = true, ty = ty, info = i1}
      else
        let ty = findExtPortType portTypeEnv i1 srcId in
        Sensor {id = srcId, ty = ty, info = i1}
    in
    let to =
      match toPortLabel with Some label then
        let ty = findTaskPortType portTypeEnv i2 dstId label.v in
        Task {id = dstId, label = label.v, isOutput = false, ty = ty, info = i2}
      else
        let ty = findExtPortType portTypeEnv i2 dstId in
        Actuator {id = dstId, ty = ty, info = i2}
    in
    digraphAddEdge srcId dstId (from, to) g

  sem findTaskPortType : PortTypeEnv -> Info -> Name -> String -> PTType
  sem findTaskPortType env info id =
  | label ->
    match mapLookup id env.taskPorts with Some ports then
      match mapLookup label ports with Some ty then
        ty
      else
        errorSingle [info] (join ["Unknown label ", label, " of task ", nameGetStr id])
    else
      errorSingle [info] (join ["Unknown label ", label, " of task ", nameGetStr id])

  sem findExtPortType : PortTypeEnv -> Info -> Name -> PTType
  sem findExtPortType env info =
  | id ->
    match mapLookup id env.extPorts with Some ty then ty
    else errorSingle [info] (join ["Unknown external port ", nameGetStr id])

  sem extToNode : ConnectionGraph -> RtpplExt -> PTNode
  sem extToNode g =
  | SensorRtpplExt t ->
    let id = t.id.v in
    let ty = lowerRtpplType t.ty in
    let outputs =
      map
        (lam edge.
          match edge with (_, _, (_, dstLabel)) in
          dstLabel)
        (digraphEdgesFrom id g)
    in
    PTNSensor {
      id = id, ty = ty, rate = lowerRtpplExpr t.r, outputs = outputs,
      info = t.info }
  | ActuatorRtpplExt t ->
    let id = t.id.v in
    let ty = lowerRtpplType t.ty in
    let inputs =
      map
        (lam edge.
          match edge with (_, _, (srcLabel, _)) in
          srcLabel)
        (digraphEdgesTo id g)
    in
    PTNActuator {
      id = id, ty = ty, rate = lowerRtpplExpr t.r, inputs = inputs,
      info = t.info }

  sem taskToNode : PortTypeEnv -> ConnectionGraph -> RtpplTask -> PTNode
  sem taskToNode env g =
  | TaskRtpplTask t ->
    let id = t.id.v in
    let outputs =
      foldl
        (lam acc. lam edge.
          match edge with (_, _, (Task {label = srcLabel}, dstLabel)) in
          mapInsertWith concat srcLabel [dstLabel] acc)
        (mapEmpty cmpString)
        (digraphEdgesFrom id g)
    in
    let inputs =
      foldl
        (lam acc. lam edge.
          match edge with (_, _, (srcLabel, Task {label = dstLabel})) in
          mapInsertWith concat dstLabel [srcLabel] acc)
        (mapEmpty cmpString)
        (digraphEdgesTo id g)
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
    {tops = map lowerRtpplTop p.tops, system = lowerRtpplMain p.tops p.main}
end
