include "ast.mc"
include "mexpr/pprint.mc"

lang ProbTimePrettyPrintBase = IdentifierPrettyPrint
end

lang ProbTimeBinOpPrettyPrint = ProbTimePrettyPrintBase + ProbTimeBinOpAst
  sem pprintBinOp : PTBinOp -> String
  sem pprintBinOp =
  | PTBAdd _ -> "+"
  | PTBSub _ -> "-"
  | PTBMul _ -> "*"
  | PTBDiv _ -> "/"
  | PTBEq _ -> "=="
  | PTBNeq _ -> "!="
  | PTBLt _ -> "<"
  | PTBGt _ -> ">"
  | PTBLeq _ -> "<="
  | PTBGeq _ -> ">="
  | PTBAnd _ -> "&&"
  | PTBOr _ -> "||"
end

lang ProbTimeConstPrettyPrint = ProbTimePrettyPrintBase + ProbTimeConstAst
  sem pprintConst : PTConst -> String
  sem pprintConst =
  | PTCInt {value = v} ->
    printIntWithSuffix v
  | PTCFloat {value = v} -> float2string v
  | PTCBool {value = v} -> bool2string v
  | PTCString {value = v} -> join ["\"", v, "\""]

  sem printIntWithSuffix : Int -> String
  sem printIntWithSuffix =
  | n ->
    match tryEvenlyDivideBy n (floorfi 1e9) with Some n then
      concat (int2string n) "s"
    else match tryEvenlyDivideBy n (floorfi 1e6) with Some n then
      concat (int2string n) "ms"
    else match tryEvenlyDivideBy n (floorfi 1e3) with Some n then
      concat (int2string n) "us"
    else int2string n

  sem tryEvenlyDivideBy : Int -> Int -> Option Int
  sem tryEvenlyDivideBy n =
  | m ->
    if and (geqi n m) (eqi (modi n m) 0) then Some (divi n m)
    else None ()
end

lang ProbTimeExprPrettyPrint =
  ProbTimePrettyPrintBase + ProbTimeExprAst + ProbTimeConstPrettyPrint +
  ProbTimeBinOpPrettyPrint

  sem pprintPTExpr : PprintEnv -> PTExpr -> (PprintEnv, String)
  sem pprintPTExpr env =
  | PTEDistSamples {e = e} ->
    match pprintPTExpr env e with (env, e) in
    (env, concat "samples " e)
  | PTEGaussianDist {mu = mu, sigma = sigma} ->
    match pprintPTExpr env mu with (env, mu) in
    match pprintPTExpr env sigma with (env, sigma) in
    (env, join ["Gaussian(", mu, ", ", sigma, ")"])
  | PTEUniformDist {lo = lo, hi = hi} ->
    match pprintPTExpr env lo with (env, lo) in
    match pprintPTExpr env hi with (env, hi) in
    (env, join ["Uniform(", lo, ", ", hi, ")"])
  | PTEBernoulliDist {p = p} ->
    match pprintPTExpr env p with (env, p) in
    (env, join ["Bernoulli(", p, ")"])
  | PTEGammaDist {k = k, theta = theta} ->
    match pprintPTExpr env k with (env, k) in
    match pprintPTExpr env theta with (env, theta) in
    (env, join ["Gamma(", k, ", ", theta, ")"])
  | PTEVar {id = id} -> pprintEnvGetStr env id
  | PTEFunctionCall {id = id, args = args} ->
    match pprintEnvGetStr env id with (env, id) in
    match mapAccumL pprintPTExpr env args with (env, args) in
    (env, join [id, "(", strJoin ", " args, ")"])
  | PTEProjection {id = id, proj = proj} ->
    match pprintEnvGetStr env id with (env, id) in
    (env, join [id, ".", proj])
  | PTEArrayAccess {e = e, idx = idx} ->
    match pprintPTExpr env e with (env, e) in
    match pprintPTExpr env idx with (env, idx) in
    (env, join [e, "[", idx, "]"])
  | PTEArrayLiteral {elems = elems} ->
    match mapAccumL pprintPTExpr env elems with (env, elems) in
    (env, join ["[", strJoin ", " elems, "]"])
  | PTERecordLiteral {fields = fields} ->
    let pprintField = lam env. lam fieldId. lam fieldExpr.
      match pprintPTExpr env fieldExpr with (env, fieldExpr) in
      (env, join [fieldId, " = ", fieldExpr])
    in
    match mapMapAccum pprintField env fields with (env, fields) in
    (env, join ["{", strJoin ", " (mapValues fields), "}"])
  | PTELiteral {const = const} -> (env, pprintConst const)
  | PTELength {e = e} ->
    match pprintPTExpr env e with (env, e) in
    (env, join ["|", e, "|"])
  | PTEBinOp {lhs = lhs, rhs = rhs, op = op} ->
    match pprintPTExpr env lhs with (env, lhs) in
    match pprintPTExpr env rhs with (env, rhs) in
    let op = pprintBinOp op in
    (env, join ["(", lhs, " ", op, " ", rhs, ")"])
end

lang ProbTimeTypePrettyPrint = ProbTimePrettyPrintBase + ProbTimeTypeAst
  sem pprintPTType : PprintEnv -> PTType -> (PprintEnv, String)
  sem pprintPTType env =
  | PTTInt _ -> (env, "Int")
  | PTTFloat _ -> (env, "Float")
  | PTTBool _ -> (env, "Bool")
  | PTTString _ -> (env, "String")
  | PTTUnit _ -> (env, "Unit")
  | PTTSeq {ty = ty} ->
    match pprintPTType env ty with (env, ty) in
    (env, join ["[", ty, "]"])
  | PTTRecord {fields = fields} ->
    let pprintField = lam env. lam fieldId. lam fieldTy.
      match pprintPTType env fieldTy with (env, fieldTy) in
      (env, join [fieldId, " : ", fieldTy])
    in
    match mapMapAccum pprintField env fields with (env, fields) in
    (env, join ["{", strJoin ", " (mapValues fields), "}"])
  | PTTFunction {from = from, to = to} ->
    match pprintPTType env from with (env, from) in
    match pprintPTType env to with (env, to) in
    (env, join ["(", from, ") -> ", to])
  | PTTDist {ty = ty} ->
    match pprintPTType env ty with (env, ty) in
    (env, join ["Dist(", ty, ")"])
  | PTTAlias {id = id, args = args} ->
    match pprintEnvGetStr env id with (env, id) in
    if null args then (env, id)
    else
      match mapAccumL pprintPTType env args with (env, args) in
      (env, join [id, "(", strJoin ", " args, ")"])
end

lang ProbTimeStmtPrettyPrint =
  ProbTimeStmtAst + ProbTimeTypePrettyPrint + ProbTimeExprPrettyPrint

  sem pprintPTStmt : Int -> PprintEnv -> PTStmt -> (PprintEnv, String)
  sem pprintPTStmt indent env =
  | stmt ->
    match pprintPTStmtH indent env stmt with (env, str) in
    (env, join [pprintSpacing indent, str])

  sem pprintPTStmtH : Int -> PprintEnv -> PTStmt -> (PprintEnv, String)
  sem pprintPTStmtH indent env =
  | PTSObserve {e = e, dist = dist} ->
    match pprintPTExpr env e with (env, e) in
    match pprintPTExpr env dist with (env, dist) in
    (env, join ["observe ", e, " ~ ", dist])
  | PTSAssume {id = id, dist = dist} ->
    match pprintEnvGetStr env id with (env, id) in
    match pprintPTExpr env dist with (env, dist) in
    (env, join ["sample ", id, " ~ ", dist])
  | PTSInfer {id = id, model = model, particles = particles} ->
    match pprintEnvGetStr env id with (env, id) in
    match pprintPTExpr env model with (env, model) in
    match
      match particles with Some p then
        match pprintPTExpr env p with (env, p) in
        (env, concat " particles " p)
      else (env, "")
    with (env, suffix) in
    (env, join ["infer ", model, " to ", id, suffix])
  | PTSDegenerate _ -> (env, "degenerate")
  | PTSResample _ -> (env, "resample")
  | PTSRead {port = port, dst = dst} ->
    match pprintEnvGetStr env dst with (env, dst) in
    (env, join ["read ", port, " to ", dst])
  | PTSWrite {src = src, port = port, delay = delay} ->
    match pprintPTExpr env src with (env, src) in
    match
      match delay with Some d then
        match pprintPTExpr env d with (env, d) in
        (env, concat " offset " d)
      else (env, "")
    with (env, suffix) in
    (env, join ["write ", src, " to ", port, suffix])
  | PTSDelay {ns = ns} ->
    match pprintPTExpr env ns with (env, ns) in
    (env, join ["delay ", ns])
  | PTSBinding {id = id, ty = ty, e = e} ->
    match pprintEnvGetStr env id with (env, id) in
    match
      match ty with Some ty then
        match pprintPTType env ty with (env, ty) in
        (env, join [" : ", ty])
      else (env, "")
    with (env, tyAnnotStr) in
    match pprintPTExpr env e with (env, e) in
    (env, join ["var " , id, tyAnnotStr, " = ", e])
  | PTSCondition {cond = cond, upd = upd, thn = thn, els = els} ->
    match pprintPTExpr env cond with (env, cond) in
    match pprintUpdateString env upd with (env, upd) in
    let ii = pprintIncr indent in
    match mapAccumL (pprintPTStmt ii) env thn with (env, thn) in
    if null els then
      (env, join [
        "if ", cond, upd, " {\n", strJoin "\n" thn, pprintNewline indent, "}"])
    else
      match mapAccumL (pprintPTStmt ii) env els with (env, els) in
      (env, join [
        "if ", cond, upd, " {\n", strJoin "\n" thn, pprintNewline indent,
        "} else {\n", strJoin "\n" els, pprintNewline indent, "}" ])
  | PTSForLoop {id = id, e = e, upd = upd, body = body} ->
    match pprintEnvGetStr env id with (env, id) in
    match pprintPTExpr env e with (env, e) in
    match pprintUpdateString env upd with (env, upd) in
    let ii = pprintIncr indent in
    match mapAccumL (pprintPTStmt ii) env body with (env, body) in
    (env, join [
      "for ", id, " in ", e, upd, " {\n", strJoin "\n" body,
      pprintNewline indent, "}" ])
  | PTSWhileLoop {cond = cond, upd = upd, body = body} ->
    match pprintPTExpr env cond with (env, cond) in
    match pprintUpdateString env upd with (env, upd) in
    let ii = pprintIncr indent in
    match mapAccumL (pprintPTStmt ii) env body with (env, body) in
    (env, join [
      "while ", cond, upd, " {\n", strJoin "\n" body, pprintNewline indent, "}"
    ])
  | PTSAssign {target = target, e = e} ->
    match pprintPTExpr env target with (env, target) in
    match pprintPTExpr env e with (env, e) in
    (env, join [target, " = ", e])
  | PTSFunctionCall {id = id, args = args} ->
    match pprintEnvGetStr env id with (env, id) in
    match mapAccumL pprintPTExpr env args with (env, args) in
    (env, join [id, "(", strJoin ", " args, ")"])

  sem pprintUpdateString : PprintEnv -> Option Name -> (PprintEnv, String)
  sem pprintUpdateString env =
  | Some id ->
    match pprintEnvGetStr env id with (env, id) in
    (env, join [" update ", id])
  | None _ -> (env, "")
end

lang ProbTimeTopPrettyPrint =
  ProbTimeTopAst + ProbTimeStmtPrettyPrint + ProbTimeTypePrettyPrint +
  ProbTimeExprPrettyPrint

  sem pprintPTTop : PprintEnv -> PTTop -> (PprintEnv, String)
  sem pprintPTTop env =
  | PTTConstant {id = id, ty = ty, e = e} ->
    match pprintEnvGetStr env id with (env, id) in
    match pprintPTType env ty with (env, ty) in
    match pprintPTExpr env e with (env, e) in
    (env, join ["const ", id, " : ", ty, " = ", e])
  | PTTTypeAlias {id = id, ty = ty} ->
    match pprintEnvGetStr env id with (env, id) in
    match pprintPTType env ty with (env, ty) in
    (env, join ["type ", id, " = ", ty])
  | PTTFunDef {id = id, params = params, ty = ty, body = body, return = return,
               funKind = funKind} ->
    match pprintEnvGetStr env id with (env, id) in
    match mapAccumL pprintParam env params with (env, params) in
    match
      match (funKind, ty) with (PTKTemplate _, PTTUnit _) then (env, "")
      else
        match pprintPTType env ty with (env, ty) in
        (env, concat " : " ty)
    with (env, tyAnnotStr) in
    match
      match funKind with PTKTemplate {inputs = inputs, outputs = outputs} then
        match mapAccumL pprintInputPort env inputs with (env, inputs) in
        match mapAccumL pprintOutputPort env outputs with (env, outputs) in
        (env, inputs, outputs)
      else (env, [], [])
    with (env, inputs, outputs) in
    let ii = pprintIncr 0 in
    match mapAccumL (pprintPTStmt ii) env body with (env, body) in
    match
      match return with Some e then
        match pprintPTExpr env e with (env, e) in
        let ret = join [pprintSpacing ii, "return ", e] in
        (env, snoc body ret)
      else (env, body)
    with (env, body) in
    let prefix = pprintFunKind funKind in
    (env, join [
      prefix, " ", id, "(", strJoin ", " params, ")", tyAnnotStr, " {\n",
      strJoin "\n" (join [inputs, outputs, body]), "\n}"
    ])

  sem pprintFunKind : PTFunKind -> String
  sem pprintFunKind =
  | PTKProbModel _ -> "model"
  | PTKTemplate _ -> "template"
  | PTKFunction _ -> "def"

  sem pprintParam : PprintEnv -> PTParam -> (PprintEnv, String)
  sem pprintParam env =
  | {id = id, ty = ty} ->
    match pprintEnvGetStr env id with (env, id) in
    match pprintPTType env ty with (env, ty) in
    (env, join [id, " : ", ty])

  sem pprintInputPort : PprintEnv -> PTPortDecl -> (PprintEnv, String)
  sem pprintInputPort env =
  | port -> pprintPortDecl "input" env port

  sem pprintOutputPort : PprintEnv -> PTPortDecl -> (PprintEnv, String)
  sem pprintOutputPort env =
  | port -> pprintPortDecl "output" env port

  sem pprintPortDecl : String -> PprintEnv -> PTPortDecl -> (PprintEnv, String)
  sem pprintPortDecl prefix env =
  | {label = label, ty = ty} ->
    match pprintPTType env ty with (env, ty) in
    let indent = pprintIncr 0 in
    (env, join [pprintSpacing indent, prefix, " ", label, " : ", ty])
end

lang ProbTimeMainPrettyPrint =
  ProbTimeMainAst + ProbTimeStmtPrettyPrint + ProbTimeTypePrettyPrint +
  ProbTimeExprPrettyPrint

  sem pprintPTMain : PprintEnv -> PTMain -> (PprintEnv, String)
  sem pprintPTMain env =
  | nodes ->
    match mapAccumL pprintPTNode env nodes with (env, nodes) in
    (env, join ["system {\n", strJoin "\n" nodes, "\n}"])

  sem pprintPTNode : PprintEnv -> PTNode -> (PprintEnv, String)
  sem pprintPTNode env =
  | PTNSensor {id = id, ty = ty, rate = rate, outputs = outputs, info = info} ->
    let src = Sensor {id = id, info = info} in
    let pprintSensorPortConnection = lam env. lam dst.
      pprintPortConnection env src dst
    in
    match pprintEnvGetStr env id with (env, id) in
    match pprintPTType env ty with (env, ty) in
    match pprintPTExpr env rate with (env, rate) in
    match mapAccumL pprintSensorPortConnection env outputs with (env, outputs) in
    let ii = pprintIncr 0 in
    (env, join [
      "  sensor ", id, " : ", ty, " rate ", rate, "\n", strJoin "\n" outputs
    ])
  | PTNActuator {id = id, ty = ty, rate = rate, inputs = inputs, info = info} ->
    let dst = Actuator {id = id, info = info} in
    let pprintActuatorPortConnection = lam env. lam src.
      pprintPortConnection env src dst
    in
    match pprintEnvGetStr env id with (env, id) in
    match pprintPTType env ty with (env, ty) in
    match pprintPTExpr env rate with (env, rate) in
    match mapAccumL pprintActuatorPortConnection env inputs with (env, inputs) in
    let ii = pprintIncr 0 in
    (env, join [
      "  actuator ", id, " : ", ty, " rate ", rate, "\n", strJoin "\n" inputs
    ])
  | PTNTask {id = id, template = template, args = args, inputs = inputs,
             outputs = outputs, importance = importance, minDelay = minDelay,
             maxDelay = maxDelay, info = info} ->
    match pprintEnvGetStr env id with (env, idStr) in
    match pprintEnvGetStr env template with (env, template) in
    match mapAccumL pprintPTExpr env args with (env, args) in
    let withStr = pprintWithArgs importance minDelay maxDelay in
    match
      mapMapAccum
        (lam env. lam dstLabel. lam srcs.
          let dst = Task {id = id, label = dstLabel, isOutput = false, info = info} in
          mapAccumL (lam acc. lam src. pprintPortConnection env src dst) env srcs)
        env inputs
    with (env, inputs) in
    match
      mapMapAccum
        (lam env. lam srcLabel. lam dsts.
          let src = Task {id = id, label = srcLabel, isOutput = true, info = info} in
          mapAccumL (lam env. lam dst. pprintPortConnection env src dst) env dsts)
        env outputs
    with (env, outputs) in
    (env, join [
      "  task ", idStr, " = ", template, "(", strJoin ", " args, ") with ",
      withStr, "\n",
      strJoin "\n"
        (concat (join (mapValues inputs)) (join (mapValues outputs)))
    ])

  sem pprintPortConnection : PprintEnv -> PTPort -> PTPort -> (PprintEnv, String)
  sem pprintPortConnection env srcPort =
  | dstPort ->
    match pprintPTPort env srcPort with (env, src) in
    match pprintPTPort env dstPort with (env, dst) in
    let indent = pprintIncr 0 in
    (env, join [pprintSpacing indent, src, " -> ", dst])

  sem pprintPTPort : PprintEnv -> PTPort -> (PprintEnv, String)
  sem pprintPTPort env =
  | Sensor {id = id} -> pprintEnvGetStr env id
  | Actuator {id = id} -> pprintEnvGetStr env id
  | Task {id = id, label = label} ->
    match pprintEnvGetStr env id with (env, id) in
    (env, join [id, ".", label])

  sem pprintConnection : (String -> String -> String) -> PprintEnv -> String
                      -> Name -> (PprintEnv, String)
  sem pprintConnection ppConn env label =
  | extPort ->
    match pprintEnvGetStr env extPort with (env, extPort) in
    (env, ppConn extPort label)

  sem pprintWithArgs : Int -> Int -> Int -> String
  sem pprintWithArgs importance minDelay =
  | maxDelay ->
    let f = lam x.
      match x with (key, value) in
      join [key, " = ", printIntWithSuffix value]
    in
    let args =
      [ ("importance", importance)
      , ("minDelay", minDelay)
      , ("maxDelay", maxDelay) ]
    in
    join ["{", strJoin ", " (map f args), "}"]
end

lang ProbTimePrettyPrint =
  ProbTimeAst + ProbTimeTopPrettyPrint + ProbTimeMainPrettyPrint

  sem pprintPTProgram : PTProgram -> String
  sem pprintPTProgram =
  | {tops = tops, system = system} ->
    let env = pprintEnvEmpty in
    match mapAccumL pprintPTTop env tops with (env, tops) in
    match pprintPTMain env system with (env, system) in
    join [strJoin "\n" tops, "\n", system]
end
