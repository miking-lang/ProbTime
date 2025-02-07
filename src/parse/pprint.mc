include "ast.mc"

lang RtpplPrettyPrint = RtpplAst
  sem pprintRtpplProgram : RtpplProgram -> String
  sem pprintRtpplProgram =
  | ProgramRtpplProgram p ->
    let topsStr = strJoin "\n" (map pprintRtpplTop p.tops) in
    let mainStr = pprintRtpplMain p.main in
    join [topsStr, "\n", mainStr]

  sem pprintRtpplTop : RtpplTop -> String
  sem pprintRtpplTop =
  | ConstantRtpplTop {id = {v = id}, ty = ty, e = e} ->
    join ["const ", nameGetStr id, " : ", pprintRtpplType ty, " = ", pprintRtpplExpr 2 e]
  | TypeAliasRtpplTop {id = {v = id}, ty = ty} ->
    join ["type ", nameGetStr id, " = ", pprintRtpplType ty]
  | FunctionDefRtpplTop {
      id = {v = id}, params = params, ty = ty,
      body = {stmts = stmts, ret = ret}} ->
    let retStr = pprintRtpplReturn ret in
    let paramsStr = pprintRtpplParams params in
    let stmtStrs = strJoin "\n" (map (pprintRtpplStmt 2) stmts) in
    join ["def ", nameGetStr id, "(", paramsStr, ") : ", pprintRtpplType ty,
          " {\n", stmtStrs, "\n", retStr, "\n}"]
  | ModelDefRtpplTop {
      id = {v = id}, params = params, ty = ty,
      body = {stmts = stmts, ret = ret}} ->
    let retStr = pprintRtpplReturn ret in
    let paramsStr = pprintRtpplParams params in
    let stmtStrs = strJoin "\n" (map (pprintRtpplStmt 2) stmts) in
    join ["model ", nameGetStr id, "(", paramsStr, ") : ", pprintRtpplType ty,
          " {\n", stmtStrs, "\n", retStr, "\n}"]
  | TemplateDefRtpplTop {
      id = {v = id}, params = params,
      body = {ports = ports, body = body}} ->
    let paramsStr = pprintRtpplParams params in
    let portsStr = strJoin "\n" (map pprintRtpplPort ports) in
    let bodyStrs = strJoin "\n" (map (pprintRtpplStmt 2) body) in
    join ["template ", nameGetStr id, "(", paramsStr, ") {\n",
          portsStr, "\n", bodyStrs, "\n}"]

  sem pprintRtpplReturn : Option RtpplExpr -> String
  sem pprintRtpplReturn =
  | Some e -> concat "  return " (pprintRtpplExpr 2 e)
  | None _ -> ""

  sem pprintRtpplPort : RtpplPort -> String
  sem pprintRtpplPort =
  | InputRtpplPort {id = {v = id}, ty = ty} ->
    join ["  input ", id, " : ", pprintRtpplType ty]
  | OutputRtpplPort {id = {v = id}, ty = ty} ->
    join ["  output ", id, " : ", pprintRtpplType ty]

  sem pprintRtpplParams : RtpplTopParams -> String
  sem pprintRtpplParams =
  | ParamsRtpplTopParams {params = params} ->
    let pprintParam = lam param.
      match param with {id = {v = id}, ty = ty} in
      join [nameGetStr id, " : ", pprintRtpplType ty]
    in
    strJoin ", " (map pprintParam params)

  sem pprintRtpplMain : RtpplMain -> String
  sem pprintRtpplMain =
  | MainRtpplMain {ext = ext, tasks = tasks, connections = connections} ->
    let extStr = strJoin "\n" (map pprintRtpplExt ext) in
    let tasksStr = strJoin "\n" (map pprintRtpplTask tasks) in
    let connectionsStr = strJoin "\n" (map pprintRtpplConnection connections) in
    join ["main {\n", tasksStr, "\n", connectionsStr, "\n}"]

  sem pprintRtpplExt : RtpplExt -> String
  sem pprintRtpplExt =
  | SensorRtpplExt {id = {v = id}, ty = ty, r = r} ->
    join ["  sensor ", nameGetStr id, " : ", pprintRtpplType ty, " rate ", pprintRtpplExpr 0 r]
  | ActuatorRtpplExt {id = {v = id}, ty = ty} ->
    join ["  actuator ", nameGetStr id, " : ", pprintRtpplType ty]

  sem pprintRtpplTask : RtpplTask -> String
  sem pprintRtpplTask =
  | TaskRtpplTask {id = {v = id}, templateId = {v = tid}, args = args} ->
    join ["  task ", nameGetStr id, " = ", nameGetStr tid, "(",
          strJoin ", " (map(pprintRtpplExpr 2) args), ")"]

  sem pprintRtpplConnection : RtpplConnection -> String
  sem pprintRtpplConnection =
  | ConnectionRtpplConnection {from = from, to = to} ->
    let pprintSpec = lam spec.
      match spec with PortSpecRtpplPortSpec {port = {v = pid}, id = id} in
      match id with Some {v = chid} then
        join [nameGetStr pid, ".", chid]
      else nameGetStr pid
    in
    join ["  ", pprintSpec from, " -> ", pprintSpec to]

  sem pprintIndent : Int -> String
  sem pprintIndent =
  | n -> create n (lam. ' ')

  sem pprintIndentIncrement : Int -> Int
  sem pprintIndentIncrement =
  | n -> addi n 2

  sem pprintNewline : Int -> String
  sem pprintNewline =
  | n -> cons '\n' (create n (lam. ' '))

  sem pprintRtpplStmt : Int -> RtpplStmt -> String
  sem pprintRtpplStmt indent =
  | BindingRtpplStmt {id = {v = id}, ty = ty, e = e} ->
    let tyStr =
      match ty with Some ty then concat " : " (pprintRtpplType ty)
      else ""
    in
    join [pprintIndent indent, "var ", nameGetStr id, "",
          tyStr, " = ", pprintRtpplExpr indent e]
  | ObserveRtpplStmt {e = e, d = d} ->
    let ii = pprintIndentIncrement indent in
    join [pprintIndent indent, "observe ", pprintRtpplExpr ii e, " ~ ", pprintRtpplExpr ii d]
  | AssumeRtpplStmt {id = {v = id}, d = d} ->
    join [pprintIndent indent, "assume ", nameGetStr id, " ~ ", pprintRtpplExpr indent d]
  | InferRtpplStmt {id = {v = id}, model = model, p = p} ->
    let ii = pprintIndentIncrement indent in
    let header =
      join [ pprintIndent indent, "infer ", pprintRtpplExpr ii model
           , " to ", nameGetStr id ]
    in
    match p with Some p then join [header, " particles ", pprintRtpplExpr ii p]
    else header
  | DegenerateRtpplStmt _ ->
    join [pprintIndent indent, "degenerate"]
  | ResampleRtpplStmt _ ->
    join [pprintIndent indent, "resample"]
  | ReadRtpplStmt {port = {v = portId}, dst = {v = dst}} ->
    join [pprintIndent indent, "read ", portId, " to ", nameGetStr dst]
  | WriteRtpplStmt {src = src, port = {v = portId}, delay = delay} ->
    let delayStr =
      match delay with Some d then concat "offset " (pprintRtpplExpr indent d)
      else ""
    in
    join [pprintIndent indent, "write ", pprintRtpplExpr indent src, " to ", portId, delayStr]
  | ForLoopRtpplStmt {id = {v = id}, e = e, upd = upd, body = body} ->
    let updStr = pprintUpdateVar upd in
    let ii = pprintIndentIncrement indent in
    join [
      pprintIndent indent, "for ", nameGetStr id, " in ",
      pprintRtpplExpr indent e, updStr, " {\n",
      strJoin "\n" (map (pprintRtpplStmt ii) body), pprintNewline indent, "}" ]
  | WhileLoopRtpplStmt {cond = cond, upd = upd, body = body} ->
    let updStr = pprintUpdateVar upd in
    let ii = pprintIndentIncrement indent in
    join [
      pprintIndent indent, "while ", pprintRtpplExpr indent cond, " {\n",
      strJoin "\n" (map (pprintRtpplStmt ii) body), pprintNewline indent, "}"]
  | DelayRtpplStmt {ns = ns} ->
    join [pprintIndent indent, "delay ", pprintRtpplExpr indent ns]
  | IdentPlusStmtRtpplStmt {id = {v = id}, next = ReassignRtpplStmtNoIdent {proj = None _, e = e}} ->
    join [pprintIndent indent, nameGetStr id, " = ", pprintRtpplExpr indent e]
  | IdentPlusStmtRtpplStmt {id = {v = id}, next = ReassignRtpplStmtNoIdent {proj = Some {v = pid}, e = e}} ->
    join [pprintIndent indent, nameGetStr id, ".", pid, " = ", pprintRtpplExpr indent e]
  | IdentPlusStmtRtpplStmt {id = {v = id}, next = FunctionCallSRtpplStmtNoIdent {args = args}} ->
    let ii = pprintIndentIncrement indent in
    join [pprintIndent indent, nameGetStr id, "(",
          strJoin ", " (map (pprintRtpplExpr ii) args), ")"]
  | ConditionRtpplStmt {id = upd, cond = cond, thn = thn, els = els} ->
    let updStr = pprintUpdateVar upd in
    let ii = pprintIndentIncrement indent in
    join [pprintIndent indent, " if ", pprintRtpplExpr indent cond,
          updStr, " {\n", strJoin "\n" (map (pprintRtpplStmt ii) thn),
          pprintNewline indent, "} else {\n",
          strJoin "\n" (map (pprintRtpplStmt ii) els),
          pprintNewline indent, "}"]

  sem pprintUpdateVar : Option {v : Name, i : Info} -> String
  sem pprintUpdateVar =
  | Some {v = id} -> concat "update " (nameGetStr id)
  | None _ -> ""

  sem pprintRtpplExpr : Int -> RtpplExpr -> String
  sem pprintRtpplExpr indent =
  | IdentPlusExprRtpplExpr {id = {v = id}, next = VariableRtpplExprNoIdent _} -> nameGetStr id
  | IdentPlusExprRtpplExpr {id = {v = id}, next = FunctionCallERtpplExprNoIdent {args = args}} ->
    join [nameGetStr id, "(", pprintRtpplArgs indent args, ")"]
  | IdentPlusExprRtpplExpr {id = {v = id}, next = ProjectionRtpplExprNoIdent {id = {v = projId}}} ->
    join [nameGetStr id, ".", projId]
  | LiteralRtpplExpr {const = c} -> pprintRtpplConst c
  | AddRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " +. ", pprintRtpplExpr indent r]
  | SubRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " -. ", pprintRtpplExpr indent r]
  | MulRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " *. ", pprintRtpplExpr indent r]
  | DivRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " /. ", pprintRtpplExpr indent r]
  | EqRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " == ", pprintRtpplExpr indent r]
  | NeqRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " != ", pprintRtpplExpr indent r]
  | LtRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " < ", pprintRtpplExpr indent r]
  | GtRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " > ", pprintRtpplExpr indent r]
  | LeqRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " <= ", pprintRtpplExpr indent r]
  | GeqRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " >= ", pprintRtpplExpr indent r]
  | AndRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " && ", pprintRtpplExpr indent r]
  | OrRtpplExpr {left = l, right = r} ->
    join [pprintRtpplExpr indent l, " || ", pprintRtpplExpr indent r]
  | RecordLitRtpplExpr {fields = fields} ->
    let ii = pprintIndentIncrement indent in
    let ppField = lam f.
      match f with {id = {v = id}, e = e} in
      join [id, " = ", pprintRtpplExpr ii e]
    in
    join ["{", strJoin ", " (map ppField fields), "}"]
  | ArrayLitRtpplExpr {elems = elems} ->
    join ["[", strJoin ", " (map (pprintRtpplExpr indent) elems), "]"]
  | ArrayAccessRtpplExpr {e = e, idx = idx} ->
    join [pprintRtpplExpr indent e, "[", pprintRtpplExpr indent idx, "]"]
  | LengthRtpplExpr {e = e} ->
    join ["|", pprintRtpplExpr indent e, "|"]
  | GaussianDistRtpplExpr {mu = mu, sigma = sigma} ->
    let ii = pprintIndentIncrement indent in
    join ["Gaussian(", pprintRtpplExpr ii mu, ", ", pprintRtpplExpr ii sigma, ")"]
  | UniformDistRtpplExpr {lo = lo, hi = hi} ->
    let ii = pprintIndentIncrement indent in
    join ["Uniform(", pprintRtpplExpr ii lo, ", ", pprintRtpplExpr ii hi, ")"]
  | BernoulliDistRtpplExpr {p = p} ->
    let ii = pprintIndentIncrement indent in
    join ["Bernoulli(", pprintRtpplExpr ii p, ")"]
  | GammaDistRtpplExpr {k = k, theta = theta} ->
    let ii = pprintIndentIncrement indent in
    join ["Gamma(", pprintRtpplExpr ii k, ", ", pprintRtpplExpr ii theta, ")"]
  | DistSamplesRtpplExpr {e = e} ->
    concat "samples " (pprintRtpplExpr indent e)

  sem pprintRtpplArgs : Int -> [RtpplExpr] -> String
  sem pprintRtpplArgs indent =
  | [arg] ++ args ->
    let tailstr =
      if null args then ""
      else concat ", " (pprintRtpplArgs indent args)
    in
    concat (pprintRtpplExpr indent arg) tailstr
  | [] -> ""

  sem pprintRtpplConst : RtpplConst -> String
  sem pprintRtpplConst =
  | LitIntRtpplConst {value = {v = i}} -> int2string i
  | LitFloatRtpplConst {value = {v = f}} -> float2string f
  | LitBoolRtpplConst {value = {v = b}} -> if b then "true" else "false"
  | LitStringRtpplConst {value = {v = s}} -> join ["\"", escapeString s, "\""]

  sem pprintRtpplType : RtpplType -> String
  sem pprintRtpplType =
  | IntRtpplType _ -> "Int"
  | FloatRtpplType _ -> "Float"
  | BoolRtpplType _ -> "Bool"
  | StringRtpplType _ -> "String"
  | UnitRtpplType _ -> "Unit"
  | SeqRtpplType {ty = ty} -> join ["[", pprintRtpplType ty, "]"]
  | DistRtpplType {ty = ty} -> join ["Dist(", pprintRtpplType ty, ")"]
  | AliasRtpplType {id = {v = id}, next = DirectRtpplTypeNoIdent _} -> nameGetStr id
  | AliasRtpplType {id = {v = id}, next = ApplicationRtpplTypeNoIdent {args = args}} ->
    join [nameGetStr id, "(", strJoin ", " (map pprintRtpplType args), ")"]
  | RecordRtpplType {fields = fields} ->
    let ppField = lam f.
      match f with {id = {v = id}, ty = ty} in
      join [id, " : ", pprintRtpplType ty]
    in
    join ["{", strJoin ", " (map ppField fields), "}"]
  | FunctionRtpplType {from = from, to = to} ->
    join ["(", pprintRtpplType from, ") -> ", pprintRtpplType to]
end
