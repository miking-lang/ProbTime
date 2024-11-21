-- Symbolization of ProbTime AST nodes.

include "ast.mc"

include "map.mc"
include "name.mc"
include "mexpr/info.mc"
include "mexpr/symbolize.mc"

lang ProbTimeSymBase
  type PTSymEnv = {
    varEnv : Map String Name,
    typeEnv : Map String Name
  }

  sem emptyPTSymEnv : () -> PTSymEnv
  sem emptyPTSymEnv =
  | _ -> { varEnv = mapEmpty cmpString, typeEnv = mapEmpty cmpString }

  sem symbolLookupError : all a. Info -> Name -> a
  sem symbolLookupError info =
  | id ->
    errorSingle [info] (join ["Unknown name: ", nameGetStr id])

  sem updateSymbol : Map String Name -> Name -> (Map String Name, Name)
  sem updateSymbol env =
  | id ->
    let id = nameSetNewSym id in
    (mapInsert (nameGetStr id) id env, id)

  sem lookupSymbol : Info -> Map String Name -> Name -> Name
  sem lookupSymbol info env =
  | id ->
    if nameHasSym id then id
    else
      optionGetOrElse
        (lam. symbolLookupError info id)
        (mapLookup (nameGetStr id) env)
end

lang ProbTimeSymExpr = ProbTimeSymBase + ProbTimeExprAst
  sem symbolizePTExpr : PTSymEnv -> PTExpr -> PTExpr
  sem symbolizePTExpr env =
  | PTEVar t ->
    let id = lookupSymbol t.info env.varEnv t.id in
    PTEVar {t with id = id}
  | PTEFunctionCall t ->
    let id = lookupSymbol t.info env.varEnv t.id in
    let args = map (symbolizePTExpr env) t.args in
    PTEFunctionCall {t with id = id, args = args}
  | PTEProjection t ->
    let id = lookupSymbol t.info env.varEnv t.id in
    PTEProjection {t with id = id}
  | e -> smapPTExprPTExpr (symbolizePTExpr env) e
end

lang ProbTimeSymType = ProbTimeSymBase + ProbTimeTypeAst
  sem symbolizePTType : PTSymEnv -> PTType -> PTType
  sem symbolizePTType env =
  | PTTAlias t ->
    let id = lookupSymbol t.info env.typeEnv t.id in
    let args = map (symbolizePTType env) t.args in
    PTTAlias {t with id = id, args = args}
  | ty -> smapPTTypePTType (symbolizePTType env) ty
end

lang ProbTimeSymStmt = ProbTimeSymType + ProbTimeSymExpr + ProbTimeStmtAst
  sem symbolizePTStmt : PTSymEnv -> PTStmt -> (PTSymEnv, PTStmt)
  sem symbolizePTStmt env =
  | PTSAssume t ->
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    let dist = symbolizePTExpr env t.dist in
    ({env with varEnv = varEnv}, PTSAssume {t with id = id, dist = dist})
  | PTSInfer t ->
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    let model = symbolizePTExpr env t.model in
    let particles = optionMap (symbolizePTExpr env) t.particles in
    ({env with varEnv = varEnv}, PTSInfer {t with id = id, model = model, particles = particles})
  | PTSRead t ->
    match updateSymbol env.varEnv t.dst with (varEnv, dst) in
    let ty = symbolizePTType env t.ty in
    ({env with varEnv = varEnv}, PTSRead {t with dst = dst, ty = ty})
  | PTSWrite t ->
    let src = symbolizePTExpr env t.src in
    let delay = optionMap (symbolizePTExpr env) t.delay in
    (env, PTSWrite {t with src = src, delay = delay})
  | PTSBinding t ->
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    let ty = optionMap (symbolizePTType env) t.ty in
    let e = symbolizePTExpr env t.e in
    ({env with varEnv = varEnv}, PTSBinding {t with id = id, ty = ty, e = e})
  | PTSCondition t ->
    match symbolizeUpdName t.info env t.upd with (bodyEnv, postEnv, upd) in
    -- NOTE(larshum, 2024-11-07): We symbolize the conditional expression in
    -- the environment including the update variable because the resulting code
    -- runs the condition inside a recursive function.
    let cond = symbolizePTExpr bodyEnv t.cond in
    match mapAccumL symbolizePTStmt bodyEnv t.thn with (thnEnv, thn) in
    match mapAccumL symbolizePTStmt bodyEnv t.els with (elsEnv, els) in
    let upd = findFinalUpdSymbols (thnEnv, elsEnv) upd in
    (postEnv, PTSCondition {t with cond = cond, upd = upd, thn = thn, els = els})
  | PTSForLoop t ->
    let e = symbolizePTExpr env t.e in
    match symbolizeUpdName t.info env t.upd with (bodyEnv, postEnv, upd) in
    match updateSymbol bodyEnv.varEnv t.id with (varEnv, id) in
    let bodyEnv = {bodyEnv with varEnv = varEnv} in
    match mapAccumL symbolizePTStmt bodyEnv t.body with (finalBodyEnv, body) in
    let upd = findFinalUpdSymbols (finalBodyEnv, env) upd in
    (postEnv, PTSForLoop {t with id = id, e = e, upd = upd, body = body})
  | PTSWhileLoop t ->
    match symbolizeUpdName t.info env t.upd with (bodyEnv, postEnv, upd) in
    let cond = symbolizePTExpr bodyEnv t.cond in
    match mapAccumL symbolizePTStmt bodyEnv t.body with (finalBodyEnv, body) in
    let upd = findFinalUpdSymbols (finalBodyEnv, bodyEnv) upd in
    (postEnv, PTSWhileLoop {t with cond = cond, upd = upd, body = body})
  | PTSAssignVar t ->
    let e = symbolizePTExpr env t.e in
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    ({env with varEnv = varEnv}, PTSAssignVar {t with id = id, e = e})
  | PTSAssignProj t ->
    let id = lookupSymbol t.info env.varEnv t.id in
    let e = symbolizePTExpr env t.e in
    match updateSymbol env.varEnv id with (postVarEnv, resultId) in
    ({env with varEnv = postVarEnv}, PTSAssignProj {t with id = id, e = e, resId = resultId})
  | PTSFunctionCall t ->
    let id = lookupSymbol t.info env.varEnv t.id in
    let args = map (symbolizePTExpr env) t.args in
    (env, PTSFunctionCall {t with id = id, args = args})
  | stmt ->
    let stmt = smapPTStmtPTExpr (symbolizePTExpr env) stmt in
    let stmt = smapPTStmtPTType (symbolizePTType env) stmt in
    smapAccumLPTStmtPTStmt symbolizePTStmt env stmt

  sem symbolizeUpdName : Info -> PTSymEnv -> UpdateEntry -> (PTSymEnv, PTSymEnv, UpdateEntry)
  sem symbolizeUpdName info env =
  | Some (t & {preId = preId, bodyParamId = bodyParamId, postId = postId}) ->
    let preId = lookupSymbol info env.varEnv preId in
    match updateSymbol env.varEnv bodyParamId with (bodyVarEnv, bodyParamId) in
    match updateSymbol env.varEnv postId with (postVarEnv, postId) in
    let bodyEnv = {env with varEnv = bodyVarEnv} in
    let postEnv = {env with varEnv = postVarEnv} in
    ( bodyEnv, postEnv
    , Some {t with preId = preId, bodyParamId = bodyParamId, postId = postId} )
  | None () -> (env, env, None ())

  sem findFinalUpdSymbols : (PTSymEnv, PTSymEnv) -> UpdateEntry -> UpdateEntry
  sem findFinalUpdSymbols envs =
  | Some t ->
    let lookupUpdSymbol = lam env.
      optionGetOrElse
        (lam. error "Internal error in symbolization of lowered ProbTime AST (update symbols)")
        (mapLookup (nameGetStr t.bodyParamId) env.varEnv)
    in
    Some {t with bodyResultIds = (lookupUpdSymbol envs.0, lookupUpdSymbol envs.1)}
  | None _ -> None ()
end

lang ProbTimeSymTop =
  ProbTimeSymStmt + ProbTimeSymExpr + ProbTimeSymType + ProbTimeTopAst

  sem symbolizePTTop : PTSymEnv -> PTTop -> (PTSymEnv, PTTop)
  sem symbolizePTTop env =
  | PTTConstant t ->
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    let ty = symbolizePTType env t.ty in
    let e = symbolizePTExpr env t.e in
    ({env with varEnv = varEnv}, PTTConstant {t with id = id, ty = ty, e = e})
  | PTTTypeAlias t ->
    match updateSymbol env.typeEnv t.id with (typeEnv, id) in
    let ty = symbolizePTType env t.ty in
    ({env with typeEnv = typeEnv}, PTTTypeAlias {t with id = id, ty = ty})
  | PTTFunDef t ->
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    match mapAccumL symbolizePTParam env t.params with (env, params) in
    let ty = symbolizePTType env t.ty in
    match mapAccumL symbolizePTStmt env t.body with (bodyEnv, body) in
    let return = optionMap (symbolizePTExpr bodyEnv) t.return in
    let funKind = symbolizePTFunKind env t.funKind in
    ( {env with varEnv = varEnv}
    , PTTFunDef {t with id = id, params = params, ty = ty, body = body,
                        return = return, funKind = funKind} )

  sem symbolizePTParam : PTSymEnv -> PTParam -> (PTSymEnv, PTParam)
  sem symbolizePTParam env =
  | param ->
    match updateSymbol env.varEnv param.id with (varEnv, id) in
    let ty = symbolizePTType env param.ty in
    ({env with varEnv = varEnv}, {param with id = id, ty = ty})

  sem symbolizePTFunKind : PTSymEnv -> PTFunKind -> PTFunKind
  sem symbolizePTFunKind env =
  | PTKTemplate t ->
    let inputs = map (symbolizePTPortDecl env) t.inputs in
    let outputs = map (symbolizePTPortDecl env) t.outputs in
    PTKTemplate {t with inputs = inputs, outputs = outputs}
  | k -> k

  sem symbolizePTPortDecl : PTSymEnv -> PTPortDecl -> PTPortDecl
  sem symbolizePTPortDecl env =
  | decl ->
    let ty = symbolizePTType env decl.ty in
    {decl with ty = ty}
end

lang ProbTimeSymMain = ProbTimeSymType + ProbTimeSymExpr + ProbTimeMainAst
  sem symbolizePTNode : PTSymEnv -> PTNode -> (PTSymEnv, PTNode)
  sem symbolizePTNode env =
  | PTNSensor t ->
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    let ty = symbolizePTType env t.ty in
    let rate = symbolizePTExpr env t.rate in
    match mapAccumL symbolizePTPort env t.outputs with (env, outputs) in
    ( {env with varEnv = varEnv}
    , PTNSensor {t with id = id, ty = ty, rate = rate, outputs = outputs} )
  | PTNActuator t ->
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    let ty = symbolizePTType env t.ty in
    let rate = symbolizePTExpr env t.rate in
    match mapAccumL symbolizePTPort env t.inputs with (env, inputs) in
    ( {env with varEnv = varEnv}
    , PTNActuator {t with id = id, ty = ty, rate = rate, inputs = inputs} )
  | PTNTask t ->
    let f = lam env. lam. lam ports.
      mapAccumL symbolizePTPort env ports
    in
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    let template = lookupSymbol t.info env.varEnv t.template in
    let args = map (symbolizePTExpr env) t.args in
    match mapMapAccum f env t.inputs with (env, inputs) in
    match mapMapAccum f env t.outputs with (env, outputs) in
    ( {env with varEnv = varEnv}
    , PTNTask {t with id = id, template = template, args = args,
                      inputs = inputs, outputs = outputs} )

  sem symbolizePTPort : PTSymEnv -> PTPort -> (PTSymEnv, PTPort)
  sem symbolizePTPort env =
  | Sensor t ->
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    ({env with varEnv = varEnv}, Sensor {t with id = id})
  | Actuator t ->
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    ({env with varEnv = varEnv}, Actuator {t with id = id})
  | Task t ->
    match updateSymbol env.varEnv t.id with (varEnv, id) in
    ({env with varEnv = varEnv}, Task {t with id = id})
end

lang ProbTimeSym = ProbTimeSymTop + ProbTimeSymMain + ProbTimeAst + Sym
  sem symbolizePTProgram : PTSymEnv -> PTProgram -> PTProgram
  sem symbolizePTProgram env =
  | {tops = tops, system = system} ->
    match mapAccumL symbolizePTTop env tops with (env, tops) in
    match mapAccumL symbolizePTNode env system with (_, system) in
    {tops = tops, system = system}

  sem symbolizeProbTime : SymEnv -> PTProgram -> PTProgram
  sem symbolizeProbTime runtimeTopEnv =
  | program ->
    -- NOTE(larshum, 2024-11-04): Convert the provided environment of the
    -- top-level variables defined in the runtime to an environment in the
    -- format of the ProbTime symbolization.
    let env = {
      varEnv = runtimeTopEnv.currentEnv.varEnv,
      typeEnv = runtimeTopEnv.currentEnv.tyConEnv
    } in
    symbolizePTProgram env program
end
