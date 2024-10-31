-- Generates Miking DPPL code from the ProbTime AST.

include "ast.mc"
include "runtime.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/duplicate-code-elimination.mc"
include "mexpr/lamlift.mc"
include "mexpr/type-check.mc"
include "coreppl::parser.mc"

lang ProbTimeCodegenBase = MExprAst
  -- TODO: What to store in this environment?
  type Env = ()

  -- TODO: What to return?
  type CompileResult = Expr

  -- Recursively set the info field of all subexpressions of a given expression
  -- to the provided info value, while avoiding to overwrite existing info
  -- fields. This function also recurses down into type fields and patterns.
  sem withInfoRec : Info -> Expr -> Expr
  sem withInfoRec info =
  | e ->
    let e =
      match infoTm e with NoInfo _ then withInfo info e
      else e
    in
    let e = smap_Expr_Pat (withInfoRecPat info) e in
    let e = smap_Expr_Type (withInfoRecTy info) e in
    smap_Expr_Expr (withInfoRec info) e

  sem withInfoRecTy : Info -> Type -> Type
  sem withInfoRecTy info =
  | ty ->
    let ty =
      match infoTy ty with NoInfo _ then tyWithInfo info ty
      else ty
    in
    smap_Type_Type (withInfoRecTy info) ty

  sem withInfoRecPat : Info -> Pat -> Pat
  sem withInfoRecPat info =
  | p ->
    let p =
      match infoPat p with NoInfo _ then withInfoPat info p
      else p
    in
    let p = smap_Pat_Expr (withInfoRec info) p in
    let p = smap_Pat_Type (withInfoRecTy info) p in
    smap_Pat_Pat (withInfoRecPat info) p
end

-- NOTE(larshum, 2024-10-31): Extension of the expressions defined in MExpr
-- with intermediate expressions. We use this in the initial codegen to be able
-- to implicitly refer to functions provided by the runtime before we merge the
-- user code with the runtime.
lang ProbTimeCodegenExprExtension =
  ProbTimeCodegenBase + MExprSym + MExprTypeCheck + DPPLParser

  syn Expr =
  | TmRead {label : String, ty : Type, info : Info}
  | TmWrite {label : String, src : Expr, delay : Expr, ty : Type, info : Info}
  | TmSdelay {e : Expr, ty : Type, info : Info}
  | TmConfigurableInfer {model : Name, ty : Type, info : Info}

  sem infoTm =
  | TmRead t -> t.info
  | TmWrite t -> t.info
  | TmSdelay t -> t.info
  | TmConfigurableInfer t -> t.info

  sem tyTm =
  | TmRead t -> t.ty
  | TmWrite t -> t.ty
  | TmSdelay t -> t.ty
  | TmConfigurableInfer t -> t.ty

  sem withInfo info =
  | TmRead t -> TmRead {t with info = info}
  | TmWrite t -> TmWrite {t with info = info}
  | TmSdelay t -> TmSdelay {t with info = info}
  | TmConfigurableInfer t -> TmConfigurableInfer {t with info = info}

  sem withType ty =
  | TmRead t -> TmRead {t with ty = ty}
  | TmWrite t -> TmWrite {t with ty = ty}
  | TmSdelay t -> TmSdelay {t with ty = ty}
  | TmConfigurableInfer t -> TmConfigurableInfer {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmRead t -> (acc, TmRead t)
  | TmWrite t ->
    match f acc t.src with (acc, src) in
    match f acc t.delay with (acc, delay) in
    (acc, TmWrite {t with src = src, delay = delay})
  | TmSdelay t ->
    match f acc t.e with (acc, e) in
    (acc, TmSdelay {t with e = e})
  | TmConfigurableInfer t -> (acc, TmConfigurableInfer t)

  sem symbolizeExpr env =
  | TmRead t ->
    TmRead {t with ty = symbolizeType env t.ty}
  | TmWrite t ->
    TmWrite {t with src = symbolizeExpr env t.src,
                    delay = symbolizeExpr env t.delay,
                    ty = symbolizeType env t.ty}
  | TmSdelay t ->
    TmSdelay {t with e = symbolizeExpr env t.e,
                     ty = symbolizeType env t.ty}
  | TmConfigurableInfer t -> TmConfigurableInfer t

  sem typeCheckExpr env =
  | TmRead t ->
    let tyData = newvar env.currentLvl t.info in
    let tyRes = newvar env.currentLvl t.info in
    unify env [t.info] (tyseq_ (tytuple_ [tytuple_ [tyint_, tyint_], tyData])) tyRes;
    TmRead {t with ty = tyRes}
  | TmWrite t ->
    let src = typeCheckExpr env t.src in
    let delay = typeCheckExpr env t.delay in
    let tyRes = newvar env.currentLvl t.info in
    let tyData = newvar env.currentLvl t.info in
    unify env [t.info] (tyTm src) tyData;
    unify env [t.info] (tytuple_ [tytuple_ [tyint_, tyint_], tyData]) tyRes;
    unify env [t.info] tyint_ (tyTm delay);
    TmWrite {t with src = src, ty = tyRes}
  | TmSdelay t ->
    let e = typeCheckExpr env t.e in
    let tyRes = newvar env.currentLvl t.info in
    unify env [t.info] tyint_ (tyTm e);
    unify env [t.info] tyunit_ tyRes;
    TmSdelay {t with e = e, ty = tyRes}
  | TmConfigurableInfer t ->
    let tyRes = newvar env.currentLvl t.info in
    TmConfigurableInfer {t with ty = TyDist {ty = tyRes, info = t.info}}

  sem isAtomic =
  | TmRead _ -> true
  | TmWrite _ -> true
  | TmSdelay _ -> true
  | TmConfigurableInfer _ -> true

  sem pprintCode indent env =
  | TmRead t ->
    (env, join ["read ", t.label])
  | TmWrite t ->
    match pprintCode indent env t.src with (env, src) in
    match pprintCode indent env t.delay with (env, delay) in
    (env, join ["write ", src, " to ", t.label, " (", delay, ")"])
  | TmSdelay t ->
    match pprintCode indent env t.e with (env, e) in
    (env, join ["sdelay ", e])
  | TmConfigurableInfer t ->
    match pprintEnvGetStr env t.model with (env, model) in
    (env, join ["inferRunner ", model])
end

lang ProbTimeCodegenBinOp = ProbTimeCodegenBase + ProbTimeBinOpAst
  sem compileProbTimeBinOp : Info -> Expr -> Expr -> PTBinOp -> Expr
  sem compileProbTimeBinOp info lhs rhs =
  | PTBAdd _ -> withInfoRec info (addf_ lhs rhs)
  | PTBSub _ -> withInfoRec info (subf_ lhs rhs)
  | PTBMul _ -> withInfoRec info (mulf_ lhs rhs)
  | PTBDiv _ -> withInfoRec info (divf_ lhs rhs)
  | PTBEq _ -> withInfoRec info (eqf_ lhs rhs)
  | PTBNeq _ -> withInfoRec info (neqf_ lhs rhs)
  | PTBLt _ -> withInfoRec info (ltf_ lhs rhs)
  | PTBGt _ -> withInfoRec info (gtf_ lhs rhs)
  | PTBLeq _ -> withInfoRec info (leqf_ lhs rhs)
  | PTBGeq _ -> withInfoRec info (geqf_ lhs rhs)
  | PTBAnd _ -> withInfoRec info (and_ lhs rhs)
  | PTBOr _ -> withInfoRec info (or_ lhs rhs)
end

lang ProbTimeCodegenConst = ProbTimeCodegenBase + ProbTimeConstAst
  sem compileProbTimeConst : Info -> PTConst -> Expr
  sem compileProbTimeConst info =
  | PTCInt {value = v} -> withInfoRec info (int_ v)
  | PTCFloat {value = v} -> withInfoRec info (float_ v)
  | PTCBool {value = v} -> withInfoRec info (bool_ v)
  | PTCString {value = v} -> withInfoRec info (str_ v)
end

lang ProbTimeCodegenExpr =
  ProbTimeCodegenBinOp + ProbTimeCodegenConst + ProbTimeExprAst + DPPLParser

  sem compileProbTimeExpr : PTExpr -> Expr
  sem compileProbTimeExpr =
  | PTEDistSamples {e = e, info = info} ->
    let s = nameNoSym "s" in
    let w = nameNoSym "w" in
    let patBinds = mapFromSeq cmpSID [
      (stringToSid "0", withInfoRecPat info (npvar_ s)),
      (stringToSid "1", withInfoRecPat info (npvar_ w))
    ] in
    let binds = mapFromSeq cmpSID [
      (stringToSid "s", withInfoRec info (nvar_ s)),
      (stringToSid "w", withInfoRec info (nvar_ w))
    ] in
    TmMatch {
      target = TmApp {
        lhs = TmConst {val = CDistEmpiricalSamples (), ty = ityunknown_ info, info = info},
        rhs = compileProbTimeExpr e, ty = ityunknown_ info, info = info },
      pat = PatRecord {bindings = patBinds, ty = ityunknown_ info, info = info},
      thn = TmRecord {bindings = binds, ty = ityunknown_ info, info = info},
      els = TmNever {ty = ityunknown_ info, info = info},
      ty = ityunknown_ info, info = info }
  | PTEGaussianDist {mu = mu, sigma = sigma, info = info} ->
    let mu = compileProbTimeExpr mu in
    let sigma = compileProbTimeExpr sigma in
    TmDist {
      dist = DGaussian {mu = mu, sigma = sigma},
      ty = ityunknown_ info, info = info }
  | PTEUniformDist {lo = lo, hi = hi, info = info} ->
    let lo = compileProbTimeExpr lo in
    let hi = compileProbTimeExpr hi in
    TmDist {
      dist = DUniform {a = lo, b = hi}, ty = ityunknown_ info, info = info }
  | PTEBernoulliDist {p = p, info = info} ->
    let p = compileProbTimeExpr p in
    TmDist {
      dist = DBernoulli {p = p}, ty = ityunknown_ info, info = info }
  | PTEGammaDist {k = k, theta = theta, info = info} ->
    let k = compileProbTimeExpr k in
    let theta = compileProbTimeExpr theta in
    TmDist {
      dist = DGamma {k = k, theta = theta}, ty = ityunknown_ info, info = info }
  | PTEVar {id = id, info = info} ->
    withInfoRec info (nvar_ id)
  | PTEFunctionCall {id = id, args = args, info = info} ->
    let appArg = lam acc. lam arg.
      withInfoRec info (app_ acc arg)
    in
    -- NOTE(larshum, 2024-10-31): If a function is declared with no arguments,
    -- we implicitly add a unit argument to ensure the result is not evaluated
    -- ahead of time.
    let args = if null args then [unit_] else map compileProbTimeExpr args in
    foldl appArg (withInfoRec info (nvar_ id)) args
  | PTEProjection {id = id, proj = proj, info = info} ->
    withInfoRec info (recordproj_ proj (withInfoRec info (nvar_ id)))
  | PTEArrayAccess {e = e, idx = idx, info = info} ->
    let e = compileProbTimeExpr e in
    let idx = compileProbTimeExpr idx in
    withInfoRec info (get_ e idx)
  | PTEArrayLiteral {elems = elems, info = info} ->
    withInfoRec info (seq_ (map compileProbTimeExpr elems))
  | PTERecordLiteral {fields = fields, info = info} ->
    let toMExprBinding = lam acc. lam label. lam e.
      mapInsert (stringToSid label) (compileProbTimeExpr e) acc
    in
    let bindings = mapFoldWithKey toMExprBinding (mapEmpty cmpSID) fields in
    TmRecord {bindings = bindings, ty = ityunknown_ info, info = info}
  | PTELiteral {const = const, info = info} ->
    compileProbTimeConst info const
  | PTELength {e = e, info = info} ->
    withInfoRec info (length_ (compileProbTimeExpr e))
  | PTEBinOp {lhs = lhs, rhs = rhs, op = op, info = info} ->
    let lhs = compileProbTimeExpr lhs in
    let rhs = compileProbTimeExpr rhs in
    compileProbTimeBinOp info lhs rhs op
end

lang ProbTimeCodegenType = ProbTimeCodegenBase + ProbTimeTypeAst + DPPLParser
  sem compileProbTimeType : PTType -> Type
  sem compileProbTimeType =
  | PTTInt t -> TyInt {info = t.info}
  | PTTFloat t -> TyFloat {info = t.info}
  | PTTBool t -> TyBool {info = t.info}
  | PTTString t -> TySeq {ty = TyChar {info = t.info}, info = t.info}
  | PTTUnit t -> TyRecord {fields = mapEmpty cmpSID, info = t.info}
  | PTTSeq t -> TySeq {ty = compileProbTimeType t.ty, info = t.info}
  | PTTRecord t ->
    let toMExprField = lam acc. lam label. lam ty.
      mapInsert (stringToSid label) (compileProbTimeType ty) acc
    in
    let fields = mapFoldWithKey toMExprField (mapEmpty cmpSID) t.fields in
    TyRecord {fields = fields, info = t.info}
  | PTTFunction t ->
    TyArrow {
      from = compileProbTimeType t.from, to = compileProbTimeType t.to,
      info = t.info }
  | PTTDist t ->
    TyDist {ty = compileProbTimeType t.ty, info = t.info}
  | PTTAlias t ->
    let appArg = lam acc. lam arg.
      TyApp {lhs = acc, rhs = compileProbTimeType arg, info = t.info}
    in
    let baseType = withInfoRecTy t.info (ntycon_ t.id) in
    foldl appArg baseType t.args
end

lang ProbTimeCodegenStmt =
  ProbTimeCodegenExprExtension + ProbTimeCodegenType + ProbTimeCodegenExpr +
  ProbTimeStmtAst

  sem compileProbTimeStmts : Env -> Expr -> [PTStmt] -> Expr
  sem compileProbTimeStmts env inexpr =
  | [stmt] ++ tl ->
    bind_ (compileProbTimeStmt env stmt) (compileProbTimeStmts env inexpr tl)
  | [] ->
    inexpr

  sem compileProbTimeStmt : Env -> PTStmt -> Expr
  sem compileProbTimeStmt env =
  | PTSObserve {e = e, dist = dist, info = info} ->
    let obsExpr = TmObserve {
      value = compileProbTimeExpr e, dist = compileProbTimeExpr dist,
      ty = ityunknown_ info, info = info
    } in
    withInfoRec info (nulet_ (nameNoSym "") obsExpr)
  | PTSAssume {id = id, dist = dist, info = info} ->
    let assumeExpr = TmAssume {
      dist = compileProbTimeExpr dist, ty = ityunknown_ info, info = info
    } in
    withInfoRec info (nulet_ id assumeExpr)
  | PTSInfer {id = id, model = model, particles = particles, info = info} ->
    let p = nameNoSym "p" in
    let inferModelId = nameNoSym "inferModel" in
    let inferExpr = TmInfer {
      method = BPF {particles = nvar_ p},
      model = nulam_ (nameNoSym "") (compileProbTimeExpr model),
      ty = ityunknown_ info, info = info
    } in
    let inferModelBind = nulet_ inferModelId (nulam_ p inferExpr) in
    let distTy = TyDist {ty = ityunknown_ info, info = info} in
    let distBind =
      match particles with Some p then
        let p = compileProbTimeExpr p in
        nlet_ id distTy (app_ (nvar_ inferModelId) p)
      else
        -- NOTE(larshum, 2024-10-31): We use this term to defer the interaction
        -- with runtime functions until a later stage in the compilation.
        let configurableInfer = TmConfigurableInfer {
          model = inferModelId, ty = distTy, info = info
        } in
        nlet_ id distTy configurableInfer
    in
    withInfoRec info (bindall_ [inferModelBind, distBind])
  | PTSDegenerate {info = info} ->
    -- NOTE(larshum, 2024-10-31): We use a small negative value instead of the
    -- actual negative infinity to ensure the weight of the particle ends up
    -- being very small, but not zero. This prevents potential situations where
    -- all particles have probability zero.
    let weightExpr = TmWeight {
      weight = float_ (negf 1e300), ty = ityunknown_ info, info = info
    } in
    withInfoRec info (nulet_ (nameNoSym "") weightExpr)
  | PTSResample {info = info} ->
    let resampleExpr = TmResample {
      ty = ityunknown_ info, info = info
    } in
    withInfoRec info (nulet_ (nameNoSym "") resampleExpr)
  | PTSRead {port = port, dst = dst, info = info} ->
    let readExpr = TmRead {
      label = port, ty = ityunknown_ info, info = info
    } in
    withInfoRec info (nulet_ dst readExpr)
  | PTSWrite {src = src, port = port, delay = delay, info = info} ->
    let delay =
      match delay with Some d then compileProbTimeExpr d
      else int_ 0
    in
    let src = compileProbTimeExpr src in
    let writeExpr = TmWrite {
      label = port, src = src, delay = delay, ty = ityunknown_ info, info = info
    } in
    withInfoRec info (nulet_ (nameNoSym "") writeExpr)
  | PTSDelay {ns = ns, info = info} ->
    let delayExpr = TmSdelay {
      e = compileProbTimeExpr ns, ty = ityunknown_ info, info = info
    } in
    withInfoRec info (nulet_ (nameNoSym "") delayExpr)
  | PTSBinding {id = id, ty = ty, e = e, info = info} ->
    let ty =
      match ty with Some ty then compileProbTimeType ty
      else ityunknown_ info
    in
    withInfoRec info (nlet_ id ty (compileProbTimeExpr e))
  | PTSCondition {cond = cond, upd = upd, thn = thn, els = els, info = info} ->
    match
      match upd with Some id then (id, nvar_ id)
      else (nameNoSym "", unit_)
    with (targetId, tailExpr) in
    let cond = compileProbTimeExpr cond in
    let thn = compileProbTimeStmts env tailExpr thn in
    let els = compileProbTimeStmts env tailExpr els in
    let condExpr = if_ cond thn els in
    withInfoRec info (nulet_ targetId condExpr)
  | PTSForLoop {id = id, e = e, upd = upd, body = body, info = info} ->
    match
      match upd with Some updId then (updId, nvar_ updId)
      else (nameNoSym "", unit_)
    with (loopVarId, tailExpr) in
    let body = compileProbTimeStmts env tailExpr body in
    let funExpr = nulam_ loopVarId (nulam_ id body) in
    let e = compileProbTimeExpr e in
    withInfoRec info (nulet_ loopVarId (foldl_ funExpr tailExpr e))
  | PTSWhileLoop {cond = cond, upd = upd, body = body, info = info} ->
    match
      match upd with Some updId then (updId, nvar_ updId)
      else (nameNoSym "", unit_)
    with (loopVarId, tailExpr) in
    let loopId = nameSym "loopFn" in
    let recursiveCall = app_ (nvar_ loopId) tailExpr in
    let cond = compileProbTimeExpr cond in
    let body = compileProbTimeStmts env recursiveCall body in
    let loopBody = if_ cond body tailExpr in
    let resultBinding = nulet_ loopVarId recursiveCall in
    withInfoRec info
      (bind_ (nureclets_ [(loopId, nulam_ loopVarId body)]) resultBinding)
  | PTSAssign {target = target, e = e, info = info} ->
    let e = compileProbTimeExpr e in
    match
      match target with PTEVar {id = id, info = i1} then
        (id, e)
      else match target with PTEProjection {id = id, proj = proj, info = i1} then
        (id, recordupdate_ (nvar_ id) proj e)
      else errorSingle [ptExprInfo target] "Invalid target of assignment statement"
    with (id, body) in
    withInfoRec info (nulet_ id body)
  | PTSFunctionCall {id = id, args = args, info = info} ->
    let args = if null args then [unit_] else map compileProbTimeExpr args in
    withInfoRec info (appSeq_ (nvar_ id) args)
end

lang ProbTimeCodegenTop =
  ProbTimeTopAst + ProbTimeCodegenStmt + ProbTimeCodegenType +
  ProbTimeCodegenExpr

  sem compileProbTimeTop : Env -> PTTop -> (Env, Expr)
  sem compileProbTimeTop env =
  | PTTConstant {id = id, ty = ty, e = e, info = info} ->
    let ty = compileProbTimeType ty in
    let e = compileProbTimeExpr e in
    (env, withInfoRec info (nlet_ id ty e))
  | PTTTypeAlias {id = id, ty = ty, info = info} ->
    -- let env = {env with aliases = mapInsert id ty env.aliases} in
    let ty = compileProbTimeType ty in
    (env, withInfoRec info (ntype_ id [] ty))
  | PTTFunDef {id = id, params = params, ty = ty, body = body,
               return = return, funKind = funKind, info = info} ->
    let params = compileProbTimeParams info params in
    let ty = compileProbTimeType ty in
    let tyAnnot = foldl (lam acc. lam p. ityarrow_ info p.1 acc) ty params in
    let return =
      match return with Some e then compileProbTimeExpr e
      else unit_
    in
    -- TODO: Handle template definitions in a slightly different way, by
    --   1. Escaping the template name to avoid shadowing - this can happen
    --      when the name of a template is the same as a function defined in
    --      the runtime.
    --   2. Ensure the task template has at most one use of infer.
    --   3. Passing along the template name in the environment so that this is
    --      known when compiling expressions.
    let body = compileProbTimeStmts env return body in
    let addParamToBody = lam acc. lam p.
      match p with (paramId, paramTy, info) in
      TmLam {
        ident = paramId, tyAnnot = ityunknown_ info, tyParam = paramTy,
        body = acc, ty = ityarrow_ info paramTy (tyTm acc), info = info }
    in
    let body = foldl addParamToBody body params in
    (env, nlet_ id tyAnnot body)

  sem compileProbTimeParams : Info -> [PTParam] -> [(Name, Type, Info)]
  sem compileProbTimeParams info =
  | params ->
    if null params then [(nameNoSym "", tyunit_, info)]
    else reverse (map compileParam params)

  sem compileParam : PTParam -> (Name, Type, Info)
  sem compileParam =
  | {id = id, ty = ty, info = info} ->
    (id, compileProbTimeType ty, info)
end

lang ProbTimeCodegenSystem = ProbTimeCodegenBase
  sem compileSystem : Env -> PTMain -> CompileResult
  sem compileSystem env =
  | _ -> error "compileSystem not implemented yet"
end

lang ProbTimeCodegen =
  ProbTimeCodegenTop + ProbTimeCodegenSystem + ProbTimeAst + ProbTimeRuntime +
  MExprLambdaLift + MExprTypeCheck + MExprEliminateDuplicateCode + MExprSym

  sem compileProbTimeProgram : RtpplOptions -> PTProgram -> CompileResult
  sem compileProbTimeProgram options =
  | {tops = tops, system = system} ->
    match compileProbTimeToExpr options tops with (llSolutions, topEnv, expr) in
    expr
    --compileSystem env system

  sem compileProbTimeToExpr : RtpplOptions -> [PTTop]
                           -> (Map Name LambdaLiftSolution, Env, Expr)
  sem compileProbTimeToExpr options =
  | tops ->
    match mapAccumL compileProbTimeTop () tops
    with (topEnv, exprs) in
    let probTimeExpr = bindall_ exprs in
    let runtime = loadProbTimeRuntime () in
    let runtimeSymEnv = addTopNames symEnvEmpty runtime in
    let probTimeExpr = symbolizeExpr runtimeSymEnv probTimeExpr in
    let ast = eliminateDuplicateCode (bind_ runtime probTimeExpr) in
    let ast = typeCheck ast in
    match liftLambdasWithSolutions ast with (solutions, ast) in
    (solutions, topEnv, ast)
end
