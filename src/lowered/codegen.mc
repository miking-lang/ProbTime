-- Generates Miking DPPL code from the ProbTime AST.

include "ast.mc"
include "codegen-base.mc"
include "runtime.mc"
include "symbolize.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/duplicate-code-elimination.mc"
include "mexpr/extract.mc"
include "mexpr/lamlift.mc"
include "mexpr/type-check.mc"

include "coreppl::parser.mc"

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

  sem infoTm =
  | TmRead t -> t.info
  | TmWrite t -> t.info
  | TmSdelay t -> t.info

  sem tyTm =
  | TmRead t -> t.ty
  | TmWrite t -> t.ty
  | TmSdelay t -> t.ty

  sem withInfo info =
  | TmRead t -> TmRead {t with info = info}
  | TmWrite t -> TmWrite {t with info = info}
  | TmSdelay t -> TmSdelay {t with info = info}

  sem withType ty =
  | TmRead t -> TmRead {t with ty = ty}
  | TmWrite t -> TmWrite {t with ty = ty}
  | TmSdelay t -> TmSdelay {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmRead t -> (acc, TmRead t)
  | TmWrite t ->
    match f acc t.src with (acc, src) in
    match f acc t.delay with (acc, delay) in
    (acc, TmWrite {t with src = src, delay = delay})
  | TmSdelay t ->
    match f acc t.e with (acc, e) in
    (acc, TmSdelay {t with e = e})

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

  sem isAtomic =
  | TmRead _ -> true
  | TmWrite _ -> true
  | TmSdelay _ -> true

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
  ProbTimeStmtAst + ProbTimeRuntime

  sem compileProbTimeStmts : PTCompileEnv -> Expr -> [PTStmt] -> Expr
  sem compileProbTimeStmts env inexpr =
  | [stmt] ++ tl ->
    bind_ (compileProbTimeStmt env stmt) (compileProbTimeStmts env inexpr tl)
  | [] ->
    inexpr

  sem compileProbTimeStmt : PTCompileEnv -> PTStmt -> Expr
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
      model = ulam_ "" (compileProbTimeExpr model),
      ty = ityunknown_ info, info = info
    } in
    let inferModelBind = nulet_ inferModelId (nulam_ p inferExpr) in
    let distTy = TyDist {ty = ityunknown_ info, info = info} in
    let distBind =
      match particles with Some p then
        let p = compileProbTimeExpr p in
        nlet_ id distTy (app_ (nvar_ inferModelId) p)
      else
        -- NOTE(larshum, 2024-11-05): Use the runner defined in the runtime to
        -- run the inference. This runner determines the number of particles to
        -- use based on a configuration file, which allows us to adjust it
        -- after compilation (e.g., by the automatic configuration).
        let inferRunnerId = lookupRuntimeId "probTimeInferRunner" in
        nlet_ id distTy (app_ (nvar_ inferRunnerId) (nvar_ inferModelId))
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
  | PTSRead {port = port, dst = dst, ty = ty, info = info} ->
    let readExpr = TmRead {
      label = port, ty = ityunknown_ info, info = info
    } in
    let ty = compileProbTimeType ty in
    let readTy = tyseq_ (tytuple_ [tytuple_ [tyint_, tyint_], ty]) in
    withInfoRec info (nlet_ dst readTy readExpr)
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
    match getUpdParams upd with (preExpr, (thnTail, elsTail), bodyId, postId) in
    let cond = compileProbTimeExpr cond in
    let thn = compileProbTimeStmts env thnTail thn in
    let els = compileProbTimeStmts env elsTail els in
    let condExpr = app_ (nulam_ bodyId (if_ cond thn els)) preExpr in
    withInfoRec info (nulet_ postId condExpr)
  | PTSForLoop {id = id, e = e, upd = upd, body = body, info = info} ->
    match getUpdParams upd with (preExpr, (tailExpr, _), bodyId, postId) in
    let body = compileProbTimeStmts env tailExpr body in
    let funExpr = nulam_ bodyId (nulam_ id body) in
    let e = compileProbTimeExpr e in
    withInfoRec info (nulet_ postId (foldl_ funExpr preExpr e))
  | PTSWhileLoop {cond = cond, upd = upd, body = body, info = info} ->
    match getUpdParams upd with (preExpr, (thnExpr, elsExpr), bodyId, postId) in
    let loopId = nameSym "while" in
    let cond = compileProbTimeExpr cond in
    let body = compileProbTimeStmts env (app_ (nvar_ loopId) thnExpr) body in
    let loopBody = if_ cond body elsExpr in
    let resultBinding = nulet_ postId (app_ (nvar_ loopId) preExpr) in
    withInfoRec info
      (bind_ (nureclets_ [(loopId, nulam_ bodyId loopBody)]) resultBinding)
  | PTSAssignVar {id = id, e = e, info = info} ->
    let e = compileProbTimeExpr e in
    withInfoRec info (nulet_ id e)
  | PTSAssignProj {id = id, label = label, e = e, resId = resId, info = info} ->
    let e = compileProbTimeExpr e in
    withInfoRec info (nulet_ resId (recordupdate_ (nvar_ id) label e))
  | PTSFunctionCall {id = id, args = args, info = info} ->
    let args = if null args then [unit_] else map compileProbTimeExpr args in
    withInfoRec info (ulet_ "" (appSeq_ (nvar_ id) args))

  -- NOTE(larshum, 2024-11-05): Produce the expressions and names required to
  -- represent the various components of the update term:
  --  1. A variable representing the value prior to the construct.
  --  2. Variables representing the final result for each separate branch of
  --     the construct.
  --  3. The name used for the corresponding parameter, in the body of the
  --     construct.
  --  4. The name used for storing the result and which we refer to in code
  --     after the construct.
  sem getUpdParams : UpdateEntry -> (Expr, (Expr, Expr), Name, Name)
  sem getUpdParams =
  | Some {preId = preId, bodyParamId = bodyParamId,
          bodyResultIds = (fst, snd), postId = postId} ->
    (nvar_ preId, (nvar_ fst, nvar_ snd), bodyParamId, postId)
  | None _ ->
    let id = nameNoSym "" in
    (uunit_, (uunit_, uunit_), id, id)
end

lang ProbTimeCodegenTop =
  ProbTimeTopAst + ProbTimeCodegenStmt + ProbTimeCodegenType +
  ProbTimeCodegenExpr

  sem compileProbTimeTop : PTCompileEnv -> PTTop -> (PTCompileEnv, Expr)
  sem compileProbTimeTop env =
  | PTTConstant {id = id, ty = ty, e = e, info = info} ->
    let env = {env with consts = mapInsert id (resolveConstants env.consts e) env.consts} in
    let ty = compileProbTimeType ty in
    let e = compileProbTimeExpr e in
    (env, withInfoRec info (nlet_ id ty e))
  | PTTTypeAlias {id = id, ty = ty, info = info} ->
    let env = {env with aliases = mapInsert id ty env.aliases} in
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
    let env =
      match funKind with PTKTemplate t then
        {env with templates = mapInsert id t env.templates}
      else env
    in
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

  sem resolveConstants : Map Name PTExpr -> PTExpr -> PTExpr
  sem resolveConstants consts =
  | var & PTEVar {id = id} ->
    match mapLookup id consts with Some e then e else var
  | e -> smapPTExprPTExpr (resolveConstants consts) e
end

lang ProbTimeCodegenSystem =
  ProbTimeCodegenExpr + ProbTimeCodegenTop + ProbTimeMainAst +
  ProbTimeRuntime + ProbTimeGenerateRuntime + MExprExtract

  sem compileSystem : PTCompileEnv -> PTMain -> Map Name Expr
  sem compileSystem env =
  | nodes ->
    foldl (compileTask env) (mapEmpty nameCmp) nodes

  sem compileTask : PTCompileEnv -> CompileResult -> PTNode -> CompileResult
  sem compileTask env acc =
  | (PTNTask {id = id, template = template, args = args, inputs = inputs,
              outputs = outputs, importance = importance, info = info}) & task ->
    let args = map (resolveConstants env.consts) args in
    let liftedArgsTask = getCapturedTopLevelVars info env template in
    let args = join [
      liftedArgsTask,
      if null args then [var_ ""] else map compileProbTimeExpr args
    ] in
    let taskRun = appSeq_ (nvar_ template) args in
    let runtimeInitId = lookupRuntimeId "rtpplRuntimeInit" in
    let liftedArgsInit = getCapturedTopLevelVars info env runtimeInitId in
    let initArgs =
      concat
        liftedArgsInit
        [ nvar_ updateInputsId
        , nvar_ closeFileDescriptorsId
        , str_ (nameGetStr id)
        , ulam_ "" taskRun ]
    in
    let tailExpr = appSeq_ (nvar_ (lookupRuntimeId "rtpplRuntimeInit")) initArgs in
    let runtimeAst = generateTaskSpecificRuntime env task in
    let ast = insertBindingsAt (nameEq runtimeInitId) runtimeAst env.ast in
    let ast = specializeProbTimeExprs env ast in
    let ast = extractAst (identifiersInExpr (setEmpty nameCmp) tailExpr) ast in
    let ast = symbolize ast in
    mapInsert id (bind_ ast tailExpr) acc
  | _ -> acc

  sem identifiersInExpr : Set Name -> Expr -> Set Name
  sem identifiersInExpr acc =
  | TmVar {ident = ident} -> setInsert ident acc
  | t -> sfold_Expr_Expr identifiersInExpr acc t

  sem insertBindingsAt : (Name -> Bool) -> Expr -> Expr -> Expr
  sem insertBindingsAt shouldInsertAt binds =
  | TmLet t ->
    if shouldInsertAt t.ident then
      TmLet {t with inexpr = bind_ binds t.inexpr}
    else
      TmLet {t with inexpr = insertBindingsAt shouldInsertAt binds t.inexpr}
  | t -> smap_Expr_Expr (insertBindingsAt shouldInsertAt binds) t

  sem getCapturedTopLevelVars : Info -> PTCompileEnv -> Name -> [Expr]
  sem getCapturedTopLevelVars info env =
  | id ->
    match mapLookup id env.llSolutions with Some argMap then
      let argIds = mapKeys argMap.vars in
      map
        (lam id.
          let s = nameGetStr id in
          match mapLookup s env.topVarEnv with Some topLevelId then
            nvar_ topLevelId
          else
            errorSingle [info]
              (concat "Could not find top-level binding of parameter " (nameGetStr id)))
        argIds
    else
      errorSingle [info]
        (concat "Could not find lambda lifted arguments for task " (nameGetStr id))

  sem specializeProbTimeExprs : PTCompileEnv -> Expr -> Expr
  sem specializeProbTimeExprs env =
  | TmRead t ->
    let target = deref_ (nvar_ inputSeqsId) in
    withInfoRec t.info (unsafeCoerce_ (recordproj_ t.label target))
  | TmWrite t ->
    let tsv =
      let tsvId = lookupRuntimeId "tsv" in
      let capturedArgs = getCapturedTopLevelVars t.info env tsvId in
      let args = join [capturedArgs, [t.delay, t.src]] in
      appSeq_ (nvar_ tsvId) args
    in
    let outputsExpr = deref_ (nvar_ outputSeqsId) in
    let outId = nameNoSym "out" in
    let recUpdExpr =
      recordupdate_ (nvar_ outId) t.label
        (cons_ tsv (recordproj_ t.label (nvar_ outId)))
    in
    withInfoRec t.info
      (bind_ (nulet_ outId outputsExpr) (modref_ (nvar_ outputSeqsId) recUpdExpr))
  | TmSdelay t ->
    let sdelayId = lookupRuntimeId "sdelay" in
    let liftedArgs = getCapturedTopLevelVars t.info env sdelayId in
    let sdelay = appSeq_ (nvar_ sdelayId) liftedArgs in
    withInfoRec t.info
      (appf3_ sdelay (nvar_ flushOutputsId) (nvar_ updateInputsId) t.e)
  | t -> smap_Expr_Expr (specializeProbTimeExprs env) t
end

lang ProbTimeCodegen =
  ProbTimeCodegenTop + ProbTimeCodegenSystem + ProbTimeAst + ProbTimeRuntime +
  MExprLambdaLift + MExprTypeCheck + MExprEliminateDuplicateCode + ProbTimeSym + MExprSym

  sem compileProbTimeProgram : RtpplOptions -> PTProgram -> CompileResult
  sem compileProbTimeProgram options =
  | program ->
    let runtime = loadProbTimeRuntime () in
    let runtimeSymEnv = addTopNames symEnvEmpty runtime in
    let program = symbolizeProbTime runtimeSymEnv program in
    let env = compileProbTimeToExpr options runtime program.tops in
    compileSystem env program.system

  sem compileProbTimeToExpr : RtpplOptions -> Expr -> [PTTop] -> PTCompileEnv
  sem compileProbTimeToExpr options runtime =
  | tops ->
    let emptyEnv = emptyPTCompileEnv options in
    match mapAccumL compileProbTimeTop emptyEnv tops
    with (env, exprs) in
    let mainAst = bindall_ exprs in
    let ast = bind_ runtime mainAst in
    let ast = symbolizeExpr symEnvEmpty ast in
    let ast = eliminateDuplicateCode ast in
    let ast = typeCheck ast in
    match liftLambdasWithSolutions ast with (solutions, ast) in
    {env with llSolutions = solutions,
              topVarEnv = (addTopNames symEnvEmpty ast).currentEnv.varEnv,
              ast = ast}
end
