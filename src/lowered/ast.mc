include "map.mc"
include "name.mc"
include "mexpr/info.mc"

lang ProbTimeBaseAst
  type SMapAccumL a b acc = (acc -> b -> (acc, b)) -> acc -> a -> (acc, a)
  type SMap a b = (b -> b) -> a -> a
  type SFold a b acc = (acc -> b -> acc) -> acc -> a -> acc
end

lang ProbTimeBinOpAst
  syn PTBinOp =
  | PTBAdd ()
  | PTBSub ()
  | PTBMul ()
  | PTBDiv ()
  | PTBEq ()
  | PTBNeq ()
  | PTBLt ()
  | PTBGt ()
  | PTBLeq ()
  | PTBGeq ()
  | PTBAnd ()
  | PTBOr ()
end

lang ProbTimeConstAst
  syn PTConst =
  | PTCInt {value : Int}
  | PTCFloat {value : Float}
  | PTCBool {value : Bool}
  | PTCString {value : String}
end

lang ProbTimeExprAst = ProbTimeConstAst + ProbTimeBinOpAst
  syn PTExpr =
  -- PPL expressions
  | PTEDistSamples {e : PTExpr, info : Info}
  | PTEGaussianDist {mu : PTExpr, sigma : PTExpr, info : Info}
  | PTEUniformDist {lo : PTExpr, hi : PTExpr, info : Info}
  | PTEBernoulliDist {p : PTExpr, info : Info}
  | PTEGammaDist {k : PTExpr, theta : PTExpr, info : Info}
  -- General expressions
  | PTEVar {id : Name, info : Info}
  | PTEFunctionCall {id : Name, args : [PTExpr], info : Info}
  | PTEProjection {id : Name, proj : String, info : Info}
  | PTEArrayAccess {e : PTExpr, idx : PTExpr, info : Info}
  | PTEArrayLiteral {elems : [PTExpr], info : Info}
  | PTERecordLiteral {fields : Map String PTExpr, info : Info}
  | PTELiteral {const : PTConst, info : Info}
  | PTELength {e : PTExpr, info : Info}
  | PTEBinOp {lhs : PTExpr, rhs : PTExpr, op : PTBinOp, info : Info}

  sem ptExprInfo : PTExpr -> Info
  sem ptExprInfo =
  | PTEDistSamples t -> t.info
  | PTEGaussianDist t -> t.info
  | PTEUniformDist t -> t.info
  | PTEBernoulliDist t -> t.info
  | PTEGammaDist t -> t.info
  | PTEVar t -> t.info
  | PTEFunctionCall t -> t.info
  | PTEProjection t -> t.info
  | PTEArrayAccess t -> t.info
  | PTEArrayLiteral t -> t.info
  | PTERecordLiteral t -> t.info
  | PTELiteral t -> t.info
  | PTELength t -> t.info
  | PTEBinOp t -> t.info

  sem smapAccumLPTExprPTExpr : all a. SMapAccumL PTExpr PTExpr a
  sem smapAccumLPTExprPTExpr f acc =
  | PTEDistSamples t ->
    match f acc t.e with (acc, e) in
    (acc, PTEDistSamples {t with e = e})
  | PTEGaussianDist t ->
    match f acc t.mu with (acc, mu) in
    match f acc t.sigma with (acc, sigma) in
    (acc, PTEGaussianDist {t with mu = mu, sigma = sigma})
  | PTEUniformDist t ->
    match f acc t.lo with (acc, lo) in
    match f acc t.hi with (acc, hi) in
    (acc, PTEUniformDist {t with lo = lo, hi = hi})
  | PTEBernoulliDist t ->
    match f acc t.p with (acc, p) in
    (acc, PTEBernoulliDist {t with p = p})
  | PTEGammaDist t ->
    match f acc t.k with (acc, k) in
    match f acc t.theta with (acc, theta) in
    (acc, PTEGammaDist {t with k = k, theta = theta})
  | PTEVar t -> (acc, PTEVar t)
  | PTEFunctionCall t ->
    match mapAccumL f acc t.args with (acc, args) in
    (acc, PTEFunctionCall {t with args = args})
  | PTEProjection t -> (acc, PTEProjection t)
  | PTEArrayAccess t ->
    match f acc t.e with (acc, e) in
    match f acc t.idx with (acc, idx) in
    (acc, PTEArrayAccess {t with e = e, idx = idx})
  | PTEArrayLiteral t ->
    match mapAccumL f acc t.elems with (acc, elems) in
    (acc, PTEArrayLiteral {t with elems = elems})
  | PTERecordLiteral t ->
    let fField = lam acc. lam. lam v. f acc v in
    match mapMapAccum fField acc t.fields with (acc, fields) in
    (acc, PTERecordLiteral {t with fields = fields})
  | PTELiteral t -> (acc, PTELiteral t)
  | PTELength t ->
    match f acc t.e with (acc, e) in
    (acc, PTELength {t with e = e})
  | PTEBinOp t ->
    match f acc t.lhs with (acc, lhs) in
    match f acc t.rhs with (acc, rhs) in
    (acc, PTEBinOp {t with lhs = lhs, rhs = rhs})

  sem smapPTExprPTExpr : SMap PTExpr PTExpr
  sem smapPTExprPTExpr f =
  | e ->
    match smapAccumLPTExprPTExpr (lam. lam a. ((), f a)) () e
    with (_, e) in e

  sem sfoldPTExprPTExpr : all a. SFold PTExpr PTExpr a
  sem sfoldPTExprPTExpr f acc =
  | e ->
    match smapAccumLPTExprPTExpr (lam acc. lam a. (f acc a, a)) acc e
    with (acc, _) in acc
end

lang ProbTimeTypeAst = ProbTimeBaseAst
  syn PTType =
  | PTTInt {info : Info}
  | PTTFloat {info : Info}
  | PTTBool {info : Info}
  | PTTString {info : Info}
  | PTTUnit {info : Info}
  | PTTSeq {ty : PTType, info : Info}
  | PTTRecord {fields : Map String PTType, info : Info}
  | PTTFunction {from : PTType, to : PTType, info : Info}
  | PTTDist {ty : PTType, info : Info}
  | PTTAlias {id : Name, args : [PTType], info : Info}

  sem ptTypeInfo : PTType -> Info
  sem ptTypeInfo =
  | PTTInt t -> t.info
  | PTTFloat t -> t.info
  | PTTBool t -> t.info
  | PTTString t -> t.info
  | PTTUnit t -> t.info
  | PTTSeq t -> t.info
  | PTTRecord t -> t.info
  | PTTFunction t -> t.info
  | PTTDist t -> t.info
  | PTTAlias t -> t.info

  sem smapAccumLPTTypePTType : all a. SMapAccumL PTType PTType a
  sem smapAccumLPTTypePTType f acc =
  | PTTSeq t ->
    match f acc t.ty with (acc, ty) in
    (acc, PTTSeq {t with ty = ty})
  | PTTRecord t ->
    let fField = lam acc. lam. lam fieldValue. f acc fieldValue in
    match mapMapAccum fField acc t.fields with (acc, fields) in
    (acc, PTTRecord {t with fields = fields})
  | PTTFunction t ->
    match f acc t.from with (acc, from) in
    match f acc t.to with (acc, to) in
    (acc, PTTFunction {t with from = from, to = to})
  | PTTDist t ->
    match f acc t.ty with (acc, ty) in
    (acc, PTTDist {t with ty = ty})
  | PTTAlias t ->
    match mapAccumL f acc t.args with (acc, args) in
    (acc, PTTAlias {t with args = args})
  | ty -> (acc, ty)

  sem smapPTTypePTType : SMap PTType PTType
  sem smapPTTypePTType f =
  | ty ->
    match smapAccumLPTTypePTType (lam. lam a. ((), f a)) () ty
    with (_, ty) in ty

  sem sfoldPTTypePTType : all a. SFold PTType PTType a
  sem sfoldPTTypePTType f acc =
  | ty ->
    match smapAccumLPTTypePTType (lam acc. lam a. (f acc a, a)) acc ty
    with (acc, _) in acc

  sem eqPTType : PTType -> PTType -> Bool
  sem eqPTType lhs =
  | rhs ->
    if eqi (constructorTag lhs) (constructorTag rhs) then eqPTTypeH (lhs, rhs)
    else false

  sem eqPTTypeH : (PTType, PTType) -> Bool
  sem eqPTTypeH =
  | (PTTSeq {ty = lty}, PTTSeq {ty = rty}) ->
    eqPTType lty rty
  | (PTTRecord {fields = lfields}, PTTRecord {fields = rfields}) ->
    mapEq eqPTType lfields rfields
  | (PTTFunction {from = lfrom, to = lto}, PTTFunction {from = rfrom, to = rto}) ->
    and (eqPTType lfrom rfrom) (eqPTType lto rto)
  | (PTTDist {ty = lty}, PTTDist {ty = rty}) ->
    eqPTType lty rty
  | (PTTAlias {id = lid, args = largs}, PTTAlias {id = rid, args = rargs}) ->
    and (nameEq lid rid) (eqSeq eqPTType largs rargs)
  | _ -> true
end

lang ProbTimeStmtAst = ProbTimeTypeAst + ProbTimeExprAst
  -- NOTE(larshum, 2024-11-05): We represent the update variable using three
  -- distinct names. The first represents the name of the variable passed to
  -- the construct, the second is the name used inside the construct, and the
  -- third is the name used after the construct. We use these three to simplify
  -- code generation to MExpr.
  type UpdateEntry = Option {
    -- The identifier of the update variable passed to the construct.
    preId : Name,

    -- The identifier used for the update parameter in the body/bodies of the
    -- construct.
    bodyParamId : Name,

    -- The identifiers storing the name of the most recent value of the
    -- parameter, for each branch.
    bodyResultIds : (Name, Name),

    -- The identifier to which the result of the construct is stored and
    -- accessible in code following the construct.
    postId : Name
  }

  syn PTStmt =
  -- PPL statements
  | PTSObserve {e : PTExpr, dist : PTExpr, info : Info}
  | PTSAssume {id : Name, dist : PTExpr, info : Info}
  | PTSInfer {id : Name, model : PTExpr, particles : Option PTExpr, info : Info}
  | PTSDegenerate {info : Info}
  | PTSResample {info : Info}
  -- Real-time and communication statements
  | PTSRead {port : String, dst : Name, ty : PTType, info : Info}
  | PTSWrite {src : PTExpr, port : String, delay : Option PTExpr, info : Info}
  | PTSDelay {ns : PTExpr, info : Info}
  -- General statements
  | PTSBinding {id : Name, ty : Option PTType, e : PTExpr, info : Info}
  | PTSCondition {cond : PTExpr, upd : UpdateEntry, thn : [PTStmt], els : [PTStmt], info : Info}
  | PTSForLoop {id : Name, e : PTExpr, upd : UpdateEntry, body : [PTStmt], info : Info}
  | PTSWhileLoop {cond : PTExpr, upd : UpdateEntry, body : [PTStmt], info : Info}
  | PTSAssignVar {id : Name, e : PTExpr, info : Info}
  | PTSAssignProj {id : Name, label : String, e : PTExpr, resId : Name, info : Info}
  | PTSFunctionCall {id : Name, args : [PTExpr], info : Info}

  sem ptStmtInfo : PTStmt -> Info
  sem ptStmtInfo =
  | PTSObserve t -> t.info
  | PTSAssume t -> t.info
  | PTSInfer t -> t.info
  | PTSDegenerate t -> t.info
  | PTSResample t -> t.info
  | PTSRead t -> t.info
  | PTSWrite t -> t.info
  | PTSDelay t -> t.info
  | PTSBinding t -> t.info
  | PTSCondition t -> t.info
  | PTSForLoop t -> t.info
  | PTSWhileLoop t -> t.info
  | PTSAssignVar t -> t.info
  | PTSAssignProj t -> t.info
  | PTSFunctionCall t -> t.info

  sem smapAccumLPTStmtPTStmt : all a. SMapAccumL PTStmt PTStmt a
  sem smapAccumLPTStmtPTStmt f acc =
  | PTSCondition t ->
    match mapAccumL f acc t.thn with (acc, thn) in
    match mapAccumL f acc t.els with (acc, els) in
    (acc, PTSCondition {t with thn = thn, els = els})
  | PTSForLoop t ->
    match mapAccumL f acc t.body with (acc, body) in
    (acc, PTSForLoop {t with body = body})
  | PTSWhileLoop t ->
    match mapAccumL f acc t.body with (acc, body) in
    (acc, PTSWhileLoop {t with body = body})
  | stmt -> (acc, stmt)

  sem smapPTStmtPTStmt : SMap PTStmt PTStmt
  sem smapPTStmtPTStmt f =
  | stmt ->
    match smapAccumLPTStmtPTStmt (lam. lam a. ((), f a)) () stmt
    with (_, stmt) in stmt

  sem sfoldPTStmtPTStmt : all a. SFold PTStmt PTStmt a
  sem sfoldPTStmtPTStmt f acc =
  | stmt ->
    match smapAccumLPTStmtPTStmt (lam acc. lam a. (f acc a, a)) acc stmt
    with (acc, _) in acc

  sem smapAccumLPTStmtPTExpr : all a. SMapAccumL PTStmt PTExpr a
  sem smapAccumLPTStmtPTExpr f acc =
  | PTSObserve t ->
    match f acc t.e with (acc, e) in
    match f acc t.dist with (acc, dist) in
    (acc, PTSObserve {t with e = e, dist = dist})
  | PTSAssume t ->
    match f acc t.dist with (acc, dist) in
    (acc, PTSAssume {t with dist = dist})
  | PTSInfer t ->
    match f acc t.model with (acc, model) in
    match optionMapAccum f acc t.particles with (acc, particles) in
    (acc, PTSInfer {t with model = model, particles = particles})
  | PTSWrite t ->
    match f acc t.src with (acc, src) in
    match optionMapAccum f acc t.delay with (acc, delay) in
    (acc, PTSWrite {t with src = src, delay = delay})
  | PTSDelay t ->
    match f acc t.ns with (acc, ns) in
    (acc, PTSDelay {t with ns = ns})
  | PTSBinding t ->
    match f acc t.e with (acc, e) in
    (acc, PTSBinding {t with e = e})
  | PTSCondition t ->
    match f acc t.cond with (acc, cond) in
    (acc, PTSCondition {t with cond = cond})
  | PTSForLoop t ->
    match f acc t.e with (acc, e) in
    (acc, PTSForLoop {t with e = e})
  | PTSWhileLoop t ->
    match f acc t.cond with (acc, cond) in
    (acc, PTSWhileLoop {t with cond = cond})
  | PTSAssignVar t ->
    match f acc t.e with (acc, e) in
    (acc, PTSAssignVar {t with e = e})
  | PTSAssignProj t ->
    match f acc t.e with (acc, e) in
    (acc, PTSAssignProj {t with e = e})
  | PTSFunctionCall t ->
    match mapAccumL f acc t.args with (acc, args) in
    (acc, PTSFunctionCall {t with args = args})
  | stmt -> (acc, stmt)

  sem smapPTStmtPTExpr : SMap PTStmt PTExpr
  sem smapPTStmtPTExpr f =
  | stmt ->
    match smapAccumLPTStmtPTExpr (lam. lam a. ((), f a)) () stmt
    with (_, stmt) in stmt

  sem sfoldPTStmtPTExpr : SFold PTStmt PTExpr
  sem sfoldPTStmtPTExpr f acc =
  | stmt ->
    match smapAccumLPTStmtPTExpr (lam acc. lam a. (f acc a, a)) acc stmt
    with (acc, _) in acc

  sem smapAccumLPTStmtPTType : all a. SMapAccumL PTStmt PTType a
  sem smapAccumLPTStmtPTType f acc =
  | PTSRead t ->
    match f acc t.ty with (acc, ty) in
    (acc, PTSRead {t with ty = ty})
  | PTSBinding t ->
    match optionMapAccum f acc t.ty with (acc, ty) in
    (acc, PTSBinding {t with ty = ty})
  | stmt -> (acc, stmt)

  sem smapPTStmtPTType : SMap PTStmt PTType
  sem smapPTStmtPTType f =
  | stmt ->
    match smapAccumLPTStmtPTType (lam. lam a. ((), f a)) () stmt
    with (_, stmt) in stmt

  sem sfoldPTStmtPTType : SFold PTStmt PTType
  sem sfoldPTStmtPTType f acc =
  | stmt ->
    match smapAccumLPTStmtPTType (lam acc. lam a. (f acc a, a)) acc stmt
    with (acc, _) in acc
end

lang ProbTimeTopAst = ProbTimeStmtAst + ProbTimeTypeAst + ProbTimeExprAst
  syn PTTop =
  | PTTConstant {id : Name, ty : PTType, e : PTExpr, info : Info}
  | PTTTypeAlias {id : Name, ty : PTType, info : Info}
  | PTTFunDef {
      id : Name, params : [PTParam], ty : PTType, body : [PTStmt],
      return : Option PTExpr, funKind : PTFunKind, info : Info
    }

  type PTParam = { id : Name, ty : PTType, info : Info }

  syn PTFunKind =
  | PTKFunction ()
  | PTKProbModel ()
  | PTKTemplate {inputs : [PTPortDecl], outputs : [PTPortDecl]}

  type PTPortDecl = {label : String, ty : PTType, info : Info}

  sem ptTopInfo : PTTop -> Info
  sem ptTopInfo =
  | PTTConstant t -> t.info
  | PTTTypeAlias t -> t.info
  | PTTFunDef t -> t.info
end

lang ProbTimeMainAst = ProbTimeStmtAst + ProbTimeTypeAst + ProbTimeExprAst
  type PTMain = [PTNode]

  syn PTPort =
  | Sensor {id : Name, ty : PTType, info : Info}
  | Actuator {id : Name, ty : PTType, info : Info}
  | Task {id : Name, label : String, isOutput : Bool, ty : PTType, info : Info}

  sem ptPortInfo : PTPort -> Info
  sem ptPortInfo =
  | Sensor t -> t.info
  | Actuator t -> t.info
  | Task t -> t.info

  sem ptPortType : PTPort -> PTType
  sem ptPortType =
  | Sensor t -> t.ty
  | Actuator t -> t.ty
  | Task t -> t.ty

  sem ptPortName : PTPort -> String
  sem ptPortName =
  | Sensor t -> nameGetStr t.id
  | Actuator t -> nameGetStr t.id
  | Task t -> join [nameGetStr t.id, ".", t.label]

  sem isInputPort : PTPort -> Bool
  sem isInputPort =
  | Sensor _ -> false
  | Actuator _ -> true
  | Task t -> not t.isOutput

  sem isOutputPort : PTPort -> Bool
  sem isOutputPort =
  | Sensor _ -> true
  | Actuator _ -> false
  | Task t -> t.isOutput

  syn PTNode =
  | PTNSensor {id : Name, ty : PTType, rate : PTExpr, outputs : [PTPort], info : Info}
  | PTNActuator {id : Name, ty : PTType, rate : PTExpr, inputs : [PTPort], info : Info}
  | PTNTask {
      id : Name, template : Name, args : [PTExpr], inputs : Map String [PTPort],
      outputs : Map String [PTPort], info : Info
    }

  sem ptNodeInfo : PTNode -> Info
  sem ptNodeInfo =
  | PTNSensor t -> t.info
  | PTNActuator t -> t.info
  | PTNTask t -> t.info
end

lang ProbTimeAst = ProbTimeTopAst + ProbTimeMainAst
  type PTProgram = {
    tops : [PTTop],
    system : PTMain
  }
end

