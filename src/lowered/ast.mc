include "map.mc"
include "name.mc"
include "mexpr/info.mc"

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
end

lang ProbTimeTypeAst
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
end

lang ProbTimeStmtAst = ProbTimeTypeAst + ProbTimeExprAst
  syn PTStmt =
  -- PPL statements
  | PTSObserve {e : PTExpr, dist : PTExpr, info : Info}
  | PTSAssume {id : Name, dist : PTExpr, info : Info}
  | PTSInfer {id : Name, model : PTExpr, particles : Option PTExpr, info : Info}
  | PTSDegenerate {info : Info}
  | PTSResample {info : Info}
  -- Real-time and communication statements
  | PTSRead {port : String, dst : Name, info : Info}
  | PTSWrite {src : PTExpr, port : String, delay : Option PTExpr, info : Info}
  | PTSDelay {ns : PTExpr, info : Info}
  -- General statements
  | PTSBinding {id : Name, ty : Option PTType, e : PTExpr, info : Info}
  | PTSCondition {cond : PTExpr, upd : Option Name, thn : [PTStmt], els : [PTStmt], info : Info}
  | PTSForLoop {id : Name, e : PTExpr, upd : Option Name, body : [PTStmt], info : Info}
  | PTSWhileLoop {cond : PTExpr, upd : Option Name, body : [PTStmt], info : Info}
  | PTSAssign {target : PTExpr, e : PTExpr, info : Info}
  | PTSFunctionCall {id : Name, args : [PTExpr], info : Info}
  | PTSReturn {e : PTExpr, info : Info}

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
  | PTSAssign t -> t.info
  | PTSFunctionCall t -> t.info
  | PTSReturn t -> t.info
end

lang ProbTimeTopAst = ProbTimeStmtAst + ProbTimeTypeAst + ProbTimeExprAst
  syn PTTop =
  | PTTConstant {id : Name, ty : PTType, e : PTExpr, info : Info}
  | PTTTypeAlias {id : Name, ty : PTType, info : Info}
  | PTTFunDef {
      id : Name, params : [PTParam], ty : PTType, body : [PTStmt],
      funKind : PTFunKind, info : Info
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
  | Sensor {id : Name, info : Info}
  | Actuator {id : Name, info : Info}
  | Task {id : Name, label : String, isOutput : Bool, info : Info}

  sem ptPortInfo : PTPort -> Info
  sem ptPortInfo =
  | Sensor t -> t.info
  | Actuator t -> t.info
  | Task t -> t.info

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
      outputs : Map String [PTPort], importance : Int, minDelay : Int,
      maxDelay : Int, info : Info
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

