include "ast.mc"

include "seq.mc"

lang RtpplTaskPeriod = RtpplAst
  type TemplateData = (RtpplExpr, [Name])

  sem findProgramTaskPeriods : RtpplProgram -> Map Name Int
  sem findProgramTaskPeriods =
  | ProgramRtpplProgram p ->
    let templateData = foldl findTaskTemplateData (mapEmpty nameCmp) p.tops in
    findTaskPeriods templateData p.main

  sem findTaskPeriods : Map Name TemplateData -> RtpplMain -> Map Name Int
  sem findTaskPeriods templateData =
  | MainRtpplMain {tasks = tasks} ->
    foldl (findTaskPeriod templateData) (mapEmpty nameCmp) tasks

  sem findTaskPeriod : Map Name TemplateData -> Map Name Int -> RtpplTask -> Map Name Int
  sem findTaskPeriod templateData taskPeriods =
  | TaskRtpplTask {id = {v = id}, templateId = {v = tid}, args = args, info = info} ->
    match mapLookup tid templateData with Some (periodExpr, paramIds) then
      let argMap = mapFromSeq nameCmp (zip paramIds args) in
      let period = resolvePeriod info argMap periodExpr in
      mapInsert id period taskPeriods
    else
      errorSingle [info] "Task is defined in terms of unknown task template"

  sem resolvePeriod : Info -> Map Name RtpplExpr -> RtpplExpr -> Int
  sem resolvePeriod info argMap =
  | LiteralRtpplExpr {const = LitIntRtpplConst {value = {v = i}}} -> i
  | IdentPlusExprRtpplExpr {id = {v = id}, next = VariableRtpplExprNoIdent _} ->
    match mapLookup id argMap with Some expr then
      resolvePeriod info argMap expr
    else
      errorSingle [info] "Could not determine the task period statically"
  | _ ->
    errorSingle [info] "Could not determine the task period statically"

  sem findTaskTemplateData : Map Name TemplateData -> RtpplTop -> Map Name TemplateData
  sem findTaskTemplateData acc =
  | TemplateDefRtpplTop {id = {v = id}, body = b, params = params, info = info} ->
    let period = findTaskTemplatePeriod info b.periodic in
    let paramIds =
      match params with ParamsRtpplTopParams {params = params} then
        map (lam p. p.id.v) params
      else errorSingle [info] "Could not extract parameter names of task template"
    in
    mapInsert id (period, paramIds) acc
  | _ -> acc

  sem findTaskTemplatePeriod : Info -> RtpplPeriodic -> RtpplExpr
  sem findTaskTemplatePeriod info =
  | PeriodicRtpplPeriodic {period = period} -> period
end

lang RtpplTaskPriority = RtpplAst
  sem findProgramTaskPriorities : RtpplProgram -> Map Name Float
  sem findProgramTaskPriorities =
  | ProgramRtpplProgram p ->
    findTaskPriorities p.main

  sem findTaskPriorities : RtpplMain -> Map Name Float
  sem findTaskPriorities =
  | MainRtpplMain {tasks = tasks} ->
    foldl findTaskPriority (mapEmpty nameCmp) tasks

  sem findTaskPriority : Map Name Float -> RtpplTask -> Map Name Float
  sem findTaskPriority priorities =
  | TaskRtpplTask {id = {v = id}, p = {v = priority}} ->
    mapInsert id (int2float priority) priorities
end

lang RtpplTaskInfers = RtpplAst
  sem countProgramTaskInfers : RtpplProgram -> Map Name Int
  sem countProgramTaskInfers =
  | ProgramRtpplProgram p ->
    let templateEnv = foldl countTemplateInfers (mapEmpty nameCmp) p.tops in
    countMainTaskInfers templateEnv p.main

  sem countMainTaskInfers : Map Name Int -> RtpplMain -> Map Name Int
  sem countMainTaskInfers templateEnv =
  | MainRtpplMain {tasks = tasks} ->
    foldl (findTaskInferCount templateEnv) (mapEmpty nameCmp) tasks

  sem findTaskInferCount : Map Name Int -> Map Name Int -> RtpplTask -> Map Name Int
  sem findTaskInferCount templateEnv acc =
  | TaskRtpplTask {id = {v = id}, templateId = {v = tid}, info = info} ->
    match mapLookup tid templateEnv with Some count then
      mapInsert id count acc
    else errorSingle [info] "Task is defined in terms of unknown task template"

  sem countTemplateInfers : Map Name Int -> RtpplTop -> Map Name Int
  sem countTemplateInfers env =
  | TemplateDefRtpplTop {id = {v = id}, body = {periodic = periodic}, info = info} ->
    let maxInt = lam l. lam. lam r. if gti l r then l else r in
    let infers = collectInfersInPeriodic periodic in
    let count = addi (mapFoldWithKey maxInt 0 infers) 1 in
    mapInsert id count env
  | _ ->
    env

  sem collectInfersInPeriodic : RtpplPeriodic -> Map Info Int
  sem collectInfersInPeriodic =
  | PeriodicRtpplPeriodic {body = body} -> collectInfersFromStatements body

  sem collectInfersFromStatements : [RtpplStmt] -> Map Info Int
  sem collectInfersFromStatements =
  | stmts ->
    match foldl collectStatementInfers (0, mapEmpty infoCmp) stmts with (_, env) in
    env

  sem collectStatementInfers : (Int, Map Info Int) -> RtpplStmt -> (Int, Map Info Int)
  sem collectStatementInfers acc =
  | InferRtpplStmt {info = info} ->
    match acc with (nextIdx, env) in
    (addi nextIdx 1, mapInsert info nextIdx env)
  | stmt ->
    sfold_RtpplStmt_RtpplStmt collectStatementInfers acc stmt
end

lang RtpplTaskData = RtpplTaskPeriod + RtpplTaskPriority + RtpplTaskInfers
  type TaskData = {
    period : Int,
    priority : Float
  }

  sem collectProgramTaskData : RtpplProgram -> Map Name TaskData
  sem collectProgramTaskData =
  | p & (ProgramRtpplProgram _) ->
    let taskPeriods = findProgramTaskPeriods p in
    let taskPriorities = findProgramTaskPriorities p in
    mapMerge
      (lam l. lam r.
        match (l, r) with (Some lhs, Some rhs) then
          Some {period = lhs, priority = rhs}
        else
          error "Internal error collecting task data")
      taskPeriods taskPriorities
end
