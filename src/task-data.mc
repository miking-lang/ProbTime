include "ast.mc"

include "seq.mc"

lang RtpplTaskPeriod = RtpplAst
  type TemplateData = (Option RtpplExpr, [Name])

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
      -- NOTE(larshum, 2024-10-17): We assign the period 0 to represent a task
      -- that is found to not be periodic with a statically known value.
      let period =
        match periodExpr with Some p then
          resolvePeriod info argMap p
        else 0
      in
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
  | TemplateDefRtpplTop {id = {v = id}, body = {body = body}, params = params, info = info} ->
    let period = findTaskTemplatePeriod info body in
    let paramIds =
      match params with ParamsRtpplTopParams {params = params} then
        map (lam p. p.id.v) params
      else errorSingle [info] "Could not extract parameter names of task template"
    in
    mapInsert id (period, paramIds) acc
  | _ -> acc

  -- Attempts to find the period of a task. First, the final statement of a
  -- peridic task must be an infinite loop. Second, it must contain exactly one
  -- use of a delay, in which case its expression is returned.
  sem findTaskTemplatePeriod : Info -> [RtpplStmt] -> Option RtpplExpr
  sem findTaskTemplatePeriod info =
  | stmts ++ [ WhileLoopRtpplStmt {
        cond = LiteralRtpplExpr {const = LitBoolRtpplConst {value = {v = true}}},
        body = body } ] ->
    let acc = foldl findDelayExpressions [] body in
    -- NOTE(larshum, 2024-10-17): If we have exactly one delay in the loop,
    -- we return its expression. Otherwise, we consider the loop to not be
    -- periodic.
    match acc with [delayExpr] then Some delayExpr else None ()

  sem findDelayExpressions : [RtpplExpr] -> RtpplStmt -> [RtpplExpr]
  sem findDelayExpressions acc =
  | DelayRtpplStmt {ns = ns} -> cons ns acc
  | stmt -> sfold_RtpplStmt_RtpplStmt findDelayExpressions acc stmt
end

lang RtpplTaskPriority = RtpplAst
  sem findProgramTaskPriorities : RtpplProgram -> Map Name Float
  sem findProgramTaskPriorities =
  | ProgramRtpplProgram p ->
    let priorities = findTaskPriorities p.main in
    let sum = foldl addf 0.0 (mapValues priorities) in
    mapMapWithKey (lam. lam p. normalizedPriority sum p) priorities

  sem findTaskPriorities : RtpplMain -> Map Name Float
  sem findTaskPriorities =
  | MainRtpplMain {tasks = tasks} ->
    foldl findTaskPriority (mapEmpty nameCmp) tasks

  sem findTaskPriority : Map Name Float -> RtpplTask -> Map Name Float
  sem findTaskPriority priorities =
  | TaskRtpplTask {id = {v = id}, p = {v = priority}} ->
    mapInsert id (int2float priority) priorities

  sem normalizedPriority : Float -> Float -> Float
  sem normalizedPriority prioritySum =
  | priority ->
    divf priority prioritySum
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
  | TemplateDefRtpplTop {id = {v = id}, body = {body = body}, info = info} ->
    let maxInt = lam l. lam. lam r. if gti l r then l else r in
    let infers = collectInfersWithoutParticles body in
    let count = addi (mapFoldWithKey maxInt 0 infers) 1 in
    mapInsert id count env
  | _ ->
    env

  -- Collects all infers for which the number of particles are not explicitly
  -- specified. These are the ones we need to configure to find the number of
  -- particles.
  sem collectInfersWithoutParticles : [RtpplStmt] -> Map Info Int
  sem collectInfersWithoutParticles =
  | stmts ->
    match foldl collectInfersWithoutParticlesHelper (0, mapEmpty infoCmp) stmts
    with (_, env) in
    env

  sem collectInfersWithoutParticlesHelper : (Int, Map Info Int) -> RtpplStmt
                                         -> (Int, Map Info Int)
  sem collectInfersWithoutParticlesHelper acc =
  | InferRtpplStmt {p = None _, info = info} ->
    match acc with (nextIdx, env) in
    (addi nextIdx 1, mapInsert info nextIdx env)
  | stmt ->
    sfold_RtpplStmt_RtpplStmt collectInfersWithoutParticlesHelper acc stmt
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
