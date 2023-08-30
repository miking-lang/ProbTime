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
      errorSingle [info] "Could not resolve period of task"
  | _ ->
    errorSingle [info] "Could not resolve period of task"

  sem findTaskTemplateData : Map Name TemplateData -> RtpplTop -> Map Name TemplateData
  sem findTaskTemplateData acc =
  | TemplateDefRtpplTop {id = {v = id}, body = b, params = params, info = info} ->
    let period = findTaskTemplatePeriod info b.stmts in
    let paramIds =
      match params with ParamsRtpplTopParams {params = params} then
        map (lam p. p.id.v) params
      else errorSingle [info] "Could not extract parameter names of task template"
    in
    mapInsert id (period, paramIds) acc
  | _ -> acc

  -- NOTE(larshum, 2023-08-28): We assume task templates are periodic and
  -- defined in a particular shape, to simplify our analysis.
  sem findTaskTemplatePeriod : Info -> [RtpplStmt] -> RtpplExpr
  sem findTaskTemplatePeriod info =
  | _ ++ [LoopPlusStmtRtpplStmt {loop = InfLoopRtpplLoopStmt {body = body}, info = info}] ->
    match findLoopPeriod info (None ()) body with Some periodExpr then
      periodExpr
    else errorSingle [info] "Task template main loop is not periodic"
  | _ ->
    errorSingle [info] "Task template body does not end with an infinite loop"

  sem findLoopPeriod : Info -> Option RtpplExpr -> [RtpplStmt] -> Option RtpplExpr
  sem findLoopPeriod info acc =
  | [h] ++ stmts ->
    let acc =
      match h with SdelayRtpplStmt {e = e} then
        match acc with Some _ then
          errorSingle [info] "Task template main loop is not periodic"
        else
          Some e
      else acc
    in
    findLoopPeriod info acc stmts
  | [] -> acc
end

lang RtpplTaskPriority = RtpplAst
  sem findProgramTaskPriorities : RtpplProgram -> Map Name Int
  sem findProgramTaskPriorities =
  | ProgramRtpplProgram p ->
    findTaskPriorities p.main

  sem findTaskPriorities : RtpplMain -> Map Name Int
  sem findTaskPriorities =
  | MainRtpplMain {tasks = tasks} ->
    foldl findTaskPriority (mapEmpty nameCmp) tasks

  sem findTaskPriority : Map Name Int -> RtpplTask -> Map Name Int
  sem findTaskPriority priorities =
  | TaskRtpplTask {id = {v = id}, p = {v = priority}} ->
    mapInsert id priority priorities
end

lang RtpplTaskAlloc = RtpplTaskPeriod + RtpplTaskPriority
  -- We compute the allocated time available to each task based on their
  -- priority relative to all tasks. This is an upper-bound on the available
  -- time.
  sem computeTaskAllocations : RtpplProgram -> Map Name Int
  sem computeTaskAllocations =
  | p ->
    let taskPeriods = findProgramTaskPeriods p in
    let taskPriorities = findProgramTaskPriorities p in
    let prioritySum = int2float (foldl addi 0 (mapValues taskPriorities)) in
    mapMerge
      (lam taskPeriod. lam taskPriority.
        match (taskPeriod, taskPriority) with (Some period, Some prio) then
          let relPriority = divf (int2float prio) prioritySum in
          let periodAlloc = mulf (int2float period) relPriority in
          Some (floorfi periodAlloc)
        else
          error "Failed to compute static task allocations")
      taskPeriods
      taskPriorities
end

lang RtpplInferTaskAlloc = RtpplTaskAlloc
  -- For each distinct task, we compute the execution budget to allocate for
  -- each of the infers based on the task allocations and the priorities of the
  -- infers. This is a preliminary allocation that does not take other tasks
  -- into account.
  -- NOTE(larshum, 2023-08-28): For now, we assume there is exactly one infer
  -- in the main loop of the task, while there may be any number of infers in
  -- the initialization stage. The allocation of the inference in the main loop
  -- will always be at the end of the resulting sequence.
  sem computeTaskInferAllocations : RtpplProgram -> Map Name [Int]
  sem computeTaskInferAllocations =
  | p ->
    let taskAllocations = computeTaskAllocations p in
    let inferPriorities = findProgramInferPriorities p in
    mapMapWithKey
      (lam id. lam taskAlloc.
        match mapLookup id inferPriorities with Some inferPriority then
          let initTaskPriority = init inferPriority in
          let prioritySum = int2float (foldl addi 0 initTaskPriority) in
          let ta = int2float taskAlloc in
          let taskBudget =
            map
              (lam priority.
                let relativePriority = divf (int2float priority) prioritySum in
                let inferBudget = mulf ta relativePriority in
                floorfi (mulf 0.8 inferBudget))
              initTaskPriority
          in
          -- NOTE(larshum, 2023-08-28): We assume the last infer is the only
          -- one executing in the main loop. Therefore, we allocate it a large
          -- budget independently of the other infers.
          let lastInferBudget = floorfi (mulf 0.8 (int2float taskAlloc)) in
          snoc taskBudget lastInferBudget
        else error "Failed to compute static infer allocations")
      taskAllocations

  sem findProgramInferPriorities : RtpplProgram -> Map Name [Int]
  sem findProgramInferPriorities =
  | ProgramRtpplProgram p ->
    let inferPrio = foldl findTemplateInferPriorities (mapEmpty nameCmp) p.tops in
    findMainTaskInferPriorities inferPrio p.main

  sem findTemplateInferPriorities : Map Name [Int] -> RtpplTop -> Map Name [Int]
  sem findTemplateInferPriorities acc =
  | TemplateDefRtpplTop {id = {v = id}, body = {stmts = stmts}} ->
    let priorities = foldl findStmtInferPriorities [] stmts in
    mapInsert id priorities acc
  | _ -> acc

  sem findStmtInferPriorities : [Int] -> RtpplStmt -> [Int]
  sem findStmtInferPriorities acc =
  | LoopPlusStmtRtpplStmt {loop = loopStmt} ->
    sfold_RtpplLoopStmt_RtpplStmt findStmtInferPriorities acc loopStmt
  | InferRtpplStmt {p = {v = priority}} ->
    snoc acc priority
  | stmt -> sfold_RtpplStmt_RtpplStmt findStmtInferPriorities acc stmt

  sem findMainTaskInferPriorities : Map Name [Int] -> RtpplMain -> Map Name [Int]
  sem findMainTaskInferPriorities templateInferPriorities =
  | MainRtpplMain {tasks = tasks} ->
    foldl (findTaskInferPriorities templateInferPriorities) (mapEmpty nameCmp) tasks

  sem findTaskInferPriorities : Map Name [Int] -> Map Name [Int] -> RtpplTask -> Map Name [Int]
  sem findTaskInferPriorities templateInferPriorities acc =
  | TaskRtpplTask {id = {v = id}, templateId = {v = templateId}, info = info} ->
    match mapLookup templateId templateInferPriorities with Some inferPriorities then
      mapInsert id inferPriorities acc
    else errorSingle [info] "Could not find infer priorities of task template"
end
