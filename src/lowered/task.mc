-- Language fragments providing functionality for extracting information about
-- tasks.

include "ast.mc"

include "error.mc"
include "set.mc"

lang ProbTimeTaskConfigurableInfer = ProbTimeAst
  -- Finds the set of names of tasks that contain an infer term with an
  -- unspecified number of particles. Such uses of infer are configurable in
  -- the sense that we can control the number of particles after compilation,
  -- in the automatic configuration. This analysis assumes all such infers are
  -- reachable independently of how the template is initialized.
  sem findTasksWithConfigurableInfer : PTProgram -> Set Name
  sem findTasksWithConfigurableInfer =
  | {tops = tops, system = system} ->
    let emptySet = setEmpty nameCmp in
    let templates = foldl findTemplatesWithConfigurableInfer emptySet tops in
    foldl (findTasksWithConfigurableInferH templates) emptySet system

  sem findTasksWithConfigurableInferH : Set Name -> Set Name -> PTNode -> Set Name
  sem findTasksWithConfigurableInferH templates tasks =
  | PTNTask {id = id, template = template} ->
    if setMem template templates then setInsert id tasks
    else tasks
  | _ -> tasks

  sem findTemplatesWithConfigurableInfer : Set Name -> PTTop -> Set Name
  sem findTemplatesWithConfigurableInfer acc =
  | PTTFunDef {id = id, body = body, funKind = PTKTemplate _} ->
    if foldl stmtWithConfigurableInfer false body then setInsert id acc
    else acc
  | _ -> acc

  sem stmtWithConfigurableInfer : Bool -> PTStmt -> Bool
  sem stmtWithConfigurableInfer acc =
  | PTSInfer {particles = None _} -> true
  | s -> sfoldPTStmtPTStmt stmtWithConfigurableInfer acc s
end

lang ProbTimeInterArrivalTimes = ProbTimeAst
  -- Finds the minimum and maximum inter-arrival times of all tasks. We do this
  -- in two steps:
  --  1. Collect all parameters passed to a delay within each template.
  --  2. For each task, use the parameters passed to the template in the
  --     instantiation to get only integer values, and then pick the minimum
  --     and maximum among those.
  sem findTaskInterArrivalTimes : PTProgram -> Map Name (Int, Int)
  sem findTaskInterArrivalTimes =
  | {tops = tops, system = system} ->
    let templateDelayArgs = foldl collectTemplateDelayArgs (mapEmpty nameCmp) tops in
    foldl (findTaskInterArrivalTimeBounds templateDelayArgs) (mapEmpty nameCmp) system

  syn DelayExpr =
  -- Represents an integer literal passed as an argument to a delay statement.
  | IntLiteral Int
  -- Represents the index of a parameter passed to a template; a task should
  -- pass an integer literal in this position, or we have an error (in which
  -- case we use the provided info field).
  | TemplateParameter (Int, Info)

  sem collectTemplateDelayArgs : Map Name [DelayExpr] -> PTTop
                              -> Map Name [DelayExpr]
  sem collectTemplateDelayArgs acc =
  | PTTFunDef {id = id, params = params, body = body, funKind = PTKTemplate _, info = info} ->
    let params = mapFromSeq nameCmp (mapi (lam i. lam p. (p.id, i)) params) in
    let delayArgs = foldl (collectDelayArgs params) [] body in
    if null delayArgs then
      errorSingle [info] (join ["Template ", nameGetStr id, " contains no uses of delay"])
    else mapInsert id delayArgs acc
  | _ -> acc

  sem collectDelayArgs : Map Name Int -> [DelayExpr] -> PTStmt -> [DelayExpr]
  sem collectDelayArgs params acc =
  | PTSDelay {ns = PTEVar {id = id}, info = info} ->
    match mapLookup id params with Some idx then
      cons (TemplateParameter (idx, info)) acc
    else errorSingle [info] "Delay parameter must be a literal value"
  | PTSDelay {ns = PTELiteral {const = PTCInt {value = v}}} ->
    cons (IntLiteral v) acc
  | PTSDelay {ns = !(PTEVar _ | PTELiteral _), info = info} ->
    errorSingle [info] "Delay parameter must be a literal value"
  | s -> sfoldPTStmtPTStmt (collectDelayArgs params) acc s

  sem findTaskInterArrivalTimeBounds : Map Name [DelayExpr] -> Map Name (Int, Int)
                                    -> PTNode -> Map Name (Int, Int)
  sem findTaskInterArrivalTimeBounds templateDelayArgs acc =
  | PTNTask {id = id, template = template, args = args, info = info} ->
    match mapLookup template templateDelayArgs with Some delays then
      let delayLiterals = map (instantiateDelay info args) delays in
      let minDelay = minOrElse (lam. never) subi delayLiterals in
      let maxDelay = maxOrElse (lam. never) subi delayLiterals in
      mapInsert id (minDelay, maxDelay) acc
    else errorSingle [info] "Task refers to unknown template"
  | _ -> acc

  sem instantiateDelay : Info -> [PTExpr] -> DelayExpr -> Int
  sem instantiateDelay taskInfo args =
  | IntLiteral n -> n
  | TemplateParameter (idx, templateInfo) ->
    -- NOTE(larshum, 2024-11-20): We do bounds checking here to prevent a
    -- cryptic error in case the user provides too few arguments to a template.
    if and (geqi idx 0) (lti idx (length args)) then
      let arg = get args idx in
      match arg with PTELiteral {const = PTCInt {value = v}} then
        v
      else
        errorSingle [templateInfo, taskInfo] "Delay parameter must be a literal"
    else
      errorSingle [taskInfo] "Too few arguments in template instantiation"
end
