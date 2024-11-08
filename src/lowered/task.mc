include "ast.mc"

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
