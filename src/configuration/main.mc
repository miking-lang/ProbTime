include "common.mc"
include "digraph.mc"
include "json.mc"
include "math.mc"
include "name.mc"
include "string.mc"

include "argparse.mc"
include "configure.mc"
include "definitions.mc"
include "json-parse.mc"
include "schedulable.mc"

let cmpFloat : Float -> Float -> Int = lam l. lam r.
  if gtf l r then 1 else if ltf l r then negi 1 else 0

let loadTaskToCoreMapping = lam options. lam tasks.
  let taskToCoreMap : Map String Int =
    let ttcFile = sysJoinPath options.systemPath taskToCoreMappingFile in
    if fileExists ttcFile then
      foldl
        (lam acc. lam line.
          match strSplit " " line with [taskname, core] in
          let coreIdx = string2int core in
          mapInsert taskname coreIdx acc)
        (mapEmpty cmpString)
        (strSplit "\n" (strTrim (readFile ttcFile)))
    else
      error (join [
        "The task-to-core mapping must be provided in a file '",
        taskToCoreMappingFile, "'" ])
  in
  map
    (lam t.
      match mapLookup t.id taskToCoreMap with Some coreIdx then
        {t with core = coreIdx}
      else error (join ["Task ", t.id, " was not assigned to a core"]))
    tasks

let printNanosAsSeconds = lam ns.
  float2string (divf (int2float ns) 1e9)

mexpr

let options = parseConfigureOptions () in

let systemSpecPath = sysJoinPath options.systemPath systemSpecFile in
let systemSpecJson = parseSystemSpecJson systemSpecPath in
match constructSystemDependencyGraph systemSpecJson with (tasks, g) in

-- NOTE(larshum, 2023-09-22): We order the tasks by increasing period using a
-- stable sort to ensure tasks with the same period always get the same
-- priority. We assume the runner script does the same when assigning
-- priorities to tasks.
let tasks = mergeSort (lam l. lam r. subi l.period r.period) tasks in
let tasks = mapi (lam i. lam t. {t with index = i}) tasks in

let tasks = loadTaskToCoreMapping options tasks in
print "Using the following task-to-core mapping\n";
iter
  (lam t.
    print (join [t.id, " -> ", int2string t.core, "\n"]))
  tasks;
flushStdout ();

let confResult =
  if options.particleFairness then
    -- 1. Find a multiple k such that all tasks use particles equal to k times
    -- their importance value. We return the resulting particle counts and
    -- budgets assigned based on our WCET estimates, with an extra margin on top.
    let state = configureTasksParticleFairness options tasks in

    let tasksPerCore =
      foldl
        (lam acc. lam t.
          let wcet =
            optionGetOrElse (lam. error (join ["Could not find budget for task ", t.id]))
                            (mapLookup t.id state.wcets)
          in
          let t = {t with budget = wcet, importance = wcet,
                          particles = muli state.k t.importance}
          in
          match mapLookup t.core acc with Some tasks then
            mapInsert t.core (snoc tasks t) acc
          else
            mapInsert t.core [t] acc)
        (mapEmpty subi) tasks
    in
    printLn (join ["k = ", int2string state.k]);
    -- NOTE(larshum, 2023-10-15): After finding an integer k for which all
    -- tasks are schedulable, we compute the budgets by extending all observed
    -- WCETs proportionally. Note that we use the maximum lambda for each core,
    -- so that tasks have as much time available as possible (to prevent
    -- "overruns" because we allocated too small budgets even though we could
    -- allocate more).
    --
    -- This step is not required for correctness. We use this to be able to
    -- detect overruns at runtime, for debugging purposes (it should never be
    -- able to happen in practice, given representative training data).
    mapFoldWithKey
      (lam acc. lam. lam coreTasks.
        let lambda = computeLambda coreTasks in
        foldl
          (lam acc. lam t.
            let budget = addi t.budget (floorfi (mulf (int2float t.budget) lambda)) in
            snoc acc (t.id, t.particles, budget))
          acc coreTasks)
      [] tasksPerCore
  else
    -- 1. Compute the execution time budgets. We optimize for fairness using a
    -- global view, where we pick fair budgets for all tasks.
    let tasksPerCore : Map Int [TaskData] =
      foldl
        (lam acc. lam t.
          match mapLookup t.core acc with Some tasks then
            mapInsert t.core (snoc tasks t) acc
          else
            mapInsert t.core [t] acc)
        (mapEmpty subi) tasks
    in
    let lambdas : Map Int Float =
      mapMapWithKey
        (lam. lam coreTasks. computeLambda coreTasks)
        tasksPerCore
    in
    match min cmpFloat (mapValues lambdas) with Some minLambda in
    let tasks =
      mapFoldWithKey
        (lam acc. lam. lam coreTasks.
          concat
            (map
              (lam t. {t with budget = addi t.budget (floorfi (mulf (int2float t.importance) minLambda))})
              coreTasks)
            acc)
        [] tasksPerCore
    in
    print "Task execution time budgets:\n";
    iter
      (lam t.
        print (join [t.id, ": ", printNanosAsSeconds t.budget, "s\n"]))
      tasks;
    flushStdout ();

    -- 3. Run the configuration using the assigned execution time budgets,
    -- following the topology of the graph.
    printLn "Configuring the number of particles to use per task";
    configureTasksExecutionTimeFairness options g tasks
in

iter
  (lam e.
    match e with (taskId, particles, budget) in
    let taskConfigFile = sysJoinPath options.systemPath (concat taskId ".config") in
    let msg = join [int2string particles, " ", int2string budget, " 1"] in
    writeFile taskConfigFile msg)
  confResult;
print "Configuration complete!\nThe tasks have been assigned the following number of particles:\n";

iter
  (lam e.
    match e with (taskId, particles, budget) in
    printLn (join [taskId, ": ", int2string particles, ", ", int2string budget]))
  confResult
