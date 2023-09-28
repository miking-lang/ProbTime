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

let estimateBaseExecutionTime = lam options. lam tasks.
  let tasks = map (lam t. {t with particles = 1}) tasks in
  let wcets : Map String Int = runTasks options.systemPath options.runnerCmd tasks in
  map
    (lam t.
      match mapLookup t.id wcets with Some wcet then
        {t with budget = wcet}
      else error (join ["Could not find WCET estimation for task ", t.id]))
    tasks

let findTaskAllocationHeuristic = lam numCores. lam tasks.
  recursive let work : [[TaskData]] -> [TaskData] -> [[TaskData]] =
    lam cores. lam tasks.
    match tasks with [t] ++ tasks then
      let lambdas =
        mapi
          (lam coreIdx. lam coreTasks.
            let orderedTasks =
              sort
                (lam l. lam r. subi l.index r.index)
                (cons t coreTasks)
            in
            (coreIdx, orderedTasks, computeLambda orderedTasks))
          cores
      in
      match max (lam l. lam r. cmpFloat l.2 r.2) lambdas
      with Some (coreIdx, orderedTasks, maxLambda) in
      if gtf maxLambda 0.0 then
        let cores = set cores coreIdx orderedTasks in
        work cores tasks
      else
        error "Provided tasks are not schedulable with estimated base execution times"
    else cores
  in
  let tasks = sort (lam l. lam r. subi r.importance l.importance) tasks in
  let coreTaskMap : [[TaskData]] = work (create numCores (lam. [])) tasks in
  foldli
    (lam acc. lam coreIdx. lam tasks.
      foldl (lam acc. lam t. mapInsert t.id (addi coreIdx 1) acc) acc tasks)
    (mapEmpty cmpString) coreTaskMap

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
      if lti options.numCores 1 then
        error "The number of cores options must be a positive integer"
      else if eqi options.numCores 1 then
        mapFromSeq cmpString (map (lam t. (t.id, t.core)) tasks)
      else
        -- NOTE(larshum, 2023-09-22): If the task-to-core map file does not
        -- exist, and we're using more than one core, we use a heuristic to
        -- find a mapping and create the task-to-core map file based on our
        -- results.
        let ttcMap = findTaskAllocationHeuristic options.numCores tasks in
        let str =
          strJoin "\n"
            (map (lam b. join [b.0, " ", int2string b.1]) (mapBindings ttcMap))
        in
        writeFile ttcFile str;
        ttcMap
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

-- 1. Retrieve the task-to-core mapping from a file, or compute a mapping based
-- on a heuristic (for a given number of cores).
let tasks = estimateBaseExecutionTime options tasks in
print "Estimated the base execution time of each task:\n";
iter
  (lam t.
    print (join [t.id, ": ", printNanosAsSeconds t.budget, "s\n"]))
  tasks;
flushStdout ();

let tasks = loadTaskToCoreMapping options tasks in
print "Using the following task-to-core mapping\n";
iter
  (lam t.
    print (join [t.id, " -> ", int2string t.core, "\n"]))
  tasks;
flushStdout ();

-- 2. Compute the execution time budgets. We either optimize for utilization
-- using a core-local view, or we optimize for fairness using a global view.
-- Also, we either measure the "base" execution time of all tasks to get an
-- estimate, or we start from (near) zero in the sensitivity analysis.
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
  mapMapWithKey (lam. lam coreTasks. computeLambda coreTasks) tasksPerCore
in
match min cmpFloat (mapValues lambdas) with Some minLambda in
let tasks =
  map
    (lam t.
      let lambda =
        if options.maximizeUtilization then
          match mapLookup t.core lambdas with Some coreLambda then
            coreLambda
          else
            let msg = join [
              "Core ", int2string t.core, " of task ", t.id,
              " was not assigned a lambda value."
            ] in
            error msg
        else
          minLambda
      in
      let budget = addi t.budget (floorfi (mulf (int2float t.importance) lambda)) in
      {t with budget = budget})
    tasks
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
let confResult = configureTasks options g tasks in
iter
  (lam e.
    match e with (taskId, particles) in
    let taskConfigFile = sysJoinPath options.systemPath (concat taskId ".config") in
    writeFile taskConfigFile (int2string particles))
  confResult;
print "Configuration complete!\nThe tasks have been assigned the following number of particles:\n";

iter
  (lam e.
    match e with (taskId, particles) in
    printLn (join [taskId, ": ", int2string particles]))
  confResult
