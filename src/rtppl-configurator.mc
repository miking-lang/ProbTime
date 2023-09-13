include "common.mc"
include "digraph.mc"
include "json.mc"
include "name.mc"
include "string.mc"

include "rtppl-runtime.mc"

type TaskData = { id : String, period : Int, importance : Int }
type Connection = { from : String, to : String }

let configTaskName = "config.task"

let jsonFail = lam. error "Error while reading system specification file"

let jsonUnwrap = lam o.
  match o with Some v then v
  else jsonFail ()

let jsonLookup : String -> Map String JsonValue -> JsonValue =
  lam key. lam kvs.
  jsonUnwrap (mapLookup key kvs)

let parseSystemSpecJson = lam systemSpecFile.
  let str = readFile systemSpecFile in
  match jsonParse str with Left json then
    json
  else jsonFail ()

let deserializeTasks : JsonValue -> [TaskData] = lam tasks.
  let deserializeTask = lam t.
    match t with JsonObject kvs then
      Some { id = jsonUnwrap (jsonDeserializeString (jsonLookup "id" kvs))
           , period = jsonUnwrap (jsonDeserializeInt (jsonLookup "period" kvs))
           , importance = jsonUnwrap (jsonDeserializeInt (jsonLookup "importance" kvs)) }
    else jsonFail ()
  in
  jsonUnwrap (jsonDeserializeSeq deserializeTask tasks)

let deserializeSeq : JsonValue -> [String] = lam sensors.
  jsonUnwrap (jsonDeserializeSeq jsonDeserializeString sensors)

let deserializeConnections : JsonValue -> [Connection] = lam connections.
  let deserializePort = lam p.
    let portStr = jsonUnwrap (jsonDeserializeString p) in
    match strSplit "-" portStr with [fst, _] ++ _ then
      Some fst
    else None ()
  in
  let deserializeConnection = lam c.
    match c with JsonObject kvs then
      match deserializePort (jsonLookup "from" kvs) with Some from then
        match deserializePort (jsonLookup "to" kvs) with Some to then
          Some { from = from, to = to }
        else None ()
      else None ()
    else jsonFail ()
  in
  match connections with JsonArray conns then
    foldl
      (lam acc. lam c.
        match deserializeConnection c with Some conn then
          cons conn acc
        else acc)
      [] conns
  else jsonFail ()

let constructSystemDependencyGraph = lam systemSpecJson.
  match systemSpecJson with JsonObject kvs then
    let tasks = deserializeTasks (jsonLookup "tasks" kvs) in
    let taskNames = map (lam t. t.id) tasks in
    let g : Digraph String () =
      digraphAddVertices taskNames (digraphEmpty cmpString (lam. lam. true))
    in
    let connections = deserializeConnections (jsonLookup "connections" kvs) in
    let g = foldl (lam g. lam c. digraphAddEdge c.from c.to () g) g connections in
    -- NOTE(larshum, 2023-09-08): We explicitly exclude the task itself and
    -- all connections to and from it, as we are not interested in this node.
    digraphRemoveVertex configTaskName g
  else jsonFail ()

-- NOTE(larshum, 2023-09-11): We compute the execution time budgets to allocate
-- to each task under the assumption that they all execute on the same core.
let computeTaskExecutionBudgets = lam systemSpecJson.
  match systemSpecJson with JsonObject kvs then
    let tasks = deserializeTasks (jsonLookup "tasks" kvs) in
    let importanceSum = foldl (lam acc. lam t. addi acc t.importance) 0 tasks in
    let is = int2float importanceSum in
    mapFromSeq cmpString
      (map
        (lam t.
          let relativeImportance = divf (int2float t.importance) is in
          let execTime = mulf (int2float t.period) relativeImportance in
          (t.id, floorfi execTime))
        tasks)
  else jsonFail ()

type TaskState = {
  infd : Int,
  outfd : Int,
  particles : Int,
  observations : [(Int, Int, Int)],
  wcets : [(Int, Int)],
  baseExecutionTime : Option Int,
  particlesUpperBound : Int,
  dependencies : Set String,
  budget : Int
}
type ConfigState = {
  active : Set String,
  finished : Set String,
  tasks : Map String TaskState
}

let defaultTaskState = lam g. lam execBudgets. lam taskId.
  let inId = join [configTaskName, "-", taskId, ".in"] in
  let outId = join [configTaskName, "-", taskId, ".out"] in
  let infd = openFileDescriptor inId in
  let outfd = openFileDescriptor outId in
  match mapLookup taskId execBudgets with Some executionTimeBudget then
    { infd = infd, outfd = outfd, particles = defaultParticles
    , observations = [], wcets = [], baseExecutionTime = None ()
    , particlesUpperBound = 7500
    , dependencies = setOfSeq cmpString (digraphPredeccessors taskId g)
    , budget = executionTimeBudget }
  else
    error (concat "Could not find execution time budget for task " taskId)

let cmpFloat : Float -> Float -> Int = lam l. lam r.
  if gtf l r then 1 else if eqf l r then 0 else negi 1

let setTaskParticles : TaskState -> Int -> TaskState = lam task. lam particles.
  rtpplWriteInts task.outfd [tsv 0 particles];
  {task with particles = particles, observations = []}

let maxExecutionTime = lam msgs.
  let execTimes = map (lam e. e.0) msgs in
  if null execTimes then 0
  else
    match max subi execTimes with Some wcet in
    wcet

let updateTaskObservations = lam state.
  let tasks =
    mapMapWithKey
      (lam taskId. lam task.
        let tsvs : [TSV (Int, Int, Int)] = unsafeCoerce (rtpplReadIntRecord task.infd 3) in
        let msgs = filter (lam e. eqi e.1 task.particles) (map value tsvs) in
        let maxExec = maxExecutionTime msgs in
        if gti maxExec task.budget then
          -- NOTE(larshum, 2023-09-13): In case the task overran, we
          -- immediately reduce the number of particles relative to the amount
          -- of overrun.
          let overrunRate = divf (int2float maxExec) (int2float task.budget) in
          let newParticles = floorfi (divf (int2float task.particles) overrunRate) in
          printLn (join ["Lowering particles of task ", taskId, " to ", int2string newParticles]);
          let task = setTaskParticles task newParticles in
          {task with particlesUpperBound = newParticles}
        else if any (lam e. gti e.2 0) msgs then
          -- sdelay overran - is this fatal?
          printLn (join ["Task ", taskId, " overran its period"]);
          let newParticles = 1 in
          setTaskParticles task newParticles
        else
          {task with observations = concat task.observations msgs})
      state.tasks
  in
  {state with tasks = tasks}

let configureTask : ConfigState -> String -> (ConfigState, Bool) =
  lam state. lam taskId.
  let sufficientObservations = lam obs. geqi (length obs) 10 in
  let minExecutionTime = lam msgs.
    match max (lam l. lam r. subi r.0 l.0) msgs with Some (met, _, _) in
    met
  in
  match mapLookup taskId state.tasks with Some task then
    let wcet = maxExecutionTime task.observations in
    if sufficientObservations task.observations then
      let task = {task with wcets = snoc task.wcets (task.particles, wcet)} in
      -- NOTE(larshum, 2023-09-13): We use the best case execution time of the
      -- initial task as our assumption of the "base" execution time, which
      -- represents the mandatory part that is independent on the number of
      -- particles used in inference.
      let baseExecutionTime =
        match task.baseExecutionTime with Some bt then
          bt
        else
          minExecutionTime task.observations
      in
      let task = {task with baseExecutionTime = Some baseExecutionTime} in
      let maxWcetPerParticle =
        divf (int2float (subi wcet baseExecutionTime)) (int2float task.particles)
      in
      let targetParticles = floorfi (mulf (divf (int2float task.budget) maxWcetPerParticle) 0.75) in
      let newParticles = mini targetParticles task.particlesUpperBound in
      if leqi newParticles task.particles then
        printLn (join ["Fixing particle count of ", taskId, " to ", int2string task.particles]);
        let state = {state with tasks = mapInsert taskId task state.tasks} in
        rtpplWriteInts task.outfd [tsv 0 0];
        (state, true)
      else
        let task = setTaskParticles task newParticles in
        printLn (join ["Increasing particle count of ", taskId, " to ", int2string task.particles]);
        let state = {state with tasks = mapInsert taskId task state.tasks} in
        (state, false)
    else
      (state, false)
  else
    error (join ["Task ", taskId, " not found in configuration state"])

let tryActivateTask = lam state. lam taskId.
  match mapLookup taskId state.tasks with Some task then
    if setIsEmpty (setSubtract task.dependencies state.finished) then
      printLn (join ["Activating configuration of task ", taskId]);
      let task = {task with observations = []} in
      let tasks = mapInsert taskId task state.tasks in
      ({state with active = setInsert taskId state.active, tasks = tasks}, true)
    else
      (state, false)
  else
    error (join ["Task ", taskId, " not found in configuration state"])

let loadExistingConfigurationFiles = lam state.
  mapFoldWithKey
    (lam state. lam taskId. lam taskState.
      match rtpplReadConfigurationFile taskId with Some (enabledCollection, p) then
        let taskState = {taskState with particles = p} in
        let state = {state with tasks = mapInsert taskId taskState state.tasks} in
        if enabledCollection then state
        else {state with finished = setInsert taskId state.finished}
      else state)
    state state.tasks

let printConfigurationCompletionMessage = lam tasks.
  mapMapWithKey
    (lam taskId. lam taskState.
      let p = taskState.particles in
      printLn (join [taskId, " -> ", int2string p]))
    tasks;
  printLn "Completed configuration of all tasks"

let configureTasks = lam g. lam execBudgets. lam tasks.
  recursive let addActiveTasks : ConfigState -> [String] -> (ConfigState, [String]) =
    lam state. lam tasks.
    match tasks with [nextTask] ++ remainingTasks then
      if setMem nextTask state.finished then
        printLn (join ["Skipping configuration of task ", nextTask]);
        addActiveTasks state remainingTasks
      else
        match tryActivateTask state nextTask with (state, activated) in
        if activated then
          addActiveTasks state remainingTasks
        else
          (state, tasks)
    else (state, tasks)
  in
  recursive let work = lam state. lam tasks.
    if and (null tasks) (setIsEmpty state.active) then
      state
    else if setIsEmpty state.active then
      match addActiveTasks state tasks with (state, tasks) in
      work state tasks
    else
      delayBy nanosPerSec;
      let state = updateTaskObservations state in
      let state =
        mapFoldWithKey
          (lam acc. lam taskId. lam.
            match configureTask acc taskId with (acc, finished) in
            if finished then
              let p =
                match mapLookup taskId acc.tasks with Some task then
                  task.particles
                else
                  error (concat "Failed to find particles of task " taskId)
              in
              let taskConfigFile = concat taskId ".config" in
              writeFile taskConfigFile (concat "0\n" (int2string p));
              printLn (join ["Finished configuring task ", taskId]);
              {acc with active = setRemove taskId acc.active,
                        finished = setInsert taskId acc.finished}
            else acc)
          state state.active
      in
      work state tasks
  in
  let initialState = {
    active = setEmpty cmpString,
    finished = setEmpty cmpString,
    tasks = mapFromSeq cmpString (map (lam t. (t, defaultTaskState g execBudgets t)) tasks)
  } in
  let state = loadExistingConfigurationFiles initialState in
  let finalState = work state tasks in
  printConfigurationCompletionMessage finalState.tasks

mexpr

let systemSpecFile = "network.json" in
let systemSpecJson = parseSystemSpecJson systemSpecFile in
let g = constructSystemDependencyGraph systemSpecJson in
let executionBudgets = computeTaskExecutionBudgets systemSpecJson in
let vertices = digraphTopologicalOrder g in
configureTasks g executionBudgets vertices
