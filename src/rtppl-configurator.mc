include "common.mc"
include "digraph.mc"
include "json.mc"
include "name.mc"

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

let constructSystemDependencyGraph = lam systemSpecFile.
  let str = readFile systemSpecFile in
  match jsonParse str with Left json then
    match json with JsonObject kvs then
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
  else jsonFail ()

type TaskState = {
  infd : Int,
  outfd : Int,
  particles : Int,
  observations : [(Int, Int, Int)],
  dependencies : Set String
}
type ConfigState = {
  active : Set String,
  finished : Set String,
  tasks : Map String TaskState
}

let defaultTaskState = lam g. lam taskId.
  let inId = join [configTaskName, "-", taskId, ".in"] in
  let outId = join [configTaskName, "-", taskId, ".out"] in
  let infd = openFileDescriptor inId in
  let outfd = openFileDescriptor outId in
  { infd = infd, outfd = outfd, particles = defaultParticles, observations = []
  , dependencies = setOfSeq cmpString (digraphPredeccessors taskId g) }

let configureTask : ConfigState -> String -> (ConfigState, Bool) =
  lam state. lam taskId.
  let taskOverran = lam msgs. any (lam e. neqi e.2 0) msgs in
  let sufficientObservations = lam obs. geqi (length obs) 5 in
  match mapLookup taskId state.tasks with Some task then
    let tsvs : [TSV (Int,Int,Int)] = unsafeCoerce (rtpplReadIntRecord task.infd 3) in
    let msgs = map value tsvs in
    iter (lam msg. printLn (strJoin " " (map int2string [msg.0, msg.1, msg.2]))) msgs;
    if null msgs then
      (state, false)
    else if taskOverran msgs then
      -- TODO(larshum, 2023-09-11): In case the task overran any of its
      -- executions, we take appropriate action by decreasing its particle
      -- count.
      let newParticles = divi task.particles 2 in
      rtpplWriteInts task.outfd [(tsv 0 newParticles)];
      let task = {task with particles = newParticles, observations = []} in
      let state = {state with tasks = mapInsert taskId task state.tasks} in
      (state, false)
    else
      let task = {task with observations = concat task.observations msgs} in
      let state = {state with tasks = mapInsert taskId task state.tasks} in
      if sufficientObservations task.observations then
        -- TODO(larshum, 2023-09-11): After making at least a sufficient number
        -- of observations, we react by updating the number of particles to use
        -- in the task.
        rtpplWriteInts task.outfd [(tsv 0 1000), (tsv 0 0)];
        let task = {task with particles = 1000, observations = []} in
        let state = {state with tasks = mapInsert taskId task state.tasks} in
        (state, true)
      else
        (state, false)
  else
    error (join ["Task ", taskId, " not found in configuration state"])

let tryActivateTask = lam state. lam taskId.
  match mapLookup taskId state.tasks with Some task then
    if setIsEmpty (setSubtract task.dependencies state.finished) then
      printLn (join ["Activating configuration of task ", taskId]);
      ({state with active = setInsert taskId state.active}, true)
    else
      (state, false)
  else
    error (join ["Task ", taskId, " not found in configuration state"])

let configureTasks = lam g. lam tasks.
  recursive let addActiveTasks : ConfigState -> [String] -> (ConfigState, [String]) =
    lam state. lam tasks.
    match tasks with [nextTask] ++ remainingTasks then
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
      if setIsEmpty state.active then
        error "No tasks could be activated"
      else
        work state tasks
    else
      let state =
        mapFoldWithKey
          (lam acc. lam taskId. lam.
            match configureTask acc taskId with (acc, finished) in
            if finished then
              printLn (join ["Finished configuring task ", taskId]);
              {acc with active = setRemove taskId acc.active,
                        finished = setInsert taskId acc.finished}
            else acc)
          state state.active
      in
      delayBy nanosPerSec;
      work state tasks
  in
  let initialState = {
    active = setEmpty cmpString,
    finished = setEmpty cmpString,
    tasks = mapFromSeq cmpString (map (lam t. (t, defaultTaskState g t)) tasks)
  } in
  let finalState = work initialState tasks in
  -- NOTE(larshum, 2023-09-11): After reaching a final state, where all tasks
  -- have been configured to use a number of particles for their main infer, we
  -- write these values to configuration files to have them run as usual
  -- without collecting data.
  mapMapWithKey
    (lam taskId. lam taskState.
      let p = taskState.particles in
      let taskConfigFile = concat taskId ".config" in
      writeFile taskConfigFile (concat "0\n" (int2string p)))
    finalState.tasks;
  printLn "Completed configuration of all tasks"

mexpr

let g = constructSystemDependencyGraph "network.json" in
let vertices = digraphTopologicalOrder g in
configureTasks g vertices
