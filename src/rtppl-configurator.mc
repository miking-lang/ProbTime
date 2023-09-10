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

let collectTaskDependencies = lam g. lam tasks.
  foldl
    (lam acc. lam task.
      mapInsert task (setOfSeq cmpString (digraphPredeccessors task g)) acc)
    (mapEmpty cmpString) tasks

type TaskData = {
  particles : Int,
  measurements : [(Int, Int, Int)]
}

let defaultTaskData = lam.
  { particles = defaultParticles, measurements = [] }

let configureTask = lam state. lam task.
  let infile = join [configTaskName, "-", task, ".in"] in
  let outfile = join [configTaskName, "-", task, ".out"] in
  -- TODO(larshum, 2023-09-08): Here, we attempt to configure the number of
  -- particles to use in the infer of the selected task. We perform the
  -- following steps:
  -- 1. We read incoming values from the port of collected data.
  -- 2. If the task has been overrunning, we react directly by decreasing
  --    particle count.
  -- 3. Otherwise, if we have sufficient data points using current particle
  --    count, we conservatively choose a new number of particles to use. If we
  --    are sufficiently close to the peak execution time of the task (computed
  --    based on its period and importance relative to other tasks), we
  --    consider this task to be finished.
  -- 4. If we updated the particle count, we write this updated value to the
  --    task using the appropriate port. Otherwise, we return true from this
  --    function to indicate that we've finished configuring this task.
  (state, true)

let configureTasks = lam g. lam tasks.
  recursive let addActiveTasks = lam state. lam remainingTasks.
    match remainingTasks with [nextTask] ++ tasks then
      match mapLookup nextTask state.dependencies with Some dependencies then
        if setIsEmpty (setSubtract dependencies state.finished) then
          let state = {state with active = setInsert nextTask state.active} in
          addActiveTasks state tasks
        else (state, remainingTasks)
      else error (join ["Task ", nextTask, " not found in task graph"])
    else (state, remainingTasks)
  in
  recursive let work = lam state. lam tasks.
    if and (null tasks) (setIsEmpty state.active) then state
    else if setIsEmpty state.active then
      match addActiveTasks state tasks with (state, tasks) in
      work state tasks
    else
      let state =
        mapFoldWithKey
          (lam acc. lam task. lam.
            match configureTask acc task with (acc, finished) in
            if finished then
              printLn (join ["Finished configuring task ", task]);
              {acc with active = setRemove task acc.active,
                        finished = setInsert task acc.finished}
            else acc)
          state state.active
      in
      work state tasks
  in
  let initialState = {
    dependencies = collectTaskDependencies g tasks,
    active = setEmpty cmpString,
    finished = setEmpty cmpString,
    tasks = map (lam. defaultTaskData) tasks
  } in
  work initialState tasks

mexpr
let g = constructSystemDependencyGraph "network.json" in
let vertices = digraphTopologicalOrder g in
configureTasks g vertices;
()
