include "digraph.mc"
include "map.mc"
include "sys.mc"

include "definitions.mc"

type TaskConfigState = {
  particles : Int,
  observations : [{particles : Int, wcet : Int}],
  budget : Int,
  maxParticles : Int
}

let writeTaskParticles = lam path. lam taskId. lam nparticles.
  let taskConfigFile = sysJoinPath path (concat taskId ".config") in
  writeFile taskConfigFile (int2string nparticles)

let readTaskWcet = lam path. lam taskId.
  let taskCollectFile = sysJoinPath path (concat taskId ".collect") in
  match map string2int (strSplit " " (readFile taskCollectFile))
  with [wcet, taskOverran] in
  if eqi taskOverran 1 then 0
  else wcet

let runTasks : String -> String -> [TaskData] -> Map String Int =
  lam path. lam runner. lam tasks.

  -- 1. Write the number of particles to use to the configuration file the
  -- respective task.
  iter (lam t. writeTaskParticles path t.id t.particles) tasks;

  -- 2. Invoke the runner.
  let result = sysRunCommand [runner] "" "." in

  -- 3. Return the WCET estimtates for each task, if the runner exited with
  -- code zero. Otherwise, we report an error and print stdout/stderr.
  -- If any task overran its period, we report this by setting the WCET to 0.
  if eqi result.returncode 0 then
    foldl
      (lam acc. lam t. mapInsert t.id (readTaskWcet path t.id) acc)
      (mapEmpty cmpString) tasks
  else
    let msg = join [
      "Runner task failed with exit code ", int2string result.returncode, "\n",
      "stdout:\n", result.stdout, "\nstderr:\n", result.stderr, "\n"
    ] in
    error msg

let tasksWithParticleCounts = lam tasks. lam taskMap.
  map
    (lam t.
      match mapLookup t.id taskMap with Some taskConfigState then
        {t with particles = taskConfigState.particles}
      else error "Task not found in map")
    tasks

let findVerticesWithIndegreeZero = lam g.
  let removeDestination = lam vertices. lam edge.
    match edge with (_, dst, _) in
    setRemove dst vertices
  in
  let vertices = setOfSeq (digraphCmpv g) (digraphVertices g) in
  foldl removeDestination vertices (digraphEdges g)

let linearRegression = lam obs.
  match obs with [(x1, y1), (x2, y2)] ++ _ in
  let slope = divf (int2float (subi y2 y1)) (int2float (subi x2 x1)) in
  let intercept = subf (int2float y2) (mulf slope (int2float x2)) in
  (slope, intercept)

let configureTasks = lam options. lam g. lam tasks.
  recursive let work = lam g. lam state.
    if eqi (digraphCountVertices g) 0 then
      map
        (lam task.
          match task with (taskId, {particles = p}) in
          (taskId, p))
        (mapBindings state)
    else
      let active = findVerticesWithIndegreeZero g in
      let wcets =
        runTasks
          options.systemPath options.runnerCmd
          (tasksWithParticleCounts tasks state)
      in
      let activeWcets =
        mapMerge
          (lam lhs. lam rhs.
            match (lhs, rhs) with (Some l, Some _) then Some l
            else None ())
          wcets active
      in

      -- Add the worst-case execution times to the accumulated sequence of
      -- observed worst-case execution times, coupled with the number of
      -- particles used.
      -- TODO(larshum, 2023-09-22): Update the task states by estimating a new
      -- number of particles to use. If we have made sufficient observations
      -- and the results found so far are convincing, we can estimate a final
      -- number of particles to use for a particular task. Once we have done
      -- this, the vertex of the task should be removed from the graph.
      let state =
        mapFoldWithKey
          (lam state. lam taskId. lam wcet.
            match mapLookup taskId state with Some task then
              let obs = snoc task.observations (task.particles, wcet) in
              let task =
                if eqi (length obs) 1 then
                  {task with particles = 100}
                else
                  match linearRegression obs with (slope, intercept) in
                  -- TODO(larshum, 2023-09-22): We should not make an
                  -- estimation after just two runs.
                  let y = mulf (int2float task.budget) 0.9 in
                  let x = floorfi (divf (subf y intercept) slope) in
                  let x = if gti x task.maxParticles then task.maxParticles else x in
                  {task with particles = x, maxParticles = x}
              in
              let task = {task with observations = obs} in
              mapInsert taskId task state
            else error "Found WCET of invalid task, likely bug in configureTasks")
          state activeWcets
      in
      let g =
        mapFoldWithKey
          (lam g. lam taskId. lam task.
            if and (digraphHasVertex taskId g) (eqi task.particles task.maxParticles) then
              printLn (join ["Finished configuration of task ", taskId]);
              digraphRemoveVertex taskId g
            else g)
          g state
      in
      work g state
  in
  let state =
    foldl
      (lam state. lam task.
        let taskState =
          { particles = task.particles, observations = [], budget = task.budget
          , maxParticles = maxParticles }
        in
        mapInsert task.id taskState state)
      (mapEmpty cmpString)
      tasks
  in
  work g state

mexpr

let g =
  foldl
    (lam g. lam str.
      digraphAddVertex str g)
    (digraphEmpty subi (lam. lam. true))
    (create 5 (lam i. i))
in
let g =
  foldl
    (lam g. lam edge.
      match edge with (from, to) in
      digraphAddEdge from to () g)
    g
    [(0, 2), (1, 2), (1, 3), (2, 4), (3, 4)]
in
utest findVerticesWithIndegreeZero g with setOfSeq subi [0, 1] in
let g = digraphRemoveVertex 1 g in
utest findVerticesWithIndegreeZero g with setOfSeq subi [0, 3] in
let g = digraphRemoveVertex 3 g in
utest findVerticesWithIndegreeZero g with setOfSeq subi [0] in
let g = digraphRemoveVertex 0 g in
utest findVerticesWithIndegreeZero g with setOfSeq subi [2] in

()
