include "common.mc"
include "digraph.mc"
include "map.mc"
include "sys.mc"

include "definitions.mc"
include "regression.mc"

type TaskConfigState = {
  particles : Int,
  observations : [(Int, Int)],
  budget : Int,
  particleBounds : (Int, Int),
  finished : Bool
}

let writeTaskParticles = lam path. lam taskId. lam nparticles.
  let taskConfigFile = sysJoinPath path (concat taskId ".config") in
  writeFile taskConfigFile (int2string nparticles)

let readTaskWcet = lam path. lam taskId.
  let taskCollectFile = sysJoinPath path (concat taskId ".collect") in
  if fileExists taskCollectFile then
    let wcet = string2int (readFile taskCollectFile) in
    printLn (join [taskId, ": ", int2string wcet]);
    wcet
  else 0

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

let clamp = lam bounds. lam x.
  match bounds with (lowerBound, upperBound) in
  if lti x lowerBound then lowerBound
  else if gti x upperBound then upperBound
  else x

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
      let estimateNewParticles = lam task. lam obs.
        match linearRegression obs with (slope, intercept) in
        -- TODO(larshum, 2023-09-26): We may want to replace the constant value
        -- with an option parameter the user can override, if they are more or
        -- less willing to risk overrunning.
        let y = mulf (int2float task.budget) 0.9 in
        floorfi (divf (subf y intercept) slope)
      in
      let state =
        mapFoldWithKey
          (lam state. lam taskId. lam wcet.
            -- NOTE(larshum, 2023-09-25): If we get a WCET of 0, it means we
            -- failed to read the collection file for some reason. Ignore the
            -- result.
            if eqi wcet 0 then state
            else match mapLookup taskId state with Some task then
              match task.particleBounds with (lowerBound, upperBound) in
              let obs = snoc task.observations (task.particles, wcet) in
              let task =
                if eqi (length obs) 1 then
                  {task with particles = 100}
                else if lti (length obs) 3 then
                  if lti wcet task.budget then
                    let np = muli task.particles 2 in
                    let bounds = (task.particles, upperBound) in
                    {task with particles = np, particleBounds = bounds}
                  else
                    let np = divi (addi lowerBound task.particles) 2 in
                    let bounds = (lowerBound, task.particles) in
                    {task with particles = np, particleBounds = bounds}
                else
                  if eqi lowerBound upperBound then
                    let minUtil = floorfi (mulf (int2float task.budget) 0.8) in
                    let maxUtil = floorfi (mulf (int2float task.budget) 0.95) in
                    if and (geqi wcet minUtil) (leqi wcet maxUtil) then
                      {task with finished = true}
                    else
                      let p = estimateNewParticles task obs in
                      {task with particles = p, particleBounds = (p, p)}
                  else
                    let p = estimateNewParticles task obs in
                    {task with particles = p, particleBounds = (p, p)}
              in
              let task = {task with particles = clamp task.particleBounds task.particles,
                                    observations = obs} in
              mapInsert taskId task state
            else error "Found WCET of invalid task, likely bug in configureTasks")
          state activeWcets
      in
      let g =
        mapFoldWithKey
          (lam g. lam taskId. lam task.
            if and (digraphHasVertex taskId g) task.finished then
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
          , particleBounds = (1, options.maxParticles), finished = false }
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
utest findVerticesWithIndegreeZero g with setOfSeq subi [0, 1] using setEq in
let g = digraphRemoveVertex 1 g in
utest findVerticesWithIndegreeZero g with setOfSeq subi [0, 3] using setEq in
let g = digraphRemoveVertex 3 g in
utest findVerticesWithIndegreeZero g with setOfSeq subi [0] using setEq in
let g = digraphRemoveVertex 0 g in
utest findVerticesWithIndegreeZero g with setOfSeq subi [2] using setEq in

()
