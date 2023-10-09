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
  upperBound : Int,
  finished : Bool
}

let defaultUpperBound = floorfi 1e10

let writeTaskConfig = lam path. lam task.
  let taskConfigFile = sysJoinPath path (concat task.id ".config") in
  let msg = join [int2string task.particles, " ", int2string task.budget] in
  writeFile taskConfigFile msg

let readTaskCollect = lam path. lam taskId.
  let taskCollectFile = sysJoinPath path (concat taskId ".collect") in
  if fileExists taskCollectFile then
    match map string2int (strSplit " " (readFile taskCollectFile))
    with [p, ovr] in
    (if eqi ovr 1 then
      printLn (join ["Task ", taskId, " overran its budget"])
    else ());
    p
  else 0

let runTasks : String -> String -> [TaskData] -> Map String Int =
  lam path. lam runner. lam tasks.

  -- 1. Write the number of particles to use to the configuration file the
  -- respective task.
  iter (lam t. writeTaskConfig path t) tasks;

  -- 2. Invoke the runner.
  let result = sysRunCommand [runner] "" "." in

  -- 3. Return the WCET estimtates for each task, if the runner exited with
  -- code zero. Otherwise, we report an error and print stdout/stderr.
  -- If any task overran its period, we report this by setting the WCET to 0.
  if eqi result.returncode 0 then
    foldl
      (lam acc. lam t.
        let wcet = readTaskCollect path t.id in
        printLn (join [t.id, "(", int2string t.particles, "): ", int2string wcet]);
        mapInsert t.id wcet acc)
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

let configureTasks = lam options. lam g. lam tasks.
  recursive let work = lam g. lam state.
    if eqi (digraphCountVertices g) 0 then
      map
        (lam task.
          match task with (taskId, {particles = p, budget = b}) in
          (taskId, p, b))
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
        -- NOTE(larshum, 2023-10-09): We do not aim to use 100 % of the budget,
        -- but rather a ratio thereof (used to determine a safety margin).
        let y = mulf (int2float task.budget) options.budgetRatio in
        let p = floorfi (divf (subf y intercept) slope) in
        if lti p task.upperBound then p else subi task.upperBound 1
      in
      let state =
        mapFoldWithKey
          (lam state. lam taskId. lam wcet.
            -- NOTE(larshum, 2023-09-25): If we get a WCET of 0, it means we
            -- failed to read the collection file for some reason. Ignore the
            -- result.
            if eqi wcet 0 then state
            else match mapLookup taskId state with Some task then
              let obs = snoc task.observations (task.particles, wcet) in
              let task =
                if eqi (length obs) 1 then
                  {task with particles = 100, observations = obs}
                else if lti (length obs) 5 then
                  if lti wcet task.budget then
                    -- NOTE(larshum, 2023-10-05): If the upper bound is at its
                    -- default value we have not overran so far, so we double
                    -- the number of particles. Otherwise, we pick a value
                    -- between the last particle count and the upper bound.
                    let np =
                      if eqi task.upperBound defaultUpperBound then
                        muli task.particles 2
                      else
                        divi (addi task.particles task.upperBound) 2
                    in
                    {task with particles = np, observations = obs}
                  else
                    -- NOTE(larshum, 2023-10-05): If the task overruns its
                    -- budget, we do not record the new observation as it might
                    -- not behave linearly, and therefore disturb our final
                    -- estimation.
                    let np = divi task.particles 2 in
                    {task with particles = np, upperBound = task.particles}
                else if eqi (length obs) 5 then
                  let np = estimateNewParticles task obs in
                  {task with particles = np, observations = obs}
                else
                  -- NOTE(larshum, 2023-10-09): We accept the current particle
                  -- count if our estimated WCET close to, but not beyond, the
                  -- assigned execution time budget.
                  let lowerExecBound = floorfi (mulf (int2float task.budget) 0.8) in
                  if and (gti wcet lowerExecBound) (leqi wcet task.budget) then
                    {task with finished = true, observations = []}
                  else
                    let upperBound =
                      if gti wcet lowerExecBound then task.particles
                      else task.upperBound
                    in
                    let np = estimateNewParticles task obs in
                    {task with particles = np, upperBound = upperBound,
                               observations = obs}
              in
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
          , upperBound = defaultUpperBound, finished = false }
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
