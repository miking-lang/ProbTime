include "common.mc"
include "digraph.mc"
include "map.mc"
include "sys.mc"

include "definitions.mc"
include "regression.mc"

type TaskConfigState = {
  particles : Int,
  observations : Map Int Int,
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
  recursive let readRetry = lam retries.
    let p =
      if fileExists taskCollectFile then
        match map string2int (strSplit " " (readFile taskCollectFile))
        with [p, _] in
        p
      else
        0
    in
    if eqi p 0 then
      if eqi retries 0 then p
      else
        sleepMs 50;
        readRetry (subi retries 1)
    else p
  in
  readRetry 3

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

-- We find the maximum offset from the line with the given slope and intercept
-- to a line with the same slope passing through an observation.
let maxObsIntercept = lam slope. lam observations.
  mapFoldWithKey
    (lam maxOfs. lam nparticles. lam wcet.
      let ofs = subf (int2float wcet) (mulf (int2float nparticles) slope) in
      maxf ofs maxOfs)
    0.0 observations

-- Add the worst-case execution times to the accumulated sequence of
-- observed worst-case execution times, coupled with the number of
-- particles used.
let estimateNewParticles = lam options. lam task. lam obs.
  match linearRegression (mapBindings obs) with (slope, intercept) in
  let maxIntercept = maxObsIntercept slope obs in
  let y = mulf (int2float task.budget) options.budgetRatio in
  let p = floorfi (divf (subf y maxIntercept) slope) in
  if leqi p 0 then 1
  else if lti p task.upperBound then p
  else subi task.upperBound 1

let configureTasks = lam options. lam taskGraph. lam tasks.
  recursive let work = lam g. lam state.
    if eqi (digraphCountVertices g) 0 then
      map
        (lam task.
          match task with (taskId, {particles = p, budget = b}) in
          (taskId, p, b))
        (mapBindings state)
    else
      let wcets =
        runTasks
          options.systemPath options.runnerCmd
          (tasksWithParticleCounts tasks state)
      in
      -- NOTE(larshum, 2023-10-12): If a task we had already fixed the number
      -- of particles for overruns, we need to re-configure it and all tasks
      -- that depend on its result.
      match
        foldl
          (lam acc. lam task.
            match acc with (state, overran) in
            match (mapLookup task.id state, mapLookup task.id wcets)
            with (Some ts, Some wcet) then
              if and ts.finished (gti wcet task.budget) then
                let obs =
                  mapInsertWith maxi ts.particles wcet ts.observations
                in
                printLn (join [
                  "Fixed task ", task.id, " overran; wcet=", int2string wcet,
                  ", budget=", int2string task.budget]);
                let p =
                  if geqi wcet task.period then
                    divi ts.particles 2
                  else
                    estimateNewParticles options ts obs
                in
                let ts = {ts with particles = p, upperBound = ts.particles,
                                  observations = obs, finished = false}
                in
                (mapInsert task.id ts state, true)
              else acc
            else acc)
          (state, false) tasks
      with (state, overran) in
      if overran then
        recursive let dropFinishedTasks = lam g.
          let active = findVerticesWithIndegreeZero g in
          let gNew =
            mapFoldWithKey
              (lam g. lam taskId. lam.
                match mapLookup taskId state with Some task then
                  if task.finished then
                    digraphRemoveVertex taskId g
                  else g
                else g)
              g active
          in
          if digraphGraphEq g gNew then g
          else dropFinishedTasks gNew
        in
        -- NOTE(larshum, 2023-10-11): If at least one task overruns its budget,
        -- we need to restart the configuration from the overrunning tasks.
        -- These tasks and all the tasks that depend on them need to be
        -- re-configured.
        let g = dropFinishedTasks taskGraph in
        let active = findVerticesWithIndegreeZero g in
        let state =
          foldl
            (lam state. lam taskId.
              if setMem taskId active then state
              else match mapLookup taskId state with Some taskState then
                let ts =
                  {taskState with finished = false,
                                  observations = mapEmpty subi}
                in
                mapInsert taskId ts state
              else state)
            state (digraphVertices g)
        in
        work g state
      else
        let active = findVerticesWithIndegreeZero g in
        print "Active tasks: ";
        printLn (strJoin " " (setToSeq active));
        let activeWcets =
          mapMerge
            (lam lhs. lam rhs.
              match (lhs, rhs) with (Some l, Some _) then Some l
              else None ())
            wcets active
        in
        let state =
          mapFoldWithKey
            (lam state. lam taskId. lam wcet.
              -- NOTE(larshum, 2023-09-25): If we get a WCET of 0, it means we
              -- failed to read the collection file for some reason. Ignore the
              -- result and re-run.
              if eqi wcet 0 then state
              else match mapLookup taskId state with Some task then
                let obs =
                  mapInsertWith maxi task.particles wcet task.observations
                in
                let task =
                  if eqi (mapSize obs) 1 then
                    {task with particles = 100, observations = obs}
                  else if lti (mapSize obs) 5 then
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
                  else
                    if gti wcet (floorfi (mulf (int2float task.budget) options.budgetRatio)) then
                      let task = {task with upperBound = task.particles} in
                      let p = estimateNewParticles options task obs in
                      {task with particles = p, observations = obs}
                    else
                      let p = estimateNewParticles options task obs in
                      if gti p task.particles then
                        {task with particles = p, observations = obs}
                      else
                        {task with finished = true, observations = obs}
                in
                mapInsert taskId task state
              else error "Found WCET of invalid task, likely bug in configureTasks")
            state activeWcets
        in
        let g =
          mapFoldWithKey
            (lam g. lam taskId. lam task.
              if digraphHasVertex taskId g then
                if task.finished then
                  printLn (join ["Finished configuration of task ", taskId]);
                  digraphRemoveVertex taskId g
                else g
              else g)
            g state
        in
        work g state
  in
  let state =
    foldl
      (lam state. lam task.
        let taskState =
          { particles = task.particles, observations = mapEmpty subi
          , budget = task.budget, upperBound = defaultUpperBound
          , finished = false }
        in
        mapInsert task.id taskState state)
      (mapEmpty cmpString)
      tasks
  in
  work taskGraph state

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
