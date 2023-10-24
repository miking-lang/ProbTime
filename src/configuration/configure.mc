include "common.mc"
include "digraph.mc"
include "map.mc"
include "sys.mc"

include "definitions.mc"
include "regression.mc"
include "schedulable.mc"

type TaskConfigState = {
  particles : Int,
  budget : Int,
  lowerBound : Int,
  upperBound : Int,
  finished : Bool
}

let defaultUpperBound = floorfi 1e10

let writeTaskConfig = lam path. lam task.
  let taskConfigFile = sysJoinPath path (concat task.id ".config") in
  -- NOTE(larshum, 2023-10-17): When configuring tasks, we always assume a
  -- slowdown factor of 1, i.e., that we are replaying data in real-time.
  let msg = join [int2string task.particles, " ", int2string task.budget, " 1"] in
  writeFile taskConfigFile msg

let readTaskCollect = lam path. lam taskId.
  let taskCollectFile = sysJoinPath path (concat taskId ".collect") in
  recursive let readRetry = lam retries.
    let wcet =
      if fileExists taskCollectFile then
        let data = map string2int (strSplit "\n" (strTrim (readFile taskCollectFile))) in
        foldl maxi 0 (init data)
      else
        0
    in
    if eqi wcet 0 then
      if eqi retries 0 then wcet
      else
        sleepMs 500;
        readRetry (subi retries 1)
    else wcet
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

let configureTasksExecutionTimeFairness = lam options. lam taskGraph. lam tasks.
  recursive let work = lam g. lam state.
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
    if eqi (digraphCountVertices g) 0 then
      map
        (lam task.
          match task with (taskId, {particles = p, budget = b}) in
          (taskId, p, b))
        (mapBindings state)
    else
      let wcets =
        let twpc = tasksWithParticleCounts tasks state in
        let res = create 3 (lam. runTasks options.systemPath options.runnerCmd twpc) in
        foldl
          (lam acc. lam wcets.
            mapMerge
              (lam lhs. lam rhs.
                match (lhs, rhs) with (Some l, Some r) then
                  Some (maxi l r)
                else error "Incompatible results from runTasks")
              acc wcets)
          (head res) (tail res)
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
                printLn (join [
                  "Fixed task ", task.id, " overran; wcet=", int2string wcet,
                  ", budget=", int2string task.budget]);
                let ts = {ts with lowerBound = 1, upperBound = ts.particles,
                                  finished = false}
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
                let ts = {taskState with lowerBound = 1, finished = false} in
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
              match mapLookup taskId state with Some task then
                let task =
                  if lti (addi task.lowerBound 1) task.upperBound then
                    let safeBudget = floorfi (mulf (int2float task.budget) options.budgetRatio) in
                    let task =
                      if gti wcet safeBudget then
                        {task with upperBound = task.particles}
                      else
                        {task with lowerBound = task.particles}
                    in
                    let p =
                      if eqi task.upperBound defaultUpperBound then
                        muli task.lowerBound 2
                      else
                        divi (addi task.lowerBound task.upperBound) 2
                    in
                    {task with particles = p}
                  else
                    {task with particles = task.lowerBound, finished = true}
                in
                mapInsert taskId task state
              else error "Found WCET of invalid task, likely bug in configureTasks")
            state activeWcets
        in
        work g state
  in
  let state =
    foldl
      (lam state. lam task.
        let taskState =
          { particles = task.particles, budget = task.budget
          , lowerBound = 1, upperBound = defaultUpperBound
          , finished = false }
        in
        mapInsert task.id taskState state)
      (mapEmpty cmpString)
      tasks
  in
  work taskGraph state

let configureTasksParticleFairness = lam options. lam tasks.
  recursive let findMaximumConstantFactor = lam state.
    if lti (addi state.lowerBound 1) state.upperBound then
      let k =
        if eqi state.upperBound defaultUpperBound then
          muli state.lowerBound 2
        else
          divi (addi state.lowerBound state.upperBound) 2
      in
      let wcets =
        let tasks = map (lam t. {t with particles = muli k t.importance}) tasks in
        -- NOTE(larshum, 2023-10-14): We repeat the estimations three times and
        -- taking the maximum WCET among the runs for each task.
        let res = create 3 (lam. runTasks options.systemPath options.runnerCmd tasks) in
        foldl
          (lam acc. lam wcets.
            mapMerge
              (lam lhs. lam rhs.
                match (lhs, rhs) with (Some l, Some r) then
                  Some (maxi l r)
                else error "Incompatible results from runTasks")
              acc wcets)
          (head res) (tail res)
      in
      let updState =
        let wcets =
          mapMerge
            (lam l. lam r.
              match (l, r) with (_, Some wcet) then
                Some (floorfi (divf (int2float wcet) options.budgetRatio))
              else
                error "Missing worst-case execution time for task")
            state.wcets wcets
        in
        {state with wcets = wcets}
      in
      let tasksPerCore =
        foldl
          (lam tasksPerCore. lam t.
            let t =
              match mapLookup t.id updState.wcets with Some budget then
                {t with budget = maxi t.budget budget}
              else
                error (concat "Found no WCET for task " t.id)
            in
            match mapLookup t.core tasksPerCore with Some coreTasks then
              mapInsert t.core (snoc coreTasks t) tasksPerCore
            else
              mapInsert t.core [t] tasksPerCore)
          (mapEmpty subi) tasks
      in
      let tasksSchedulable =
        mapFoldWithKey
          (lam acc. lam. lam coreTasks.
            if acc then schedulable coreTasks else false)
          true tasksPerCore
      in
      let state =
        if tasksSchedulable then
          {updState with lowerBound = k}
        else
          {updState with upperBound = k}
      in
      findMaximumConstantFactor state
    else state
  in
  let initState =
    {lowerBound = 1, upperBound = defaultUpperBound, wcets = mapEmpty cmpString}
  in
  findMaximumConstantFactor initState

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
