include "common.mc"
include "math.mc"
include "set.mc"

include "definitions.mc"

let getPeriod = lam tasks. lam i.
  (get tasks i).period

let getExecTime = lam tasks. lam i.
  (get tasks i).budget

let schedulingPoints = lam tasks. lam i.
  recursive let work = lam i. lam t.
    if lti i 0 then setOfSeq cmpFloat [int2float t]
    else
      let periodi = getPeriod tasks i in
      setUnion
        (work (subi i 1)
          (muli (floorfi (divf (int2float t) (int2float periodi))) periodi))
        (work (subi i 1) t)
  in
  let periodi = getPeriod tasks i in
  setToSeq (work (subi i 1) periodi)

let schedulable : [TaskData] -> Bool = lam tasks.
  let n = length tasks in
  foldl
    (lam acc. lam i.
      if acc then
        foldl
          (lam acc. lam t.
            if acc then true
            else
              let execi = getExecTime tasks i in
              let inner =
                create i
                  (lam j.
                    let periodj = getPeriod tasks j in
                    let execj = getExecTime tasks j in
                    muli (ceilfi (divf t (int2float periodj))) execj)
              in
              if leqf (int2float (foldl addi execi inner)) t then true
              else false)
          false
          (schedulingPoints tasks i)
      else false)
    true
    (create n (lam i. i))

let dotProduct = lam lhs. lam rhs.
  foldl
    (lam acc. lam e.
      match e with (l, r) in
      addf acc (mulf l r))
    0.0
    (zip lhs rhs)

let computeLambda : [TaskData] -> Float = lam tasks.
  let d = map (lam t. t.importance) tasks in
  let n = length tasks in
  let values =
    create n
      (lam i.
        let ni = lam t.
          snoc
            (create i
              (lam j.
                let tj = getPeriod tasks j in
                int2float (ceilfi (divf t (int2float tj)))))
            1.0
        in
        let ci = create (addi i 1) (lam j. int2float (getExecTime tasks j)) in
        let di = subsequence d 0 (addi i 1) in
        let schedules =
          map
            (lam t. divf (subf t (dotProduct (ni t) ci))
                         (dotProduct (ni t) di))
            (schedulingPoints tasks i)
        in
        match max (cmpfApprox 0.0) schedules with Some v in
        v)
  in
  match min (cmpfApprox 0.0) values with Some lambda in
  lambda

mexpr

let tasks = [] in
utest schedulable tasks with true in

let tasks = [
  {defaultTaskData with period = 100, budget = 50},
  {defaultTaskData with period = 100, budget = 50}
] in
utest schedulingPoints tasks 0 with [100] in
utest schedulingPoints tasks 1 with [100] in
utest schedulable tasks with true in
utest computeLambda tasks with 0.0 using eqfApprox 1e-6 in

let tasks = [
  {defaultTaskData with period = 100, budget = 50},
  {defaultTaskData with period = 100, budget = 51}
] in
utest schedulable tasks with false in
utest computeLambda tasks with 0.0 using ltf in

let tasks = [
  {defaultTaskData with period = 300, budget = 10},
  {defaultTaskData with period = 350, budget = 10},
  {defaultTaskData with period = 1000, budget = 900}
] in
utest schedulingPoints tasks 0 with [300] in
utest schedulingPoints tasks 1 with [300, 350] in
utest schedulingPoints tasks 2 with [600, 700, 900, 1000] in
utest schedulable tasks with true in
utest computeLambda tasks with 0.0 using gtf in

let tasks = [
  {defaultTaskData with period = 1000}
] in
utest computeLambda tasks with 1000.0 using eqfApprox 1e-6 in

let tasks = [
  {defaultTaskData with period = 500},
  {defaultTaskData with period = 1000}
] in
utest computeLambda tasks with 333.333333 using eqfApprox 1e-6 in

()
