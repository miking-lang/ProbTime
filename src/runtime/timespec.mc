include "ext/rtppl-ext.mc"

let nanosPerSec = 1000000000
let millisPerSec = 1000
let millisPerNano = divi nanosPerSec millisPerSec

let nanosToTimespec : Int -> Timespec = lam nanos.
  let s = divi nanos nanosPerSec in
  let ns = modi nanos nanosPerSec in
  (s, ns)

let millisToTimespec : Int -> Timespec = lam ms.
  let ns = muli millisPerNano ms in
  nanosToTimespec ns

let timespecToNanos : Timespec -> Int = lam ts.
  match ts with (s, ns) in
  addi (muli s nanosPerSec) ns

let timespecToMillis : Timespec -> Int = lam ts.
  let ns = timespecToNanos ts in
  divi ns millisPerNano

let addTimespec : Timespec -> Timespec -> Timespec = lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  let s = addi ls rs in
  let ns = addi lns rns in
  if geqi ns nanosPerSec then (addi s 1, subi ns nanosPerSec)
  else (s, ns)

let diffTimespec : Timespec -> Timespec -> Timespec = lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  let s = subi ls rs in
  let ns = subi lns rns in
  if lti ns 0 then (subi s 1, addi ns nanosPerSec)
  else (s, ns)

let cmpTimespec : Timespec -> Timespec -> Int = lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  if gti ls rs then 1
  else if lti ls rs then -1
  else if gti lns rns then 1
  else if lti lns rns then -1
  else 0

 mexpr

let eqTimespec = lam lhs. lam rhs. eqi (cmpTimespec lhs rhs) 0 in

utest millisToTimespec 0 with (0, 0) using eqTimespec in
utest millisToTimespec 30 with (0, muli 30 millisPerNano)
using eqTimespec in
utest millisToTimespec 1020 with (1, muli 20 millisPerNano)
using eqTimespec in
utest millisToTimespec 2000 with (2, 0) using eqTimespec in

utest timespecToMillis (0, 1) with 0 using eqi in
utest timespecToMillis (0, muli 10 millisPerNano) with 10 using eqi in
utest timespecToMillis (2, muli 22 millisPerNano) with 2022 using eqi in
utest timespecToMillis (0, 123456789) with 123 using eqi in
utest timespecToMillis (0, 987654321) with 987 using eqi in

let zero = millisToTimespec 0 in
let a = millisToTimespec 10 in
let b = millisToTimespec 20 in
let c = millisToTimespec 2022 in
utest addTimespec a a with b using eqTimespec in
utest addTimespec b c with millisToTimespec 2042 using eqTimespec in
utest addTimespec b c with addTimespec c b using eqTimespec in
utest diffTimespec a b with (negi 1, 990000000) using eqTimespec in
utest diffTimespec b a with a using eqTimespec in
utest diffTimespec (diffTimespec b a) a with zero using eqTimespec in
utest diffTimespec c a with millisToTimespec 2012 using eqTimespec in
utest diffTimespec b c with (negi 3, 998000000) using eqTimespec in

utest cmpTimespec a a with 0 using eqi in
utest cmpTimespec a b with negi 1 using eqi in
utest cmpTimespec b a with 1 using eqi in
utest cmpTimespec a c with negi 1 using eqi in
utest cmpTimespec c b with 1 using eqi in
utest cmpTimespec c c with 0 using eqi in
utest cmpTimespec zero a with negi 1 using eqi in

()
