include "math.mc"
include "seq.mc"

let matMulConst : [[Float]] -> Float -> [[Float]] = lam m. lam x.
  map (map (mulf x)) m

let matInv : [[Float]] -> [[Float]] = lam m.
  match m with [[a, b], [c, d]] then
    let x = divf 1.0 (subf (mulf a d) (mulf b c)) in
    matMulConst [[d, negf b], [negf c, a]] x
  else error "Inverse only supported for 2x2 matrix"

let matTranspose : [[Float]] -> [[Float]] = lam m.
  let n1 = length m in
  if eqi n1 0 then [[]]
  else
    let n2 = length (head m) in
    create n2 (lam i. create n1 (lam j. get (get m j) i))

let matMul = lam l. lam r.
  map
    (lam row.
      map
        (lam col.
          foldl addf 0.0 (map (lam lr. mulf lr.0 lr.1) (zip row col)))
        (matTranspose r))
    l

let linearRegression = lam obs.
  match unzip obs with (xvals, yvals) in
  let x = map (lam xv. [1.0, int2float xv]) xvals in
  let y = map (lam yv. [int2float yv]) yvals in
  match
    matMul
      (matInv (matMul (matTranspose x) x))
      (matMul (matTranspose x) y)
  with [[intercept], [slope]] in
  (slope, intercept)

mexpr

let eqMat = eqSeq (eqSeq (eqfApprox 1e-6)) in

utest matMulConst [[1.0]] 2.0 with [[2.0]] using eqMat in
utest matMulConst [[1.0,2.0],[3.0,4.0]] 2.5 with [[2.5,5.0],[7.5,10.0]] using eqMat in

utest matInv [[4.0,7.0],[2.0,6.0]] with [[0.6,negf 0.7],[negf 0.2, 0.4]] using eqMat in

utest matTranspose [[1.0,2.0],[3.0,4.0]] with [[1.0,3.0],[2.0,4.0]] using eqMat in

utest matMul [[1.0,2.0],[3.0,4.0]] [[5.0,6.0],[7.0,8.0]] with [[19.0,22.0],[43.0,50.0]]
using eqMat in

utest linearRegression [(1,1423753),(100,2012120),(200,3358323),(400,4317528),(800,6382378)]
with (6147.920917, 1653214.540706)
using lam l. lam r. and (eqfApprox 1e-5 l.0 r.0) (eqfApprox 1e-5 l.1 r.1) in

()
