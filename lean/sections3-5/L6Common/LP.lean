import L6Common.Rows

/-!
# A floating-point simplex that proposes certificates, and their exact recovery

For a system of rows `lo ≤ a · h + c · s ≤ hi` (integer data, `n` heights), the program of the engine maximizes `s`
subject to the rows and `0 ≤ s ≤ 1`, and prunes when the maximum is at most `1e-9` (or the system is infeasible).

We solve the dual of that program by the revised primal simplex in floating point:

  minimize `Σ_{hi} hiᵢ uᵢ − Σ_{lo} loᵢ wᵢ + t`
  subject to `Σ uᵢ aᵢ − Σ wᵢ aᵢ = 0` (one equation per height), `Σ uᵢ cᵢ − Σ wᵢ cᵢ + t − σ = 1`, all variables ≥ 0.

It is feasible (`t = 1`), and its value is the maximum of `s` (or it is unbounded when the rows are infeasible). The
floating-point solution only proposes: at an optimal basis of value `≤ 1e-9`, and along an unbounded ray, the exact
vertex (or ray) is recomputed from the basis by fraction-free integer elimination, and the multipliers `y = u − w`
are passed to `Farkas.check` (Lemma 4.6). Any optimal or unbounded dual solution satisfies the hypotheses of
Lemma 4.6 in exact arithmetic, so a correct basis always yields an accepted certificate.

Nothing here is trusted: a prune is used only if `Farkas.check` accepts its certificate.
-/

namespace L6

namespace LP

/-- The columns of the dual program: `(row index, sign)` for `uᵢ` (`+1`, rows with an upper bound) and `wᵢ` (`−1`,
rows with a lower bound), then `t` and `σ` (row index `none`). -/
structure Col where
  row : Option Nat
  sign : Int
  deriving Inhabited

/-- Float entry `k` of the column `j` (length `n + 1`). -/
@[inline] def colEntry (rows : Array Row) (n : Nat) (col : Col) (k : Nat) : Float :=
  match col.row with
  | some i =>
    let r := rows[i]!
    let v : Int := if k < n then r.a[k]! else r.c
    Float.ofInt (col.sign * v)
  | none => if k == n then (if col.sign == 1 then 1.0 else -1.0) else 0.0

/-- Integer entry `k` of the column `j`. -/
@[inline] def colEntryInt (rows : Array Row) (n : Nat) (col : Col) (k : Nat) : Int :=
  match col.row with
  | some i =>
    let r := rows[i]!
    let v : Int := if k < n then r.a[k]! else r.c
    col.sign * v
  | none => if k == n then col.sign else 0

/-- The cost of a column. -/
def colCost (rows : Array Row) (col : Col) : Float :=
  match col.row with
  | some i =>
    let r := rows[i]!
    if col.sign == 1 then Float.ofInt (r.hi.getD 0) else Float.ofInt (-(r.lo.getD 0))
  | none => if col.sign == 1 then 1.0 else 0.0

/-- The columns of the dual program of a system. -/
def columns (rows : Array Row) : Array Col := Id.run do
  let mut cs : Array Col := #[]
  for i in [0:rows.size] do
    let r := rows[i]!
    if r.hi.isSome then cs := cs.push ⟨some i, 1⟩
    if r.lo.isSome then cs := cs.push ⟨some i, -1⟩
  cs := cs.push ⟨none, 1⟩     -- t
  cs := cs.push ⟨none, -1⟩    -- σ
  return cs

/-- Result of the floating-point solve: the basis (column indices; `≥ ncols` = artificial `k`), and how it ended. -/
inductive Outcome where
  | optimal (value : Float)
  | unbounded (entering : Nat)
  | stalled
  deriving Inhabited

structure Solve where
  basis : Array Nat
  outcome : Outcome
  iters : Nat
  deriving Inhabited

/-- The revised simplex on the dual program, from the basis (artificial 0, …, artificial n−1, t). Artificials never
enter, and a basic artificial blocks every nonzero step (it has bounds `[0, 0]`). Dantzig's rule, switching to Bland's
rule after degenerate stretches; `maxIter` caps the work (`stalled`). -/
def solve (rows : Array Row) (n : Nat) (cols : Array Col) (maxIter : Nat := 500) : Solve := Id.run do
  let m := n + 1
  let K := cols.size
  let tIdx := K - 2
  -- the columns as a dense K × m matrix, and the costs
  let mut cmat : FloatArray := FloatArray.mk (Array.replicate (K * m) 0.0)
  for j in [0:K] do
    for l in [0:m] do
      cmat := cmat.set! (j * m + l) (colEntry rows n cols[j]! l)
  let costs : FloatArray := FloatArray.mk (cols.map (colCost rows))
  -- basis inverse, row-major m × m
  let mut binv : FloatArray := FloatArray.mk (Array.replicate (m * m) 0.0)
  for k in [0:m] do
    binv := binv.set! (k * m + k) 1.0
  let mut basis : Array Nat := Array.ofFn (n := m) fun k => if k.val < n then K + k.val else tIdx
  let mut xB : FloatArray := FloatArray.mk ((Array.replicate m 0.0).set! n 1.0)
  let mut inBasis : Array Bool := (Array.replicate K false).set! tIdx true
  let mut iter := 0
  let mut degenerate := 0
  let eps := 1e-9
  let mut outcome := Outcome.stalled
  let mut done := false
  let mut pi : FloatArray := FloatArray.mk (Array.replicate m 0.0)
  let mut alpha : FloatArray := FloatArray.mk (Array.replicate m 0.0)
  while !done && iter < maxIter do
    iter := iter + 1
    -- duals π = c_B B⁻¹
    for l in [0:m] do
      pi := pi.set! l 0.0
    for k in [0:m] do
      let bk := basis[k]!
      let cb := if bk < K then costs[bk]! else 0.0
      if cb != 0.0 then
        for l in [0:m] do
          pi := pi.set! l (pi[l]! + cb * binv[k * m + l]!)
    -- pricing
    let bland := degenerate > 20
    let mut q := K
    let mut best := -eps
    for j in [0:K] do
      if !inBasis[j]! then
        let mut d := costs[j]!
        for l in [0:m] do
          d := d - pi[l]! * cmat[j * m + l]!
        if d < -eps then
          if bland then
            if q == K then q := j; best := d
          else if d < best then
            q := j; best := d
    if q == K then
      let mut v := 0.0
      for k in [0:m] do
        let bk := basis[k]!
        if bk < K then v := v + costs[bk]! * xB[k]!
      outcome := Outcome.optimal v
      done := true
    else
      -- direction α = B⁻¹ col_q
      for k in [0:m] do
        let mut a := 0.0
        for l in [0:m] do
          a := a + binv[k * m + l]! * cmat[q * m + l]!
        alpha := alpha.set! k a
      -- ratio test (basic artificials block any nonzero step)
      let mut r := m
      let mut theta := 0.0
      for k in [0:m] do
        let ak := alpha[k]!
        let bk := basis[k]!
        if bk ≥ K then
          if ak > eps || ak < -eps then
            if r == m || theta > 0.0 || bk < basis[r]! then
              r := k; theta := 0.0
        else if ak > eps then
          let ratio := xB[k]! / ak
          if r == m || ratio < theta - 1e-12 || (ratio ≤ theta + 1e-12 && bk < basis[r]!) then
            r := k; theta := ratio
      if r == m then
        outcome := Outcome.unbounded q
        done := true
      else
        if theta ≤ 1e-12 then degenerate := degenerate + 1 else degenerate := 0
        for k in [0:m] do
          xB := xB.set! k (xB[k]! - theta * alpha[k]!)
        xB := xB.set! r theta
        let ar := alpha[r]!
        for l in [0:m] do
          binv := binv.set! (r * m + l) (binv[r * m + l]! / ar)
        for k in [0:m] do
          if k != r then
            let f := alpha[k]!
            if f != 0.0 then
              for l in [0:m] do
                binv := binv.set! (k * m + l) (binv[k * m + l]! - f * binv[r * m + l]!)
        let old := basis[r]!
        if old < K then inBasis := inBasis.set! old false
        inBasis := inBasis.set! q true
        basis := basis.set! r q
  return { basis, outcome, iters := iter }

/-! ## Exact recovery -/

/-- Fraction-free elimination (Bareiss) on the `m × (m+1)` augmented integer matrix `[B | b]`; returns `(det, x·det)`
with `B x = b`, or `none` if `B` is singular. -/
def bareissSolve (m : Nat) (mat0 : Array (Array Int)) : Option (Int × Array Int) := Id.run do
  let mut mat := mat0
  let mut prev : Int := 1
  let mut sign : Int := 1
  for k in [0:m] do
    -- pivot search
    let mut p := m
    for i in [k:m] do
      if p == m && mat[i]![k]! != 0 then p := i
    if p == m then return none
    if p != k then
      let rk := mat[k]!
      mat := (mat.set! k mat[p]!).set! p rk
      sign := -sign
    let piv := mat[k]![k]!
    for i in [k+1:m] do
      let rowi := mat[i]!
      let rowk := mat[k]!
      let f := rowi[k]!
      let mut newRow := rowi
      for j in [k+1:m+1] do
        newRow := newRow.set! j ((piv * rowi[j]! - f * rowk[j]!) / prev)
      newRow := newRow.set! k 0
      mat := mat.set! i newRow
    prev := piv
  let det := prev
  -- back substitution with integers: x_i · det
  let mut x : Array Int := Array.replicate m 0
  let mut i := m
  while i > 0 do
    i := i - 1
    let row := mat[i]!
    let mut s : Int := row[m]! * det
    for j in [i+1:m] do
      s := s - row[j]! * x[j]!
    x := x.set! i (s / row[i]!)
  return some (det, x)

/-- The exact basic solution of the dual program for a basis: column values `x·D` with a common positive denominator
`D` (column index `≥ K` is an artificial); `none` if the basis matrix is singular. `rhs` is `e_n` for a vertex and
`col_q` for the direction of a ray. -/
def exactBasic (rows : Array Row) (n : Nat) (cols : Array Col) (basis : Array Nat) (rhs : Array Int) :
    Option (Int × Array Int) := Id.run do
  let m := n + 1
  let K := cols.size
  let mut mat : Array (Array Int) := #[]
  for i in [0:m] do
    let mut row : Array Int := #[]
    for k in [0:m] do
      let bk := basis[k]!
      let e : Int := if bk < K then colEntryInt rows n cols[bk]! i else (if bk - K == i then 1 else 0)
      row := row.push e
    row := row.push rhs[i]!
    mat := mat.push row
  match bareissSolve m mat with
  | none => return none
  | some (det, xd) =>
    if det < 0 then return some (-det, xd.map (- ·)) else return some (det, xd)

/-- The multipliers `y = u − w` (per row) of a dual vector given on the basis plus an extra column. -/
def multipliers (cols : Array Col) (entries : List (Nat × Int)) : List (Nat × Int) :=
  let K := cols.size
  let ys : List (Nat × Int) := entries.filterMap fun (j, v) =>
    if j < K then (cols[j]!.row.map fun i => (i, cols[j]!.sign * v)) else none
  -- merge equal row indices (a row may carry both u and w)
  ys.foldl (fun acc (i, v) =>
    match acc.find? (·.1 == i) with
    | some _ => acc.map fun (i', v') => if i' == i then (i', v' + v) else (i', v')
    | none => acc ++ [(i, v)]) []

/-- Verdict on a system: `true` = kept (the floating-point maximum of `s` exceeds `1e-9`, or no certificate was
verified); `false` = pruned with a certificate accepted by `Farkas.check`. Also returns whether a prune was refused
for lack of a verified certificate (a failure), and the certificate. -/
structure Verdict where
  kept : Bool
  failure : Bool
  cert : List (Nat × Int)
  deriving Inhabited

def decide (rows : Array Row) (n : Nat) : Verdict := Id.run do
  let cols := columns rows
  let K := cols.size
  let sol := solve rows n cols
  match sol.outcome with
  | .optimal v =>
    if v > 1e-9 then return { kept := true, failure := false, cert := [] }
    match exactBasic rows n cols sol.basis ((Array.replicate (n + 1) 0).set! n 1) with
    | none => return { kept := true, failure := true, cert := [] }
    | some (_, xd) =>
      -- basic artificials must vanish exactly
      let mut ok := true
      let mut entries : List (Nat × Int) := []
      for k in [0:n+1] do
        let bk := sol.basis[k]!
        if bk ≥ K then
          if xd[k]! != 0 then ok := false
        else entries := entries ++ [(bk, xd[k]!)]
      let cert := multipliers cols entries
      if ok && Farkas.check n rows cert then return { kept := false, failure := false, cert }
      return { kept := true, failure := true, cert := [] }
  | .unbounded q =>
    let rhs := Array.ofFn (n := n + 1) fun i => colEntryInt rows n cols[q]! i.val
    match exactBasic rows n cols sol.basis rhs with
    | none => return { kept := true, failure := true, cert := [] }
    | some (det, zd) =>
      -- ray: x_q = det, x_B = −z·det (scaled by det > 0)
      let mut ok := true
      let mut entries : List (Nat × Int) := [(q, det)]
      for k in [0:n+1] do
        let bk := sol.basis[k]!
        if bk ≥ K then
          if zd[k]! != 0 then ok := false
        else entries := entries ++ [(bk, -zd[k]!)]
      let cert := multipliers cols entries
      if ok && Farkas.check n rows cert then return { kept := false, failure := false, cert }
      return { kept := true, failure := true, cert := [] }
  | .stalled => return { kept := true, failure := true, cert := [] }

end LP

end L6
