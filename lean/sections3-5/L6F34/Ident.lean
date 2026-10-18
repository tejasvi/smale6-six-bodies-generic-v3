import L6F34.Basic
import L6Common.Rows

/-!
# F3, F4: the cell polyhedron and the identities with their terms

For a stored cell of a class representative this module builds, independently of the search of F2:

* the heights: one variable per internal node of each tree (z-tree first);
* the rows of the relatively open cell `Π` (`tsec.cell_lp` of the engine: the rows of `tengine.base_lp` over all
  points and, for every base identity, the rows saying that exactly its argmin terms attain the least exponent),
  with every row multiplied by `2` so that the data are integers;
* the identities of §2.3 and §5.1 by name (`texact.identities`, the rows `D`, `tsec.secondary`), each term with its
  exponent form (twice the exponent, as an integer vector over the heights) and its leading coefficient: twice the
  rational coefficient, the mass factors, `M = Σ m`, the powers of the leading coefficients `D_kl` of `p_kl`, `E`, and
  the leading coefficients of separations and positions (differences of node coordinates, Lemma 4.2).

The conventions (signs, mass factors, the `½` of the partial virials, `−M E` in `I`, `−E` in `U` and `Ip`) are those of
the engine's `tinit.system` and `tsec.term_expr`, which wrote the stored cores.
-/

namespace L6.F34

/-- The leading coefficient of one term: `num / 2` times the product of the factors. -/
structure Coef where
  num : Int
  masses : List Nat := []
  massSum : Bool := false
  dvars : List (Nat × Nat × Nat) := []
  evar : Bool := false
  /-- `(z?, p, q)`: the leading coefficient of `z_p − z_q` (or `w`); `q = 6` is the centre of mass. -/
  leads : List (Bool × Nat × Nat) := []
  deriving Inhabited, Repr

/-- A term of an identity: label, twice its exponent (integer vector over the heights), coefficient. -/
structure Term where
  lab : Lab
  expo : Array Int
  coef : Coef
  deriving Inhabited

/-- The context of a cell: diagram, trees, height indices. -/
structure Ctx where
  d : Diagram
  zt : Tree
  wt : Tree
  zIdx : Array (Option Nat)
  wIdx : Array (Option Nat)
  nh : Nat
  deriving Inhabited

def Ctx.mk' (d : Diagram) (c : Cell) : Ctx := Id.run do
  let mut zIdx : Array (Option Nat) := Array.replicate maxNode none
  let mut wIdx : Array (Option Nat) := Array.replicate maxNode none
  let mut i := 0
  for (v, _) in c.zt.kids do
    zIdx := zIdx.set! v (some i)
    i := i + 1
  for (v, _) in c.wt.kids do
    wIdx := wIdx.set! v (some i)
    i := i + 1
  return { d, zt := c.zt, wt := c.wt, zIdx, wIdx, nh := i }

/-- The unit vector of height `j` times `c`. -/
def Ctx.unit (x : Ctx) (j : Nat) (c : Int) : Array Int := (Array.replicate x.nh 0).set! j c

def vadd (a b : Array Int) : Array Int := Array.zipWith (· + ·) a b

def vsub (a b : Array Int) : Array Int := Array.zipWith (· - ·) a b

def vscale (c : Int) (a : Array Int) : Array Int := a.map (c * ·)

/-- Height index of the meet of `p, q` in the z-tree (or w-tree). -/
def Ctx.meetIdx (x : Ctx) (z : Bool) (p q : Nat) : Option Nat :=
  if z then (x.zt.meet p q).bind fun v => x.zIdx.getD v none
  else (x.wt.meet p q).bind fun v => x.wIdx.getD v none

/-- Twice the exponent of the position `z_k` (`w_k`), or `none` if the body sits at `O` in that tree. -/
def Ctx.posE (x : Ctx) (z : Bool) (k : Nat) : Option (Array Int) :=
  (x.meetIdx z k nB).map fun j => x.unit j 2

/-- Twice the exponent of the separation `z_kl` (`w_kl`). -/
def Ctx.sepE (x : Ctx) (z : Bool) (k l : Nat) : Array Int :=
  match x.meetIdx z k l with
  | some j => x.unit j 2
  | none => Array.replicate x.nh 0

/-- Twice `x_kl = (ζ_kl + ω_kl) / 2`. -/
def Ctx.xE (x : Ctx) (k l : Nat) : Array Int := Id.run do
  let mut v := Array.replicate x.nh 0
  if let some j := x.meetIdx true k l then v := v.set! j (v[j]! + 1)
  if let some j := x.meetIdx false k l then v := v.set! j (v[j]! + 1)
  return v

/-- Twice the exponent of `p_kl` (`−x_kl`). -/
def Ctx.dlE (x : Ctx) (k l : Nat) : Array Int := vscale (-1) (x.xE k l)

/-- Twice the exponent of `Z_kl = p_kl³ z_kl` (or `W_kl`): `3 e(p_kl) + e(z_kl)`. -/
def Ctx.bigE (x : Ctx) (z : Bool) (k l : Nat) : Array Int := vadd (vscale 3 (x.dlE k l)) (x.sepE z k l)

/-- The pairs `(k, l)`, `k < l`, in the order of `itertools.combinations(range(6), 2)`. -/
def pairs6 : List (Nat × Nat) := (List.range 6).flatMap fun k => ((List.range 6).filter (k < ·)).map fun l => (k, l)

/-- The `D` variable of a pair. -/
def dv (k l : Nat) : Nat × Nat := if k < l then (k, l) else (l, k)

/-- The base identities (`texact.identities`): terms in the engine's order. -/
def Ctx.baseTerms (x : Ctx) : IdName → Option (Array Term)
  | .body z k => some <| Id.run do
    let mut ts : Array Term := #[]
    if let some e := x.posE z k then
      ts := ts.push { lab := .pos k, expo := e, coef := { num := 2, masses := [k], leads := [(z, k, nB)] } }
    for j in List.range 6 do
      if j != k then
        let (a, b) := dv k j
        ts := ts.push { lab := .cross k j, expo := x.bigE z k j, coef := { num := -2, masses := [k, j], dvars := [(a, b, 3)], leads := [(z, k, j)] } }
    return ts
  | .U => some <| #[{ lab := .E, expo := Array.replicate x.nh 0, coef := { num := -2, evar := true } }] ++
      (pairs6.map fun (k, l) => ({ lab := .delta k l, expo := x.dlE k l,
                                   coef := { num := 2, masses := [k, l], dvars := [(k, l, 1)] } } : Term)).toArray
  | .I => some <| #[{ lab := .E, expo := Array.replicate x.nh 0, coef := { num := -2, massSum := true, evar := true } }] ++
      (pairs6.map fun (k, l) => ({ lab := .zw k l, expo := vscale 2 (x.xE k l),
                                   coef := { num := 2, masses := [k, l], leads := [(true, k, l), (false, k, l)] } } : Term)).toArray
  | _ => none

/-- `J` is a strictly increasing list of bodies. -/
def validSet (J : List Nat) : Bool := J.all (· < 6) && (J.zip (J.drop 1)).all fun (a, b) => a < b

/-- The complement of `J` in the bodies, increasing. -/
def compl (J : List Nat) : List Nat := (List.range 6).filter fun j => !J.contains j

/-- The secondary identities of §5.1 (`tsec.secondary`), with the membership conditions of the paper's list:
torques for `J ∋ 0`, `|J| ≤ 5`; partial virials for nonempty `J ≠ {0, …, 5}`; subset sums for `2 ≤ |J| ≤ 4`;
differences for pairs `k < l`; `Ip`; `UI`. -/
def Ctx.secTerms (x : Ctx) : IdName → Option (Array Term)
  | .torque J =>
    if !(validSet J && J.head? == some 0 && J.length ≤ 5) then none else some <| Id.run do
      let mut ts : Array Term := #[]
      for k in J do
        for l in compl J do
          let (a, b) := dv k l
          if let (some za, some wb) := (x.posE true k, x.posE false l) then
            ts := ts.push { lab := .T1 k l, expo := vadd (vadd (vscale 3 (x.dlE k l)) za) wb, coef := { num := 2, masses := [k, l], dvars := [(a, b, 3)], leads := [(true, k, nB), (false, l, nB)] } }
          if let (some wb, some za) := (x.posE false k, x.posE true l) then
            ts := ts.push { lab := .T2 k l, expo := vadd (vadd (vscale 3 (x.dlE k l)) wb) za, coef := { num := -2, masses := [k, l], dvars := [(a, b, 3)], leads := [(false, k, nB), (true, l, nB)] } }
      return ts
  | .virial J =>
    if !(validSet J && 1 ≤ J.length && J.length ≤ 5) then none else some <| Id.run do
      let mut ts : Array Term := #[]
      for k in J do
        if let (some za, some wb) := (x.posE true k, x.posE false k) then
          ts := ts.push { lab := .V0 k, expo := vadd za wb, coef := { num := 2, masses := [k], leads := [(true, k, nB), (false, k, nB)] } }
      for (k, l) in pairs6 do
        if J.contains k && J.contains l then
          ts := ts.push { lab := .V1 k l, expo := x.dlE k l, coef := { num := -2, masses := [k, l], dvars := [(k, l, 1)] } }
      for k in J do
        for l in compl J do
          let (a, b) := dv k l
          if let some wb := x.posE false k then
            ts := ts.push { lab := .V2 k l, expo := vadd (vadd (vscale 3 (x.dlE k l)) wb) (x.sepE true k l), coef := { num := -1, masses := [k, l], dvars := [(a, b, 3)], leads := [(false, k, nB), (true, k, l)] } }
          if let some za := x.posE true k then
            ts := ts.push { lab := .V3 k l, expo := vadd (vadd (vscale 3 (x.dlE k l)) za) (x.sepE false k l), coef := { num := -1, masses := [k, l], dvars := [(a, b, 3)], leads := [(true, k, nB), (false, k, l)] } }
      return ts
  | .diff z k l =>
    if !(k < l && l < 6) then none else some <| Id.run do
      let mut ts : Array Term := #[{ lab := .D0 z k l, expo := x.sepE z k l, coef := { num := 2, leads := [(z, k, l)] } }]
      for j in List.range 6 do
        if j != k then
          let (a, b) := dv k j
          ts := ts.push { lab := .D1 z k j, expo := x.bigE z k j, coef := { num := -2, masses := [j], dvars := [(a, b, 3)], leads := [(z, k, j)] } }
        if j != l then
          let (a, b) := dv l j
          ts := ts.push { lab := .D2 z l j, expo := x.bigE z l j, coef := { num := 2, masses := [j], dvars := [(a, b, 3)], leads := [(z, l, j)] } }
      return ts
  | .subset z J =>
    if !(validSet J && 2 ≤ J.length && J.length ≤ 4) then none else some <| Id.run do
      let mut ts : Array Term := #[]
      for i in J do
        if let some e := x.posE z i then
          ts := ts.push { lab := .SP z i, expo := e, coef := { num := 2, masses := [i], leads := [(z, i, nB)] } }
      for i in J do
        for j in compl J do
          let (a, b) := dv i j
          ts := ts.push { lab := .SC z i j, expo := x.bigE z i j, coef := { num := -2, masses := [i, j], dvars := [(a, b, 3)], leads := [(z, i, j)] } }
      return ts
  | .Ip => some <| Id.run do
    let mut ts : Array Term := #[{ lab := .E0, expo := Array.replicate x.nh 0, coef := { num := -2, evar := true } }]
    for k in List.range 6 do
      if let (some za, some wb) := (x.posE true k, x.posE false k) then
        ts := ts.push { lab := .V0 k, expo := vadd za wb, coef := { num := 2, masses := [k], leads := [(true, k, nB), (false, k, nB)] } }
    return ts
  | .UI => some <| Id.run do
    let mut ts : Array Term := (pairs6.map fun (k, l) =>
      ({ lab := .U k l, expo := x.dlE k l, coef := { num := 2, masses := [k, l], dvars := [(k, l, 1)] } } : Term)).toArray
    for k in List.range 6 do
      if let (some za, some wb) := (x.posE true k, x.posE false k) then
        ts := ts.push { lab := .Ip k, expo := vadd za wb, coef := { num := -2, masses := [k], leads := [(true, k, nB), (false, k, nB)] } }
    return ts
  | _ => none

/-- Index of a label in a term list. -/
def findLab (ts : Array Term) (l : Lab) : Option Nat := ts.findIdx? (·.lab == l)

/-! ## Rows -/

/-- The rows of `tengine.base_lp` over all points (times 2); `none` if a circled body sits at `O`. -/
def Ctx.baseRows (x : Ctx) : Option (Array Row) := Id.run do
  let nh := x.nh
  let mut rows : Array Row := #[]
  for (t, idx) in [(x.zt, x.zIdx), (x.wt, x.wIdx)] do
    if let some r := idx.getD t.root none then
      rows := rows.push { a := x.unit r 2, c := 0, lo := some (-4), hi := none }
    for (v, cs) in t.kids do
      for c in cs do
        if let (some ic, some iv) := (idx.getD c none, idx.getD v none) then
          rows := rows.push { a := (x.unit ic 2).set! iv (-2), c := -2, lo := some 0, hi := none }
  for (k, l) in pairs6 do
    let some zj := x.meetIdx true k l | return none
    let some wj := x.meetIdx false k l | return none
    let a1 := ((Array.replicate nh 0).set! zj 2).set! wj 6
    let a2 := ((Array.replicate nh 0).set! zj 6).set! wj 2
    rows := rows.push (if x.d.zstroke k l then { a := a1, c := 0, lo := some 8, hi := some 8 }
                       else { a := a1, c := 2, lo := none, hi := some 8 })
    rows := rows.push (if x.d.wstroke k l then { a := a2, c := 0, lo := some 8, hi := some 8 }
                       else { a := a2, c := 2, lo := none, hi := some 8 })
  for k in List.range 6 do
    for (z, circ) in [(true, x.d.zc), (false, x.d.wc)] do
      match x.meetIdx z k nB with
      | none => if circ.getD k false then return none
      | some j =>
        if circ.getD k false then rows := rows.push { a := x.unit j 2, c := 0, lo := some (-4), hi := some (-4) }
        else rows := rows.push { a := x.unit j 2, c := -2, lo := some (-4), hi := none }
  return some rows

/-- `texact.forced_rows`: exactly the terms `S` (first element `S[0]`) attain the least exponent. -/
def forcedRows (ts : Array Term) (S : Array Nat) : Option (Array Row) := Id.run do
  let some f0 := S[0]? | return none
  let some t0 := ts[f0]? | return none
  let mut rows : Array Row := #[]
  for t in [0:ts.size] do
    if t != f0 then
      let d := vsub ts[t]!.expo t0.expo
      if S.contains t then rows := rows.push { a := d, c := 0, lo := some 0, hi := some 0 }
      else rows := rows.push { a := d, c := -2, lo := some 0, hi := none }
  return some rows

/-- The rows of the cell `Π` (`tsec.cell_lp`), and the argmin index sets of its base identities. -/
def Ctx.cellRows (x : Ctx) (c : Cell) : Option (Array Row) := do
  let mut rows ← x.baseRows
  for (nm, labs) in c.argmin do
    let ts ← x.baseTerms nm
    let S ← labs.mapM (findLab ts)
    rows := rows ++ (← forcedRows ts S)
  some rows

end L6.F34
