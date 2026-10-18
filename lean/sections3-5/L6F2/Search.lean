import L6Common.LP
import L6F1.Rules
import L6F2.Tree
import L6F2.Point

/-!
# The search of Proposition 4.5: a replica of the engine's certified enumeration

`runPart` replicates `treplay.enumerate_cells` of the engine (tag generic-v1) with the options of the stored run
(`--mode le --base --split 3 --nparts 384`): the bodies are inserted into both trees in the order `orderBodies`, every
pair of partial trees is tested by a linear program (the constraints of `base_lp` and the relaxation of `ℓ(x) ≤ 0`
of `threshold_row`), and below each complete pair the argmin sets of the base identities (the twelve equations of
the bodies, `U = E`, `I = ME`) are chosen one identity and one term at a time (`exact_argmins`), each choice tested
by a linear program. Every row is the engine's row multiplied by `2`.

Every linear program is decided by `decideLP`: the floating-point simplex of `L6Common.LP` proposes, and a program is
discarded only if `Farkas.check` (the hypotheses of Lemma 4.6) accepts a certificate for its rows; otherwise it is
kept, and if the floating-point verdict was "discard" this is counted as a failure. The counters `lp` and `pruned`
are those of the engine's `Certifier` (`c['lp']`, `c['pruned']`).

A cell is written as the engine writes it, up to the key `"x"`: `{"ztree": …, "wtree": …, "argmin": […], "x": `.
-/

namespace L6.F2

/-- The pairs `k < l` of six bodies in the order of `itertools.combinations(range(6), 2)`. -/
def pairs6 : Array (Nat × Nat) :=
  #[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

/-- A diagram as the engine reads it: strokes of each colour (by `6k + l`, `k < l`) and circles. -/
structure Diag where
  zs : Array Bool
  ws : Array Bool
  zc : Array Bool
  wc : Array Bool
  deriving Inhabited

/-- The diagram of a labelled diagram of `L6F1` (kinds 1 `z`, 2 `w`, 3 `zw`; circle masks). -/
def Diag.ofF1 (d : L6F1.Diagram) : Diag :=
  { zs := Array.ofFn (n := 36) fun i => let k := i.val / 6; let l := i.val % 6; k < l && L6F1.zStroke d.e k l
    ws := Array.ofFn (n := 36) fun i => let k := i.val / 6; let l := i.val % 6; k < l && L6F1.wStroke d.e k l
    zc := Array.ofFn (n := 6) fun k => L6F1.circled d.zc k.val
    wc := Array.ofFn (n := 6) fun k => L6F1.circled d.wc k.val }

@[inline] def Diag.zstroke (D : Diag) (k l : Nat) : Bool := D.zs[6 * min k l + max k l]!
@[inline] def Diag.wstroke (D : Diag) (k l : Nat) : Bool := D.ws[6 * min k l + max k l]!

/-- `order_bodies`: first the body of largest degree (smallest index on ties), then repeatedly the body with the most
edges to the bodies already ordered (then degree, then smallest index). -/
def orderBodies (D : Diag) : Array Nat := Id.run do
  let edge := fun (k l : Nat) => k != l && (D.zstroke k l || D.wstroke k l)
  let deg := Array.ofFn (n := 6) fun k => ((List.range 6).filter fun l => edge k.val l).length
  -- key comparison (a, b, -k): larger a, then larger b, then smaller k
  let better := fun (a1 b1 k1 a2 b2 k2 : Nat) => a1 > a2 || (a1 == a2 && (b1 > b2 || (b1 == b2 && k1 < k2)))
  let mut first := 0
  for k in [1:6] do
    if better 0 deg[k]! k 0 deg[first]! first then first := k
  let mut order : Array Nat := #[first]
  while order.size < 6 do
    let mut best := NONE
    for k in [0:6] do
      if !order.contains k then
        if best == NONE then best := k
        else
          let ak := ((List.range 6).filter fun l => edge k l && order.contains l).length
          let ab := ((List.range 6).filter fun l => edge best l && order.contains l).length
          if better ak deg[k]! k ab deg[best]! best then best := k
    order := order.push best
  return order

/-- A linear form in the heights (`nv` entries). -/
abbrev Form := Array Int

/-- `e · coefficient` at the position `i` of a zero form. -/
def unit (nv i : Nat) (c : Int) : Form := (Array.replicate nv 0).set! i c

/-- The form with `c₁` at `i` and `c₂` at `j` (`i ≠ j`). -/
def two (nv i j : Nat) (c1 c2 : Int) : Form := ((Array.replicate nv 0).set! i c1).set! j c2

def Form.sub (a b : Form) : Form := Array.zipWith (· - ·) a b

/-- The variables of a pair of trees: internal nodes of the `z`-tree in the order of `children`, then those of the
`w`-tree. -/
structure Vars where
  nz : Nat
  nv : Nat
  zIdx : Array Nat
  wIdx : Array Nat

def Vars.of (zt wt : Tree) : Vars :=
  let nz := zt.childOrder.size
  { nz, nv := nz + wt.childOrder.size, zIdx := zt.indexMap 0, wIdx := wt.indexMap nz }

/-- `base_lp`: (T) root heights `≥ −2` and heights increasing along the trees, (O1)/(O2) for the pairs of inserted
bodies, (C) for the positions of the inserted bodies; `none` when a circled body sits at `O`. `pts` lists the
inserted points (with `O = 6`) in the engine's order. -/
def baseLP (D : Diag) (zt wt : Tree) (V : Vars) (pts : Array Nat) : Option (Array Row) := Id.run do
  let nv := V.nv
  let mut rows : Array Row := #[]
  for (T, idx) in [(zt, V.zIdx), (wt, V.wIdx)] do
    if T.root != NONE && T.isInternal T.root then
      rows := rows.push { a := unit nv idx[T.root]! 2, c := 0, lo := some (-4), hi := none }
    for v in T.childOrder do
      for c in T.childrenOf[v]! do
        if T.isInternal c then
          rows := rows.push { a := two nv idx[c]! idx[v]! 2 (-2), c := -2, lo := some 0, hi := none }
  let bodies := pts.filter (· != 6)
  let sorted := bodies.qsort (· < ·)
  for x in [0:sorted.size] do
    for y in [x+1:sorted.size] do
      let k := sorted[x]!
      let l := sorted[y]!
      let Z := V.zIdx[(zt.meet k l).getD NONE]!
      let W := V.wIdx[(wt.meet k l).getD NONE]!
      if D.zstroke k l then
        rows := rows.push { a := two nv Z W 2 6, c := 0, lo := some 8, hi := some 8 }
      else
        rows := rows.push { a := two nv Z W 2 6, c := 2, lo := none, hi := some 8 }
      if D.wstroke k l then
        rows := rows.push { a := two nv Z W 6 2, c := 0, lo := some 8, hi := some 8 }
      else
        rows := rows.push { a := two nv Z W 6 2, c := 2, lo := none, hi := some 8 }
  if pts.contains 6 then
    for k in bodies do
      for (T, idx, circ) in [(zt, V.zIdx, D.zc), (wt, V.wIdx, D.wc)] do
        match T.meet k 6 with
        | none => if circ[k]! then return none
        | some m =>
          if circ[k]! then
            rows := rows.push { a := unit nv idx[m]! 2, c := 0, lo := some (-4), hi := some (-4) }
          else
            rows := rows.push { a := unit nv idx[m]! 2, c := -2, lo := some (-4), hi := none }
  return some rows

/-- `threshold_row` with `mode le`: the sum of `x` over the pairs placed so far plus, for every other pair, its least
possible value (`1` on a `zw`-edge, `0` on a stroke, `−2` otherwise) is `≤ 0`. -/
def thresholdRow (D : Diag) (zt wt : Tree) (V : Vars) (pts : Array Nat) : Row := Id.run do
  let mut a : Form := Array.replicate V.nv 0
  let mut const : Int := 0
  for (k, l) in pairs6 do
    if pts.contains k && pts.contains l then
      let Z := V.zIdx[(zt.meet k l).getD NONE]!
      let W := V.wIdx[(wt.meet k l).getD NONE]!
      a := a.set! Z (a[Z]! + 1)
      a := a.set! W (a[W]! + 1)
    else
      let zw := D.zstroke k l && D.wstroke k l
      let st := D.zstroke k l || D.wstroke k l
      const := const + (if zw then 1 else if st then 0 else -2)
  return { a, c := 0, lo := none, hi := some (-2 * const) }

/-- Term labels of the base identities. -/
inductive Label where
  | pos (i : Nat)
  | cross (i j : Nat)
  | E
  | delta (k l : Nat)
  | zw (k l : Nat)
  deriving Inhabited, BEq

def Label.render : Label → String
  | .pos i => s!"[\"pos\", {i}]"
  | .cross i j => s!"[\"cross\", {i}, {j}]"
  | .E => "[\"E\"]"
  | .delta k l => s!"[\"delta\", {k}, {l}]"
  | .zw k l => s!"[\"zw\", {k}, {l}]"

/-- Names of the base identities. -/
inductive IdName where
  | S (colour : Bool) (i : Nat)   -- `colour = true`: `z`
  | U
  | I
  deriving Inhabited, BEq

def IdName.render : IdName → String
  | .S true i => s!"[\"z\", \"S\", [{i}]]"
  | .S false i => s!"[\"w\", \"S\", [{i}]]"
  | .U => "[\"U\"]"
  | .I => "[\"I\"]"

/-- An identity: name, term labels, exponent forms of the terms, and the forced argmin set (if any). -/
structure Ident where
  name : IdName
  labels : Array Label
  terms : Array Form
  forced : Option (Array Nat)
  deriving Inhabited

/-- `texact.identities` restricted to the base groups, in the engine's order: the `z`-equations of the bodies
`0 … 5`, the `w`-equations, then `U` and `I`. -/
def identities (D : Diag) (zt wt : Tree) (V : Vars) : Array Ident := Id.run do
  let nv := V.nv
  let mut out : Array Ident := #[]
  for colour in [true, false] do
    let T := if colour then zt else wt
    let idx := if colour then V.zIdx else V.wIdx
    for i in [0:6] do
      let mut terms : Array Form := #[]
      let mut labels : Array Label := #[]
      match T.meet i 6 with
      | some m =>
        terms := terms.push (unit nv idx[m]! 2)
        labels := labels.push (.pos i)
      | none => pure ()
      for j in [0:6] do
        if j != i then
          let Z := V.zIdx[(zt.meet i j).getD NONE]!
          let W := V.wIdx[(wt.meet i j).getD NONE]!
          terms := terms.push (if colour then two nv Z W (-1) (-3) else two nv Z W (-3) (-1))
          labels := labels.push (.cross i j)
      let mut forced : Array Nat := #[]
      for t in [0:labels.size] do
        match labels[t]! with
        | .pos k => if (if colour then D.zc[k]! else D.wc[k]!) then forced := forced.push t
        | .cross k l => if (if colour then D.zstroke k l else D.wstroke k l) then forced := forced.push t
        | _ => pure ()
      out := out.push { name := .S colour i, labels, terms, forced := if forced.isEmpty then none else some forced }
  -- U
  let mut termsU : Array Form := #[Array.replicate nv 0]
  let mut labelsU : Array Label := #[.E]
  let mut forcedU : Array Nat := #[]
  for pi in [0:pairs6.size] do
    let (k, l) := pairs6[pi]!
    let Z := V.zIdx[(zt.meet k l).getD NONE]!
    let W := V.wIdx[(wt.meet k l).getD NONE]!
    termsU := termsU.push (two nv Z W (-1) (-1))
    labelsU := labelsU.push (.delta k l)
    if D.zstroke k l && D.wstroke k l then forcedU := forcedU.push (1 + pi)
  out := out.push { name := .U, labels := labelsU, terms := termsU,
                    forced := if forcedU.isEmpty then none else some forcedU }
  -- I
  let mut termsI : Array Form := #[Array.replicate nv 0]
  let mut labelsI : Array Label := #[.E]
  for (k, l) in pairs6 do
    let Z := V.zIdx[(zt.meet k l).getD NONE]!
    let W := V.wIdx[(wt.meet k l).getD NONE]!
    termsI := termsI.push (two nv Z W 2 2)
    labelsI := labelsI.push (.zw k l)
  out := out.push { name := .I, labels := labelsI, terms := termsI, forced := none }
  return out

/-- `forced_rows`: the forced terms are equal to the first of them, all other terms are larger. -/
def forcedRows (terms : Array Form) (forced : Array Nat) : Array Row := Id.run do
  let f0 := forced[0]!
  let mut rows : Array Row := #[]
  for t in [0:terms.size] do
    if t != f0 then
      let d := (terms[t]!).sub terms[f0]!
      if forced.contains t then rows := rows.push { a := d, c := 0, lo := some 0, hi := some 0 }
      else rows := rows.push { a := d, c := -2, lo := some 0, hi := none }
  return rows

/-- Counters of the search and the cells written. -/
structure St where
  lp : Nat := 0
  pruned : Nat := 0
  fail : Nat := 0
  counter : Nat := 0
  leafFail : Nat := 0
  cells : Array String := #[]
  deriving Inhabited

/-- The decision on a linear program: `true` = kept. A program is discarded only when `Farkas.check` accepts the
certificate proposed by `LP.decide` (checked again here, so that this property holds by construction). -/
def decideLP (rows : Array Row) (nv : Nat) : Bool × Bool :=
  let v := LP.decide rows nv
  if v.kept then (true, v.failure)
  else if Farkas.check nv rows v.cert then (false, false)
  else (true, true)

/-- One linear program of the search, with the counters. -/
@[inline] def feasible (st : St) (rows : Array Row) (nv : Nat) : Bool × St :=
  let (kept, failure) := decideLP rows nv
  (kept, { st with lp := st.lp + 1, pruned := if kept then st.pruned else st.pruned + 1,
                   fail := if failure then st.fail + 1 else st.fail })

/-- `exact_argmins`: all argmin sets `S` (`|S| ≥ 2`) of an identity realizable together with `base` (the rows of the
cell so far), each with its rows; the terms are decided in order, IN before OUT. -/
partial def argmins (nv : Nat) (base : Array Row) (terms : Array Form) (j : Nat) (first : Option Nat)
    (ins outs : Array Nat) (rows : Array Row) (st : St) (res : Array (Array Nat × Array Row)) :
    St × Array (Array Nat × Array Row) :=
  let N := terms.size
  if j == N then
    (st, if first.isSome && ins.size ≥ 2 then res.push (ins, rows) else res)
  else
    -- IN
    let (st, res) :=
      match first with
      | none =>
        let nrows := outs.foldl (fun acc o => acc.push { a := (terms[o]!).sub terms[j]!, c := -2, lo := some 0,
                                                          hi := none }) rows
        let (ok, st) := feasible st (base ++ nrows) nv
        if ok then argmins nv base terms (j + 1) (some j) (ins.push j) outs nrows st res else (st, res)
      | some f =>
        let nrows := rows.push { a := (terms[j]!).sub terms[f]!, c := 0, lo := some 0, hi := some 0 }
        let (ok, st) := feasible st (base ++ nrows) nv
        if ok then argmins nv base terms (j + 1) (some f) (ins.push j) outs nrows st res else (st, res)
    -- OUT
    match first with
    | none =>
      if N - j - 1 ≥ 2 then argmins nv base terms (j + 1) none ins (outs.push j) rows st res else (st, res)
    | some f =>
      let nrows := rows.push { a := (terms[j]!).sub terms[f]!, c := -2, lo := some 0, hi := none }
      if ins.size ≥ 2 || N - j - 1 ≥ 2 - ins.size then
        let (ok, st) := feasible st (base ++ nrows) nv
        if ok then argmins nv base terms (j + 1) (some f) ins (outs.push j) nrows st res else (st, res)
      else (st, res)

/-- The argmin entry of a cell, written as the engine writes it. -/
def renderEntry (name : IdName) (labels : Array Label) : String :=
  "[" ++ name.render ++ ", [" ++ ", ".intercalate (labels.toList.map Label.render) ++ "]]"

/-- The beginning of the line of a cell, up to the key `"x"`. -/
def renderCell (zt wt : Tree) (entries : Array String) : String :=
  "{\"ztree\": " ++ zt.render ++ ", \"wtree\": " ++ wt.render ++ ", \"argmin\": [" ++
    ", ".intercalate entries.toList ++ "], \"x\": "

/-- The choice of argmin sets of the identities `branch[gi:]` (recursion of `cells_below`). -/
partial def branchRec (nv : Nat) (L0 : Array Row) (branch : Array Ident) (zt wt : Tree) (gi : Nat)
    (extra : Array Row) (chosen : Array String) (fixed : Array String) (st : St) : St :=
  if gi == branch.size then
    { st with cells := st.cells.push (renderCell zt wt (fixed ++ chosen)),
              leafFail := if leafCertified (L0 ++ extra) nv then st.leafFail else st.leafFail + 1 }
  else
    let id := branch[gi]!
    let (st, res) := argmins nv (L0 ++ extra) id.terms 0 none #[] #[] #[] st #[]
    res.foldl (fun st (S, rows) =>
      branchRec nv L0 branch zt wt (gi + 1) (extra ++ rows)
        (chosen.push (renderEntry id.name (S.map fun t => id.labels[t]!))) fixed st) st

/-- `cells_below`: the cells below a complete pair of trees. -/
def cellsBelow (D : Diag) (zt wt : Tree) (st : St) : St := Id.run do
  if !(zt.comOk && wt.comOk) then return st
  let V := Vars.of zt wt
  let all : Array Nat := #[0, 1, 2, 3, 4, 5, 6]
  let some L0 := baseLP D zt wt V all | return st
  let L0 := L0.push (thresholdRow D zt wt V all)
  let (ok, st) := feasible st L0 V.nv
  if !ok then return st
  let ids := identities D zt wt V
  let mut baseExtra : Array Row := #[]
  let mut fixed : Array String := #[]
  let mut branch : Array Ident := #[]
  for id in ids do
    match id.forced with
    | some f =>
      if f.size < 2 then return st
      baseExtra := baseExtra ++ forcedRows id.terms f
      fixed := fixed.push (renderEntry id.name (f.map fun t => id.labels[t]!))
    | none => branch := branch.push id
  let (ok, st) := feasible st (L0 ++ baseExtra) V.nv
  if !ok then return st
  return branchRec V.nv L0 branch zt wt 0 baseExtra #[] fixed st

/-- `enumerate_cells` with the split at depth `3` into `nparts` parts: the part `part`. -/
partial def enumRec (D : Diag) (order : Array Nat) (part nparts : Nat) (i : Nat) (zt wt : Tree) (pts : Array Nat)
    (st : St) : St :=
  if i == 6 then cellsBelow D zt wt st
  else
    let p := order[i]!
    let npts := pts.push p
    (zt.options 6 p).foldl (fun st zt2 =>
      (wt.options 6 p).foldl (fun st wt2 =>
        let (skip, st) :=
          if i + 1 == 3 then
            let c := st.counter
            (c % nparts != part, { st with counter := c + 1 })
          else (false, st)
        if skip then st
        else
          let V := Vars.of zt2 wt2
          match baseLP D zt2 wt2 V npts with
          | none => st
          | some L =>
            let L := L.push (thresholdRow D zt2 wt2 V npts)
            let (ok, st) := feasible st L V.nv
            if ok then enumRec D order part nparts (i + 1) zt2 wt2 npts st else st) st) st

/-- The search of one part (counter reset as in each run of the engine). -/
def runPart (D : Diag) (part nparts : Nat) : St :=
  let t0 := (Tree.empty 6).options 6 6
  let zt0 := t0[0]!
  enumRec D (orderBodies D) part nparts 0 zt0 zt0 #[6] {}

end L6.F2
