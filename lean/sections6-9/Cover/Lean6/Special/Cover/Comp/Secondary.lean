import Lean6.Special.Cover.Comp.Tally
import L6F34.Check

/-!
# Proposition 9.23: Lemmas 9.11(c) and 9.22, and Lemma 5.1 on a torque

The hypotheses of these lemmas ask for the argmin set of a secondary identity (a subset sum, a torque) to be constant
on the cell. As in the companion project `lean6` (its checks of Proposition 5.3, `L6F34/Check.lean`), the argmin set is
guessed at a floating-point point of the cell (`interiorPoint`, `guessArgmin`) and certified on the whole cell
polyhedron `Π` by exact Farkas certificates (`constantArgmin`, `strictlyLeast`, Lemma 4.6): the floating point only
proposes. The cell polyhedron is `lean6`'s (`Ctx.cellRows`: the rows of the trees, the strokes and circles, and the
argmin sets of the base identities of the cell).

* `subsetTerms`, `torqueTerms`: the terms of the subset sum of `J` in a colour (positions `SP`, forces `SC`) and of
  the torque `T_J` (`T1 k l`: `z_k w_l`, `T2 k l`: `w_k z_l`, `k ∈ J`, `l ∉ J`), for any `J`, with the exponents of
  `lean6`'s `Ctx.secTerms` (which lists the subset sums with `2 ≤ |J| ≤ 4` and the torques with `0 ∈ J`). The subset
  sum of all six bodies is the centre of mass.
* `argminIs`: the argmin set of a list of terms is the set of terms with given labels, certified.
* **Lemma 9.11(c)** (`rcWit`): a triangle `T = {a, b, s}` centred in colour `c` at `s` with `a`, `b` balanced in
  colour `c` (`Generic.centredBal`), and a set `J ⊇ {a, b}` whose subset sum in colour `c` has the certified argmin set
  `{m_a c_a, m_b c_b}`. The statement allows every `J ⊇ {a, b}` (16 sets, `J` = all bodies included); `rcProgWit`
  takes `J = T` only, the set of the certificates of the supplement.
* **Lemma 9.22** (`tqWit`): (i) the root of `T_c` has exactly three children: the leaves of `l₁` and `l₂`, and the
  `O`-child, below which `k₁` and `k₂` lie; (ii) `k₁`, `k₂` and `O` lie below three distinct children of
  `v′ = meet_{c′}(k₁, k₂)`, `l₁` and `l₂` lie below the `O`-child of `v′`, and `{k₁, k₂}` is a set as in Lemma 9.1 for
  the colour `c′` with both positions minimal: both positions are minimal (with `meet_{c′}(k_i, O) = v′` their
  equations have the least exponent `h_{v′}`) and every minimal force on `k₁` or `k₂` is the force of the other one
  (`ssetPaper`); (iii) the argmin set of `T_{l₁,l₂}` is constant on the cell and consists of the four terms
  `c_{l_i} c′_{k_j}`. `tqProgWit` reads "a set as in Lemma 9.1" as the program of the supplement does (`ssetsProg`:
  `{k₁, k₂}` is a closed class of the bodies with a minimal position that meet `O` at `v′`, joined by minimal forces).
* **Lemma 5.1 on a torque** (`tdAt`, `tdWit`): one term of a torque `T_J` has strictly the least exponent on the cell.
-/

namespace Lean6.Special.Cover.Secondary

open L6 L6.F34

/-! ## Terms and certified argmin sets -/

/-- The terms of the subset sum of `J` in colour `z`: the positions `m_i c_i`, `i ∈ J` (absent if `i` shares the leaf
of `O`), and the forces `m_i m_j Z^c_{ij}`, `i ∈ J`, `j ∉ J`. -/
def subsetTerms (x : Ctx) (z : Bool) (J : List Nat) : Array Term := Id.run do
  let mut ts : Array Term := #[]
  for i in J do
    if let some e := x.posE z i then
      ts := ts.push { lab := .SP z i, expo := e, coef := { num := 2, masses := [i], leads := [(z, i, 6)] } }
  for i in J do
    for j in compl J do
      let (a, b) := dv i j
      ts := ts.push { lab := .SC z i j, expo := x.bigE z i j,
                      coef := { num := -2, masses := [i, j], dvars := [(a, b, 3)], leads := [(z, i, j)] } }
  return ts

/-- The terms of the torque `T_J`: `± m_k m_l p_kl³ z_k w_l` (`T1 k l`) and `∓ m_k m_l p_kl³ w_k z_l` (`T2 k l`) for
`k ∈ J`, `l ∉ J`, each absent if one of its positions vanishes identically. -/
def torqueTerms (x : Ctx) (J : List Nat) : Array Term := Id.run do
  let mut ts : Array Term := #[]
  for k in J do
    for l in compl J do
      let (a, b) := dv k l
      if let (some za, some wb) := (x.posE true k, x.posE false l) then
        ts := ts.push { lab := .T1 k l, expo := vadd (vadd (vscale 3 (x.dlE k l)) za) wb,
                        coef := { num := 2, masses := [k, l], dvars := [(a, b, 3)], leads := [(true, k, 6), (false, l, 6)] } }
      if let (some wb, some za) := (x.posE false k, x.posE true l) then
        ts := ts.push { lab := .T2 k l, expo := vadd (vadd (vscale 3 (x.dlE k l)) wb) za,
                        coef := { num := -2, masses := [k, l], dvars := [(a, b, 3)], leads := [(false, k, 6), (true, l, 6)] } }
  return ts

/-- The cell for the certificates: `lean6`'s context, the rows of `Π` and a floating-point point of `Π`. -/
structure LPCtx where
  x : Ctx
  rows : Array Row
  pt : Array Float

/-- The certificate context of a cell (`none` if the rows are not built or no interior point is found). -/
def lpCtx (c : CCell) : Option LPCtx := do
  let x := Ctx.mk' c.d c.x
  let rows ← x.cellRows c.x
  let pt ← interiorPoint rows x.nh
  some ⟨x, rows, pt⟩

/-- The labels of the terms with the indices `S`. -/
def labsOf (ts : Array Term) (S : List Nat) : List Lab := S.filterMap fun i => (ts[i]?).map (·.lab)

/-- Two lists of labels (without repetitions) are the same set. -/
def sameLabs (a b : List Lab) : Bool := a.length == b.length && a.all b.contains && b.all a.contains

/-- **The argmin set of the terms `ts` on the cell consists of the terms with the labels `want`**: the set guessed at
the point of the cell has these labels, and `constantArgmin` certifies that it is the argmin set on all of `Π`. -/
def argminIs (lp : LPCtx) (ts : Array Term) (want : List Lab) : Bool :=
  let S := guessArgmin lp.pt ts
  sameLabs (labsOf ts S) want && constantArgmin lp.x.nh lp.rows ts S

/-! ## Lemma 9.11(c) -/

/-- The sets `J ⊇ {a, b}` of bodies, increasing. -/
def supersets (a b : Nat) : List (List Nat) :=
  let others := bodies.filter fun k => k != a && k != b
  (List.range (others.length + 1)).flatMap fun r =>
    (subsets r others).map fun E => (a :: b :: E).mergeSort (· ≤ ·)

/-- Lemma 9.11(c) at `(c, T, s)`, with the sets `Js a b s` to try: `T` is centred in colour `c` at `s` with `a`, `b`
balanced, and some `J` has a subset sum in colour `c` with the certified argmin set `{m_a c_a, m_b c_b}`; returns `J`. -/
def rcAtWith (Js : Nat → Nat → Nat → List (List Nat)) (cl : CCell) (lp : LPCtx) (c : Bool) (T : List Nat) (s : Nat) :
    Option (List Nat) :=
  match Generic.centredBal cl.x c T s, Generic.rest T s with
  | some _, [a, b] => (Js a b s).find? fun J => argminIs lp (subsetTerms lp.x c J) [.SP c a, .SP c b]
  | _, _ => none

/-- The witnesses `(c, T, s, J)` of Lemma 9.11(c) (every `J ⊇ {a, b}`). -/
def rcWit (cl : CCell) (lp : LPCtx) : List (Bool × List Nat × Nat × List Nat) :=
  [true, false].flatMap fun c => Generic.triples.flatMap fun T => T.filterMap fun s =>
    (rcAtWith (fun a b _ => supersets a b) cl lp c T s).map fun J => (c, T, s, J)

/-- The witnesses of Lemma 9.11(c) with `J = T`, the sets of the supplement's certificates. -/
def rcProgWit (cl : CCell) (lp : LPCtx) : List (Bool × List Nat × Nat × List Nat) :=
  [true, false].flatMap fun c => Generic.triples.flatMap fun T => T.filterMap fun s =>
    (rcAtWith (fun a b s => [[a, b, s].mergeSort (· ≤ ·)]) cl lp c T s).map fun J => (c, T, s, J)

/-! ## Lemma 9.22 -/

/-- (i) in the tree `t`: the root has exactly three children, the leaves of `l₁` and of `l₂` and the `O`-child, below
which `k₁` and `k₂` lie. -/
def tqI (t : Tree) (l1 l2 k1 k2 : Nat) : Bool :=
  let r := t.root
  (t.children r).size == 3 && t.childTo r l1 == some (t.leafOf l1) && t.childTo r l2 == some (t.leafOf l2) &&
    match t.childTo r O with
    | some o => o != t.leafOf l1 && o != t.leafOf l2 && t.childTo r k1 == some o && t.childTo r k2 == some o
    | none => false

/-- `{k₁, k₂}` is a set as in Lemma 9.1 in colour `c′` with both positions minimal (the bodies meet `O` at the same
node, so their equations have the same least exponent): both positions are minimal and every minimal force on `k₁`
or `k₂` is the force of the other one. -/
def ssetPaper (x : Cell) (c' : Bool) (k1 k2 : Nat) : Bool :=
  x.posMin c' k1 && x.posMin c' k2 && (Generic.forcesOn x c' k1).all (· == k2) &&
    (Generic.forcesOn x c' k2).all (· == k1)

/-- The program's sets of Lemma 9.1 at `v` in colour `c` (the supplement's `lemma_S_sets`): the classes of the bodies
not at `O` with `meet_c(k, O) = v` and a minimal position, joined when one has a minimal force from the other, that are
closed under minimal forces. -/
def ssetsProg (x : Cell) (c : Bool) (v : Nat) : List (List Nat) :=
  let t := x.tree c
  let cand := bodies.filter fun k => !t.atO k && t.meetC k O == some v && x.posMin c k
  let rel := fun k j => x.forceMin c k j || x.forceMin c j k
  (Generic.classes rel cand).filter fun K => K.all fun i => (Generic.forcesOn x c i).all K.contains

/-- (ii) in the tree of colour `c′`, with the paper's (`paper = true`) or the program's reading of Lemma 9.1. -/
def tqII (x : Cell) (c' : Bool) (l1 l2 k1 k2 : Nat) (paper : Bool) : Bool :=
  let t := x.tree c'
  Every.threeKids t k1 k2 &&
    match t.meetC k1 k2 with
    | some v' =>
      t.inOChild v' l1 && t.inOChild v' l2 &&
        (if paper then ssetPaper x c' k1 k2
         else (ssetsProg x c' v').any fun K => K.mergeSort (· ≤ ·) == [k1, k2].mergeSort (· ≤ ·))
    | none => false

/-- (iii): the argmin set of the torque `T_{l₁,l₂}` is the four terms `c_{l_i} c′_{k_j}` (`T1 l k` for `c = z`,
`T2 l k` for `c = w`), certified. -/
def tqIII (lp : LPCtx) (c : Bool) (l1 l2 k1 k2 : Nat) : Bool :=
  let want := [l1, l2].flatMap fun l => [k1, k2].map fun k => if c then Lab.T1 l k else Lab.T2 l k
  argminIs lp (torqueTerms lp.x [l1, l2]) want

/-- The witnesses `(c, l₁, l₂, k₁, k₂)` of Lemma 9.22 (`l₁ < l₂`, `k₁ < k₂`). -/
def tqWitWith (paper : Bool) (cl : CCell) (lp : LPCtx) : List (Bool × Nat × Nat × Nat × Nat) :=
  [true, false].flatMap fun c =>
    (subsets 2 bodies).flatMap fun L =>
      match L with
      | [l1, l2] =>
        (subsets 2 (bodies.filter fun k => k != l1 && k != l2)).filterMap fun K =>
          match K with
          | [k1, k2] =>
            if tqI (cl.x.tree c) l1 l2 k1 k2 && tqII cl.x (!c) l1 l2 k1 k2 paper && tqIII lp c l1 l2 k1 k2 then
              some (c, l1, l2, k1, k2)
            else none
          | _ => none
      | _ => []

/-- The witnesses of Lemma 9.22 (paper's reading of Lemma 9.1). -/
def tqWit (cl : CCell) (lp : LPCtx) : List (Bool × Nat × Nat × Nat × Nat) := tqWitWith true cl lp

/-- The witnesses of Lemma 9.22 (program's reading of Lemma 9.1). -/
def tqProgWit (cl : CCell) (lp : LPCtx) : List (Bool × Nat × Nat × Nat × Nat) := tqWitWith false cl lp

/-! ## Lemma 5.1 on a torque -/

/-- **Lemma 5.1 on the torque `T_J`**: the term with the label `lab` has strictly the least exponent on the cell
(`strictlyLeast`: for every other term an accepted certificate that it is not below it anywhere on `Π`). -/
def tdAt (lp : LPCtx) (J : List Nat) (lab : Lab) : Bool :=
  let ts := torqueTerms lp.x J
  match ts.findIdx? (·.lab == lab) with
  | some i => strictlyLeast lp.x.nh lp.rows ts i
  | none => false

/-- The torques `T_J` (`0 ∈ J`, `1 ≤ |J| ≤ 5`, one of `T_J`, `T_{J^c}`) one of whose terms has strictly the least
exponent on the cell, with that term. -/
def tdWit (lp : LPCtx) : List (List Nat × Lab) :=
  (Every.properSubsets.filter (·.head? == some 0)).filterMap fun J =>
    let ts := torqueTerms lp.x J
    match guessArgmin lp.pt ts with
    | [i] => if strictlyLeast lp.x.nh lp.rows ts i then (ts[i]?).map fun t => (J, t.lab) else none
    | _ => none

/-! ## The cells outside the first group of (b) -/

/-- The cells in which no test of the first group of Proposition 9.23(b) holds. -/
def outsideFirst (cs : Array CCell) : List CCell := cs.toList.filter fun c => !(firstFlags c).any id

/-- The cells in which no test of the first group other than Corollary 9.18 holds. -/
def outsideFirstNoClique (cs : Array CCell) : List CCell :=
  cs.toList.filter fun c => !((firstFlags c).take 14).any id

/-- The cells of `l` by class: `(class, number)`, increasing. -/
def classCounts (l : List CCell) : List (Nat × Nat) := byClass (l.map (·.cls))

/-- The tests of Lemma 9.11(c) and Lemma 9.22 (paper's readings) in a cell; both `false` without a certificate
context. -/
def secondFlags (c : CCell) : Bool × Bool :=
  match lpCtx c with
  | none => (false, false)
  | some lp => (!(rcWit c lp).isEmpty, !(tqWit c lp).isEmpty)

/-- The tests with the programs' readings (Lemma 9.11(c) with `J = T`; Lemma 9.22 with the program's sets of
Lemma 9.1). -/
def secondFlagsProg (c : CCell) : Bool × Bool :=
  match lpCtx c with
  | none => (false, false)
  | some lp => (!(rcProgWit c lp).isEmpty, !(tqProgWit c lp).isEmpty)

/-- Lemma 5.1 on the torque `T_J` with the term `lab`, in a cell. -/
def tdCell (c : CCell) (J : List Nat) (lab : Lab) : Bool :=
  match lpCtx c with
  | none => false
  | some lp => tdAt lp J lab

/-- The cells outside the first group in which neither Lemma 9.11(c) nor Lemma 9.22 holds and the test `other` (of
Lemmas 9.20 and 9.21) fails, by class: the remaining cells of Proposition 9.23(b). -/
def remainingByClass (cs : Array CCell) (other : CCell → Bool) : List (Nat × Nat) :=
  classCounts ((outsideFirst cs).filter fun c => let f := secondFlags c; !f.1 && !f.2 && !other c)

/-- The counts about Lemmas 9.11(c), 9.22 and Lemma 5.1 on a torque. -/
structure SecTally where
  /-- the cells outside the first group, and by class -/
  outside : Nat
  outsideByClass : List (Nat × Nat)
  /-- the cells outside the first group in which Lemma 9.11(c), resp. Lemma 9.22, holds: `(class, cell)` -/
  rcCells : List (Nat × Nat)
  tqCells : List (Nat × Nat)
  /-- the same with the programs' readings -/
  rcProgCells : List (Nat × Nat)
  tqProgCells : List (Nat × Nat)
  /-- the cells outside the first group with neither, by class -/
  neitherByClass : List (Nat × Nat)
  /-- the cells outside the first group without Corollary 9.18, and those of them with Lemma 9.11(c), Lemma 9.22 -/
  outsideNoClique : Nat
  rcNoClique : List (Nat × Nat)
  tqNoClique : List (Nat × Nat)
  /-- the cell 0 of class 15: Lemma 5.1 on `T_{0,3,4}` with the term `w_0 z_2` (`T2 0 2`), and no test of Lemmas
  9.2–9.7 -/
  td15 : Bool
  td15NotEvery : Bool
  deriving DecidableEq, Repr

/-- **The counts about Lemmas 9.11(c), 9.22 and Lemma 5.1 on a torque.** -/
def secTally (cs : Array CCell) : SecTally :=
  let ff := cs.toList.map fun c => (c, firstFlags c)
  let out := (ff.filter fun (_, f) => !f.any id).map (·.1)
  let onc := (ff.filter fun (_, f) => !(f.take 14).any id).map (·.1)
  let fl := out.map fun c => (c, secondFlags c, secondFlagsProg c)
  let key := fun (c : CCell) => (c.cls, c.idx)
  let flc := onc.map fun c => (c, secondFlags c)
  let c15 := ff.filter fun (c, _) => c.cls == 15 && c.idx == 0
  { outside := out.length
    outsideByClass := classCounts out
    rcCells := (fl.filter fun (_, f, _) => f.1).map (key ·.1)
    tqCells := (fl.filter fun (_, f, _) => f.2).map (key ·.1)
    rcProgCells := (fl.filter fun (_, _, g) => g.1).map (key ·.1)
    tqProgCells := (fl.filter fun (_, _, g) => g.2).map (key ·.1)
    neitherByClass := classCounts ((fl.filter fun (_, f, _) => !f.1 && !f.2).map (·.1))
    outsideNoClique := onc.length
    rcNoClique := (flc.filter fun (_, f) => f.1).map (key ·.1)
    tqNoClique := (flc.filter fun (_, f) => f.2).map (key ·.1)
    td15 := c15.any fun (c, _) => tdCell c [0, 3, 4] (.T2 0 2)
    td15NotEvery := c15.any fun (_, f) => !(f.take 6).any id }

end Lean6.Special.Cover.Secondary
