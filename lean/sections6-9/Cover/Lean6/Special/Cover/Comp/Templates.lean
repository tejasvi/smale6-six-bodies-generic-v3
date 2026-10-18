import Lean6.Special.Cover.Comp.Tally
import L6F34.Check
import Std.Data.HashMap

/-!
# Proposition 9.23: Lemmas 9.20 (P4) and 9.21 (LIN) on the cores of the cells

In the cells where the paper uses Lemmas 9.20 and 9.21, the relations among leading coefficients that the lemmas assume
are initial forms of identities whose argmin sets are constant on the cell: "(i) is the initial form of the centre of
mass or of a subset sum, (ii) is that of the equation of `s`, of a torque or of a subset sum, and (iii) holds because `a`
and `b` lie below one child of the node `meet_{c′}(s, a) = meet_{c′}(s, b)`" (after Lemma 9.20); "the relations are
initial forms of subset sums or of the centre of mass whose terms of least exponent are positions of one colour, `y_j`
is the common leading coefficient `X^c_{v,u}` of the positions below one child `u` of a node `v`, and `M_ij` is the sum
of their masses in the `i`-th relation" (after Lemma 9.21). Both programs of the supplement take these identities from
the core of the cell (the identities of the computation of Proposition 5.3, whose initial forms generate the unit ideal)
and match the initial forms against templates. This file does the same over the cores of the companion project `lean6`.

**The core and its initial forms.** The identities of the core of a cell are the names of its link line (`lean6`:
`data/f4/links/c<N>.txt`, read by `L6.F34.parseLink`). These are the engine's cores that the programs classified,
except in 66 cells where `lean6` replaced the core; each of the 66 has a test of the first group of (b) and one of the
notes' cell-level tests, so it lies outside both sets of cells counted here. For a base identity the argmin set is the cell's; for a
secondary identity it is guessed at a point of the cell and certified constant on the cell polyhedron by Farkas
certificates (`L6.F34.guessArgmin`, `L6.F34.constantArgmin`, Lemma 4.6), as `lean6` does in its check of Proposition
5.3. Each term of an initial form is read as the programs read the engine's printed initial forms (`coreparse.py`:
`parse_term`): a position `m_k · lead`, a force `m_k m_l D_kl³ · lead`, a torque term with two leads, a potential, `E`,
a bare separation. A lead is the leading coefficient of `c_p − c_q`, a difference of node coordinates of the children of
`meet_c(p, q)` (Lemma 4.2), with the engine's convention that the first child in the stored order has coordinate `0`
(`Lead`).

**The templates** (`corefam.py`, tried in the order `B`, `LIN`, `P4`; `classify`):

* `famB`: the initial form of a difference of the equations of two bodies `k`, `l` has no separation and only the forces
  between `k` and `l` (the binary case, which the paper does not use; it is tried first, as in the programs).
* `famLin`: the position-sum relations are the subset sums whose initial forms have no force; each is a row `{lead ↦ Σ
  ±m_i}` (the sign of a lead `0 − X` is `−1`). The first set of rows (by size, then lexicographically in the order of
  the core) whose leads are single coordinates, at most as many as the rows, with a matrix of full column rank over
  `ℚ(m)`, gives the nonzero maximal minors. `linAll`: one of them has all its coefficients of one sign, so it does not
  vanish at positive masses (the case of Proposition 9.23(a)).
* `famP4`: a balance of `s` by the forces of `a` and `b` alone (the equation of `s` without its position, or a torque,
  or a subset sum, with two terms sharing `s`), a subset sum of the same colour whose initial form consists of the
  positions of `a` and `b` with two distinct leads, the distance rows of `sa` and `sb` in the core with the same lead
  variables in the other colour, and the `c`-leads of these rows equal to the position leads.

**Where the programs applied them.** The notes' program classified the core of a cell only if none of its cell-level
tests applied: the class-level case of Corollary 9.10, Lemmas 9.2–9.4, its binary lemma, Corollary 9.10 with a variant
using the argmin set of `U`, its narrow reading of Lemma 9.11 with the same variant, a lemma `R5` and Lemmas 9.12, 9.15
(`notesLemma`; `Bn`, `E1n`, `R1n`, `R5n` are its tests that the paper does not state). Proposition 9.23(a) counts the
cells so classified as `P4` or as `LIN` with a minor of one sign that have none of Lemmas 9.5–9.7 (171 and 1); the
second group of (b) counts, among the cells outside the first group, those whose core is `P4` (169) or `LIN` (116).
-/

namespace Lean6.Special.Cover.Templates

open L6 L6.F34 Lean6.Special.Cover Lean6.Special.Cover.MP

/-! ## Leads and terms -/

/-- The leading coefficient `X^c_{v,i} − X^c_{v,j}` of `c_p − c_q`: the colour and the two coordinates `(v, i)`, `none`
for the coordinate `0` of the first child of `v`. -/
structure Lead where
  z : Bool
  a : Option (Nat × Nat)
  b : Option (Nat × Nat)
  deriving BEq, Repr

/-- The lead of `c_p − c_q` in colour `z` (`q = 6` for a position). -/
def leadOf (x : Ctx) (z : Bool) (p q : Nat) : Option Lead := do
  let t := if z then x.zt else x.wt
  let v ← t.meet p q
  let cp ← t.childIdx v (t.leaf.getD p maxNode)
  let cq ← t.childIdx v (t.leaf.getD q maxNode)
  let co (i : Nat) : Option (Nat × Nat) := if i == 0 then none else some (v, i)
  some ⟨z, co cp, co cq⟩

/-- The variables of a lead as the programs normalize it: `[a]` for `a − 0`, `[b]` for `0 − b`, `[a, b]` for a
difference of two coordinates. -/
def Lead.vars (l : Lead) : List (Nat × Nat) :=
  match l.a, l.b with
  | some a, none => [a]
  | none, some b => [b]
  | some a, some b => [a, b]
  | none, none => []

/-- The sign of a lead normalized to its variable (`−1` for `0 − b`). -/
def Lead.sign (l : Lead) : Int :=
  match l.a, l.b with
  | none, some _ => -1
  | _, _ => 1

/-- A term of an initial form, as the programs read it (`coreparse.py`, `parse_term`). -/
inductive ATerm where
  | E
  | pos (m : Nat) (l : Lead)
  | zw (m : Nat)
  | force (k l : Nat) (z : Bool) (ms : List Nat)
  | torq (k l : Nat) (ls : List Lead)
  | pot (k l : Nat)
  | sep (l : Lead)
  | other
  deriving BEq, Repr

/-- The reading of a term of `lean6`'s identities (its leading coefficient: masses, powers of `D_kl`, `E`, leads). -/
def ofTerm (x : Ctx) (t : Term) : ATerm :=
  let cf := t.coef
  match cf.leads.mapM fun (z, p, q) => leadOf x z p q with
  | none => .other
  | some ls =>
    if cf.evar then .E
    else
      match cf.dvars, cf.masses, ls with
      | [], [m], [l] => .pos m l
      | [], [m], [_, _] => .zw m
      | (a, b, 3) :: _, ms, [l] => .force (min a b) (max a b) l.z ms
      | (a, b, 3) :: _, _, [l, l'] => .torq a b [l, l']
      | (a, b, 1) :: _, _, [] => .pot a b
      | [], [], [l] => .sep l
      | _, _, _ => .other

/-! ## The core of a cell -/

/-- An identity of the core of a cell: its name, the terms of its certified initial form (`none` if the argmin set of
a secondary identity is not certified, or for a distance row), and for a distance row `D_kl² z_kl w_kl − 1` its two
leads. -/
structure Iden where
  nm : IdName
  init : Option (List ATerm)
  dist : Option (Lead × Lead)

/-- The identity named `s` in a cell with the context `x`, the rows `rows` of the cell polyhedron and the point `pt`. -/
def idenOf (x : Ctx) (c : Cell) (rows : Array Row) (pt : Array Float) (s : String) : Option Iden := do
  let nm ← IdName.parse s
  match nm with
  | .dist k l => some ⟨nm, none, (do some (← leadOf x true k l, ← leadOf x false k l))⟩
  | _ =>
    if isBase nm then
      let init : Option (List ATerm) := do
        let ts ← x.baseTerms nm
        let (_, labs) ← c.argmin.find? (·.1 == nm)
        let S ← labs.toList.mapM (findLab ts)
        S.mapM fun i => (ts[i]?).map (ofTerm x)
      some ⟨nm, init, none⟩
    else
      let init : Option (List ATerm) := do
        let ts ← x.secTerms nm
        let S := guessArgmin pt ts
        if constantArgmin x.nh rows ts S then S.mapM fun i => (ts[i]?).map (ofTerm x) else none
      some ⟨nm, init, none⟩

/-- The core of a cell from the names of its link line: `none` if the cell polyhedron or a name is not read. -/
def coreOf (x : Ctx) (c : Cell) (names : Array String) : Option (List Iden) := do
  let rows ← x.cellRows c
  let pt ← interiorPoint rows x.nh
  names.toList.mapM (idenOf x c rows pt)

/-- Every identity of the core other than a distance row has a certified initial form. -/
def certified (core : List Iden) : Bool :=
  core.all fun i => match i.nm with
    | .dist _ _ => i.dist.isSome
    | _ => i.init.isSome

/-! ## The templates -/

/-- The pairs of bodies of the force terms, sorted and without repetition. -/
def forcePairs (ts : List ATerm) : List (Nat × Nat) :=
  ((ts.filterMap fun t => match t with | .force k l _ _ => some (k, l) | _ => none).eraseDups).mergeSort
    fun p q => p.1 < q.1 || (p.1 == q.1 && p.2 ≤ q.2)

/-- **The binary template** (`fam_B`): a difference of the equations of `k` and `l` whose initial form has no
separation and only the forces between `k` and `l`. -/
def famB (core : List Iden) : Bool :=
  core.any fun i =>
    match i.nm, i.init with
    | .diff _ k l, some ts => !(ts.any fun t => match t with | .sep _ => true | _ => false) &&
        forcePairs ts == [(min k l, max k l)]
    | _, _ => false

/-- The key of a lead variable: colour, node, child. -/
abbrev Key := Bool × List (Nat × Nat)

/-- The name the programs give a key (`X<v>_<i>` or `Y<v>_<i>`; a difference of two coordinates as a pair), by which
they order the columns. -/
def keyName (k : Key) : String :=
  let tag := if k.1 then "X" else "Y"
  match k.2 with
  | [(v, i)] => s!"{tag}{v}_{i}"
  | l => toString (l.map fun (v, i) => s!"{tag}{v}_{i}")

/-- The position-sum relations of a core (`pos_sum_rows`): for each subset sum whose initial form has no force term,
in the order of the core, the coefficient `Σ ± m_i` of each lead. -/
def posSumRows (core : List Iden) : List (List (Key × MPoly)) :=
  core.filterMap fun i =>
    match i.nm, i.init with
    | .subset _ _, some ts =>
      if ts.any (fun t => match t with | .force .. => true | _ => false) then none
      else some <| ts.foldl (fun row t =>
        match t with
        | .pos m l =>
          let key : Key := (l.z, l.vars)
          let c := MPoly.smul l.sign (MPoly.var m)
          match row.find? (·.1 == key) with
          | some _ => row.map fun (k', p) => if k' == key then (k', MPoly.add p c) else (k', p)
          | none => row ++ [(key, c)]
        | _ => row) []
    | _, _ => none

/-- **The linear template** (`fam_lin`): the nonzero maximal minors of the first set of position-sum relations, by
size and then lexicographically, whose leads are single coordinates, at most as many as the relations, with a matrix of
full column rank over `ℚ(m)`. -/
def famLin (core : List Iden) : Option (List MPoly) :=
  let rows := posSumRows core
  let n := rows.length
  let cands := (List.range (n + 1)).drop 1 |>.flatMap fun r => (subsets r (List.range n)).map fun s => (r, s)
  cands.findSome? fun (r, sel) =>
    let rs := sel.filterMap fun i => rows[i]?
    let cols := ((rs.flatMap fun row => row.map (·.1)).eraseDups).mergeSort fun a b => keyName a ≤ keyName b
    let k := cols.length
    if k > r || cols.any (fun c => c.2.length != 1) then none
    else
      let M := rs.map fun row => cols.map fun c => ((row.find? (·.1 == c)).map (·.2)).getD MPoly.zero
      if Lines.rank M k != k then none
      else some ((subsets k (List.range r)).filterMap fun rr =>
        let d := det k (sub M rr (List.range k))
        if d.isZero then none else some d)

/-- A minor has all its coefficients of one sign (so it does not vanish at positive masses). -/
def oneSign (p : MPoly) : Bool := !p.isZero && (p.terms.all (·.2 > 0) || p.terms.all (·.2 < 0))

/-- A balance `(c, s, a, b)`: an initial form `m_a P_sa³ Y_a + m_b P_sb³ Y_b` in colour `c` (`fam_P4`). -/
def bals (core : List Iden) : List (Bool × Nat × Nat × Nat) :=
  core.flatMap fun i =>
    match i.nm, i.init with
    | .body z k, some ts =>
      let pos := ts.any fun t => match t with | .pos .. => true | _ => false
      let fl := ((ts.filterMap fun t => match t with
        | .force a b _ _ => some (if a == k then b else a) | _ => none).eraseDups).mergeSort (· ≤ ·)
      match pos, fl with
      | false, [a, b] => [(z, k, a, b)]
      | _, _ => []
    | .torque _, some [.torq k1 l1 ls1, .torq k2 l2 ls2] =>
      let p1 := [k1, l1]
      let p2 := [k2, l2]
      let common := p1.filter p2.contains
      let others := ((p1 ++ p2).filter fun j => !common.contains j).mergeSort (· ≤ ·)
      let shared := ls1.filter ls2.contains
      match common, others, shared with
      | [s], [a, b], [l] => [(!l.z, s, a, b)]
      | _, _, _ => []
    | .subset _ _, some [.force k1 l1 z1 _, .force k2 l2 _ _] =>
      let p1 := [k1, l1]
      let p2 := [k2, l2]
      let common := p1.filter p2.contains
      let others := ((p1 ++ p2).filter fun j => !common.contains j).mergeSort (· ≤ ·)
      match common, others with
      | [s], [a, b] => [(z1, s, a, b)]
      | _, _ => []
    | _, _ => []

/-- The subset sums whose initial form consists of the positions of two bodies with two distinct leads: colour, the
two bodies and their position leads. -/
def posPairs (core : List Iden) : List (Bool × List (Nat × Lead)) :=
  core.filterMap fun i =>
    match i.nm, i.init with
    | .subset z _, some ts =>
      if ts.any (fun t => match t with | .force .. => true | _ => false) then none
      else
        let ps := ts.filterMap fun t => match t with | .pos m l => some (m, l) | _ => none
        let bodies := (ps.map (·.1)).eraseDups
        let leads := (ps.map (·.2)).eraseDups
        if bodies.length == 2 && leads.length == 2 then some (z, ps) else none
    | _, _ => none

/-- **The template of Lemma 9.20** (`fam_P4`): `(c, s, a, b)`. -/
def famP4 (core : List Iden) : Option (Bool × Nat × Nat × Nat) :=
  let dists := core.filterMap fun i => match i.nm, i.dist with
    | .dist k l, some d => some ((k, l), d)
    | _, _ => none
  let dist (p q : Nat) : Option (Lead × Lead) := (dists.find? (·.1 == (min p q, max p q))).map (·.2)
  let leadIn (d : Lead × Lead) (z : Bool) : Lead := if z then d.1 else d.2
  (bals core).findSome? fun (c, s, a1, a2) =>
    (posPairs core).findSome? fun (c', ps) =>
      if c' != c || !((ps.map (·.1)).all [a1, a2].contains && [a1, a2].all (ps.map (·.1)).contains) then none
      else
        match dist s a1, dist s a2 with
        | some d1, some d2 =>
          if (leadIn d1 (!c)).vars != (leadIn d2 (!c)).vars then none
          else
            let ok := [(a1, d1), (a2, d2)].all fun (ai, d) =>
              match (ps.reverse.find? (·.1 == ai)).map (·.2) with
              | some pl =>
                let v := if pl.b.isNone then pl.a else pl.b
                match v with
                | some v => (leadIn d c).vars == [v]
                | none => false
              | none => false
            if ok then some (c, s, a1, a2) else none
        | _, _ => none

/-- The template of a core, in the order `B`, `LIN`, `P4`. -/
inductive Tmpl where
  | unmatched
  | B
  | lin (minors : List MPoly)
  | p4 (c : Bool) (s a b : Nat)

/-- **The classification of a core** (`corefam.classify`). -/
def classify (core : List Iden) : Tmpl :=
  if famB core then .B
  else match famLin core with
    | some ms => .lin ms
    | none => match famP4 core with
      | some (c, s, a, b) => .p4 c s a b
      | none => .unmatched

/-! ## The order of the notes' program -/

/-- The three bodies lie below distinct children of one node (their pairwise meets are equal). -/
def commonMeet (t : Tree) (T : List Nat) : Option Nat :=
  match T with
  | [a, b, s] =>
    match t.meetC a b with
    | some v => if t.meetC a s == some v && t.meetC b s == some v then some v else none
    | none => none
  | _ => none

/-- The argmin set of `U = E` consists of the terms `p_kl` of the pairs of `T` (`U_tri`). -/
def uTri (x : Cell) (T : List Nat) : Bool :=
  labSetEq (x.am .U) ((subsets 2 T).filterMap fun p => match p with | [a, b] => some (Lab.delta a b) | _ => none).toArray

/-- The notes' Corollary 9.10 (`lemma_E1`): as `Generic.lemE1`, or one body balanced in each colour and `U_tri`. -/
def E1n (x : Cell) : Bool :=
  (subsets 3 bodies).any fun T =>
    (commonMeet x.zt T).isSome && (commonMeet x.wt T).isSome &&
      (let bz := (T.filter (x.balanced true T)).length
       let bw := (T.filter (x.balanced false T)).length
       (bz ≥ 2 && bw ≥ 1) || (bw ≥ 2 && bz ≥ 1) || (bz ≥ 1 && bw ≥ 1 && uTri x T))

/-- `s`, `O` and the bodies outside `T` lie below one child of the node of `T` (`centred` of the notes). -/
def centredN (t : Tree) (T : List Nat) (s : Nat) : Bool :=
  match commonMeet t T with
  | none => false
  | some v =>
    let cs := t.childTo v s
    t.childTo v O == cs && bodies.all fun j => T.contains j || t.childTo v j == cs

/-- The notes' narrow reading of Lemma 9.11 (`lemma_R1`): balance at both other bodies, or at one of them and
`U_tri`, with `s` centred as in `centredN`. -/
def R1n (x : Cell) : Bool :=
  (subsets 3 bodies).any fun T =>
    (commonMeet x.zt T).isSome && (commonMeet x.wt T).isSome &&
      [true, false].any fun c => T.any fun s =>
        let nb := ((T.filter (· != s)).filter (x.balanced c T)).length
        (nb == 2 || (nb == 1 && uTri x T)) && centredN (x.tree c) T s

/-- The notes' lemma `R5` (`lemma_R5`): `U_tri`, `s` centred in one colour, a body of `T` other than `s` balanced in
the other. -/
def R5n (x : Cell) : Bool :=
  (subsets 3 bodies).any fun T =>
    (commonMeet x.zt T).isSome && (commonMeet x.wt T).isSome && uTri x T &&
      [true, false].any fun c => T.any fun s =>
        centredN (x.tree !c) T s && T.any fun a => a != s && x.balanced c T a

/-- The notes' binary lemma (`lemma_B`): in some colour the argmin sets of `k` and `l` contain the forces between them
and lie in `{force, position}`, and `x_kl > 0` is forced. -/
def Bn (x : Cell) (d : Diagram) : Bool :=
  [true, false].any fun c => (subsets 2 bodies).any fun p =>
    match p with
    | [k, l] =>
      let ak := x.eqSet c k
      let al := x.eqSet c l
      ak.contains (.cross k l) && al.contains (.cross l k) &&
        ak.all (fun t => t == .cross k l || t == .pos k) && al.all (fun t => t == .cross l k || t == .pos l) &&
        Every.forced x d k l
    | _ => false

/-- One of the cell-level tests of the notes' program holds (then it did not classify the core). -/
def notesLemma (c : CCell) : Bool :=
  Generic.lemE c.d || Every.lemT c.x || Every.lemP c.x c.d || Every.lemCProg c.x || Bn c.x c.d || E1n c.x ||
    R1n c.x || R5n c.x || Generic.lemR6 c.x || Generic.lemQ c.x

/-! ## The core links -/

/-- The names of the core of each cell, from the link files `(class, text)`. -/
def linkTable (files : List (Nat × String)) : Std.HashMap (Nat × Nat) (Array String) :=
  files.foldl (fun m (_, txt) =>
    (lines txt).foldl (fun m l =>
      match parseLink l with
      | some lk => m.insert (lk.cls, lk.cell) lk.names
      | none => m) m) {}

/-- The core of a stored cell (`none` if it has no link line or its core is not read). -/
def cellCore (tbl : Std.HashMap (Nat × Nat) (Array String)) (c : CCell) : Option (List Iden) := do
  let names ← tbl.get? (c.cls, c.idx)
  coreOf (Ctx.mk' c.d c.x) c.x names

/-! ## The counts -/

/-- The counts of the templates. -/
structure TTally where
  /-- the cells outside the first group of Proposition 9.23(b) -/
  outside : Nat
  /-- among them, those whose core is classified `B`, `LIN`, `LIN` with a minor of one sign, `P4`, and none -/
  outB : Nat
  outLin : Nat
  outLinAll : Nat
  outP4 : Nat
  outNone : Nat
  /-- the core cells where none of the notes' cell-level tests holds -/
  notesDom : Nat
  /-- among them, with none of Lemmas 9.5–9.7: `P4`, `LIN` with a minor of one sign, `B`, `LIN` otherwise -/
  aP4 : Nat
  aLinAll : Nat
  aB : Nat
  aLinGen : Nat
  /-- cells of these sets with a core identity whose argmin set is not certified -/
  uncertified : Nat
  deriving DecidableEq, Repr

/-- The template of a cell, if its core is read and certified. -/
def cellTmpl (tbl : Std.HashMap (Nat × Nat) (Array String)) (c : CCell) : Option Tmpl :=
  match cellCore tbl c with
  | some core => if certified core then some (classify core) else none
  | none => none

/-- **The counts of the templates over the stored cells.** -/
def ttally (links : List (Nat × String)) (cs : Array CCell) : TTally :=
  let tbl := linkTable links
  let rs := cs.toList.map fun c =>
    let f := firstFlags c
    let outside := !(f.any id)
    let core := tbl.contains (c.cls, c.idx)
    let dom := core && !notesLemma c
    let tm : Option (Option Tmpl) := if outside || dom then some (cellTmpl tbl c) else none
    let b0kl := f.getD 3 false || f.getD 4 false || f.getD 5 false
    (outside, dom, b0kl, core, tm)
  let isT (p : Tmpl → Bool) (tm : Option (Option Tmpl)) : Bool :=
    match tm with
    | some (some t) => p t
    | _ => false
  let isB : Tmpl → Bool := fun t => match t with | .B => true | _ => false
  let isLin : Tmpl → Bool := fun t => match t with | .lin _ => true | _ => false
  let isLinAll : Tmpl → Bool := fun t => match t with | .lin ms => ms.any oneSign | _ => false
  let isP4 : Tmpl → Bool := fun t => match t with | .p4 .. => true | _ => false
  let isNone : Tmpl → Bool := fun t => match t with | .unmatched => true | _ => false
  let out := rs.filter (·.1)
  let dom := rs.filter fun r => r.2.1
  let aDom := dom.filter fun r => !r.2.2.1
  { outside := out.length
    outB := (out.filter fun r => isT isB r.2.2.2.2).length
    outLin := (out.filter fun r => isT isLin r.2.2.2.2).length
    outLinAll := (out.filter fun r => isT isLinAll r.2.2.2.2).length
    outP4 := (out.filter fun r => isT isP4 r.2.2.2.2).length
    outNone := (out.filter fun r => !r.2.2.2.1 || isT isNone r.2.2.2.2).length
    notesDom := dom.length
    aP4 := (aDom.filter fun r => isT isP4 r.2.2.2.2).length
    aLinAll := (aDom.filter fun r => isT isLinAll r.2.2.2.2).length
    aB := (aDom.filter fun r => isT isB r.2.2.2.2).length
    aLinGen := (aDom.filter fun r => isT isLin r.2.2.2.2 && !isT isLinAll r.2.2.2.2).length
    uncertified := (rs.filter fun r => r.2.2.2.1 && match r.2.2.2.2 with | some none => true | _ => false).length }

/-- A broader count, not used for Proposition 9.23 (it ignores the programs' order): over the cells without any of
Lemmas 9.2–9.7, the numbers of cells,
of core cells, and of core cells classified `P4`, `LIN` with a minor of one sign, `LIN` otherwise, `B`, none, and with
an uncertified core identity. -/
def broadCounts (links : List (Nat × String)) (cs : Array CCell) : List Nat :=
  let tbl := linkTable links
  let rs := (cs.toList.filter fun c => !((firstFlags c).take 6).any id).map fun c =>
    (tbl.contains (c.cls, c.idx), if tbl.contains (c.cls, c.idx) then cellTmpl tbl c else none)
  let cnt (p : Tmpl → Bool) : Nat := (rs.filter fun r => match r.2 with | some t => p t | none => false).length
  [rs.length, (rs.filter (·.1)).length,
   cnt (fun t => match t with | .p4 .. => true | _ => false),
   cnt (fun t => match t with | .lin ms => ms.any oneSign | _ => false),
   cnt (fun t => match t with | .lin ms => !ms.any oneSign | _ => false),
   cnt (fun t => match t with | .B => true | _ => false),
   cnt (fun t => match t with | .unmatched => true | _ => false),
   (rs.filter fun r => r.1 && r.2.isNone).length]

end Lean6.Special.Cover.Templates
