import Lean6.Special.Cover.Comp.Basic
import Lean6.Special.Cover.Comp.MPoly

/-!
# Proposition 9.23: Lemmas 9.13 (W3) and 9.14 (EQ2)

Both lemmas need, besides conditions on the trees and the argmin sets, a linear relation among the node coordinates of
the children of a node `v` that holds at every place in the cell with `g(m) ≠ 0`. The paper takes these relations from
(eq:rootcm) at the root and from Lemma 9.1 at `v`, and solves them over `ℚ(m)` ("Linear algebra over `ℚ(m)` then gives
`e` and `g` as in the lemma", after Lemma 9.13; "`M_A`, `M_B` and `g` come from (eq:rootcm) and Lemma 9.1 at `v`, as after
Lemma 9.13", after Lemma 9.14). This file does that linear algebra exactly, with polynomials in `ℤ[m]` (`MPoly`).

**The relations at `v` in colour `c`.** The unknowns are the node coordinates `X^c_{v,u}` of the children `u` of `v`
other than the `O`-child (`kids`). The rows are

* (eq:rootcm), if `v` is the root of `T_c`: the coefficient of `X^c_{v,u}` is the sum of the masses of the bodies below
  `u`;
* one row for each set `K` of Lemma 9.1 at `v` (`sSets`): `Σ_{k∈K} m_k X^c_{v,u(k)} = 0`, where `u(k)` is the child of
  `v` below which `k` lies. The sets are those of both programs of the supplement: the closed components of the graph of
  minimal forces among the bodies `k` with `meet_c(k, O) = v` whose position is minimal (for such `k`,
  `ĉ_k = X^c_{v,u(k)}` by the lemma on the trees, `lem:tree`, and all their equations have the least exponent `h_v`). `sSetsBroad` is a broader
  reading of Lemma 9.1 (components that also contain bodies without a minimal position, joined by mutual minimal forces),
  computed only to compare.

**The linear algebra.** Ranks over `ℚ(m)` are the largest sizes of minors that are not the zero polynomial (`rank`). The
projection of the solution space onto a set `T` of columns has dimension `|T| − rank A + rank A'`, with `A'` the matrix
without the columns of `T` (`projDim`). For a witness, `kernel` takes a nonzero minor of maximal size, with determinant
`D`, and the kernel vectors of Cramer's rule (entry `D` at a free column, polynomial entries elsewhere). If `D(m) ≠ 0`,
the rank at `m` is the rank over `ℚ(m)` and these vectors, evaluated at `m`, span the solution space at `m`; so with `g`
the product of `D` and a nonzero entry of the witness, the coordinates at any place with `g(m) ≠ 0` are proportional to
the witness evaluated at `m`, which is not zero.

**Lemma 9.13 (W3)** (`w3Insts`): for a colour `c` and a triangle `T = {a, b, s}` (`triNode` in both trees: one node,
three distinct children), `O` lies below the node `v` of `T` in `T_c` but not below the children of `v` that contain
`a`, `b`, `s`; two bodies of `T` are balanced in colour `c` with respect to `T`; and the projection of the solution space
of the relations at `v` onto the coordinates of these three children is a line (`dimP = 1`). Then `e` is a nonzero
projected kernel vector, `g = D · e_j`, and `H_W` is evaluated at `m = (1, …, 6)` from `e(m)`.

**Lemma 9.14 (EQ2)** (`eq2Insts`): for a colour `c` and a labelling `T = {a, b, s}` of a triangle, `s` lies below the
`O`-children of `v` (in `T_c`) and `v′` (in `T_{c′}`) or shares the leaf of `O`, `a` and `b` do not; `s` is balanced in
colour `c` with respect to `T`; `A^c_a` and `A^{c′}_a` consist of the position of `a` and the forces of `s` and `b`; and
the projection of the solution space onto the coordinates `X^c_{v,u(a)}`, `X^c_{v,u(b)}` (these are `ĉ_a`, `ĉ_b`) has
dimension at most `1` (a relation `M_A ĉ_a + M_B ĉ_b = 0` with `(M_A, M_B) ≠ 0`). If it is a line spanned by
`(f_a, f_b)`, then `M_A = f_b`, `M_B = −f_a` and `g = D · f_j`; if it is `0`, then `M_A = 1`, `M_B = 0` and `g = D`.

`w3NonzeroAtM0`, `eq2NonzeroAtM0`: the lemma applies, and at each of its instances `g(m) ≠ 0` and the polynomial of
the lemma (`H_W`, resp. `m_a² M_A⁴ − m_b² M_B⁴`) is not zero at `m = (1, …, 6)` (body `k` has mass `k + 1`).

The two programs of the supplement read the last hypothesis differently, and both readings are computed too: for W3
the notes also ask that the whole solution space (on the children that occur in a relation, and those of `T`) be a line
and that all three entries of `e` be nonzero (`notesOK`); for EQ2 the notes ask for one relation whose support is
exactly the two children (`notesOK`), and the independent program for a projection of dimension exactly `1`. Both
programs test ranks at random masses; here they are exact.
-/

namespace Lean6.Special.Cover.Lines

open L6.F34 Lean6.Special.Cover Lean6.Special.Cover.MP

/-- The point `m = (1, 2, 3, 4, 5, 6)` of the paper: body `k` has mass `k + 1`. -/
def m0 : List Int := [1, 2, 3, 4, 5, 6]

/-- The mass of body `k` at `m0`. -/
def mass0 (k : Nat) : Int := m0.getD k 0

/-! ## Trees and the sets of Lemma 9.1 -/

/-- The node `v` of three bodies in a tree: `meet(a, b) = meet(a, s) = meet(b, s) = v`; then the three bodies lie below
three distinct children of `v`. -/
def triNode (t : Tree) (a b s : Nat) : Option Nat :=
  match t.meet a b, t.meet a s, t.meet b s with
  | some u, some u', some u'' => if u == u' && u == u'' then some u else none
  | _, _, _ => none

/-- The bodies below a node. -/
def bodiesBelow (t : Tree) (u : Nat) : List Nat := (t.pts u).filter (· != O)

/-- The children of `v` other than its `O`-child, in the stored order. -/
def kids (t : Tree) (v : Nat) : List Nat :=
  let o := t.childTo v O
  (t.children v).toList.filter fun u => o != some u

/-- The bodies whose force on `k` is minimal in colour `c`. -/
def partners (x : Cell) (c : Bool) (k : Nat) : List Nat := bodies.filter fun l => l != k && x.forceMin c k l

/-- The bodies reached from `k` along minimal forces inside `cand`. -/
def comp (cand : List Nat) (nb : Nat → List Nat) (k : Nat) : List Nat := Id.run do
  let mut K := [k]
  for _ in [0:6] do
    let new := (K.flatMap nb).filter fun j => cand.contains j && !K.contains j
    K := K ++ new.eraseDups
  return K

/-- The sets of Lemma 9.1 at `v` in colour `c` (the reading of both programs): the closed components of the graph of
minimal forces among the bodies `k` with `meet_c(k, O) = v` whose position is minimal. -/
def sSets (x : Cell) (c : Bool) (v : Nat) : List (List Nat) :=
  let t := x.tree c
  let cand := bodies.filter fun k => t.meet k O == some v && x.posMin c k
  let nb := partners x c
  let comps := cand.foldl (fun acc k => if acc.any (·.contains k) then acc else acc ++ [comp cand nb k]) []
  comps.filter fun K => K.all fun i => (nb i).all K.contains

/-- A broader reading of Lemma 9.1 at `v` (only to compare): the components `K` of the graph of minimal forces on all
bodies that are closed, in which every minimal force is mutual (so all equations of `K` have one least exponent), that
contain a body with a minimal position, and all of whose bodies with a minimal position have `meet_c(k, O) = v`. -/
def sSetsBroad (x : Cell) (c : Bool) (v : Nat) : List (List Nat) :=
  let t := x.tree c
  let nb := partners x c
  let comps := bodies.foldl (fun acc k => if acc.any (·.contains k) then acc else acc ++ [comp bodies nb k]) []
  comps.filter fun K =>
    K.all (fun i => (nb i).all K.contains) &&
    K.all (fun i => (nb i).all fun j => (nb j).contains i) &&
    K.any (x.posMin c) &&
    K.all fun k => !x.posMin c k || t.meet k O == some v

/-! ## The relations and their linear algebra -/

/-- The row of `Σ_{k ∈ L} m_k X^c_{v,u(k)} = 0` on the columns `ks`. -/
def relRow (t : Tree) (v : Nat) (ks L : List Nat) : List MPoly :=
  ks.map fun u => MPoly.sum (L.filterMap fun k => if t.childTo v k == some u then some (MPoly.var k) else none)

/-- The relations at `v` in colour `c` on the columns `kids t v`: (eq:rootcm) if `v` is the root, and one row for each
set of `sets` (over its bodies with a minimal position). -/
def rows (x : Cell) (c : Bool) (v : Nat) (sets : List (List Nat)) : List (List MPoly) :=
  let t := x.tree c
  let ks := kids t v
  let root := if t.root == v then [ks.map fun u => MPoly.sum ((bodiesBelow t u).map MPoly.var)] else []
  root ++ sets.map fun K => relRow t v ks (K.filter (x.posMin c))

/-- The rank over `ℚ(m)` of a matrix with `n` columns: the largest size of a minor that is not zero. -/
def rank (A : List (List MPoly)) (n : Nat) : Nat :=
  let r := A.length
  let nz (k : Nat) : Bool :=
    (subsets k (List.range r)).any fun R => (subsets k (List.range n)).any fun C => !(det k (sub A R C)).isZero
  ((List.range (min r n + 1)).reverse.find? fun k => k == 0 || nz k).getD 0

/-- A nonzero minor of maximal size: its rows, its columns and its determinant (`[]`, `[]`, `1` for rank `0`). -/
def maxMinor (A : List (List MPoly)) (n : Nat) : List Nat × List Nat × MPoly :=
  let k := rank A n
  let cands := (subsets k (List.range A.length)).flatMap fun R => (subsets k (List.range n)).map fun C => (R, C)
  match cands.find? (fun (R, C) => !(det k (sub A R C)).isZero) with
  | some (R, C) => (R, C, det k (sub A R C))
  | none => ([], [], MPoly.one)

/-- The kernel of `A` over `ℚ(m)`: the determinant `D` of a maximal nonzero minor `(R, C)`, and for each column `f`
outside `C` the vector with `D` at `f`, `−det(A_{R,C} with the column `C_i` replaced by `f`)` at `C_i`, and `0`
elsewhere (Cramer's rule). -/
def kernel (A : List (List MPoly)) (n : Nat) : MPoly × List (List MPoly) :=
  let (R, C, D) := maxMinor A n
  let k := R.length
  let free := (List.range n).filter fun j => !C.contains j
  let vecs := free.map fun f =>
    (List.range n).map fun j =>
      if j == f then D
      else match C.findIdx? (· == j) with
        | some i => MPoly.neg (det k (sub A R (C.set i f)))
        | none => MPoly.zero
  (D, vecs)

/-- The matrix on the columns `cs`. -/
def cols (A : List (List MPoly)) (cs : List Nat) : List (List MPoly) := A.map fun row => cs.map (row.getD · MPoly.zero)

/-- The dimension over `ℚ(m)` of the projection of the solution space onto the columns `T`. -/
def projDim (A : List (List MPoly)) (n : Nat) (T : List Nat) : Nat :=
  let others := (List.range n).filter fun j => !T.contains j
  T.length + rank (cols A others) others.length - rank A n

/-- The first kernel vector whose projection onto `T` is not zero, projected; and `D`. -/
def witness (A : List (List MPoly)) (n : Nat) (T : List Nat) : MPoly × List MPoly :=
  let (D, vecs) := kernel A n
  let projs := vecs.map fun w => T.map (w.getD · MPoly.zero)
  (D, (projs.find? fun p => p.any fun q => !q.isZero).getD (T.map fun _ => MPoly.zero))

/-- The first nonzero entry (`1` if there is none). -/
def firstNZ (e : List MPoly) : MPoly := (e.find? fun q => !q.isZero).getD MPoly.one

/-! ## Lemma 9.13 (W3) -/

/-- An instance of the hypotheses of Lemma 9.13 up to the line condition, with the linear algebra. -/
structure W3Inst where
  /-- the colour (`true` for `z`) -/
  c : Bool
  /-- the triangle `[a, b, s]` (increasing) -/
  tri : List Nat
  /-- its node in `T_c` -/
  v : Nat
  /-- the bodies of `T` balanced in colour `c` -/
  bal : List Nat
  /-- the number of relations -/
  nrel : Nat
  /-- the dimension over `ℚ(m)` of the projection onto the children of `a`, `b`, `s` -/
  dimP : Nat
  /-- the notes' reading: the whole solution space (on the children in a relation and those of `T`) is a line and all
  entries of `e` are nonzero -/
  notesOK : Bool
  /-- `e` (on the children of `a`, `b`, `s`) -/
  e : List MPoly
  /-- `g = D · e_j` -/
  g : MPoly

/-- `H_W` at `m0`, from `e(m0)`: `u₁ = m_s²(e_a − e_b)`, `u₂ = m_a²(e_b − e_s)`, `u₃ = m_b²(e_s − e_a)`. -/
def hW0 (i : W3Inst) : Int :=
  match i.tri, i.e.map (MPoly.eval m0) with
  | [a, b, s], [ea, eb, es] =>
    let u1 := mass0 s ^ 2 * (ea - eb)
    let u2 := mass0 a ^ 2 * (eb - es)
    let u3 := mass0 b ^ 2 * (es - ea)
    (u1 * u2 + u2 * u3 + u3 * u1) ^ 3 - 27 * (u1 * u2 * u3) ^ 2
  | _, _ => 0

/-- The instances of Lemma 9.13 in a cell (all with the combinatorial hypotheses; `dimP = 1` is the line condition),
with the sets of Lemma 9.1 given by `setsOf` (`sSets` for the paper and the programs). -/
def w3InstsWith (setsOf : Cell → Bool → Nat → List (List Nat)) (x : Cell) : List W3Inst :=
  [true, false].flatMap fun c =>
    (subsets 3 bodies).filterMap fun tri =>
      match tri with
      | [a, b, s] =>
        let t := x.tree c
        match triNode t a b s, triNode (x.tree !c) a b s with
        | some v, some _ =>
          let o := t.childTo v O
          let chs := tri.map (t.childTo v ·)
          let bal := tri.filter (x.balanced c tri)
          if o.isNone || chs.any (· == o) || bal.length < 2 then none
          else
            let ks := kids t v
            let n := ks.length
            let A := rows x c v (setsOf x c v)
            let T := chs.filterMap fun ch => ch.bind fun u => ks.findIdx? (· == u)
            let dimP := projDim A n T
            let (D, e) := witness A n T
            let occ := (List.range n).filter fun j => T.contains j || A.any fun row => !(row.getD j MPoly.zero).isZero
            let notesOK := dimP == 1 && occ.length - rank (cols A occ) occ.length == 1 && e.all fun q => !q.isZero
            some { c, tri, v, bal, nrel := A.length, dimP, notesOK, e, g := MPoly.mul D (firstNZ e) }
        | _, _ => none
      | _ => none

/-- The instances of Lemma 9.13 (sets of Lemma 9.1 as in `sSets`). -/
def w3Insts (x : Cell) : List W3Inst := w3InstsWith sSets x

/-- **The hypotheses of Lemma 9.13 hold in the cell** (the paper's reading: the projection is a line). -/
def lemW3 (x : Cell) : Bool := (w3Insts x).any (·.dimP == 1)

/-- The notes' reading of Lemma 9.13. -/
def lemW3Notes (x : Cell) : Bool := (w3Insts x).any (·.notesOK)

/-- Lemma 9.13 with the broader reading of Lemma 9.1 (`sSetsBroad`). -/
def lemW3Broad (x : Cell) : Bool := (w3InstsWith sSetsBroad x).any (·.dimP == 1)

/-! ## Lemma 9.14 (EQ2) -/

/-- An instance of the hypotheses of Lemma 9.14 up to the relation, with the linear algebra. -/
structure EQ2Inst where
  /-- the colour `c` (`true` for `z`) -/
  c : Bool
  s : Nat
  a : Nat
  b : Nat
  /-- the node of `T` in `T_c` -/
  v : Nat
  /-- the number of relations -/
  nrel : Nat
  /-- the dimension over `ℚ(m)` of the projection onto `(ĉ_a, ĉ_b)` -/
  dimP : Nat
  /-- the notes' reading: one relation has support exactly the children of `a` and `b` -/
  notesOK : Bool
  MA : MPoly
  MB : MPoly
  g : MPoly

/-- `m_a² M_A⁴ − m_b² M_B⁴` at `m0`. -/
def eq2Val0 (i : EQ2Inst) : Int :=
  mass0 i.a ^ 2 * (i.MA.eval m0) ^ 4 - mass0 i.b ^ 2 * (i.MB.eval m0) ^ 4

/-- The instances of Lemma 9.14 in a cell (all with the conditions on the trees and the argmin sets; `dimP ≤ 1` is the
relation), with the sets of Lemma 9.1 given by `setsOf`. -/
def eq2InstsWith (setsOf : Cell → Bool → Nat → List (List Nat)) (x : Cell) : List EQ2Inst :=
  [true, false].flatMap fun c =>
    bodies.flatMap fun s => bodies.flatMap fun a => bodies.filterMap fun b =>
      if s == a || s == b || a == b then none
      else
        let t := x.tree c
        let t' := x.tree !c
        match triNode t a b s, triNode t' a b s with
        | some v, some v' =>
          if !(t.inOChild v s && t'.inOChild v' s) || t.inOChild v a || t.inOChild v b || t'.inOChild v' a ||
              t'.inOChild v' b || !x.eqSetIs c s false [a, b] || !x.eqSetIs c a true [s, b] ||
              !x.eqSetIs (!c) a true [s, b] then none
          else
            let ks := kids t v
            let n := ks.length
            let A := rows x c v (setsOf x c v)
            let T := [a, b].filterMap fun k => (t.childTo v k).bind fun u => ks.findIdx? (· == u)
            let dimP := projDim A n T
            let (D, f) := witness A n T
            let notesOK := A.any fun row =>
              (List.range n).all fun j => T.contains j == !(row.getD j MPoly.zero).isZero
            let (MA, MB, g) := match f with
              | [fa, fb] => if dimP == 1 then (fb, MPoly.neg fa, MPoly.mul D (firstNZ f)) else (MPoly.one, MPoly.zero, D)
              | _ => (MPoly.one, MPoly.zero, D)
            some { c, s, a, b, v, nrel := A.length, dimP, notesOK, MA, MB, g }
        | _, _ => none

/-- The instances of Lemma 9.14 (sets of Lemma 9.1 as in `sSets`). -/
def eq2Insts (x : Cell) : List EQ2Inst := eq2InstsWith sSets x

/-- **The hypotheses of Lemma 9.14 hold in the cell** (the paper's reading: a relation `M_A ĉ_a + M_B ĉ_b = 0` with
`(M_A, M_B) ≠ 0`, i.e. a projection of dimension at most `1`). -/
def lemEQ2 (x : Cell) : Bool := (eq2Insts x).any (·.dimP ≤ 1)

/-- The independent program's reading of Lemma 9.14: a projection of dimension exactly `1`. -/
def lemEQ2Line (x : Cell) : Bool := (eq2Insts x).any (·.dimP == 1)

/-- The notes' reading of Lemma 9.14: one relation with support exactly the children of `a` and `b`. -/
def lemEQ2Notes (x : Cell) : Bool := (eq2Insts x).any (·.notesOK)

/-- Lemma 9.14 with the broader reading of Lemma 9.1 (`sSetsBroad`). -/
def lemEQ2Broad (x : Cell) : Bool := (eq2InstsWith sSetsBroad x).any (·.dimP ≤ 1)

/-! ## The polynomials at `m = (1, …, 6)` -/

/-- In the cell, Lemma 9.13 applies, and at every instance with the line condition `g(m0) ≠ 0` and `H_W(m0) ≠ 0`. -/
def w3NonzeroAtM0 (x : Cell) : Bool :=
  let is := (w3Insts x).filter (·.dimP == 1)
  !is.isEmpty && is.all fun i => i.g.eval m0 != 0 && hW0 i != 0

/-- In the cell, Lemma 9.14 applies, and at every instance with a relation `g(m0) ≠ 0` and
`m_a² M_A⁴ − m_b² M_B⁴ ≠ 0` at `m0`. -/
def eq2NonzeroAtM0 (x : Cell) : Bool :=
  let is := (eq2Insts x).filter (·.dimP ≤ 1)
  !is.isEmpty && is.all fun i => i.g.eval m0 != 0 && eq2Val0 i != 0

end Lean6.Special.Cover.Lines
