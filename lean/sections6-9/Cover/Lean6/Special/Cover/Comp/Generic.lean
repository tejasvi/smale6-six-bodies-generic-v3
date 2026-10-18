import Lean6.Special.Cover.Comp.Driver
import L6F5.Clique

/-!
# Proposition 9.23: the lemmas of §9.2 and §9.3 at generic masses

The hypotheses, read off the trees and the argmin sets of a cell (or off the diagram), of the lemmas of the first group
of Proposition 9.23(b) that hold at generic masses:

* `lemE`: the class-level case after Corollary 9.10. Three bodies of the diagram are pairwise joined by `zw`-edges,
  none of them is circled (in either colour), and no other stroke (of either colour) meets them.
* `lemE1`: Corollary 9.10. A triangle `T` (three bodies below distinct children of one node of `T_z` and of one node of
  `T_w`), two of whose bodies are balanced with respect to `T` in one colour and one in the other colour.
* `lemRa`, `lemRb`: Lemma 9.11 (a) and (b). A triangle `T = {a, b, s}` centred in colour `c` at `s` (at the node `v` of
  `T` in `T_c`, `s` lies below the `O`-child of `v` or shares the leaf of `O`, and `a`, `b` lie below two other
  children `A`, `B`), with `a` and `b` balanced in colour `c`; in (a) `v` is the root of `T_c` and has exactly three
  children; in (b) `v` is the root of `T_c`, every body below a child of `v` other than `A`, `B` and the `O`-child has
  a minimal position, and these bodies form a disjoint union of sets `K` as in Lemma 9.1.
* `lemR6`: Lemma 9.12. A triangle `T = {a, b, s}` whose node in `T_c` is the root of `T_c`, with exactly three children:
  the leaves of `a` and of `b`, and a child below which all other points lie; `s` is balanced in colour `c` and `a`
  in the other colour.
* `lemQ`: Lemma 9.15. A body `s` and a set `K` of at least two bodies such that `A^c_s` consists of the forces of the
  bodies of `K` on `s`, and in each tree a node `v` with `meet(s, k) = v` for all `k ∈ K`, the bodies of `K` lying
  below one child of `v`.
* `lemClique3`: Corollary 9.18 for a clique of three bodies, by the function `L6F5.cliqueOK` of the companion project
  (whose census, Proposition 9.19, is checked there), applied to the cell and the diagram in its formats.

Transcription choices.

* Three bodies lie below distinct children of one node `v` exactly when their three pairwise meets are equal to `v`
  (`triNode`).
* In Lemma 9.11(b), the bodies below the children of `v` other than `A`, `B` and the `O`-child all meet `O` at `v`, so
  their equations, with minimal positions, have the same least exponent `h_v`, as Lemma 9.1 asks. A union of sets
  that are closed under minimal forces (every minimal force on a body of the set is the force of a body of the set)
  is closed, and a closed set is such a union with one term; so the condition is that these bodies have minimal
  positions and form a set closed under minimal forces (`rbAt`). The program of the supplement (`rbProgAt`) is
  stricter: it forms the classes of the bodies with a minimal position that meet `O` at `v`, joined by minimal forces
  in either direction, and asks that the closed classes inside the set cover it.
* In Lemma 9.12, the three children of the root are the leaf of `a`, the leaf of `b` and a third child below which
  every point other than `a` and `b` lies.
* The labels of the argmin set of the equation of a body are its position (`pos`) and the forces on it (`cross`); the
  census of the companion project reads every stored cell and finds no other label there.
-/

namespace Lean6.Special.Cover.Generic

open L6.F34

/-- The colours: `true` for `z`, `false` for `w`. -/
def colours : List Bool := [true, false]

/-- The sets of three bodies, as increasing lists. -/
def triples : List (List Nat) := subsets 3 bodies

/-- The node `v` such that `a`, `b`, `s` lie below distinct children of `v`: the common value of their three pairwise
meets; `none` if the meets differ. -/
def triNode (t : Tree) (a b s : Nat) : Option Nat :=
  match t.meetC a b with
  | some v => if t.meetC a s == some v && t.meetC b s == some v then some v else none
  | none => none

/-- The node of the set `T` (three bodies, as a list) in `t`. -/
def triNodeL (t : Tree) (T : List Nat) : Option Nat :=
  match T with
  | [a, b, s] => triNode t a b s
  | _ => none

/-- `T` is a triangle: its bodies lie below distinct children of one node of `T_z` and of one node of `T_w`. -/
def isTri (x : Cell) (T : List Nat) : Bool := (triNodeL x.zt T).isSome && (triNodeL x.wt T).isSome

/-- The bodies of `T` other than `s`, in their order in `T`. -/
def rest (T : List Nat) (s : Nat) : List Nat := T.filter (· != s)

/-- The forces in the argmin set `A^c_k`: the bodies `j` with the label `cross k j`. -/
def forcesOn (x : Cell) (c : Bool) (k : Nat) : List Nat :=
  (x.eqSet c k).toList.filterMap fun l =>
    match l with
    | .cross i j => if i == k then some j else none
    | _ => none

/-! ## The class-level case and Corollary 9.10 -/

/-- `ab` is a `zw`-edge of the diagram. -/
def zwEdge (d : Diagram) (a b : Nat) : Bool := d.zstroke a b && d.wstroke a b

/-- **The class-level case**: three bodies pairwise joined by `zw`-edges, none circled, no other stroke meeting them. -/
def eWit (d : Diagram) : List (List Nat) :=
  triples.filter fun T =>
    (T.all fun a => T.all fun b => a == b || zwEdge d a b) &&
    (T.all fun k => !d.zc.getD k false && !d.wc.getD k false) &&
    (T.all fun k => bodies.all fun j => T.contains j || !(d.zstroke k j || d.wstroke k j))

/-- The hypotheses of Corollary 9.10 for the triangle `T`: two bodies balanced in one colour, one in the other. -/
def e1At (x : Cell) (T : List Nat) : Bool :=
  let bz := (T.filter (x.balanced true T)).length
  let bw := (T.filter (x.balanced false T)).length
  (bz ≥ 2 && bw ≥ 1) || (bw ≥ 2 && bz ≥ 1)

/-- **Corollary 9.10**: the triangles that satisfy its hypotheses. -/
def e1Wit (x : Cell) : List (List Nat) := triples.filter fun T => isTri x T && e1At x T

/-! ## Lemma 9.11 (a), (b) -/

/-- A triangle `T` centred in colour `c` at `s`, with `a`, `b` (the other two bodies, in their order in `T`) balanced
in colour `c`: returns the node `v` of `T` in `T_c`, the `O`-child of `v` and the children `A`, `B` of `v` below which
`a`, `b` lie. Centred: `s` lies below the `O`-child of `v` or shares the leaf of `O`, and `A`, `B` are not the
`O`-child (they are distinct, as `T` is a triangle). -/
def centredBal (x : Cell) (c : Bool) (T : List Nat) (s : Nat) : Option (Nat × Nat × Nat × Nat) :=
  let t := x.tree c
  match rest T s with
  | [a, b] =>
    if !isTri x T then none else
    match triNode t a b s with
    | none => none
    | some v =>
      match t.childTo v O, t.childTo v a, t.childTo v b with
      | some oc, some ca, some cb =>
        if t.inOChild v s && ca != oc && cb != oc && x.balanced c T a && x.balanced c T b then
          some (v, oc, ca, cb)
        else none
      | _, _, _ => none
  | _ => none

/-- **Lemma 9.11(a)** at `(c, T, s)`: centred and balanced, and `v` is the root of `T_c` with exactly three children. -/
def raAt (x : Cell) (c : Bool) (T : List Nat) (s : Nat) : Bool :=
  match centredBal x c T s with
  | some (v, _, _, _) => v == (x.tree c).root && ((x.tree c).children v).size == 3
  | none => false

/-- The bodies below the children of `v` other than `A`, `B` and the `O`-child `oc`. -/
def othersAt (t : Tree) (v oc ca cb : Nat) : List Nat :=
  bodies.filter fun k =>
    match t.childTo v k with
    | some u => u != oc && u != ca && u != cb
    | none => false

/-- **Lemma 9.11(b)** at `(c, T, s)`: centred and balanced, `v` is the root of `T_c`, and the bodies below the other
children of `v` have minimal positions and form a set closed under minimal forces. -/
def rbAt (x : Cell) (c : Bool) (T : List Nat) (s : Nat) : Bool :=
  match centredBal x c T s with
  | some (v, oc, ca, cb) =>
    let t := x.tree c
    let K := othersAt t v oc ca cb
    v == t.root && K.all (x.posMin c) && K.all fun k => (forcesOn x c k).all K.contains
  | none => false

/-- The classes of the list `cand` joined by `rel` (a symmetric relation given as a test), by repeated merging. -/
def classes (rel : Nat → Nat → Bool) (cand : List Nat) : List (List Nat) :=
  cand.foldl (fun acc k =>
    let (joined, apart) := acc.partition fun cl => cl.any (rel k)
    (k :: joined.flatten) :: apart) []

/-- The program's reading of Lemma 9.11(b) at `(c, T, s)` (the supplement's `lemma_R1star`, case `beta`): the bodies
that are not at `O`, meet `O` at `v` and have a minimal position, joined when one has a minimal force from the other;
the classes closed under minimal forces that lie in the set of `othersAt` must cover it. -/
def rbProgAt (x : Cell) (c : Bool) (T : List Nat) (s : Nat) : Bool :=
  match centredBal x c T s with
  | some (v, oc, ca, cb) =>
    let t := x.tree c
    let K := othersAt t v oc ca cb
    let cand := bodies.filter fun k => !t.atO k && t.meetC k O == some v && x.posMin c k
    let rel := fun k j => (forcesOn x c k).contains j || (forcesOn x c j).contains k
    let cls := (classes rel cand).filter fun cl =>
      (cl.all fun k => (forcesOn x c k).all cl.contains) && cl.all K.contains
    v == t.root && K.all fun k => cls.any (·.contains k)
  | none => false

/-- The witnesses `(c, T, s)` of a test at a centred triangle. -/
def centredWit (f : Cell → Bool → List Nat → Nat → Bool) (x : Cell) : List (Bool × List Nat × Nat) :=
  colours.flatMap fun c => triples.flatMap fun T => (T.filter (f x c T)).map fun s => (c, T, s)

/-- The witnesses of Lemma 9.11(a). -/
def raWit (x : Cell) : List (Bool × List Nat × Nat) := centredWit raAt x

/-- The witnesses of Lemma 9.11(b). -/
def rbWit (x : Cell) : List (Bool × List Nat × Nat) := centredWit rbAt x

/-- The witnesses of the program's reading of Lemma 9.11(b). -/
def rbProgWit (x : Cell) : List (Bool × List Nat × Nat) := centredWit rbProgAt x

/-- The program's narrower reading of Lemma 9.11 (the supplement's `lemma_R1`): centred and balanced, with `a` and `b`
alone below their children and every other point below the child of `s` (so `v` is the root, with three children,
and `M_A = m_a`, `M_B = m_b`). -/
def r1ProgAt (x : Cell) (c : Bool) (T : List Nat) (s : Nat) : Bool :=
  match centredBal x c T s with
  | some (v, _, ca, cb) =>
    let t := x.tree c
    match rest T s, t.childTo v s with
    | [a, b], some cs =>
      t.pts ca == [a] && t.pts cb == [b] &&
        (List.range 7).all fun p => p == a || p == b || t.childTo v p == some cs
    | _, _ => false
  | none => false

/-- The witnesses of the program's narrower reading. -/
def r1ProgWit (x : Cell) : List (Bool × List Nat × Nat) := centredWit r1ProgAt x

/-! ## Lemma 9.12 -/

/-- **Lemma 9.12** at `(c, T, s, a)`, `b` the third body of `T`: the node of `T` in `T_c` is the root, with exactly
three children, the leaves of `a` and `b` and a child below which every other point lies; `s` is balanced in colour
`c` and `a` in the other colour. -/
def r6At (x : Cell) (c : Bool) (T : List Nat) (s a : Nat) : Bool :=
  let t := x.tree c
  match T.filter (fun k => k != s && k != a) with
  | [b] =>
    if !isTri x T || a == s then false else
    match triNode t a b s with
    | none => false
    | some v =>
      let la := t.leafOf a
      let lb := t.leafOf b
      let others := (List.range 7).filter fun p => p != a && p != b
      v == t.root && (t.children v).size == 3 && t.childTo v a == some la && t.childTo v b == some lb &&
        (match t.childTo v s with
          | some u => u != la && u != lb && others.all fun p => t.childTo v p == some u
          | none => false) &&
        x.balanced c T s && x.balanced (!c) T a
  | _ => false

/-- The witnesses `(c, T, s, a)` of Lemma 9.12. -/
def r6Wit (x : Cell) : List (Bool × List Nat × Nat × Nat) :=
  colours.flatMap fun c => triples.flatMap fun T =>
    T.flatMap fun s => ((T.filter (· != s)).filter (r6At x c T s)).map fun a => (c, T, s, a)

/-! ## Lemma 9.15 -/

/-- **Lemma 9.15** at `(c, s)`: `A^c_s` consists of the forces of the bodies of a set `K` of at least two bodies, and in
each tree the meets `meet(s, k)`, `k ∈ K`, are one node `v` and the bodies of `K` lie below one child of `v`. Returns
`K` (in the order of the labels). -/
def qAt (x : Cell) (c : Bool) (s : Nat) : Option (List Nat) :=
  let K := forcesOn x c s
  let inTree (t : Tree) : Bool :=
    match K with
    | k0 :: _ =>
      match t.meetC s k0 with
      | some v => K.all (fun k => t.meetC s k == some v) && K.all fun k => t.childTo v k == t.childTo v k0
      | none => false
    | [] => false
  if K.length == (x.eqSet c s).size && K.eraseDups.length ≥ 2 && inTree x.zt && inTree x.wt then some K else none

/-- The witnesses `(c, s, K)` of Lemma 9.15. -/
def qWit (x : Cell) : List (Bool × Nat × List Nat) :=
  colours.flatMap fun c => bodies.filterMap fun s => (qAt x c s).map fun K => (c, s, K)

/-! ## Corollary 9.18 for three bodies, by the census of the companion project -/

/-- The argmin set of the `c`-equation of `t` in the format of `L6F5`: whether the position belongs to it, and the
bit mask of the bodies whose forces belong to it. -/
def toEqSet (x : Cell) (c : Bool) (t : Nat) : L6F5.EqSet :=
  ⟨(x.eqSet c t).contains (.pos t),
   (List.range 6).foldl (fun m j => if (x.eqSet c t).contains (.cross t j) then m + 2 ^ j else m) 0⟩

/-- The cell in the format of `L6F5`: the `c`-equation of `t` at the index `6 c + t` (`c = 0` for `z`). -/
def toF5Cell (x : Cell) : L6F5.Cell := ⟨((List.range 12).map fun i => toEqSet x (i < 6) (i % 6)).toArray⟩

/-- The diagram in the format of `L6F1`: the kind of each pair (`1` for a `z`-stroke only, `2` for a `w`-stroke only,
`3` for a `zw`-edge) and the circle masks. -/
def toF1Diagram (d : Diagram) : L6F1.Diagram :=
  ⟨L6F1.codeOf 6 (fun a b => (if d.zstroke a b then 1 else 0) + (if d.wstroke a b then 2 else 0)),
   L6F1.maskOf 6 (fun k => d.zc.getD k false), L6F1.maskOf 6 (fun k => d.wc.getD k false)⟩

/-- The cliques of three bodies as in Corollary 9.18. (The sets of three bodies are `triples`, the same sets as
`L6F5.sets3`: compiled code of this package calls the functions of the companion project but does not refer to its
constants, whose symbols the shared library of this package does not resolve.) -/
def clique3Wit (x : Cell) (d : Diagram) : List (List Nat) :=
  let d' := toF1Diagram d
  let x' := toF5Cell x
  triples.filter (L6F5.cliqueOK d' x')

/-! ## The lemmas -/

/-- The class-level case of Corollary 9.10 holds in the diagram. -/
def lemE (d : Diagram) : Bool := !(eWit d).isEmpty
/-- The hypotheses of Corollary 9.10 hold in the cell. -/
def lemE1 (x : Cell) : Bool := !(e1Wit x).isEmpty
/-- The hypotheses of Lemma 9.11(a) hold in the cell. -/
def lemRa (x : Cell) : Bool := !(raWit x).isEmpty
/-- The hypotheses of Lemma 9.11(b) hold in the cell. -/
def lemRb (x : Cell) : Bool := !(rbWit x).isEmpty
/-- The hypotheses of Lemma 9.12 hold in the cell. -/
def lemR6 (x : Cell) : Bool := !(r6Wit x).isEmpty
/-- The hypotheses of Lemma 9.15 hold in the cell. -/
def lemQ (x : Cell) : Bool := !(qWit x).isEmpty
/-- The cell has a clique of three bodies as in Corollary 9.18. -/
def lemClique3 (x : Cell) (d : Diagram) : Bool := !(clique3Wit x d).isEmpty

/-! ## Counts -/

/-- The tests of the class-level case, Corollary 9.10, Lemma 9.11(a), Lemma 9.11(b), Lemma 9.12, Lemma 9.15 and
Corollary 9.18 for three bodies, in this order. -/
def flags (c : CCell) : List Bool :=
  [lemE c.d, lemE1 c.x, lemRa c.x, lemRb c.x, lemR6 c.x, lemQ c.x, lemClique3 c.x c.d]

/-- The numbers of cells in which each of the seven tests of `flags` holds, then the number of cells in which at
least one holds. -/
def genericCounts (cs : Array CCell) : List Nat :=
  let fl := cs.toList.map flags
  (List.range 7).map (fun i => (fl.filter fun f => f.getD i false).length) ++ [(fl.filter fun f => f.any id).length]

/-- The classes (all of `n6.json`, with or without stored cells) whose diagram has a triangle as in the class-level
case; `none` if a class is not read. -/
def eClasses (n6 : String) (nClasses : Nat) : Option (List Nat) := do
  let j ← (Lean.Json.parse n6).toOption
  let ds ← (List.range nClasses).mapM fun c => (Diagram.ofN6 j c).map fun d => (c, d)
  return (ds.filter fun (_, d) => lemE d).map (·.1)

/-- In every cell of a class with a triangle `T` as in the class-level case, `T` is a triangle of the cell and its
three bodies are balanced with respect to `T` in both colours (the argument after Corollary 9.10). -/
def eConsistent (cs : Array CCell) : Bool :=
  cs.all fun c => (eWit c.d).all fun T => isTri c.x T && T.all fun k => c.x.balanced true T k && c.x.balanced false T k

end Lean6.Special.Cover.Generic
