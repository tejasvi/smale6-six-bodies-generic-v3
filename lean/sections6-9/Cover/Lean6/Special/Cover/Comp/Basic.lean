import L6F34.Basic

/-!
# Proposition 9.23: trees, argmin sets and the notation of §9.1

The stored cells are read with the reader of the companion project `lean6` (`L6.F34.Cell.ofJson`: the two trees and
the argmin sets of the fourteen base identities), the class representatives with `L6.F34.Diagram.ofN6`. This file adds
the notation of §9.1 of the paper on top of them, as functions in the namespaces `L6.F34.Tree` and `L6.F34.Cell`.

* Points: the bodies `0, …, 5` and the centre of mass `O = 6`. A body that shares the leaf of `O` has `c_k ≡ 0`.
* `Tree.preceq t u v`: `u ⪯ v`, the node `u` lies on the path from the root to `v`.
* `Tree.childTo t v p`: the child of the node `v` below which the point `p` lies (`none` if `p` is not below a child of
  `v`); the `O`-child of `v` is `childTo t v O`.
* `Tree.meetC t p q`: `meet_c(p, q)`, the lowest common ancestor of the leaves of `p` and `q` (`none` if they share a
  leaf).
* `Cell.am x n`: the argmin set of the identity `n`; `Cell.eqSet x c k`: the argmin set `A^c_k` of the `c`-equation of
  body `k` (`c = true` for `z`). Its labels are `pos k` (the position `c_k`) and `cross k l` (the force `m_l Z^c_{kl}`).
-/

namespace Lean6.Special.Cover

open L6.F34

/-- The centre of mass `O`. -/
abbrev O : Nat := 6

/-- The bodies. -/
def bodies : List Nat := [0, 1, 2, 3, 4, 5]

/-- The sets of `r` elements of a list, in lexicographic order of positions. -/
def subsets : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | r + 1, x :: xs => (subsets r xs).map (x :: ·) ++ subsets (r + 1) xs

/-! ## Trees -/

/-- The leaf of the point `p`. -/
def _root_.L6.F34.Tree.leafOf (t : Tree) (p : Nat) : Nat := t.leaf.getD p maxNode

/-- `u ⪯ v`: `u` lies on the path from the root to `v` (`u = v` included). -/
def _root_.L6.F34.Tree.preceq (t : Tree) (u v : Nat) : Bool := (t.ancestors v).contains u

/-- The point `p` lies below the node `v` (its leaf is `v` or below `v`). -/
def _root_.L6.F34.Tree.below (t : Tree) (v p : Nat) : Bool := t.preceq v (t.leafOf p)

/-- The child of `v` on the path from `v` to the leaf of `p`; `none` if `p` is not below a child of `v`. -/
def _root_.L6.F34.Tree.childTo (t : Tree) (v p : Nat) : Option Nat := Id.run do
  let mut u := t.leafOf p
  for _ in [0:maxNode] do
    let q := t.par.getD u maxNode
    if q == v then return some u
    if q ≥ maxNode then return none
    u := q
  return none

/-- `meet_c(p, q)`; `none` if `p` and `q` share a leaf. -/
def _root_.L6.F34.Tree.meetC (t : Tree) (p q : Nat) : Option Nat := t.meet p q

/-- The body `k` shares the leaf of `O` (so `c_k ≡ 0`). -/
def _root_.L6.F34.Tree.atO (t : Tree) (k : Nat) : Bool := t.leafOf k == t.leafOf O

/-- The points `0, …, 6` below the node `v`. -/
def _root_.L6.F34.Tree.pts (t : Tree) (v : Nat) : List Nat := (List.range 7).filter (t.below v)

/-- The internal nodes. -/
def _root_.L6.F34.Tree.internal (t : Tree) : List Nat := t.kids.toList.map (·.1)

/-- `k` lies below the `O`-child of `v`, or shares the leaf of `O`. -/
def _root_.L6.F34.Tree.inOChild (t : Tree) (v k : Nat) : Bool :=
  t.atO k || (match t.childTo v O, t.childTo v k with
    | some a, some b => a == b
    | _, _ => false)

/-! ## Argmin sets -/

/-- The argmin set of the identity `n` (empty if the cell does not list it). -/
def _root_.L6.F34.Cell.am (x : Cell) (n : IdName) : Array Lab :=
  match x.argmin.find? (·.1 == n) with
  | some (_, l) => l
  | none => #[]

/-- `A^c_k`, the argmin set of the `c`-equation of body `k` (`c = true` for `z`). -/
def _root_.L6.F34.Cell.eqSet (x : Cell) (c : Bool) (k : Nat) : Array Lab := x.am (.body c k)

/-- The tree of colour `c`. -/
def _root_.L6.F34.Cell.tree (x : Cell) (c : Bool) : Tree := if c then x.zt else x.wt

/-- Two label sets are equal. -/
def labSetEq (a b : Array Lab) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

/-- The position of `k` is minimal in colour `c`. -/
def _root_.L6.F34.Cell.posMin (x : Cell) (c : Bool) (k : Nat) : Bool := (x.eqSet c k).contains (.pos k)

/-- The force of `l` on `k` is minimal in colour `c`. -/
def _root_.L6.F34.Cell.forceMin (x : Cell) (c : Bool) (k l : Nat) : Bool := (x.eqSet c k).contains (.cross k l)

/-- `A^c_k` consists of the forces on `k` of the bodies of `L`, and of the position of `k` if `withPos`. -/
def _root_.L6.F34.Cell.eqSetIs (x : Cell) (c : Bool) (k : Nat) (withPos : Bool) (L : List Nat) : Bool :=
  labSetEq (x.eqSet c k) ((if withPos then [Lab.pos k] else []) ++ L.map (Lab.cross k ·)).toArray

/-- `k` is balanced in colour `c` with respect to `T`: `A^c_k` consists of the forces of the bodies of `T \ k`. -/
def _root_.L6.F34.Cell.balanced (x : Cell) (c : Bool) (T : List Nat) (k : Nat) : Bool :=
  x.eqSetIs c k false (T.filter (· != k))

/-! ## Reading the stored cells -/

/-- The cells of the text of a cell file (one JSON object per nonempty line); `none` if a line is not read. -/
def readCells (s : String) : Option (Array Cell) := parseCells s

end Lean6.Special.Cover
