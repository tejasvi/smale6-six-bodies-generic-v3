/-!
# The search of Proposition 4.5, specification: trees as families of point sets

A specification of the search of Proposition 4.5, written to be reasoned about (total functions, structural
recursion) rather than to replicate the engine line by line (`L6F2`). It visits the same pairs of trees and decides
the same linear programs, so its cost is that of the engine's search; its cells are compared with the stored cells
(as families of point sets and argmin labels), and its completeness is proved in `L6Sound.F2S`.

Points: the bodies `0, …, 5` and the centre of mass `O = 6`. A set of points is a bit mask (bit `p` for the point `p`).
A tree without heights (Definition 4.1) on the points inserted so far is the list of its internal nodes, each given by
the set of the points below it, together with the body on the leaf of `O`, if any (that body lies below every node
that contains `O`).

Inserting a point `p` (Proposition 4.5, proof) gives the trees in which `p` is put on the leaf of `O` (`atO`), below a
node as a new child (`attach`), on a new node subdividing the edge above a node or a leaf (`subdivide`), or under a new
root (`newRoot`).
-/

namespace L6.F2S

/-- The centre of mass. -/
def O : Nat := 6

/-- The set `{p}`. -/
@[inline] def single (p : Nat) : Nat := 1 <<< p

/-- `p ∈ c`. -/
@[inline] def mem (p c : Nat) : Bool := c.testBit p

/-- `c ⊆ d`. -/
@[inline] def subset (c d : Nat) : Bool := c &&& d == c

/-- `c ⊂ d`. -/
@[inline] def ssubset (c d : Nat) : Bool := subset c d && c != d

/-- `insert p c`. -/
@[inline] def ins (p c : Nat) : Nat := c ||| single p

/-- The points `0, …, 6` of a set, in increasing order. -/
def toList (c : Nat) : List Nat := (List.range 7).filter fun p => mem p c

/-- A tree without heights: its internal nodes (sets of points) and the body on the leaf of `O`. -/
structure TS where
  nodes : List Nat
  leafO : Option Nat
  deriving DecidableEq, Inhabited, Repr

namespace TS

/-- The leaf class of a point: `{O, k}` for `O` and the body `k` on its leaf, else `{p}`. -/
def leafClass (T : TS) (p : Nat) : Nat :=
  match T.leafO with
  | some k => if p == O || p == k then single O ||| single k else single p
  | none => single p

/-- The representative of the leaf of a point (the body on the leaf of `O` is sent to `O`). -/
def lrep (T : TS) (p : Nat) : Nat :=
  match T.leafO with
  | some k => if p == k then O else p
  | none => p

/-- The leaf classes of the points of `S`, one per leaf (keyed by `lrep`, in increasing order of `lrep`). -/
def classes (T : TS) (S : Nat) : List Nat :=
  ((toList S).filter fun p => T.lrep p == p).map T.leafClass

/-- The node that is the whole set `S`, if the tree has one. -/
def isRoot (S c : Nat) : Bool := c == S

/-- `p` on the leaf of `O` (bodies only): every node containing `O` gets `p`. -/
def atO (T : TS) (p : Nat) : TS := ⟨T.nodes.map fun C => if mem O C then ins p C else C, some p⟩

/-- `p` as a new child of the node `v`: `v` and every node containing it get `p`. -/
def attach (T : TS) (v p : Nat) : TS := ⟨T.nodes.map fun C => if subset v C then ins p C else C, T.leafO⟩

/-- `p` on a new node subdividing the edge above `c` (a node other than the root, or a leaf class): the new node
`c ∪ {p}`, and every node strictly containing `c` gets `p`. -/
def subdivide (T : TS) (c p : Nat) : TS :=
  ⟨(T.nodes.map fun C => if ssubset c C then ins p C else C) ++ [ins p c], T.leafO⟩

/-- `p` under a new root `S ∪ {p}`. -/
def newRoot (T : TS) (S p : Nat) : TS := ⟨T.nodes ++ [ins p S], T.leafO⟩

/-- The edges that can be subdivided: the nodes other than `S`, and the leaf classes other than `S`. -/
def edges (T : TS) (S : Nat) : List Nat :=
  (T.nodes.filter fun c => c != S) ++ ((T.classes S).filter fun c => c != S)

/-- The insertions of the point `p` into a tree on the set `S` (`p ∉ S`, `O ∈ S`). -/
def options (T : TS) (S p : Nat) : List TS :=
  (if p != O && mem O S && T.leafO.isNone then [T.atO p] else []) ++
    T.nodes.map (fun v => T.attach v p) ++ (T.edges S).map (fun c => T.subdivide c p) ++ [T.newRoot S p]

/-- The internal node of the lowest common ancestor of `p` and `q`: the smallest node containing both (`none` if no
node contains both). -/
def lca (T : TS) (p q : Nat) : Option Nat :=
  T.nodes.foldl (fun acc C =>
    if mem p C && mem q C then
      match acc with
      | none => some C
      | some D => if subset C D then some C else some D
    else acc) none

/-- The parent of a node: the smallest node strictly containing it. -/
def parent (T : TS) (c : Nat) : Option Nat :=
  T.nodes.foldl (fun acc C =>
    if ssubset c C then
      match acc with
      | none => some C
      | some D => if subset C D then some C else some D
    else acc) none

/-- `p` and `q` lie on the same leaf. -/
def sameLeaf (T : TS) (p q : Nat) : Bool := T.lrep p == T.lrep q

/-- The index of a node in the list of nodes. -/
def idx (T : TS) (c : Nat) : Nat := T.nodes.idxOf c

/-- The canonical key of a tree: its nodes in increasing order and the body on the leaf of `O`. -/
def key (T : TS) : List Nat × Option Nat := (T.nodes.mergeSort (· ≤ ·), T.leafO)

end TS

/-- The tree on the single point `O`. -/
def TS.init : TS := ⟨[], none⟩

end L6.F2S
