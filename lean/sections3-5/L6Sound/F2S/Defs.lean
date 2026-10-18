import Mathlib
import L6F2S.Search
import L6Sound.Common.Farkas

/-!
# The specification search: semantic definitions

The objects of the completeness theorem of the specification search (`L6F2S`):

* `twoLeaves`, `WF T S`: a tree without heights on the set of points `S` (Definition 4.1 for the points inserted so
  far): distinct nodes, subsets of `S`, each with two points on different leaves, pairwise nested or disjoint, `S` a
  node when it has two leaves, and the body on the leaf of `O` below exactly the nodes containing `O`.
* `restrict T S`: the restriction of a tree to a subset `S` of its points (the tree of the points of `S`).
* `TS.Equiv`: two trees with the same nodes (as sets) and the same body on the leaf of `O`.
* `TS.cover T D`: the smallest node containing the set `D`.
* `ExpTree`: a complete tree (on all seven points) with heights on its nodes; `ExpTree.e p q`: the exponent of
  `pos_p − pos_q`, the height of the lowest common ancestor.
* `Cond D Xz Xw`: the conditions of Lemma 4.3 for the diagram `D` and `ℓ(x) ≤ 0`, on a pair of complete trees with
  heights: (a) root heights `≥ −2`, (O1), (O2) with the strokes of `D`, the circles of `D`; (b) the root rule; (c) the
  least exponent of each base identity is attained twice; and `Σ_{k<l} x_kl ≤ 0`.
* `baseExps`: the exponents of the terms of the fourteen base identities, in the order of the specification's terms.
* `argminString`: the argmin part of the line of the cell of `(Xz, Xw)`.
-/

namespace L6.F2S

open L6.F2 (Diag Label IdName renderEntry pairs6)

/-! ## Trees without heights -/

/-- Two points of `C` (among the seven) on different leaves of `T`. -/
def twoLeaves (T : TS) (C : Nat) : Bool :=
  (toList C).any fun p => (toList C).any fun q => T.lrep p != T.lrep q

/-- A tree without heights on the set of points `S`. -/
structure WF (T : TS) (S : Nat) : Prop where
  S_lt : S < 128
  O_mem : mem O S = true
  nodup : T.nodes.Nodup
  sub : ∀ C ∈ T.nodes, subset C S = true
  two : ∀ C ∈ T.nodes, twoLeaves T C = true
  lam : ∀ C ∈ T.nodes, ∀ D ∈ T.nodes, subset C D = true ∨ subset D C = true ∨ C &&& D = 0
  root : twoLeaves T S = true → S ∈ T.nodes
  leafO : ∀ k, T.leafO = some k → k < 6 ∧ mem k S = true ∧ ∀ C ∈ T.nodes, mem O C = mem k C

/-- The body on the leaf of `O` after restriction to `S`. -/
def restrictLeafO (lo : Option Nat) (S : Nat) : Option Nat :=
  match lo with
  | some k => if mem k S then some k else none
  | none => none

/-- The restriction of a tree to the set of points `S`. -/
def restrict (T : TS) (S : Nat) : TS :=
  let lo := restrictLeafO T.leafO S
  ⟨((T.nodes.map (· &&& S)).filter fun D => twoLeaves ⟨[], lo⟩ D).dedup, lo⟩

/-- Same nodes (as sets) and the same body on the leaf of `O`. -/
def TS.Equiv (T T' : TS) : Prop := T.nodes.toFinset = T'.nodes.toFinset ∧ T.leafO = T'.leafO

/-- The smallest node containing the set `D`. -/
def TS.cover (T : TS) (D : Nat) : Option Nat :=
  T.nodes.foldl (fun acc C =>
    if subset D C then
      match acc with
      | none => some C
      | some E => if subset C E then some C else some E
    else acc) none

/-! ## Trees with heights -/

/-- A tree with heights on its nodes. -/
structure ExpTree where
  T : TS
  h : Nat → ℚ

/-- A complete tree (on all seven points) whose heights increase strictly from the root to the leaves. -/
def ExpTree.Good (X : ExpTree) : Prop :=
  WF X.T all ∧ ∀ C ∈ X.T.nodes, ∀ D ∈ X.T.nodes, ssubset C D = true → X.h D < X.h C

/-- The exponent of `pos_p − pos_q` for points on different leaves: the height of their lowest common ancestor. -/
def ExpTree.e (X : ExpTree) (p q : Nat) : ℚ :=
  match X.T.lca p q with
  | some C => X.h C
  | none => 0

/-- The height of a node of a partial tree, read off the complete tree: the height of the smallest node of the
complete tree containing it. -/
def ExpTree.hc (X : ExpTree) (D : Nat) : ℚ := X.h ((X.T.cover D).getD 0)

/-- The vector of heights of a pair of partial trees (variables of `Pair`), read off the complete trees. -/
def heightVec (Xz Xw : ExpTree) (P : Pair) (i : Nat) : ℚ :=
  if i < P.nz then Xz.hc (P.tz.nodes.getD i 0) else Xw.hc (P.tw.nodes.getD (i - P.nz) 0)

/-! ## The base identities at a pair of complete trees with heights -/

/-- `ζ_kl`, `ω_kl`, `x_kl`. -/
def zeta (Xz : ExpTree) (k l : Nat) : ℚ := Xz.e k l
def omega (Xw : ExpTree) (k l : Nat) : ℚ := Xw.e k l
def xkl (Xz Xw : ExpTree) (k l : Nat) : ℚ := (Xz.e k l + Xw.e k l) / 2

/-- The exponents of the terms of the equation of body `i` in one colour, in the order of `bodyIdent`: the position
(when the body is not on the leaf of `O`), then `Z_ij` (or `W_ij`) for `j ≠ i` in increasing order. -/
def bodyExps (Xz Xw : ExpTree) (colour : Bool) (i : Nat) : List ℚ :=
  let X := if colour then Xz else Xw
  (if X.T.sameLeaf i O then [] else [X.e i O]) ++
    ((List.range 6).filter (· != i)).map fun j =>
      if colour then -(Xz.e i j + 3 * Xw.e i j) / 2 else -(3 * Xz.e i j + Xw.e i j) / 2

/-- The exponents of the terms of `U = E`: `E` (`0`), then `p_kl` (`−x_kl`) in the order of `pairs6`. -/
def uExps (Xz Xw : ExpTree) : List ℚ := 0 :: pairs6.toList.map fun kl => -xkl Xz Xw kl.1 kl.2

/-- The exponents of the terms of `I = ME`: `E` (`0`), then `z_kl w_kl` (`2 x_kl`). -/
def iExps (Xz Xw : ExpTree) : List ℚ := 0 :: pairs6.toList.map fun kl => 2 * xkl Xz Xw kl.1 kl.2

/-- The exponents of the terms of the fourteen base identities, in the order of `idents`. -/
def baseExps (Xz Xw : ExpTree) : List (List ℚ) :=
  (List.range 6).map (bodyExps Xz Xw true) ++ (List.range 6).map (bodyExps Xz Xw false) ++
    [uExps Xz Xw, iExps Xz Xw]

/-- The least value of a list is attained at two positions. -/
def MinTwice (l : List ℚ) : Prop :=
  ∃ i j, i < l.length ∧ j < l.length ∧ i ≠ j ∧ l[i]! = l[j]! ∧ ∀ k < l.length, l[i]! ≤ l[k]!

/-- The positions of the least value of a list. -/
noncomputable def argminPos (l : List ℚ) : List Nat :=
  (List.range l.length).filter fun i => decide (∀ k < l.length, l[i]! ≤ l[k]!)

/-! ## The conditions of Lemma 4.3 and `ℓ ≤ 0` -/

/-- The conditions on a pair of complete trees with heights for the diagram `D`. -/
structure Cond (D : Diag) (Xz Xw : ExpTree) : Prop where
  gz : Xz.Good
  gw : Xw.Good
  root_z : -2 ≤ Xz.h all
  root_w : -2 ≤ Xw.h all
  O1z : ∀ k l, k < l → l < 6 → Xz.e k l + 3 * Xw.e k l ≤ 4
  O1w : ∀ k l, k < l → l < 6 → 3 * Xz.e k l + Xw.e k l ≤ 4
  O2z : ∀ k l, k < l → l < 6 → (Xz.e k l + 3 * Xw.e k l = 4 ↔ D.zstroke k l = true)
  O2w : ∀ k l, k < l → l < 6 → (3 * Xz.e k l + Xw.e k l = 4 ↔ D.wstroke k l = true)
  circ_z : ∀ k < 6, if Xz.T.sameLeaf k O then D.zc[k]! = false else (Xz.e k O = -2 ↔ D.zc[k]! = true)
  circ_w : ∀ k < 6, if Xw.T.sameLeaf k O then D.wc[k]! = false else (Xw.e k O = -2 ↔ D.wc[k]! = true)
  com_z : comOk Xz.T all = true
  com_w : comOk Xw.T all = true
  twice : ∀ l ∈ baseExps Xz Xw, MinTwice l
  ell : (pairs6.toList.map fun kl => xkl Xz Xw kl.1 kl.2).sum ≤ 0

/-! ## The cell of a pair of complete trees with heights -/

/-- The labels and the forced argmin set of the equation of body `i` (in the order of `bodyIdent`), from the diagram
and the body on the leaf of `O` of the tree of that colour. -/
def bodyMeta (D : Diag) (lo : Option Nat) (colour : Bool) (i : Nat) : IdName × List Label × Option (List Nat) :=
  let labels : List Label :=
    (if lo = some i then [] else [Label.pos i]) ++ ((List.range 6).filter (· != i)).map fun j => Label.cross i j
  let forced := (List.range labels.length).filter fun t =>
    match labels[t]! with
    | .pos k => if colour then D.zc[k]! else D.wc[k]!
    | .cross k l => if colour then D.zstroke k l else D.wstroke k l
    | _ => false
  (.S colour i, labels, if forced.isEmpty then none else some forced)

/-- The labels and forced set of `U = E`. -/
def uMeta (D : Diag) : IdName × List Label × Option (List Nat) :=
  let forced := ((List.range 15).filter fun pi =>
    let kl := pairs6[pi]!; D.zstroke kl.1 kl.2 && D.wstroke kl.1 kl.2).map (· + 1)
  (.U, Label.E :: pairs6.toList.map (fun kl => Label.delta kl.1 kl.2), if forced.isEmpty then none else some forced)

/-- The labels of `I = ME`. -/
def iMeta : IdName × List Label × Option (List Nat) :=
  (.I, Label.E :: pairs6.toList.map (fun kl => Label.zw kl.1 kl.2), none)

/-- The names, labels and forced sets of the fourteen base identities, in the order of `idents`. -/
def identsMeta (D : Diag) (lz lw : Option Nat) : List (IdName × List Label × Option (List Nat)) :=
  (List.range 6).map (bodyMeta D lz true) ++ (List.range 6).map (bodyMeta D lw false) ++ [uMeta D, iMeta]

/-- The argmin part of the line of the cell of `(Xz, Xw)`: the entries of the identities whose argmin set the
diagram forces, then those of the other base identities, each with the labels of its terms of least exponent. -/
noncomputable def argminString (D : Diag) (Xz Xw : ExpTree) : String :=
  let es := (identsMeta D Xz.T.leafO Xw.T.leafO).zip (baseExps Xz Xw)
  let fixed := (es.filter fun ie => ie.1.2.2.isSome).map fun ie =>
    renderEntry ie.1.1 ((ie.1.2.2.getD []).map fun t => ie.1.2.1.getD t .E).toArray
  let branch := (es.filter fun ie => ie.1.2.2.isNone).map fun ie =>
    renderEntry ie.1.1 ((argminPos ie.2).map fun t => ie.1.2.1.getD t .E).toArray
  ", ".intercalate (fixed ++ branch)

/-! ## Values of forms, and the facts about a partial tree that its rows use -/

/-- The value of a form (an array of integer coefficients of the variables `0, …, nv − 1`) at `h`; `Row.lin nv r h`
is `formVal nv r.a h`. -/
def formVal (nv : Nat) (a : Array Int) (h : ℕ → ℚ) : ℚ := ∑ j ∈ Finset.range nv, (a[j]! : ℚ) * h j

/-- The facts about a partial tree `T` on the set `S` that its rows use, read off a complete tree with heights `X`:
distinct nodes; every node is a root (no parent) with height `≥ −2`, or has a parent node of smaller height; the
lowest common ancestor of two inserted bodies, and of an inserted body and `O`, is a node whose height is the exponent
of the pair in `X`; and a body shares the leaf of `O` in `T` exactly when it does in `X`. -/
structure LevelFacts (X : ExpTree) (T : TS) (S : Nat) : Prop where
  nodup : T.nodes.Nodup
  par : ∀ C ∈ T.nodes, (T.parent C = none ∧ -2 ≤ X.hc C) ∨ (∃ P ∈ T.nodes, T.parent C = some P ∧ X.hc P < X.hc C)
  lca : ∀ k l, k < 6 → l < 6 → k ≠ l → mem k S = true → mem l S = true →
    ∃ D ∈ T.nodes, T.lca k l = some D ∧ X.hc D = X.e k l
  same : ∀ k, k < 6 → mem k S = true → mem O S = true → T.sameLeaf k O = X.T.sameLeaf k O
  pos : ∀ k, k < 6 → mem k S = true → mem O S = true → T.sameLeaf k O = false →
    ∃ D ∈ T.nodes, T.lca k O = some D ∧ X.hc D = X.e k O

end L6.F2S
