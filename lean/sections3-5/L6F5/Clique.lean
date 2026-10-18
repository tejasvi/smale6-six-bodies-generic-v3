import L6F1.Rules
import L6F5.Json

/-!
# The cliques of Corollary 5.8

Corollary 5.8 of the paper concerns a set `K` of three or four bodies in a cell of a diagram such that

1. `K` is a `zw`-clique (all its pairs are `zw`-edges), or a `z`-clique (all its pairs are `z`-strokes and none is a
   `zw`-edge) none of whose bodies is `z`-circled, or a `w`-clique none of whose bodies is `w`-circled;
2. for each colour `c` and each `t ∈ K` the terms `Z^c_{tt'}`, `t' ∈ K \ t`, belong to the argmin set of the
   `c`-equation of `t`;
3. with `L^c ⊆ ℚ^K` the span of the vectors `e_t` of the bodies `t ∈ K` whose `c`-equation has a term `Z^c_{tX}`
   with `X ∉ K` in its argmin set, together with the vector `𝟙` if the position `c_t` belongs to the argmin set of
   the `c`-equation of some `t ∈ K`: if `K` has three bodies, `dim L^z, dim L^w ≤ 2` and
   `dim L^z + dim L^w ≤ 3`; if `K` has four bodies, `dim L^z, dim L^w ≤ 1`.

Proposition 5.9 counts the cells that have such a clique. This file states the three conditions for a cell given by
the argmin sets of the equations of the bodies (`Cell`) and for a diagram of the family F1 (`L6F1.Diagram`: the kind
of each pair, `0` none, `1` `z`, `2` `w`, `3` `zw`, and the circle masks); `cliqueOK d x K` is their conjunction.
The dimensions are ranks over `ℚ` of integer vectors, computed by fraction-free Gaussian elimination (`rank`).

The stored cells (`data/cells/c<N>.jsonl`) list, for each of the fourteen base identities (the equations of the six
bodies in both colours, `U = E`, stored as `["U"]`, and `Σ_{k<l} m_k m_l z_{kl} w_{kl} = M E`, stored as `["I"]`),
the terms of its argmin set. The `c`-equation of the body `t` is stored
under the name `[c, "S", [t]]` (the subset sum of `J = {t}`, which is `m_t` times the equation), the position `c_t`
as the label `["pos", t]` and the term `m_t m_X Z^c_{tX}` as `["cross", t, X]`.
-/

namespace L6F5

open L6F1 (Diagram kind circled zStroke wStroke)

/-! ## Cells -/

/-- The argmin set of the `c`-equation `c_t = Σ_{l ≠ t} m_l Z^c_{tl}` of a body `t` in a cell: `pos` says whether the
position `c_t` belongs to it, and bit `X` of `cross` whether the term `Z^c_{tX}` does. -/
structure EqSet where
  pos : Bool
  cross : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A cell, as far as Corollary 5.8 needs it: the argmin sets of the twelve equations of the bodies, the `c`-equation
of the body `t` at the index `6 c + t` (`c = 0` for `z`, `c = 1` for `w`). -/
structure Cell where
  eqs : Array EqSet
  deriving Inhabited

/-- The argmin set of the `c`-equation of the body `t`. -/
def Cell.eq (x : Cell) (c t : Nat) : EqSet := x.eqs[6 * c + t]!

/-- The stored labels of the argmin set of the equation of the body `t`: `["pos", t]` and `["cross", t, X]` with
`X < 6`, `X ≠ t`, each at most once. Any other label gives `none`. -/
def readLabels (t : Nat) : List JV → Option EqSet
  | [] => some ⟨false, 0⟩
  | l :: ls =>
    match readLabels t ls with
    | none => none
    | some r =>
      match l with
      | .arr [.str "pos", .num i] => if i == t && !r.pos then some { r with pos := true } else none
      | .arr [.str "cross", .num i, .num j] =>
        if i == t && j < 6 && j != t && !r.cross.testBit j then some { r with cross := r.cross + 2 ^ j } else none
      | _ => none

/-- The labels of the argmin set of `U = E` (`name = "delta"`) or of `I` (`name = "zw"`): `["E"]` and
`[name, k, l]` with `k < l < 6`. -/
def labelsUI (name : String) : List JV → Bool
  | [] => true
  | .arr [.str "E"] :: ls => labelsUI name ls
  | .arr [.str s, .num k, .num l] :: ls => s == name && k < l && l < 6 && labelsUI name ls
  | _ => false

/-- The index of a base identity from its stored name: `6 c + t` for the `c`-equation of the body `t`, `12` for
`U = E` and `13` for `I`. -/
def identIndex : JV → Option Nat
  | .arr [.str "z", .str "S", .arr [.num t]] => if t < 6 then some t else none
  | .arr [.str "w", .str "S", .arr [.num t]] => if t < 6 then some (6 + t) else none
  | .arr [.str "U"] => some 12
  | .arr [.str "I"] => some 13
  | _ => none

/-- **Reads the value of `argmin`**: a list of pairs `[name, labels]` in which each of the fourteen base identities
occurs exactly once, with labels as above. Any other value gives `none`. -/
def readCell (v : JV) : Option Cell :=
  match v with
  | .arr entries => go entries (List.replicate 14 (none : Option EqSet)).toArray
  | _ => none
where
  /-- The entries `es`, the argmin sets read so far being `tbl`. -/
  go : List JV → Array (Option EqSet) → Option Cell
    | [], tbl => if tbl.all Option.isSome then some ⟨(tbl.extract 0 12).map fun o => o.getD default⟩ else none
    | e :: es, tbl =>
      match e with
      | .arr [name, .arr labels] =>
        match identIndex name with
        | none => none
        | some k =>
          if tbl[k]!.isSome then none
          else if k < 12 then
            match readLabels (k % 6) labels with
            | none => none
            | some s => go es (tbl.set! k (some s))
          else if labelsUI (if k == 12 then "delta" else "zw") labels then go es (tbl.set! k (some default))
          else none
      | _ => none

/-! ## The conditions of Corollary 5.8 -/

/-- The bodies. -/
def bodies : List Nat := List.range 6

/-- The sublists of `xs` of length `k`, in lexicographic order. -/
def choose : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (choose k xs).map (x :: ·) ++ choose (k + 1) xs

/-- The sets of three bodies (20) and of four bodies (15), as increasing lists. -/
def sets3 : List (List Nat) := choose 3 bodies
/-- The sets of four bodies. -/
def sets4 : List (List Nat) := choose 4 bodies

/-- `f a b` for all `a` before `b` in the list. -/
def allPairs (f : Nat → Nat → Bool) : List Nat → Bool
  | [] => true
  | a :: rest => rest.all (f a) && allPairs f rest

/-- `K` is a `zw`-clique: all its pairs are `zw`-edges. -/
def isZWClique (d : Diagram) (K : List Nat) : Bool := allPairs (fun a b => kind d.e a b == 3) K

/-- `K` is a `z`-clique none of whose bodies is `z`-circled: all its pairs are `z`-strokes and none is a `zw`-edge
(their kind is `z`), and no body of `K` is `z`-circled. -/
def isZCliqueUncircled (d : Diagram) (K : List Nat) : Bool :=
  allPairs (fun a b => kind d.e a b == 1) K && K.all fun t => !circled d.zc t

/-- `K` is a `w`-clique none of whose bodies is `w`-circled. -/
def isWCliqueUncircled (d : Diagram) (K : List Nat) : Bool :=
  allPairs (fun a b => kind d.e a b == 2) K && K.all fun t => !circled d.wc t

/-- Condition 1: `K` is a `zw`-clique, or a `z`- or `w`-clique none of whose bodies is circled in the colour of its
strokes. -/
def kindOK (d : Diagram) (K : List Nat) : Bool :=
  isZWClique d K || isZCliqueUncircled d K || isWCliqueUncircled d K

/-- Condition 2 for the colour `c`: for each `t ∈ K` the terms `Z^c_{tt'}`, `t' ∈ K \ t`, belong to the argmin set
of the `c`-equation of `t`. -/
def internalIn (x : Cell) (c : Nat) (K : List Nat) : Bool :=
  K.all fun t => K.all fun t' => t' == t || (x.eq c t).cross.testBit t'

/-- The `c`-equation of `t` has a term `Z^c_{tX}` with `X ∉ K` in its argmin set. -/
def hasOutside (x : Cell) (c : Nat) (K : List Nat) (t : Nat) : Bool :=
  bodies.any fun X => !K.contains X && (x.eq c t).cross.testBit X

/-- The position `c_t` belongs to the argmin set of the `c`-equation of some `t ∈ K`. -/
def hasPosition (x : Cell) (c : Nat) (K : List Nat) : Bool := K.any fun t => (x.eq c t).pos

/-- The vector `e_t` of `ℚ^K` (coordinates in the order of the list `K`). -/
def unitVec (K : List Nat) (t : Nat) : List Int := K.map fun s => if s == t then 1 else 0

/-- The spanning vectors of `L^c`: `e_t` for the bodies `t ∈ K` with an outside term in the argmin set of their
`c`-equation, and `𝟙` if some position `c_t`, `t ∈ K`, belongs to the argmin set of the `c`-equation of `t`. -/
def generators (x : Cell) (c : Nat) (K : List Nat) : List (List Int) :=
  let es := (K.filter (hasOutside x c K)).map (unitVec K)
  if hasPosition x c K then es ++ [K.map fun _ => 1] else es

/-- The rank over `ℚ` of a list of integer vectors of length `n`, by fraction-free Gaussian elimination: if some
vector `p` has a nonzero first coordinate `a`, then `p` is a pivot, every other vector `r` is replaced by
`a r - r₀ p` (whose first coordinate is `0`, and which spans with `p` the same space as `r` and `p`), and the rank is
one more than the rank of these vectors without their first coordinates; otherwise the first coordinates, all zero,
are dropped. -/
def rank : Nat → List (List Int) → Nat
  | 0, _ => 0
  | n + 1, rows =>
    match rows.find? (fun r => r.headD 0 != 0) with
    | none => rank n (rows.map List.tail)
    | some p =>
      let a := p.headD 0
      rank n ((rows.erase p).map fun r => (List.zipWith (fun u v => a * u - r.headD 0 * v) r p).tail) + 1

/-- `dim L^c`. -/
def dimL (x : Cell) (c : Nat) (K : List Nat) : Nat := rank K.length (generators x c K)

/-- Condition 3 on `dim L^z = dz` and `dim L^w = dw` for a clique of `k` bodies. -/
def dimsOK (k dz dw : Nat) : Bool :=
  if k == 3 then dz ≤ 2 && dw ≤ 2 && dz + dw ≤ 3
  else if k == 4 then dz ≤ 1 && dw ≤ 1
  else false

/-- **`K` is a clique as in Corollary 5.8 in the cell `x` of the diagram `d`.** -/
def cliqueOK (d : Diagram) (x : Cell) (K : List Nat) : Bool :=
  (K.length == 3 || K.length == 4) && kindOK d K && internalIn x 0 K && internalIn x 1 K &&
    dimsOK K.length (dimL x 0 K) (dimL x 1 K)

/-- The cell has a clique of three bodies as in Corollary 5.8. -/
def has3 (d : Diagram) (x : Cell) : Bool := sets3.any (cliqueOK d x)

/-- The cell has a clique of four bodies as in Corollary 5.8. -/
def has4 (d : Diagram) (x : Cell) : Bool := sets4.any (cliqueOK d x)

/-- **The cell has a clique as in Corollary 5.8.** -/
def hasClique (d : Diagram) (x : Cell) : Bool := has3 d x || has4 d x

/-! ## The forced argmin sets

Where the diagram has a stroke or a circle in the `c`-equation of a body `t`, the terms of exponent `-2` are the
position `c_t` (if `t` is `c`-circled) and the terms `Z^c_{tl}` of the `c`-strokes `tl`, and they form the argmin
set (the paper, after the definition of a cell). `forcedOK` checks that the stored argmin sets of these equations
are exactly these sets. It is not a condition of Corollary 5.8; it explains why the census program of the paper,
which reads the `zw`-cliques and the colour of the strokes of a `z`- or `w`-clique off the diagram, reads the same
sets as Corollary 5.8. -/

/-- The bit mask of the bodies `l` such that `tl` is a `c`-stroke. -/
def strokeMask (d : Diagram) (c t : Nat) : Nat :=
  (bodies.filter fun l => l != t && (if c == 0 then zStroke d.e t l else wStroke d.e t l)).foldl
    (fun m l => m + 2 ^ l) 0

/-- The stored argmin sets of the equations with a stroke or a circle are the forced ones. -/
def forcedOK (d : Diagram) (x : Cell) : Bool :=
  [0, 1].all fun c => bodies.all fun t =>
    let circ := circled (if c == 0 then d.zc else d.wc) t
    let sm := strokeMask d c t
    if circ || sm != 0 then x.eq c t == ⟨circ, sm⟩ else true

end L6F5
