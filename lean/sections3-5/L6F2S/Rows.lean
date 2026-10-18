import L6Common.Rows
import L6F2S.Basic
import L6F2.Search

/-!
# The rows of the specification search

The linear conditions of Lemma 4.3 (a) and Definition 4.4 on the heights of the internal nodes of a pair of trees,
as rows of `L6.Row` (every row times `2`). Variables: the nodes of the `z`-tree in list order, then those of the
`w`-tree; the slack `s` is the coefficient `c` of a row.

* `treeRows`: the root height is `≥ −2`, and every node is strictly higher than its parent.
* `pairRows`: (O1), (O2) for the pairs of inserted bodies.
* `posRows`: (C) for the inserted bodies: `a_k = −2` for a circled body, `a_k > −2` otherwise; a circled body on the leaf
  of `O` makes the pair impossible (`none`).
* `thresholdRow`: the relaxation of `ℓ(x) ≤ 0` of the proof of Proposition 4.5.
* `idents`: the base identities (the equations of the bodies in both colours, `U = E`, `I = ME`) with their terms,
  the exponent form of each term, and the forced argmin set when the diagram forces one.
-/

namespace L6.F2S

open L6.F2 (Diag Label IdName pairs6)

/-- A form with the given coefficients at the given variables (repeated variables add up). -/
def form (nv : Nat) (cs : List (Nat × Int)) : Array Int :=
  cs.foldl (fun a ic => a.set! ic.1 (a[ic.1]! + ic.2)) (Array.replicate nv 0)

/-- The difference of two forms. -/
def fsub (a b : Array Int) : Array Int := Array.zipWith (· - ·) a b

/-- The row `d ≥ s` (strict `d > 0`; times 2: `d − 2s ≥ 0` for a form `d` already doubled). -/
def rowGt (d : Array Int) : Row := { a := d, c := -2, lo := some 0, hi := none }

/-- The row `d = 0`. -/
def rowEq (d : Array Int) : Row := { a := d, c := 0, lo := some 0, hi := some 0 }

/-- A pair of trees with the offsets of their variables. -/
structure Pair where
  tz : TS
  tw : TS
  deriving Inhabited

namespace Pair

def nz (P : Pair) : Nat := P.tz.nodes.length
def nv (P : Pair) : Nat := P.tz.nodes.length + P.tw.nodes.length

/-- The variable of a node of the `z`-tree, of the `w`-tree. -/
def vz (P : Pair) (c : Nat) : Nat := P.tz.idx c
def vw (P : Pair) (c : Nat) : Nat := P.nz + P.tw.idx c

end Pair

/-- The tree rows of one tree (`off` = the offset of its variables). -/
def treeRows (T : TS) (off nv : Nat) : List Row :=
  T.nodes.map fun C =>
    match T.parent C with
    | none => { a := form nv [(off + T.idx C, 2)], c := 0, lo := some (-4), hi := none }
    | some P => rowGt (form nv [(off + T.idx C, 2), (off + T.idx P, -2)])

/-- The bodies of a set of points, in increasing order. -/
def bodies (S : Nat) : List Nat := (List.range 6).filter fun k => mem k S

/-- The pairs `k < l` of bodies of a set, in the order of `pairs6`. -/
def placedPairs (S : Nat) : List (Nat × Nat) := pairs6.toList.filter fun kl => mem kl.1 S && mem kl.2 S

/-- (O1), (O2) for the pair `kl` with the meets `Z`, `W` (variables). -/
def pairRowsAt (D : Diag) (nv Z W : Nat) (k l : Nat) : List Row :=
  [ if D.zstroke k l then { a := form nv [(Z, 2), (W, 6)], c := 0, lo := some 8, hi := some 8 }
    else { a := form nv [(Z, 2), (W, 6)], c := 2, lo := none, hi := some 8 },
    if D.wstroke k l then { a := form nv [(Z, 6), (W, 2)], c := 0, lo := some 8, hi := some 8 }
    else { a := form nv [(Z, 6), (W, 2)], c := 2, lo := none, hi := some 8 } ]

/-- The meets of the pair `kl` in both trees, as variables. -/
def meets (P : Pair) (k l : Nat) : Option (Nat × Nat) := do
  let Z ← P.tz.lca k l
  let W ← P.tw.lca k l
  some (P.vz Z, P.vw W)

/-- (O1), (O2) for all placed pairs; `none` if a meet is missing. -/
def pairRows (D : Diag) (P : Pair) (S : Nat) : Option (List Row) :=
  (placedPairs S).foldr (fun kl acc => do
    let rs ← acc
    let (Z, W) ← meets P kl.1 kl.2
    some (pairRowsAt D P.nv Z W kl.1 kl.2 ++ rs)) (some [])

/-- (C) for one body in one tree: `none` if circled and on the leaf of `O`. -/
def posRowsAt (T : TS) (off nv : Nat) (circled : Bool) (k : Nat) : Option (List Row) :=
  if T.sameLeaf k O then (if circled then none else some [])
  else
    match T.lca k O with
    | none => none
    | some m =>
      if circled then some [{ a := form nv [(off + T.idx m, 2)], c := 0, lo := some (-4), hi := some (-4) }]
      else some [{ a := form nv [(off + T.idx m, 2)], c := -2, lo := some (-4), hi := none }]

/-- (C) for the inserted bodies (when `O` is inserted). -/
def posRows (D : Diag) (P : Pair) (S : Nat) : Option (List Row) :=
  if !mem O S then some []
  else (bodies S).foldr (fun k acc => do
    let rs ← acc
    let rz ← posRowsAt P.tz 0 P.nv D.zc[k]! k
    let rw ← posRowsAt P.tw P.nz P.nv D.wc[k]! k
    some (rz ++ rw ++ rs)) (some [])

/-- The least possible value of `x_kl`: `1` on a `zw`-edge, `0` on a stroke, `−2` otherwise. -/
def lowerX (D : Diag) (k l : Nat) : Int :=
  if D.zstroke k l && D.wstroke k l then 1 else if D.zstroke k l || D.wstroke k l then 0 else -2

/-- The relaxation of `ℓ(x) ≤ 0`: `Σ_{placed} x_kl + Σ_{other} lowerX ≤ 0` (times 2); `none` if a meet is missing. -/
def thresholdRow (D : Diag) (P : Pair) (S : Nat) : Option Row := do
  let cs ← (placedPairs S).foldr (fun kl acc => do
    let cs ← acc
    let (Z, W) ← meets P kl.1 kl.2
    some ((Z, (1 : Int)) :: (W, (1 : Int)) :: cs)) (some ([] : List (Nat × Int)))
  let const : Int := (pairs6.toList.filter fun kl => !(mem kl.1 S && mem kl.2 S)).foldl
    (fun acc kl => acc + lowerX D kl.1 kl.2) 0
  some { a := form P.nv cs, c := 0, lo := none, hi := some (-2 * const) }

/-- All rows of a pair of trees on the set `S`: tree rows, pair rows, position rows and the threshold row. -/
def partialRows (D : Diag) (P : Pair) (S : Nat) : Option (Array Row) := do
  let pr ← pairRows D P S
  let qr ← posRows D P S
  let th ← thresholdRow D P S
  some (treeRows P.tz 0 P.nv ++ treeRows P.tw P.nz P.nv ++ pr ++ qr ++ [th]).toArray

/-- The same rows without the threshold row (`base_lp` of the engine). -/
def baseRows (D : Diag) (P : Pair) (S : Nat) : Option (Array Row) := do
  let pr ← pairRows D P S
  let qr ← posRows D P S
  some (treeRows P.tz 0 P.nv ++ treeRows P.tw P.nz P.nv ++ pr ++ qr).toArray

/-! ## The base identities -/

/-- An identity of a cell: name, term labels, exponent forms (times 2), forced argmin set (if any). -/
structure SIdent where
  name : IdName
  labels : List Label
  terms : List (Array Int)
  forced : Option (List Nat)
  deriving Inhabited

/-- The equation of body `i` in one colour (`colour = true`: `z`). -/
def bodyIdent (D : Diag) (P : Pair) (colour : Bool) (i : Nat) : Option SIdent := do
  let T := if colour then P.tz else P.tw
  let off := if colour then 0 else P.nz
  let pos : List (Label × Array Int) :=
    if T.sameLeaf i O then [] else
      match T.lca i O with
      | some m => [(.pos i, form P.nv [(off + T.idx m, 2)])]
      | none => []
  let crosses ← ((List.range 6).filter (· != i)).foldr (fun j acc => do
    let cs ← acc
    let (Z, W) ← meets P (min i j) (max i j)
    let f := if colour then form P.nv [(Z, -1), (W, -3)] else form P.nv [(Z, -3), (W, -1)]
    some ((Label.cross i j, f) :: cs)) (some [])
  let all := pos ++ crosses
  let labels := all.map (·.1)
  let forced := ((List.range all.length).filter fun t =>
    match labels[t]! with
    | .pos k => if colour then D.zc[k]! else D.wc[k]!
    | .cross k l => if colour then D.zstroke k l else D.wstroke k l
    | _ => false)
  some { name := .S colour i, labels, terms := all.map (·.2), forced := if forced.isEmpty then none else some forced }

/-- `U = E`: the term `E` (exponent `0`) and `m_k m_l p_kl` (exponent `−x_kl`); forced on the `zw`-edges. -/
def identU (D : Diag) (P : Pair) : Option SIdent := do
  let ds ← pairs6.toList.foldr (fun kl acc => do
    let cs ← acc
    let (Z, W) ← meets P kl.1 kl.2
    some ((Label.delta kl.1 kl.2, form P.nv [(Z, -1), (W, -1)]) :: cs)) (some [])
  let all := (Label.E, Array.replicate P.nv 0) :: ds
  let forced := (List.range 15).filter (fun pi => let kl := pairs6[pi]!; D.zstroke kl.1 kl.2 && D.wstroke kl.1 kl.2)
    |>.map (· + 1)
  some { name := .U, labels := all.map (·.1), terms := all.map (·.2),
         forced := if forced.isEmpty then none else some forced }

/-- `I = ME`: the term `E` and `m_k m_l z_kl w_kl` (exponent `2 x_kl`). -/
def identI (P : Pair) : Option SIdent := do
  let ds ← pairs6.toList.foldr (fun kl acc => do
    let cs ← acc
    let (Z, W) ← meets P kl.1 kl.2
    some ((Label.zw kl.1 kl.2, form P.nv [(Z, 2), (W, 2)]) :: cs)) (some [])
  let all := (Label.E, Array.replicate P.nv 0) :: ds
  some { name := .I, labels := all.map (·.1), terms := all.map (·.2), forced := none }

/-- The fourteen base identities in the engine's order: `z`-equations of the bodies `0 … 5`, `w`-equations, `U`, `I`. -/
def idents (D : Diag) (P : Pair) : Option (List SIdent) := do
  let zs ← (List.range 6).mapM (bodyIdent D P true)
  let ws ← (List.range 6).mapM (bodyIdent D P false)
  let u ← identU D P
  let i ← identI P
  some (zs ++ ws ++ [u, i])

/-- `forced_rows`: the forced terms equal the first of them, the other terms are strictly larger. -/
def forcedRows (terms : List (Array Int)) (forced : List Nat) : List Row :=
  match forced with
  | [] => []
  | f0 :: _ =>
    ((List.range terms.length).filter (· != f0)).map fun t =>
      let d := fsub terms[t]! terms[f0]!
      if forced.contains t then rowEq d else rowGt d

end L6.F2S
