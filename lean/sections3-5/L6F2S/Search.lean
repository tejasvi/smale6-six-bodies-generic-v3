import L6Common.LP
import L6F2S.Rows

/-!
# The specification search

* `keepLP rows nv`: the decision on a linear program; `false` (discard) only when `Farkas.check` accepts the
  certificate proposed by the floating-point simplex (`LP.decide`), so that a discarded program has no solution of its
  strict form (Lemma 4.6).
* `treeLevel`: the insertion of the remaining bodies into both trees, each pair of partial trees tested by its rows
  (`partialRows`, which includes the relaxation of `ℓ(x) ≤ 0`).
* `argminRec`: the argmin sets of one identity, one term at a time (IN before OUT), each choice tested.
* `cellsBelow`: the cells below a complete pair of trees: the root rule, the rows of the pair, the forced argmin sets,
  then the argmin sets of the other base identities.
* `search D`: all cells of the representative `D`; `prefixPairs D d` and `below D d pr` split it at depth `d`.

All functions are total (structural recursion), so their completeness can be proved.
-/

namespace L6.F2S

open L6.F2 (Diag Label IdName renderEntry)

/-- The decision on a linear program: `false` only with a certificate accepted by `Farkas.check`. -/
def keepLP (rows : Array Row) (nv : Nat) : Bool :=
  let v := LP.decide rows nv
  !(!v.kept && Farkas.check nv rows v.cert)

/-- The argmin sets `S` (`|S| ≥ 2`) of an identity with terms `terms`, realizable together with `base`; each with its
rows. `fuel` is the number of terms still to decide (`= terms.length − j`). -/
def argminRec (keep : Array Row → Bool) (base : Array Row) (terms : List (Array Int)) :
    Nat → Nat → Option Nat → List Nat → List Nat → Array Row → List (List Nat × Array Row)
  | 0, _, first, ins, _, rows => if first.isSome && 2 ≤ ins.length then [(ins, rows)] else []
  | fuel + 1, j, first, ins, outs, rows =>
    let N := terms.length
    let tj := terms[j]!
    let inB : List (List Nat × Array Row) :=
      match first with
      | none =>
        let nrows := rows ++ (outs.map fun o => rowGt (fsub terms[o]! tj)).toArray
        if keep (base ++ nrows) then argminRec keep base terms fuel (j + 1) (some j) (ins ++ [j]) outs nrows else []
      | some f =>
        let nrows := rows.push (rowEq (fsub tj terms[f]!))
        if keep (base ++ nrows) then argminRec keep base terms fuel (j + 1) (some f) (ins ++ [j]) outs nrows else []
    let outB : List (List Nat × Array Row) :=
      match first with
      | none => if 2 ≤ N - j - 1 then argminRec keep base terms fuel (j + 1) none ins (outs ++ [j]) rows else []
      | some f =>
        let nrows := rows.push (rowGt (fsub tj terms[f]!))
        if 2 ≤ ins.length || 2 - ins.length ≤ N - j - 1 then
          (if keep (base ++ nrows) then argminRec keep base terms fuel (j + 1) (some f) ins (outs ++ [j]) nrows
           else [])
        else []
    inB ++ outB

/-- The argmin sets of the identities `branch`, one after the other (recursion of `cells_below`). -/
def branchRec (keep : Array Row → Bool) (L0 : Array Row) :
    List SIdent → Array Row → List String → List (List String)
  | [], _, chosen => [chosen]
  | id :: rest, extra, chosen =>
    (argminRec keep (L0 ++ extra) id.terms id.terms.length 0 none [] [] #[]).flatMap fun Sr =>
      branchRec keep L0 rest (extra ++ Sr.2)
        (chosen ++ [renderEntry id.name (Sr.1.map fun t => id.labels.getD t .E).toArray])

/-- The number of children of a node `C` of a tree on `S`: its maximal proper sub-nodes and its leaf classes not
below any proper sub-node. -/
def numChildren (T : TS) (S C : Nat) : Nat :=
  let subs := T.nodes.filter fun D => ssubset D C
  let maxl := subs.filter fun D => !(subs.any fun E => ssubset D E)
  let lc := (T.classes S).filter fun L => subset L C && !(subs.any fun D => subset L D)
  maxl.length + lc.length

/-- The root rule (Lemma 4.3 (b)): the root `S` has at least three children. -/
def comOk (T : TS) (S : Nat) : Bool := T.nodes.contains S && 3 ≤ numChildren T S S

/-- The forced and the other identities: the rows and the entries of the forced ones (`none` if a forced set has
fewer than two terms). -/
def splitForced (ids : List SIdent) : Option (Array Row × List String × List SIdent) :=
  ids.foldl (fun acc id =>
    match acc with
    | none => none
    | some (rows, fixed, branch) =>
      match id.forced with
      | some f =>
        if f.length < 2 then none
        else some (rows ++ (forcedRows id.terms f).toArray,
                   fixed ++ [renderEntry id.name (f.map fun t => id.labels.getD t .E).toArray], branch)
      | none => some (rows, fixed, branch ++ [id])) (some (#[], [], []))

/-- The set of all seven points. -/
def all : Nat := 127

/-- The cells below a complete pair of trees, as the argmin part of the stored line (the entries joined). -/
def cellsBelow (keep : Array Row → Nat → Bool) (D : Diag) (P : Pair) : List String :=
  if !(comOk P.tz all && comOk P.tw all) then [] else
  match partialRows D P all, idents D P with
  | some L0, some ids =>
    if !keep L0 P.nv then [] else
    match splitForced ids with
    | none => []
    | some (extra, fixed, branch) =>
      if !keep (L0 ++ extra) P.nv then [] else
      (branchRec (fun r => keep r P.nv) L0 branch extra []).map fun chosen => ", ".intercalate (fixed ++ chosen)
  | _, _ => []

/-- The insertion of the bodies `rest` into both trees on the set `S`. -/
def treeLevel (keep : Array Row → Nat → Bool) (D : Diag) : List Nat → Nat → TS → TS → List (Nat × TS × TS)
  | [], S, tz, tw => [(S, tz, tw)]
  | p :: rest, S, tz, tw =>
    let S' := ins p S
    (tz.options S p).flatMap fun tz' => (tw.options S p).flatMap fun tw' =>
      match partialRows D ⟨tz', tw'⟩ S' with
      | none => []
      | some L => if keep L (Pair.nv ⟨tz', tw'⟩) then treeLevel keep D rest S' tz' tw' else []

/-- The insertion order of the bodies of a representative. -/
def order (D : Diag) : List Nat := (L6.F2.orderBodies D).toList

/-- A cell of the specification: the two trees and the argmin part of the line. -/
structure SCell where
  tz : TS
  tw : TS
  argmin : String

/-- The key of a cell: the trees as sorted node sets with the body on the leaf of `O`, and the argmin part. -/
def SCell.key (c : SCell) : (List Nat × Option Nat) × (List Nat × Option Nat) × String :=
  (c.tz.key, c.tw.key, c.argmin)

/-- The cells below one complete pair. -/
def cellsOf (keep : Array Row → Nat → Bool) (D : Diag) (x : Nat × TS × TS) : List SCell :=
  (cellsBelow keep D ⟨x.2.1, x.2.2⟩).map fun a => ⟨x.2.1, x.2.2, a⟩

/-- The pairs of trees after the first `d` insertions. -/
def prefixPairs (keep : Array Row → Nat → Bool) (D : Diag) (d : Nat) : List (Nat × TS × TS) :=
  treeLevel keep D ((order D).take d) (single O) TS.init TS.init

/-- The cells below a pair of partial trees after the first `d` insertions. -/
def below (keep : Array Row → Nat → Bool) (D : Diag) (d : Nat) (x : Nat × TS × TS) : List SCell :=
  (treeLevel keep D ((order D).drop d) x.1 x.2.1 x.2.2).flatMap (cellsOf keep D)

/-- All cells of the representative `D`. -/
def search (keep : Array Row → Nat → Bool) (D : Diag) : List SCell :=
  (treeLevel keep D (order D) (single O) TS.init TS.init).flatMap (cellsOf keep D)

end L6.F2S
