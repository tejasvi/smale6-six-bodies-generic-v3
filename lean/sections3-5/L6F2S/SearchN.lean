import L6F2S.SearchL

/-!
# The specification search with the rows of each cell, newest first

A variant of `L6F2S.SearchL` for a decision `keep` that reads the rows of a linear program newest first: in the
argmin recursion the state is the whole list of rows of the cell so far, base rows included, with each new row put in
front, and `keep` is applied to that list itself. The cells carry their rows (`SCellN.rows`, newest first), so that
the claim of a cell can be checked on them. The tree level is that of `SearchL` (`treeLevelL`). The completeness of
the search, with the rows of the cell holding strictly at the heights of every pair satisfying `Cond`, is
`searchN_complete` (`L6Sound.F2S.SearchN`).
-/

namespace L6.F2S

open L6.F2 (Diag Label IdName)

/-- `argminRec` with the rows of the cell newest first: `state` is the whole list of rows so far (base rows
included), and `keep` is applied to it. -/
def argminRecN (keep : List Row → Bool) (terms : List (Array Int)) :
    Nat → Nat → Option Nat → List Nat → List Nat → List Row → List (List Nat × List Row)
  | 0, _, first, ins, _, state => if first.isSome && 2 ≤ ins.length then [(ins, state)] else []
  | fuel + 1, j, first, ins, outs, state =>
    let N := terms.length
    let tj := terms[j]!
    let inB : List (List Nat × List Row) :=
      match first with
      | none =>
        let nstate := (outs.map fun o => rowGt (fsub terms[o]! tj)).reverse ++ state
        if keep nstate then argminRecN keep terms fuel (j + 1) (some j) (ins ++ [j]) outs nstate else []
      | some f =>
        let nstate := rowEq (fsub tj terms[f]!) :: state
        if keep nstate then argminRecN keep terms fuel (j + 1) (some f) (ins ++ [j]) outs nstate else []
    let outB : List (List Nat × List Row) :=
      match first with
      | none => if 2 ≤ N - j - 1 then argminRecN keep terms fuel (j + 1) none ins (outs ++ [j]) state else []
      | some f =>
        let nstate := rowGt (fsub tj terms[f]!) :: state
        if 2 ≤ ins.length || 2 - ins.length ≤ N - j - 1 then
          (if keep nstate then argminRecN keep terms fuel (j + 1) (some f) ins (outs ++ [j]) nstate else [])
        else []
    inB ++ outB

/-- The argmin sets of the identities `branch`, one after the other, carrying the rows of the cell newest first;
each result with the final rows. -/
def branchRecN (keep : List Row → Bool) :
    List SIdent → List Row → List (Nat × List Nat) → List (List (Nat × List Nat) × List Row)
  | [], state, chosen => [(chosen, state)]
  | id :: rest, state, chosen =>
    (argminRecN keep id.terms id.terms.length 0 none [] [] state).flatMap fun Sr =>
      branchRecN keep rest Sr.2 (chosen ++ [(idCode id.name, Sr.1)])

/-- The cells below a complete pair of trees: the structured argmin part and the rows of each cell, newest first. -/
def cellsBelowN (keep : List Row → Nat → Bool) (D : Diag) (P : Pair) : List (List (Nat × List Nat) × List Row) :=
  if !(comOk P.tz all && comOk P.tw all) then [] else
  match partialRowsL D P all, idents D P with
  | some L0, some ids =>
    if !keep L0.reverse P.nv then [] else
    match splitForcedL ids with
    | none => []
    | some (extra, fixed, branch) =>
      if !keep (L0 ++ extra).reverse P.nv then [] else
      (branchRecN (fun r => keep r P.nv) branch (L0 ++ extra).reverse []).map fun cr => (fixed ++ cr.1, cr.2)
  | _, _ => []

/-- A cell of the search with its structured argmin part and its rows (newest first). -/
structure SCellN where
  tz : TS
  tw : TS
  argmin : List (Nat × List Nat)
  rows : List Row

/-- The key of a cell. -/
def SCellN.key (c : SCellN) : (List Nat × Option Nat) × (List Nat × Option Nat) × List (Nat × List Nat) :=
  (c.tz.key, c.tw.key, c.argmin)

/-- The pair of trees of a cell. -/
def SCellN.pair (c : SCellN) : Pair := ⟨c.tz, c.tw⟩

/-- The cells below one complete pair. -/
def cellsOfN (keep : List Row → Nat → Bool) (D : Diag) (x : Nat × TS × TS) : List SCellN :=
  (cellsBelowN keep D ⟨x.2.1, x.2.2⟩).map fun ar => ⟨x.2.1, x.2.2, ar.1, ar.2⟩

/-- The cells below a pair of partial trees after the first `d` insertions of `ord` (the pairs after `d`
insertions are `prefixPairsL keep D ord d`). -/
def belowN (keep : List Row → Nat → Bool) (D : Diag) (ord : List Nat) (d : Nat) (x : Nat × TS × TS) :
    List SCellN :=
  (treeLevelL keep D (ord.drop d) x.1 x.2.1 x.2.2).flatMap (cellsOfN keep D)

/-- All cells of the representative `D`, with their rows, inserting the bodies in the order `ord`. -/
def searchN (keep : List Row → Nat → Bool) (D : Diag) (ord : List Nat) : List SCellN :=
  (treeLevelL keep D ord (single O) TS.init TS.init).flatMap (cellsOfN keep D)

end L6.F2S
