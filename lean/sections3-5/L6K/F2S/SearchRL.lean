import L6F2S.SearchL

/-!
# The specification search with the rows of each cell

`branchRecL`, `cellsBelowL` and `belowL` of lean6's `L6F2S.SearchL`, keeping the rows of each cell (the rows of the
pair, the forced argmin sets and the argmin choices, in the order in which the search builds them), as
`L6F34S.cellsBelowR` does for the search on arrays. The claims of Proposition 5.3 are checked on these rows.
-/

namespace L6K.F2S

open L6 L6.F2S

open L6.F2 (Diag)

/-- `branchRecL`, keeping the rows of each choice. -/
def branchRecRL (keep : List Row → Bool) (L0 : List Row) :
    List SIdent → List Row → List (Nat × List Nat) → List (List (Nat × List Nat) × List Row)
  | [], extra, chosen => [(chosen, extra)]
  | id :: rest, extra, chosen =>
    (argminRecL keep (L0 ++ extra) id.terms id.terms.length 0 none [] [] []).flatMap fun Sr =>
      branchRecRL keep L0 rest (extra ++ Sr.2) (chosen ++ [(idCode id.name, Sr.1)])

/-- `cellsBelowL`, keeping the rows of each cell. -/
def cellsBelowRL (keep : List Row → Nat → Bool) (D : Diag) (P : Pair) : List (List (Nat × List Nat) × List Row) :=
  if !(comOk P.tz all && comOk P.tw all) then [] else
  match partialRowsL D P all, idents D P with
  | some L0, some ids =>
    if !keep L0 P.nv then [] else
    match splitForcedL ids with
    | none => []
    | some (extra, fixed, branch) =>
      if !keep (L0 ++ extra) P.nv then [] else
      (branchRecRL (fun r => keep r P.nv) L0 branch extra []).map fun cr => (fixed ++ cr.1, L0 ++ cr.2)
  | _, _ => []

/-- A cell of the search with its rows. -/
structure RCell where
  tz : TS
  tw : TS
  argmin : List (Nat × List Nat)
  rows : List Row

/-- The cells below one complete pair, with their rows. -/
def cellsOfRL (keep : List Row → Nat → Bool) (D : Diag) (x : Nat × TS × TS) : List RCell :=
  (cellsBelowRL keep D ⟨x.2.1, x.2.2⟩).map fun a => ⟨x.2.1, x.2.2, a.1, a.2⟩

/-- `belowL` with the rows of each cell. -/
def belowRL (keep : List Row → Nat → Bool) (D : Diag) (ord : List Nat) (d : Nat) (x : Nat × TS × TS) :
    List RCell :=
  (treeLevelL keep D (ord.drop d) x.1 x.2.1 x.2.2).flatMap (cellsOfRL keep D)

end L6K.F2S
