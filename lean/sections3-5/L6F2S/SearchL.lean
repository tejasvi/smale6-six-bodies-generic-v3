import L6F2S.Search

/-!
# The specification search with lists of rows, structured argmin sets and a given insertion order

A variant of the specification search (`L6F2S.Search`) for evaluation in the kernel: the rows of the linear programs
are lists (`List Row`), the argmin part of a cell is structured (for each base identity, the code of its name and the
positions of its terms of least exponent, `List (Nat × List Nat)`) instead of rendered as a string, and the insertion
order of the bodies is a parameter. The functions follow those of `L6F2S.Search` line by line; their completeness is
proved in `L6Sound.F2S.SearchL` (`searchL_complete`), and `argminString` is the rendering of the structured argmin
sets (`argminString_eq_renderIdx`).
-/

namespace L6.F2S

open L6.F2 (Diag Label IdName)

/-- The code of the name of a base identity: its position in the order of `idents` (the equations of the bodies in
`z`, then in `w`, then `U = E`, then `I = ME`). -/
def idCode : IdName → Nat
  | .S true i => i
  | .S false i => 6 + i
  | .U => 12
  | .I => 13

/-- `partialRows` as a list. -/
def partialRowsL (D : Diag) (P : Pair) (S : Nat) : Option (List Row) := do
  let pr ← pairRows D P S
  let qr ← posRows D P S
  let th ← thresholdRow D P S
  some (treeRows P.tz 0 P.nv ++ treeRows P.tw P.nz P.nv ++ pr ++ qr ++ [th])

/-- `argminRec` with lists of rows. -/
def argminRecL (keep : List Row → Bool) (base : List Row) (terms : List (Array Int)) :
    Nat → Nat → Option Nat → List Nat → List Nat → List Row → List (List Nat × List Row)
  | 0, _, first, ins, _, rows => if first.isSome && 2 ≤ ins.length then [(ins, rows)] else []
  | fuel + 1, j, first, ins, outs, rows =>
    let N := terms.length
    let tj := terms[j]!
    let inB : List (List Nat × List Row) :=
      match first with
      | none =>
        let nrows := rows ++ outs.map fun o => rowGt (fsub terms[o]! tj)
        if keep (base ++ nrows) then argminRecL keep base terms fuel (j + 1) (some j) (ins ++ [j]) outs nrows else []
      | some f =>
        let nrows := rows ++ [rowEq (fsub tj terms[f]!)]
        if keep (base ++ nrows) then argminRecL keep base terms fuel (j + 1) (some f) (ins ++ [j]) outs nrows
        else []
    let outB : List (List Nat × List Row) :=
      match first with
      | none => if 2 ≤ N - j - 1 then argminRecL keep base terms fuel (j + 1) none ins (outs ++ [j]) rows else []
      | some f =>
        let nrows := rows ++ [rowGt (fsub tj terms[f]!)]
        if 2 ≤ ins.length || 2 - ins.length ≤ N - j - 1 then
          (if keep (base ++ nrows) then argminRecL keep base terms fuel (j + 1) (some f) ins (outs ++ [j]) nrows
           else [])
        else []
    inB ++ outB

/-- `branchRec` with lists of rows and structured entries (code of the identity, positions of the argmin set). -/
def branchRecL (keep : List Row → Bool) (L0 : List Row) :
    List SIdent → List Row → List (Nat × List Nat) → List (List (Nat × List Nat))
  | [], _, chosen => [chosen]
  | id :: rest, extra, chosen =>
    (argminRecL keep (L0 ++ extra) id.terms id.terms.length 0 none [] [] []).flatMap fun Sr =>
      branchRecL keep L0 rest (extra ++ Sr.2) (chosen ++ [(idCode id.name, Sr.1)])

/-- `splitForced` with lists of rows and structured entries. -/
def splitForcedL (ids : List SIdent) : Option (List Row × List (Nat × List Nat) × List SIdent) :=
  ids.foldl (fun acc id =>
    match acc with
    | none => none
    | some (rows, fixed, branch) =>
      match id.forced with
      | some f =>
        if f.length < 2 then none
        else some (rows ++ forcedRows id.terms f, fixed ++ [(idCode id.name, f)], branch)
      | none => some (rows, fixed, branch ++ [id])) (some ([], [], []))

/-- `cellsBelow` with lists of rows: the structured argmin parts of the cells below a complete pair of trees. -/
def cellsBelowL (keep : List Row → Nat → Bool) (D : Diag) (P : Pair) : List (List (Nat × List Nat)) :=
  if !(comOk P.tz all && comOk P.tw all) then [] else
  match partialRowsL D P all, idents D P with
  | some L0, some ids =>
    if !keep L0 P.nv then [] else
    match splitForcedL ids with
    | none => []
    | some (extra, fixed, branch) =>
      if !keep (L0 ++ extra) P.nv then [] else
      (branchRecL (fun r => keep r P.nv) L0 branch extra []).map fun chosen => fixed ++ chosen
  | _, _ => []

/-- `treeLevel` with lists of rows. -/
def treeLevelL (keep : List Row → Nat → Bool) (D : Diag) : List Nat → Nat → TS → TS → List (Nat × TS × TS)
  | [], S, tz, tw => [(S, tz, tw)]
  | p :: rest, S, tz, tw =>
    let S' := ins p S
    (tz.options S p).flatMap fun tz' => (tw.options S p).flatMap fun tw' =>
      match partialRowsL D ⟨tz', tw'⟩ S' with
      | none => []
      | some L => if keep L (Pair.nv ⟨tz', tw'⟩) then treeLevelL keep D rest S' tz' tw' else []

/-- A cell of the search with its structured argmin part. -/
structure SCellL where
  tz : TS
  tw : TS
  argmin : List (Nat × List Nat)
  deriving DecidableEq, Repr

/-- The key of a cell: the trees as sorted node sets with the body on the leaf of `O`, and the structured argmin
part. -/
def SCellL.key (c : SCellL) : (List Nat × Option Nat) × (List Nat × Option Nat) × List (Nat × List Nat) :=
  (c.tz.key, c.tw.key, c.argmin)

/-- The cells below one complete pair. -/
def cellsOfL (keep : List Row → Nat → Bool) (D : Diag) (x : Nat × TS × TS) : List SCellL :=
  (cellsBelowL keep D ⟨x.2.1, x.2.2⟩).map fun a => ⟨x.2.1, x.2.2, a⟩

/-- The pairs of trees after the first `d` insertions of the insertion order `ord`. -/
def prefixPairsL (keep : List Row → Nat → Bool) (D : Diag) (ord : List Nat) (d : Nat) : List (Nat × TS × TS) :=
  treeLevelL keep D (ord.take d) (single O) TS.init TS.init

/-- The cells below a pair of partial trees after the first `d` insertions of `ord`. -/
def belowL (keep : List Row → Nat → Bool) (D : Diag) (ord : List Nat) (d : Nat) (x : Nat × TS × TS) :
    List SCellL :=
  (treeLevelL keep D (ord.drop d) x.1 x.2.1 x.2.2).flatMap (cellsOfL keep D)

/-- All cells of the representative `D`, inserting the bodies in the order `ord`. -/
def searchL (keep : List Row → Nat → Bool) (D : Diag) (ord : List Nat) : List SCellL :=
  (treeLevelL keep D ord (single O) TS.init TS.init).flatMap (cellsOfL keep D)

/-- The rendering of a structured argmin part with the names and labels `md` of the base identities (indexed by the
codes): the argmin part of a stored line. -/
def renderIdx (md : List (IdName × List Label × Option (List Nat))) (es : List (Nat × List Nat)) : String :=
  ", ".intercalate (es.map fun e =>
    L6.F2.renderEntry (md.getD e.1 default).1 (e.2.map fun t => (md.getD e.1 default).2.1.getD t .E).toArray)

end L6.F2S
