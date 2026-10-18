import L6F34S.Check
import L6F34.Point
import L6F2.Check

/-!
# Sizes of the F3/F4 checks on the cells of the specification search (compiled code, untrusted)

For each class, as `checkChunkS` runs it: the cells, the open cells, the distinct pairs of trees (runs of lines with
the same pair, as `kindsRun`), the programs of `cellsBelowR keepLP` at those pairs and their rows, the entries
checked (cells of the search with the line's argmin part), and the linear programs of the claims with their rows
(single term: one per other term with a finite exponent; core: per name of the link, one per other term with a
finite exponent and one more per other term of the guessed argmin set).

Output, one line per class: `K cls cells C open O pairs P programs N rows R entries E single S lpS L rowsS RS
core K lpK M rowsK RK ms T`.
-/

namespace L6K.F34S

open L6 L6.F2S L6.F34S

initialize progRef : IO.Ref Nat ← IO.mkRef 0
initialize rowsRef : IO.Ref Nat ← IO.mkRef 0

/-- `keepLP`, counting the programs and their rows. -/
unsafe def keepCntImpl (rows : Array Row) (nv : Nat) : Bool :=
  -- depends on the program, so that the compiler does not evaluate it once for all calls
  let c := unsafeBaseIO (do progRef.modify (· + 1); rowsRef.modify (· + rows.size); return (← progRef.get))
  c != 0 && keepLP rows nv

@[implemented_by keepCntImpl] opaque keepCnt : Array Row → Nat → Bool

/-- The linear programs of `strictlyLeastS` for the term `i`: one per other term with a finite exponent. -/
def lpsSingle (fs : List (Option (Array Int))) (i : Nat) : Nat :=
  ((List.range fs.length).filter fun k => k != i && (fs.getD k none).isSome).length

/-- The linear programs of `constantArgminS` for the set `S`: one per other term with a finite exponent, two for
those in `S`. -/
def lpsConst (fs : List (Option (Array Int))) (S : List Nat) : Nat :=
  match S with
  | [] => 0
  | i0 :: _ =>
    ((List.range fs.length).filter fun k => k != i0 && (fs.getD k none).isSome).foldl
      (fun acc k => acc + if S.contains k then 2 else 1) 0

/-- The text of a file, or `""` if it does not exist (classes without cores have no link file). -/
def readOr (p : String) : IO String := do
  if ← System.FilePath.pathExists p then IO.FS.readFile p else pure ""

def runClass (dir : String) (openTxt : String) (c : Nat) : IO String := do
  let t0 ← IO.monoMsNow
  let cells ← readOr s!"{dir}/data/cells/c{c}.jsonl"
  let single ← readOr s!"{dir}/data/f34/single/c{c}.txt"
  let links ← readOr s!"{dir}/data/f4/links/c{c}.txt"
  let pass ← readOr s!"{dir}/data/f34/pass/c{c}.txt"
  let D := L6.F2.diagOf c
  match prepareS c D cells single links pass openTxt [] with
  | none => return s!"K {c} prepare-failed"
  | some cd =>
    progRef.set 0
    rowsRef.set 0
    let mut lastKey : Option ((List Nat × Option Nat) × (List Nat × Option Nat)) := none
    let mut lastEs : List (String × Array Row) := []
    let mut pairs := 0
    let mut nopen := 0
    let mut nent := 0
    let mut nsingle := 0
    let mut ncore := 0
    let mut lpS := 0
    let mut rowsS := 0
    let mut lpK := 0
    let mut rowsK := 0
    for idx in List.range cd.ncells do
      if cd.opens.contains idx then
        nopen := nopen + 1
      else
        let line := cd.cells.getD idx ""
        match pairKeyOf line, keyOfLine line with
        | some pk, some (_, _, am) =>
          if lastKey != some pk then
            lastEs := cellsBelowR keepCnt cd.D (pairOfKeys pk.1 pk.2)
            lastKey := some pk
            pairs := pairs + 1
          let P := pairOfKeys pk.1 pk.2
          let es := lastEs.filter (·.1 == am)
          nent := nent + es.length
          match cd.single.getD idx none, cd.links.getD idx none with
          | some (nm, lab), _ =>
            nsingle := nsingle + 1
            match XId.ofName nm with
            | some I =>
              let fs := I.terms.map (termForm P)
              match findLabX I.terms lab with
              | some i =>
                for e in es do
                  lpS := lpS + lpsSingle fs i
                  rowsS := rowsS + lpsSingle fs i * (e.2.size + 1)
              | none => pure ()
            | none => pure ()
          | none, some lk =>
            ncore := ncore + 1
            for e in es do
              match L6.F34.interiorPoint e.2 P.nv with
              | some pt =>
                for nmS in lk.names do
                  match L6.F34.IdName.parse nmS with
                  | some nm =>
                    match XId.ofName nm with
                    | some I =>
                      let fs := I.terms.map (termForm P)
                      let n := lpsConst fs (guessArgminS pt fs)
                      lpK := lpK + n
                      rowsK := rowsK + n * (e.2.size + 1)
                    | none => pure ()
                  | none => pure ()
              | none => pure ()
          | none, none => pure ()
        | _, _ => pure ()
    let t1 ← IO.monoMsNow
    return s!"K {c} cells {cd.ncells} open {nopen} pairs {pairs} programs {← progRef.get} rows {← rowsRef.get} entries {nent} single {nsingle} lpS {lpS} rowsS {rowsS} core {ncore} lpK {lpK} rowsK {rowsK} ms {t1 - t0}"

/-- `f34sstats DIR OUT CLASS…`: the sizes of the classes, with the data files of the lean6 tree `DIR`. -/
def main (args : List String) : IO Unit := do
  let dir := args[0]!
  let h ← IO.FS.Handle.mk args[1]! .write
  let openTxt ← IO.FS.readFile s!"{dir}/data/cells/open43.tsv"
  for c in (args.drop 2).map String.toNat! do
    h.putStrLn (← runClass dir openTxt c)
    h.flush

end L6K.F34S

def main (args : List String) : IO Unit := L6K.F34S.main args
