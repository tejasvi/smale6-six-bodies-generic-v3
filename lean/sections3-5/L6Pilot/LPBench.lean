import L6Common.LP

/-! Pilot: the LP proposer and the exact certificate check on LPs dumped from the engine's search. -/

namespace L6.Pilot

/-- Integer tokens of a line (`x` = absent). -/
def parseTok (t : String) : Option Int := if t == "x" then none else t.toInt?

/-- Parse the dump format of `scripts/pilot/dump_lps.py`. -/
def parseLPs (s : String) : Array (Nat × Array Row × Bool) := Id.run do
  let lines := (s.splitOn "\n").toArray
  let mut out := #[]
  let mut i := 0
  while i < lines.size do
    let ws := (lines[i]!.splitOn " ").filter (· ≠ "")
    if ws.length == 4 && ws[0]! == "LP" then
      let n := ws[1]!.toNat!
      let m := ws[2]!.toNat!
      let kept := ws[3]! == "1"
      let mut rows : Array Row := #[]
      for k in [0:m] do
        let ts := ((lines[i + 1 + k]!.splitOn " ").filter (· ≠ "")).toArray
        let c := ts[0]!.toInt!
        let lo := parseTok ts[1]!
        let hi := parseTok ts[2]!
        let a := (ts.extract 3 (3 + n)).map String.toInt!
        rows := rows.push { a, c, lo, hi }
      out := out.push (n, rows, kept)
      i := i + 1 + m
    else
      i := i + 1
  return out

structure Stats where
  total : Nat := 0
  agree : Nat := 0
  keptBoth : Nat := 0
  prunedBoth : Nat := 0
  leanKeptPyPruned : Nat := 0
  leanPrunedPyKept : Nat := 0
  failures : Nat := 0
  deriving Repr

def bench (lps : Array (Nat × Array Row × Bool)) : Stats := Id.run do
  let mut st : Stats := {}
  for (n, rows, kept) in lps do
    let v := LP.decide rows n
    st := { st with total := st.total + 1 }
    if v.failure then st := { st with failures := st.failures + 1 }
    if v.kept == kept then
      st := { st with agree := st.agree + 1 }
      if kept then st := { st with keptBoth := st.keptBoth + 1 } else st := { st with prunedBoth := st.prunedBoth + 1 }
    else if v.kept then st := { st with leanKeptPyPruned := st.leanKeptPyPruned + 1 }
    else st := { st with leanPrunedPyKept := st.leanPrunedPyKept + 1 }
  return st

/-- Read a dump file and run the bench; prints statistics and the time. -/
def runFile (path : String) : IO Unit := do
  let s ← IO.FS.readFile path
  let t0 ← IO.monoMsNow
  let lps := parseLPs s
  let t1 ← IO.monoMsNow
  let st := bench lps
  IO.println s!"{path}: parsed {lps.size} LPs in {t1 - t0} ms"
  let t2 ← IO.monoMsNow
  IO.println s!"{repr st}"
  IO.println s!"decide time {t2 - t1} ms"

end L6.Pilot
