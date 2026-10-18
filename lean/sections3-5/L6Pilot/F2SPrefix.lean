import L6F2S.Stored
import L6F2.Check

/-! Pilot: the number of pairs of trees after three insertions, per class. -/

namespace L6.Pilot

open L6.F2S

def prefixCounts : IO Unit := do
  let mut out := ""
  for k in [0:191] do
    let D := L6.F2.diagOf k
    let n := (prefixPairs keepLP D 3).length
    out := out ++ s!"{k} {n}\n"
  IO.FS.writeFile "../pilot/prefix_counts.txt" out
  IO.println "done"

end L6.Pilot
