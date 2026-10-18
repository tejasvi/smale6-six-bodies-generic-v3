import L6Pilot.F2SPrefix
open L6.F2S
#eval do
  let mut out := ""
  for k in [0:191] do
    let d := if k == 3 || k == 128 || k == 148 then 4 else 3
    out := out ++ s!"{k} {d} {(prefixPairs keepLP (L6.F2.diagOf k) d).length}\n"
  IO.FS.writeFile "../pilot/prefix_counts_d.txt" out
  IO.println "written"
