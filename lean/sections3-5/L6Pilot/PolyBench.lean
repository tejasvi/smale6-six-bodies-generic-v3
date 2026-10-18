import L6Poly.Basic
namespace L6.Pilot
def checkFiles (paths : List String) : IO Unit := do
  for p in paths do
    let s ← IO.FS.readFile p
    let t0 ← IO.monoMsNow
    let r := L6.Poly.checkCert s
    let t1 ← IO.monoMsNow
    IO.println s!"{p}: {r} ({s.length} bytes, {t1 - t0} ms)"
end L6.Pilot
