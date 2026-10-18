import Lean6.Special.Comp.D88.Boxes.Check
open Lean6.Special.D88.Boxes

/-! The classes of the sorted KC box strings, one line `t sm` (or `none`) per box, from lean6_special's `kcClass`: run
with `lean --run scripts/kc_classes.lean` from a directory holding `data/ksp/KC_sorted.txt` (written by `ksp_gen.py ... KC`),
with lean6_special on LEAN_PATH; it writes `data/ksp/KC_classes.txt`, which `kspc_gen.py` reads (untrusted: the kernel
checks the counts). -/

def main : IO Unit := do
  let ls ← IO.FS.lines "data/ksp/KC_sorted.txt"
  let h ← IO.FS.Handle.mk "data/ksp/KC_classes.txt" .write
  for s in ls do
    if s.isEmpty then continue
    match kcClass s with
    | some (t, sm) => h.putStrLn s!"{t} {sm}"
    | none => h.putStrLn "none"
