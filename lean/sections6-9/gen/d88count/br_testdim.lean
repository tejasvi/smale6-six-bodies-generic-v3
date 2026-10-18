import Lean6.Special.Comp.D88.Count.DimCheck

/-!
Native test of `dimCheck` on a basis read from a file (test only, not part of the proof; the results are in
`logs/d88count/br_native_test.log`). The file, named by the environment variable `BRTEST_FILE`, is the output of
`gen/d88count/br_msolve2lst.py`; `BRTEST_N` is the bound. To run the checker as compiled code, copy this file to
`Lean6/Special/Comp/D88/Count/BrTestDim.lean` (a module of the precompiled checker library) and build it with
`lake build Lean6.Special.Comp.D88.Count.BrTestDim -v`.
-/

namespace Lean6.Special.Comp.Count

open Lean6.Special.Comp

def parseTerm (s : String) : Option (Nat × Mono) :=
  match s.splitOn ":" with
  | [c, es] => do
    let c ← c.toNat?
    let es ← (es.splitOn ",").mapM String.toNat?
    pure (c, es)
  | _ => none

def parsePoly (line : String) : Option (Poly Nat) :=
  ((line.splitOn " ").filter (· ≠ "")).mapM parseTerm

#eval show IO Unit from do
  match ← IO.getEnv "BRTEST_FILE" with
  | none => IO.println "BRTEST_FILE not set"
  | some path =>
    let txt ← IO.FS.readFile path
    let lines := (txt.splitOn "\n").filter (· ≠ "")
    match lines.mapM parsePoly with
    | none => IO.println "parse error"
    | some B =>
      let N := (← IO.getEnv "BRTEST_N").bind String.toNat? |>.getD 0
      IO.println s!"polys {B.length} terms {(B.map List.length).sum}"
      IO.println s!"polyOK all: {B.all (polyOK 65521 11)}"
      let L := (B.map leadOf).toArray
      let r := staircase 11 L N (N + 2)
      IO.println s!"staircase size {r.1.length}"
      IO.println s!"dimCheck N={N}: {dimCheck 65521 11 B N}"
      IO.println s!"dimCheck N-1={N - 1}: {dimCheck 65521 11 B (N - 1)}"
      IO.println s!"dimCheck without the last polynomial: {dimCheck 65521 11 B.dropLast N}"

end Lean6.Special.Comp.Count
