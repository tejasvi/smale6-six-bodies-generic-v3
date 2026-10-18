import L6K.F1.Shard
import L6F1

/-!
# Generator of the representative data of F1 (compiled code, untrusted)

One line per class of `n6.json`, in order: `e zc wc size code …` with the codes `orbitCodesK` of its orbit.
-/

open L6F1 L6K.F1

def main (args : List String) : IO Unit := do
  let out := args.headD "f1reps.txt"
  let cls : List (Diagram × Nat) := match parseFile n6json with
    | some (_, _, c) => c
    | none => []
  let h ← IO.FS.Handle.mk (System.FilePath.mk out) .write
  let mut tot := 0
  for x in cls do
    let oc := orbitCodesK x.1
    tot := tot + oc.length
    h.putStrLn (" ".intercalate ((x.1.e :: x.1.zc :: x.1.wc :: x.2 :: oc).map toString))
  IO.println s!"classes {cls.length}, orbit codes {tot}, checkClassK {(cls.filter checkClassK).length}"
