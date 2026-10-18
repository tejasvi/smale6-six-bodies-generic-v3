import L6K.F1.Shard
import L6F1

/-!
# Generator of the shard data of F1 (compiled code, untrusted)

For each prefix of `edgesUpTo 6 7`, in order: the prefix, the number of leaves of its shard, and the sorted codes of
the diagrams found at them, one line `prefix cnt code …` per shard (text, for the module generator). Also checks
`shardOK` on every shard and prints the totals.
-/

open L6F1 L6K.F1

def main (args : List String) : IO Unit := do
  let out := args.headD "f1shards.txt"
  let m := (args.getD 1 "7").toNat!
  let prefixes := edgesUpTo 6 m
  IO.println s!"prefixes {prefixes.length}"
  let h ← IO.FS.Handle.mk (System.FilePath.mk out) .write
  let mut totL := 0
  let mut totF := 0
  let mut bad := 0
  let mut maxL := 0
  for p in prefixes do
    let L := extendFrom m p
    let F := searchFrom 6 L
    let codes := msort 20 (F.map (dcode 6))
    totL := totL + L.length
    totF := totF + F.length
    maxL := max maxL L.length
    if !shardOK m p L.length codes then bad := bad + 1
    h.putStrLn (" ".intercalate ((p :: L.length :: codes).map toString))
  IO.println s!"leaves {totL}, found {totF}, largest shard {maxL}, failing shards {bad}"
