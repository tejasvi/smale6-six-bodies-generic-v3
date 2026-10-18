import L6K.F1.Check
import L6F1

/-!
# Generator of the F1 kernel data (compiled code, untrusted: the kernel checks everything it produces)

Writes, under the directory given as argument:
* `witnesses.bin`: the witness stream of the orderly search, 32-bit words;
* `leaves.bin`: the canonical edge codes (leaves), 32-bit words;
* `found.bin`: the labelled diagrams of `searchFrom 6 leaves`, 64-bit words `e + 2^30 zc + 2^36 wc`;
* `foundwit.bin`: per found diagram a symmetry and a class index mapping it to the representative,
  32-bit words `encodeWit p s + 2^20 index`;
* `classes.txt`: the classes of `n6.json` as a Lean term;
* `edgesizes.bin`: the orbit size of each leaf (32-bit words).
-/

open L6F1 L6K.F1

def packWords (w : Nat) (xs : List Nat) : ByteArray := Id.run do
  let mut b : ByteArray := ByteArray.empty
  for x in xs do
    for i in [0:w / 8] do
      b := b.push ((x >>> (8 * i)) % 256).toUInt8
  return b

def main (args : List String) : IO Unit := do
  let dir := args.headD "f1data"
  IO.FS.createDirAll dir
  let (leaves, ws) := generate
  IO.println s!"leaves {leaves.length}, witness entries {ws.length}, prunes {ws.countP (· != 0)}"
  IO.FS.writeBinFile (System.FilePath.mk dir / "witnesses.bin") (packWords 32 ws)
  IO.FS.writeBinFile (System.FilePath.mk dir / "leaves.bin") (packWords 32 leaves)
  let found := searchFrom 6 leaves
  IO.println s!"found diagrams {found.length}"
  IO.FS.writeBinFile (System.FilePath.mk dir / "found.bin")
    (packWords 64 (found.map fun d => d.e + 2 ^ 30 * d.zc + 2 ^ 36 * d.wc))
  let cls : List (Diagram × Nat) := match parseFile n6json with
    | some (_, _, c) => c
    | none => []
  IO.println s!"classes {cls.length}"
  -- for each found diagram: a symmetry and the index of the representative it maps to
  let reps := cls.map (·.1)
  let syms : List (List Nat × Bool) := (perms 6).flatMap fun p => [(p, false), (p, true)]
  let mut fw : List Nat := []
  let mut missing := 0
  for d in found do
    let r := syms.findSome? fun g =>
      let d' := act 6 g.1 g.2 d
      (reps.findIdx? (· == d')).map fun i => encodeWit g.1 g.2 + 2 ^ 20 * i
    match r with
    | some x => fw := x :: fw
    | none => missing := missing + 1; fw := 0 :: fw
  IO.println s!"found witnesses missing {missing}"
  IO.FS.writeBinFile (System.FilePath.mk dir / "foundwit.bin") (packWords 32 fw.reverse)
  let term := "[" ++ ", ".intercalate (cls.map fun x => s!"(⟨{x.1.e}, {x.1.zc}, {x.1.wc}⟩, {x.2})") ++ "]"
  IO.FS.writeFile (System.FilePath.mk dir / "classes.txt") term
  -- sizes of the orbits of the canonical edge codes (0 if a leaf were not the least code of its orbit)
  let sizes := leaves.map edgeOrbitSize
  IO.println s!"edge orbit sizes: sum {sizes.foldl (· + ·) 0}, zeros {sizes.countP (· == 0)}"
  IO.FS.writeBinFile (System.FilePath.mk dir / "edgesizes.bin") (packWords 32 sizes)
  IO.println s!"representatives: repOK {(cls.filter repOK).length} of {cls.length}, sizes sum {(cls.map (·.2)).foldl (· + ·) 0}"
