import L6F2S.Search
import L6F2.Check
import L6K.F2S.Keep

/-!
# Exporter of the certificate data of the specification search (compiled code, untrusted)

Runs the specification search of a class (`L6F2S`) natively with the decisions of `keepLP`, recording for every
discarded program the hash of its rows and its certificate. The search is split at depth `d` (`prefixPairs`,
`below`): one table for the prefix stage and one per pair of partial trees after `d` insertions.

Output (text, one item per line): `O ord…` the insertion order; `D d npairs`; for the prefix stage and then for each
pair `x` (`X S tz-nodes / tz-leafO / tw-nodes / tw-leafO` with `-` for none), the number of cells of `below` and the
certificates `C hash i:y …` sorted by hash.
-/

namespace L6K.F2S

open L6 L6.F2S

initialize logRef : IO.Ref (Array (Nat × List (Nat × Int))) ← IO.mkRef #[]
initialize countRef : IO.Ref Nat ← IO.mkRef 0

/-- `keepLP`, counting the programs and recording the certificate of every discarded one. -/
unsafe def keepRecImpl (rows : Array Row) (nv : Nat) : Bool :=
  let v := LP.decide rows nv
  -- depends on the program, so that the compiler does not evaluate it once for all calls
  let c := unsafeBaseIO (do countRef.modify (· + (if rows.size == 0 then 2 else 1)); return (← countRef.get))
  if c != 0 && !v.kept && Farkas.check nv rows v.cert then
    let n := unsafeBaseIO (do logRef.modify (·.push (rowsHash rows, v.cert)); return (← logRef.get).size)
    n == 0
  else true

@[implemented_by keepRecImpl] opaque keepRec : Array Row → Nat → Bool

def tsLine (t : TS) : String :=
  " ".intercalate (t.nodes.map toString) ++ " / " ++ (match t.leafO with | some k => toString k | none => "-")

/-- The certificates by hash (several programs may share a hash), sorted by hash; one line per certificate. -/
def certLines (log : Array (Nat × List (Nat × Int))) : List String :=
  let sorted := log.toList.mergeSort fun a b => a.1 ≤ b.1
  sorted.map fun (h, c) => "C " ++ toString h ++ " " ++ " ".intercalate (c.map fun (i, y) => s!"{i}:{y}")

/-- `stats C D OUT STEP`: the number of pairs after `D` insertions and, for every `STEP`-th pair, its numbers of
programs, certificates and cells. -/
def stats (args : List String) : IO Unit := do
  let c := args[0]!.toNat!
  let d := args[1]!.toNat!
  let out := args[2]!
  let step := args[3]!.toNat!
  let D := L6.F2.diagOf c
  let ord := order D
  let h ← IO.FS.Handle.mk out .write
  countRef.set 0
  logRef.set #[]
  let pre := treeLevel keepRec D (ord.take d) (single O) TS.init TS.init
  if pre.length == 0 then h.putStrLn "P 0" else h.putStrLn s!"P {pre.length} programs {← countRef.get} certs {(← logRef.get).size}"
  h.flush
  let mut i := 0
  for x in pre do
    if i % step == 0 then
      countRef.set 0
      logRef.set #[]
      let n := ((treeLevel keepRec D (ord.drop d) x.1 x.2.1 x.2.2).flatMap (cellsOf keepRec D)).length
      h.putStrLn s!"S {i} programs {← countRef.get} certs {(← logRef.get).size} cells {n}"
      h.flush
    i := i + 1

def main (args : List String) : IO Unit := do
  if args.head? == some "stats" then stats args.tail else
  let c := args[0]!.toNat!
  let d := args[1]!.toNat!
  let out := args[2]!
  let D := L6.F2.diagOf c
  let ord := order D
  let h ← IO.FS.Handle.mk out .write
  h.putStrLn ("O " ++ " ".intercalate (ord.map toString))
  logRef.set #[]
  let pre := treeLevel keepRec D (ord.take d) (single O) TS.init TS.init
  if pre.length == 0 then h.putStrLn "D 0 0" else h.putStrLn s!"D {d} {pre.length}"
  for l in certLines (← logRef.get) do h.putStrLn l
  for x in pre do
    logRef.set #[]
    countRef.set 0
    let n := ((treeLevel keepRec D (ord.drop d) x.1 x.2.1 x.2.2).flatMap (cellsOf keepRec D)).length
    h.putStrLn s!"X {x.1} {tsLine x.2.1} / {tsLine x.2.2} N {n} P {← countRef.get}"
    for l in certLines (← logRef.get) do h.putStrLn l
  h.flush

end L6K.F2S

def main (args : List String) : IO Unit := L6K.F2S.main args
