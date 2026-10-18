import L6F2S.SearchL
import L6F2.Check
import L6K.F2S.Keep

/-!
# Profile of the specification search on one shard (compiled code, untrusted)

For the shard of class 57 used in the kernel measurements (depth 3, pair 1): the number of programs of the tree
levels, the complete pairs reached, and for each complete pair the programs of `cellsBelowL` (with `keepLP`), its
cells and the number of rows of its partial rows; the first pairs are printed with their trees, for kernel tests.
-/

namespace L6K.F2S.Prof

open L6 L6.F2S

initialize cntRef : IO.Ref Nat ← IO.mkRef 0

/-- `keepLP`, counting the programs. -/
unsafe def keepCImpl (rows : List Row) (nv : Nat) : Bool :=
  -- depends on the program, so that the compiler does not evaluate it once for all calls
  let c := unsafeBaseIO (do cntRef.modify (· + (if rows.length == 0 then 2 else 1)); return (← cntRef.get))
  c != 0 && keepLP rows.toArray nv

@[implemented_by keepCImpl] opaque keepC : List Row → Nat → Bool

def tsStr (t : TS) : String := s!"⟨{t.nodes}, {t.leafO}⟩"

initialize logRef : IO.Ref (Array (Nat × List (Nat × Int))) ← IO.mkRef #[]

/-- `keepLP`, counting the programs and recording the certificate of every discarded one under its hash. -/
unsafe def keepRImpl (rows : List Row) (nv : Nat) : Bool :=
  let arr := rows.toArray
  let v := LP.decide arr nv
  let c := unsafeBaseIO (do cntRef.modify (· + (if rows.length == 0 then 2 else 1)); return (← cntRef.get))
  if c != 0 && !v.kept && Farkas.check nv arr v.cert then
    let n := unsafeBaseIO (do logRef.modify (·.push (L6K.F2S.rowsHash arr, v.cert)); return (← logRef.get).size)
    n == 0
  else true

@[implemented_by keepRImpl] opaque keepR : List Row → Nat → Bool

/-- The certificate lines `C hash i:y …`, sorted by hash, the entries of each certificate by row index. -/
def certLines (log : Array (Nat × List (Nat × Int))) : List String :=
  (log.toList.mergeSort fun a b => a.1 ≤ b.1).map fun (h, c) =>
    "C " ++ toString h ++ " " ++ " ".intercalate ((c.mergeSort fun a b => a.1 ≤ b.1).map fun (i, y) => s!"{i}:{y}")

/-- The default shard (class 57, depth 3, pair 1): tree levels and complete pairs. -/
def shard57 : IO Unit := do
  let D := L6.F2.Diag.ofF1 ⟨305710080, 63, 63⟩
  let ord := [4, 5, 2, 3, 0, 1]
  let x : Nat × TS × TS := (116, ⟨[116, 36], none⟩, ⟨[116, 48, 52], none⟩)
  cntRef.set 0
  let pairs := treeLevelL keepC D (ord.drop 3) x.1 x.2.1 x.2.2
  IO.println s!"tree levels: complete pairs {pairs.length} programs {← cntRef.get}"
  let mut i := 0
  let mut tot := 0
  let mut totc := 0
  for y in pairs do
    cntRef.set 0
    let P : Pair := ⟨y.2.1, y.2.2⟩
    let cs := cellsBelowL keepC D P
    let n ← cntRef.get
    let nrows := match partialRowsL D P all with | some L => L.length | none => 0
    let nid := match idents D P with | some ids => ids.length | none => 0
    IO.println s!"pair {i}: S {y.1} tz {tsStr y.2.1} tw {tsStr y.2.2} nv {P.nv} rows {nrows} idents {nid} cells {cs.length} programs {n}"
    tot := tot + n
    totc := totc + cs.length
    i := i + 1
  IO.println s!"argmin stage: programs {tot} cells {totc}"

/-- `c d i out`: the pair `i` after `d` insertions of class `c`: its tree-level programs, its complete pairs with
their argmin-stage programs and cells, and the certificate table of all its discarded programs (file `out`). -/
def profPair (c d i : Nat) (out : String) : IO Unit := do
  let dg := L6.F2.classes6[c]!
  let D := L6.F2.diagOf c
  let ord := order D
  IO.println s!"class {c} diagram ⟨{dg.e}, {dg.zc}, {dg.wc}⟩ order {ord} depth {d}"
  let pre := prefixPairsL (fun r nv => keepLP r.toArray nv) D ord d
  let x := pre[i]!
  IO.println s!"pairs {pre.length}; pair {i}: S {x.1} tz {tsStr x.2.1} tw {tsStr x.2.2}"
  cntRef.set 0
  logRef.set #[]
  let pairs := treeLevelL keepR D (ord.drop d) x.1 x.2.1 x.2.2
  IO.println s!"tree levels: complete pairs {pairs.length} programs {← cntRef.get}"
  let mut j := 0
  let mut tot := 0
  for y in pairs do
    cntRef.set 0
    let P : Pair := ⟨y.2.1, y.2.2⟩
    let cs := cellsBelowL keepR D P
    let n ← cntRef.get
    let nrows := match partialRowsL D P all with | some L => L.length | none => 0
    IO.println s!"cpair {j}: tz {tsStr y.2.1} tw {tsStr y.2.2} nv {P.nv} rows {nrows} cells {cs.length} programs {n}"
    tot := tot + n
    j := j + 1
  IO.println s!"argmin stage: programs {tot}; certificates {(← logRef.get).size}"
  let h ← IO.FS.Handle.mk out .write
  for l in certLines (← logRef.get) do h.putStrLn l
  h.flush

initialize progRef : IO.Ref (Array (List Row × Bool)) ← IO.mkRef #[]

/-- `keepLP`, recording every program (its rows and the decision). -/
unsafe def keepDImpl (rows : List Row) (nv : Nat) : Bool :=
  let v := keepLP rows.toArray nv
  let n := unsafeBaseIO (do progRef.modify (·.push (rows, v)); return (← progRef.get).size)
  n != 0 && v

@[implemented_by keepDImpl] opaque keepD : List Row → Nat → Bool

def intStr (z : Int) : String := if z < 0 then s!"({z})" else toString z

def optStr : Option Int → String
  | none => "none"
  | some z => s!"some {intStr z}"

def rowStr (r : Row) : String :=
  "{ a := #[" ++ ", ".intercalate (r.a.toList.map intStr) ++ s!"], c := {intStr r.c}, lo := {optStr r.lo}, hi := {optStr r.hi} " ++ "}"

initialize nvRef : IO.Ref (Array Nat) ← IO.mkRef #[]

/-- `keepLP`, recording every program (its rows, the decision and the number of heights). -/
unsafe def keepTImpl (rows : List Row) (nv : Nat) : Bool :=
  let v := keepLP rows.toArray nv
  let n := unsafeBaseIO (do progRef.modify (·.push (rows, v)); nvRef.modify (·.push nv); return (← progRef.get).size)
  n != 0 && v

@[implemented_by keepTImpl] opaque keepT : List Row → Nat → Bool

/-- `dumpkeep c d i j out`: the programs of `cellsBelowL` at the complete pair `j` below the pair `i` after `d`
insertions of class `c`, as a Lean file defining `progs : List (List Row)` and the number kept. -/
def dumpKeep (c d i j : Nat) (out : String) : IO Unit := do
  let D := L6.F2.diagOf c
  let ord := order D
  let pre := prefixPairsL (fun r nv => keepLP r.toArray nv) D ord d
  let x := pre[i]!
  let pairs := treeLevelL (fun r nv => keepLP r.toArray nv) D (ord.drop d) x.1 x.2.1 x.2.2
  let y := pairs[j]!
  let P : Pair := ⟨y.2.1, y.2.2⟩
  progRef.set #[]
  let cs := cellsBelowL keepD D P
  let ps ← progRef.get
  let h ← IO.FS.Handle.mk out .write
  h.putStrLn s!"-- class {c} depth {d} pair {i} complete pair {j}: nv {P.nv}, programs {ps.size}, kept {(ps.filter (·.2)).size}, cells {cs.length}"
  let L0 : List Row := match ps[0]? with | some (r, _) => r | none => []
  h.putStrLn ("def L0 : List L6.Row := [" ++ ",\n    ".intercalate (L0.map rowStr) ++ "]")
  h.putStrLn "def progs : List (List L6.Row) := ["
  let mut k := 0
  for (rows, _) in ps do
    let body := if rows.take L0.length == L0 then
        "L0 ++ [" ++ ",\n    ".intercalate ((rows.drop L0.length).map rowStr) ++ "]"
      else "[" ++ ",\n    ".intercalate (rows.map rowStr) ++ "]"
    h.putStrLn ((if k == 0 then "  " else "  , ") ++ body)
    k := k + 1
  h.putStrLn "]"
  h.putStrLn s!"def nKept : Nat := {(ps.filter (·.2)).size}"
  h.flush
  IO.println s!"programs {ps.size} kept {(ps.filter (·.2)).size} cells {cs.length} nv {P.nv}"

/-- `dumptree c d i out`: the programs of the tree levels below the pair `i` after `d` insertions of class `c`, as a
Lean file defining `progs : List (List Row)` (each with its number of heights in `nvs`) and the number kept. -/
def dumpTree (c d i : Nat) (out : String) : IO Unit := do
  let D := L6.F2.diagOf c
  let ord := order D
  let pre := prefixPairsL (fun r nv => keepLP r.toArray nv) D ord d
  let x := pre[i]!
  progRef.set #[]
  nvRef.set #[]
  let pairs := treeLevelL keepT D (ord.drop d) x.1 x.2.1 x.2.2
  let ps ← progRef.get
  let nvs ← nvRef.get
  let h ← IO.FS.Handle.mk out .write
  h.putStrLn s!"-- class {c} depth {d} pair {i}: tree-level programs {ps.size}, kept {(ps.filter (·.2)).size}, complete pairs {pairs.length}"
  h.putStrLn "def progs : List (List L6.Row) := ["
  let mut k := 0
  for (rows, _) in ps do
    h.putStrLn ((if k == 0 then "  [" else "  , [") ++ ",\n    ".intercalate (rows.map rowStr) ++ "]")
    k := k + 1
  h.putStrLn "]"
  h.putStrLn ("def nvs : List Nat := " ++ toString nvs.toList)
  h.putStrLn s!"def nKept : Nat := {(ps.filter (·.2)).size}"
  h.flush
  IO.println s!"programs {ps.size} kept {(ps.filter (·.2)).size} complete pairs {pairs.length}"

def main (args : List String) : IO Unit := do
  match args with
  | [c, d, i, out] => profPair c.toNat! d.toNat! i.toNat! out
  | ["dumpkeep", c, d, i, j, out] => dumpKeep c.toNat! d.toNat! i.toNat! j.toNat! out
  | ["dumptree", c, d, i, out] => dumpTree c.toNat! d.toNat! i.toNat! out
  | _ => shard57

end L6K.F2S.Prof

def main (args : List String) : IO Unit := L6K.F2S.Prof.main args
