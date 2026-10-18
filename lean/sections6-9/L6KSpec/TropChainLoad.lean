import Lean
import L6KSpec.Load
import L6KSpec.C4Load
import L6KSpec.TropChain

/-!
# Loading the data of a chain of identities

The data files hold chunks (8-byte little-endian lengths, little-endian numbers `x0, x1, …`) of packed records, read
as in `load_c4_cert`; the definitions are written out as literals (natural-number literals, no elaboration). Their
meaning comes from the checks.

* `load_chain_table "T.bin" size "T.idx"` defines `T : List NTerms`: line `K KB CB` gives the bits of a key and of a
  coefficient, line `T cnt j` adds the entry of the `cnt` records `key + c · 2^KB` of chunk `j`, in order.
* `load_chain_steps "S.bin" size "S.idx"` defines `s<j> : ChainStep` and the list `steps` of all of them: line
  `K RB KB CB` gives the bits of a record `r + m · 2^RB + c · 2^(RB + KB)`, line `S j k F R cnt i` defines
  `s<j> := (k, F, R, cofactor terms)` with the `cnt` records of chunk `i`.
-/

open Lean Elab Command

namespace L6KSpec.Trop

open L6KSpec.C4

private def lit (n : Nat) : Expr := mkRawNatLit n

private def natE : Expr := mkConst ``Nat

private def listE (t : Expr) : Expr := mkApp (mkConst ``List [0]) t

private def listLit (t : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) t x acc) (mkApp (mkConst ``List.nil [0]) t)

private def prodE (a b : Expr) : Expr := mkApp2 (mkConst ``Prod [0, 0]) a b

private def pairE (a b : Expr) (x y : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) a b x y

private def addData (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl <| Declaration.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }

/-- The chunks of a data file. -/
private def readChunks (path : String) (size : Nat) : CommandElabM (Array Nat) := do
  let bytes ← IO.FS.readBinFile (← L6KSpec.dataPath path)
  if bytes.size != size then
    throwError "load_chain: {path} has {bytes.size} bytes, expected {size}"
  let mut pos : Nat := 0
  let mut chunks : Array Nat := #[]
  while pos + 8 ≤ bytes.size do
    let len := natOfBytes bytes pos (pos + 8)
    if pos + 8 + len > bytes.size then
      throwError "load_chain: {path}: chunk {chunks.size} overruns the file"
    chunks := chunks.push (natOfBytes bytes (pos + 8) (pos + 8 + len))
    pos := pos + 8 + len
  if pos != bytes.size then
    throwError "load_chain: {path}: trailing bytes"
  return chunks

/-- The `cnt` records of `rb` bits of `n`, low record first. -/
private def records (rb cnt n : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty cnt
  let mut m := n
  for _ in [0:cnt] do
    out := out.push (m % 2 ^ rb)
    m := m / 2 ^ rb
  return out

elab "load_chain_table " path:str size:num idx:str : command => do
  let chunks ← readChunks path.getString size.getNat
  let ns ← getCurrNamespace
  let tT := prodE natE natE
  let mut kb : Nat := 0
  let mut cb : Nat := 0
  let mut entries : Array Expr := #[]
  for line in (← IO.FS.lines (← L6KSpec.dataPath idx.getString)) do
    let ws := (line.splitOn " ").filter (· ≠ "")
    let nums := (ws.drop 1).map String.toNat!
    match ws.head?, nums with
    | some "K", [k, c] => kb := k; cb := c
    | some "T", [cnt, j] =>
      if h : j < chunks.size then
        let ts := (records (kb + cb) cnt chunks[j]).map fun r => pairE natE natE (lit (r % 2 ^ kb)) (lit (r / 2 ^ kb))
        entries := entries.push (listLit tT ts)
      else throwError "load_chain_table: chunk {j} out of range"
    | _, _ => throwError "load_chain_table: bad index line: {line}"
  liftCoreM <| addData (ns ++ `T) (listE (listE tT)) (listLit (listE tT) entries)

elab "load_chain_steps " path:str size:num idx:str : command => do
  let chunks ← readChunks path.getString size.getNat
  let ns ← getCurrNamespace
  let cT := prodE natE (prodE natE natE)
  let sT := mkConst ``ChainStep
  let mut rb : Nat := 0
  let mut kb : Nat := 0
  let mut cb : Nat := 0
  let mut names : Array Expr := #[]
  for line in (← IO.FS.lines (← L6KSpec.dataPath idx.getString)) do
    let ws := (line.splitOn " ").filter (· ≠ "")
    let nums := (ws.drop 1).map String.toNat!
    match ws.head?, nums with
    | some "K", [r, k, c] => rb := r; kb := k; cb := c
    | some "S", [j, k, f, rr, cnt, i] =>
      if h : i < chunks.size then
        let cofs := (records (rb + kb + cb) cnt chunks[i]).map fun x =>
          pairE natE (prodE natE natE) (lit (x % 2 ^ rb))
            (pairE natE natE (lit (x / 2 ^ rb % 2 ^ kb)) (lit (x / 2 ^ (rb + kb))))
        let value := pairE natE (prodE natE (prodE natE (listE cT))) (lit k)
          (pairE natE (prodE natE (listE cT)) (lit f) (pairE natE (listE cT) (lit rr) (listLit cT cofs)))
        let name := ns ++ Name.mkSimple ("s" ++ toString j)
        liftCoreM <| addData name sT value
        names := names.push (mkConst name)
      else throwError "load_chain_steps: chunk {i} out of range"
    | _, _ => throwError "load_chain_steps: bad index line: {line}"
  liftCoreM <| addData (ns ++ `steps) (listE sT) (listLit sT names)

end L6KSpec.Trop
