import Lean
import L6KSpec.Load
import L6KSpec.C4Check

/-!
# Loading the data of a cofactor certificate modulo a prime

`load_c4_cert "H.bin" size "H.idx"` reads the chunks of `H.bin` (8-byte little-endian lengths, little-endian numbers
`x0, x1, …`) and the index `H.idx`, and defines in the current namespace

* `pcs : List (List Piece)`: line `P i CB cp kp cn kn` adds to cofactor `i` the piece
  `⟨terms KB CB cp x<kp>, terms KB CB cn x<kn>⟩`;
* `b<j> : Nat × Nat × List Nat × Piece`: line `B j F R nc kc HB cp kp cn kn` defines
  `(F, R, codesOf nc x<kc>, ⟨terms KB HB cp x<kp>, terms KB HB cn x<kn>⟩)` (with the `KB` of line `K KB`).

The terms are built directly (natural-number literals, no elaboration). The definitions are data for the kernel; their
meaning comes from the checks. (The loader of the F4 kernel modules of `lean6`, `load_f4_cert`.)
-/

open Lean Elab Command

namespace L6KSpec.C4

/-- The number with little-endian bytes `b[lo:hi]`, by binary splitting (linear-time pieces, GMP products). -/
partial def natOfBytes (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi - lo ≤ 64 then Id.run do
    let mut n := 0
    let mut i := hi
    while i > lo do
      i := i - 1
      n := n * 256 + (b.get! i).toNat
    return n
  else
    let mid := lo + (hi - lo) / 2
    natOfBytes b lo mid + (natOfBytes b mid hi <<< (8 * (mid - lo)))

private def lit (n : Nat) : Expr := mkRawNatLit n

private def natE : Expr := mkConst ``Nat

private def listE (t : Expr) : Expr := mkApp (mkConst ``List [0]) t

private def listLit (t : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) t x acc) (mkApp (mkConst ``List.nil [0]) t)

private def prodE (a b : Expr) : Expr := mkApp2 (mkConst ``Prod [0, 0]) a b

private def pairE (a b : Expr) (x y : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) a b x y

private def addData (name : Name) (type value : Expr) : CoreM Unit :=
  addDecl <| Declaration.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }

elab "load_c4_cert " path:str size:num idx:str : command => do
  let bytes ← IO.FS.readBinFile (← L6KSpec.dataPath path.getString)
  if bytes.size != size.getNat then
    throwError "load_c4_cert: {path.getString} has {bytes.size} bytes, expected {size.getNat}"
  let ns ← getCurrNamespace
  let mut pos : Nat := 0
  let mut chunks : Array Nat := #[]
  while pos + 8 ≤ bytes.size do
    let len := natOfBytes bytes pos (pos + 8)
    if pos + 8 + len > bytes.size then
      throwError "load_c4_cert: {path.getString}: chunk {chunks.size} overruns the file"
    chunks := chunks.push (natOfBytes bytes (pos + 8) (pos + 8 + len))
    pos := pos + 8 + len
  if pos != bytes.size then
    throwError "load_c4_cert: {path.getString}: trailing bytes"
  let x (j : Nat) : Except String Expr :=
    if h : j < chunks.size then .ok (lit chunks[j]) else .error s!"chunk {j} out of range"
  let pieceT := mkConst ``Piece
  let terms (kb cb c j : Nat) : Except String Expr := do
    return mkApp4 (mkConst ``terms) (lit kb) (lit cb) (lit c) (← x j)
  let mut kbits : Nat := 0
  let mut pcs : Array (Array Expr) := #[]
  let mut nb : Nat := 0
  let bT := prodE natE (prodE natE (prodE (listE natE) pieceT))
  for line in (← IO.FS.lines (← L6KSpec.dataPath idx.getString)) do
    let ws := (line.splitOn " ").filter (· ≠ "")
    let nums := (ws.drop 1).map String.toNat!
    match ws.head?, nums with
    | some "K", [kb] => kbits := kb
    | some "P", [i, cb, cp, kp, cn, kn] =>
      let r : Except String Expr := do
        return mkApp2 (mkConst ``Piece.mk) (← terms kbits cb cp kp) (← terms kbits cb cn kn)
      let e ← match r with
        | .ok e => pure e
        | .error m => throwError "load_c4_cert: {m}"
      while pcs.size ≤ i do pcs := pcs.push #[]
      pcs := pcs.modify i (·.push e)
    | some "B", [j, f, r, nc, kc, hb, cp, kp, cn, kn] =>
      let res : Except String Expr := do
        let codes := mkApp2 (mkConst ``codesOf) (lit nc) (← x kc)
        let hp := mkApp2 (mkConst ``Piece.mk) (← terms kbits hb cp kp) (← terms kbits hb cn kn)
        return pairE natE (prodE natE (prodE (listE natE) pieceT)) (lit f)
          (pairE natE (prodE (listE natE) pieceT) (lit r) (pairE (listE natE) pieceT codes hp))
      let e ← match res with
        | .ok e => pure e
        | .error m => throwError "load_c4_cert: {m}"
      if j != nb then throwError "load_c4_cert: bucket {j} out of order"
      liftCoreM <| addData (ns ++ Name.mkSimple ("b" ++ toString j)) bT e
      nb := nb + 1
    | some "G", [ng] => while pcs.size < ng do pcs := pcs.push #[]
    | _, _ => throwError "load_c4_cert: bad index line: {line}"
  let value := listLit (listE pieceT) (pcs.map (listLit pieceT ·))
  liftCoreM <| addData (ns ++ `pcs) (listE (listE pieceT)) value

end L6KSpec.C4
