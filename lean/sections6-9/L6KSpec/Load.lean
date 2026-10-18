import Lean
/-!
# Loading big natural-number literals from binary files

`load_box_nat foo "path"` defines `foo : Nat` as the number whose little-endian bytes are the contents of the file (a
relative path is looked up from the directory of the source file upwards: `dataPath`). The literal is built directly
as an expression (`Expr.lit`), so its size costs nothing at parse time; the kernel reads it as one literal.
-/
open Lean Elab Command

namespace L6KSpec

/-- The directory `d` and its ancestors, nearest first, joined with `rel`: the first that exists. -/
partial def findUp (d rel : System.FilePath) : IO (Option System.FilePath) := do
  let c := d / rel
  if ← c.pathExists then return some c
  match d.parent with
  | some q => if q == d then return none else findUp q rel
  | none => return none

/-- The data file `rel` of the module being elaborated: an absolute path as it is; a relative path looked up from the
directory of the source file upwards (as `include_str` resolves paths relative to the source file), so that the module
builds from any working directory (a dependent package included); else relative to the working directory. -/
def dataPath (rel : String) : CommandElabM System.FilePath := do
  let p : System.FilePath := rel
  if p.isAbsolute then return p
  let f : System.FilePath := (← getFileName)
  match ← findUp (f.parent.getD ".") p with
  | some q => return q
  | none => return p

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

elab "load_box_nat " id:ident path:str : command => do
  let bytes ← IO.FS.readBinFile (← dataPath path.getString)
  let n := natOfBytes bytes 0 bytes.size
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addDecl <| Declaration.defnDecl {
    name, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit n,
    hints := .abbrev, safety := .safe }

/-- `load_box_chunks x "path" size`: the file (of `size` bytes) is a sequence of chunks, each an 8-byte little-endian
length followed by that many bytes; defines `x0, x1, …` as the numbers with these little-endian bytes. -/
elab "load_box_chunks " id:ident path:str size:num : command => do
  let bytes ← IO.FS.readBinFile (← dataPath path.getString)
  if bytes.size != size.getNat then
    throwError "load_box_chunks: {path.getString} has {bytes.size} bytes, expected {size.getNat}"
  let ns ← getCurrNamespace
  let mut pos : Nat := 0
  let mut k : Nat := 0
  while pos + 8 ≤ bytes.size do
    let len := natOfBytes bytes pos (pos + 8)
    if pos + 8 + len > bytes.size then
      throwError "load_box_chunks: {path.getString}: chunk {k} overruns the file"
    let n := natOfBytes bytes (pos + 8) (pos + 8 + len)
    let name := ns ++ Name.mkSimple (id.getId.toString ++ toString k)
    liftCoreM <| addDecl <| Declaration.defnDecl {
      name, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit n,
      hints := .abbrev, safety := .safe }
    pos := pos + 8 + len
    k := k + 1
  if pos != bytes.size then
    throwError "load_box_chunks: {path.getString}: trailing bytes"

end L6KSpec
