import L6F1.Json
import L6F1.ChangChen
import L6F5.Clique

/-!
# The census of Proposition 5.9

`census n6 files` reads the classes of `n6.json` (with the reader of the family F1, and only if it writes them back
identically) and, for each class, the stored cells `files[c]` (the text of `data/cells/c<c>.jsonl`, one cell per
line, the cell `k` on the line `k`, counted from `0`). For each class it returns

* the number of cells,
* the number of cells with a clique as in Corollary 5.8 (`hasClique`),
* the number of cells with such a clique of three bodies (`has3`),
* the number of cells with such a clique of four bodies (`has4`),
* the number of cells whose forced argmin sets are those of the diagram (`forcedOK`).

It returns `none` if a line cannot be read: every line must begin with `{"ztree": `, contain `"argmin": ` followed
by a value that `render` writes back byte for byte and that is followed by `, "x": `, and this value must be read by
`readCell` (all fourteen base identities, each once, with labels of the expected form).
-/

namespace L6F5

open L6F1 (Diagram)

/-- The ends of the lines of `b`: for each line, the position of its first byte and of its terminating newline;
`none` if the bytes do not end with a newline (unless there are none). -/
def lineBounds (b : ByteArray) : Option (Array (Nat × Nat)) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut start := 0
  for i in [0:b.size] do
    if byteAt b i == 10 then
      out := out.push (start, i)
      start := i + 1
  return if start == b.size then some out else none

/-- `{"ztree": `. -/
def lineHead : ByteArray := "{\"ztree\": ".toUTF8
/-- `"argmin": `. -/
def keyArgmin : ByteArray := "\"argmin\": ".toUTF8
/-- `, "x": `. -/
def keyX : ByteArray := ", \"x\": ".toUTF8

/-- The bytes `[i, k)` of `b` are the UTF-8 bytes of `t`. -/
def sliceIs (b : ByteArray) (i k : Nat) (t : String) : Bool :=
  let tb := t.toUTF8
  i + tb.size == k && matchAt b tb i

/-- **Reads the cell on the line `[s, e)` of `b`.** -/
def readLine (b : ByteArray) (s e : Nat) : Option Cell :=
  if !matchAt b lineHead s then none else
  match findFrom b keyArgmin s e with
  | none => none
  | some j =>
    let i := j + keyArgmin.size
    match parseVal b (e - i) i with
    | none => none
    | some (v, k) =>
      if k + keyX.size ≤ e && matchAt b keyX k && sliceIs b i k (render v) then readCell v else none

/-- The tally of the stored cells of one class. -/
structure Tally where
  /-- The number of cells. -/
  cells : Nat
  /-- The number of cells with a clique as in Corollary 5.8. -/
  clique : Nat
  /-- The number of cells with such a clique of three bodies. -/
  three : Nat
  /-- The number of cells with such a clique of four bodies. -/
  four : Nat
  /-- The number of cells whose forced argmin sets are those of the diagram (`forcedOK`). -/
  forced : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The status of one cell: whether it has a clique as in Corollary 5.8, one of three bodies, one of four bodies. -/
structure Status where
  /-- A clique as in Corollary 5.8. -/
  clique : Bool
  /-- Such a clique of three bodies. -/
  three : Bool
  /-- Such a clique of four bodies. -/
  four : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The status of a cell `x` of the diagram `d`. -/
def statusOf (d : Diagram) (x : Cell) : Status := ⟨hasClique d x, has3 d x, has4 d x⟩

/-- The tally of the stored cells `s` (one per line) of the diagram `d`; `none` if a line cannot be read. -/
def censusFile (d : Diagram) (s : String) : Option Tally := Id.run do
  let b := s.toUTF8
  match lineBounds b with
  | none => return none
  | some ls =>
    let mut t : Tally := ⟨0, 0, 0, 0, 0⟩
    for (st, en) in ls do
      match readLine b st en with
      | none => return none
      | some x =>
        let h := statusOf d x
        t := ⟨t.cells + 1, t.clique + (if h.clique then 1 else 0), t.three + (if h.three then 1 else 0),
          t.four + (if h.four then 1 else 0), t.forced + (if forcedOK d x then 1 else 0)⟩
    return some t

/-- The statuses of the stored cells `s` (one per line) of the diagram `d`, in order; `none` if a line cannot be
read. -/
def statusesFile (d : Diagram) (s : String) : Option (Array Status) := Id.run do
  let b := s.toUTF8
  match lineBounds b with
  | none => return none
  | some ls =>
    let mut out : Array Status := #[]
    for (st, en) in ls do
      match readLine b st en with
      | none => return none
      | some x => out := out.push (statusOf d x)
    return some out

/-- The class representatives of `n6.json` (six bodies), read by `L6F1.parseFile`, provided `L6F1.renderFile`
writes them back identically. -/
def classesOf (n6 : String) : Option (List Diagram) :=
  match L6F1.parseFile n6 with
  | some (n, total, cls) => if n == 6 && L6F1.renderFile n total cls == n6 then some (cls.map (·.1)) else none
  | none => none

/-- **The census**: for each class of `n6.json`, in order, the tally of its stored cells `files[c]`. -/
def census (n6 : String) (files : List String) : Option (List Tally) :=
  match classesOf n6 with
  | none => none
  | some ds => if ds.length == files.length then (ds.zip files).mapM fun p => censusFile p.1 p.2 else none

/-- The statuses of all stored cells, class by class. -/
def statuses (n6 : String) (files : List String) : Option (List (Array Status)) :=
  match classesOf n6 with
  | none => none
  | some ds => if ds.length == files.length then (ds.zip files).mapM fun p => statusesFile p.1 p.2 else none

/-- The status of the cell `k` (the line `k` of `files[c]`) of the class `c`. -/
def cellStatus (n6 : String) (files : List String) (c k : Nat) : Option Status := do
  let ds ← classesOf n6
  let d ← ds[c]?
  let s ← files[c]?
  let b := s.toUTF8
  let ls ← lineBounds b
  let (st, en) ← ls[k]?
  let x ← readLine b st en
  return statusOf d x

/-- The cells listed in `open43.tsv`: `(class, diagram of Chang and Chen, cell)` for each line that is not empty and
does not begin with `#`; `none` if such a line is not three numbers separated by tabs, written back identically. -/
def readOpen (s : String) : Option (List (Nat × Nat × Nat)) :=
  ((s.splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "#").mapM fun l =>
    match l.splitOn "\t" with
    | [a, b, c] =>
      match a.toNat?, b.toNat?, c.toNat? with
      | some x, some y, some z => if s!"{x}\t{y}\t{z}" == l then some (x, y, z) else none
      | _, _, _ => none
    | _ => none

/-- The status of each cell listed in `open43.tsv`: `(class, diagram, cell, status)`. -/
def openStatus (n6 : String) (files : List String) (open43 : String) :
    Option (List (Nat × Nat × Nat × Status)) := do
  let qs ← readOpen open43
  qs.mapM fun q => (cellStatus n6 files q.1 q.2.2).map fun st => (q.1, q.2.1, q.2.2, st)

/-- The diagram number `i` of Chang and Chen (read from `cc` by `L6F1.parseCC`) lies in the orbit, under the
relabellings and the exchange of the colours, of the representative of the class `c` of `n6`. -/
def ccInClass (cc n6 : String) (i c : Nat) : Bool :=
  match L6F1.parseCC cc, classesOf n6 with
  | some xs, some ds =>
    match xs.find? (·.num == i), ds[c]? with
    | some x, some d => (L6F1.orbitList 6 d).contains (L6F1.ccToDiagram x)
    | _, _ => false
  | _, _ => false

/-- The digest recorded for the file `name` in the text of a `SHA256SUMS` file (lines `digest  name`). -/
def sumFor (sums name : String) : Option String :=
  ((sums.splitOn "\n").filterMap fun l =>
    match l.splitOn "  " with
    | [h, n] => if n == name then some h else none
    | _ => none).head?

end L6F5
