/-!
# Reading the argmin lists of the stored cells

A stored cell is one line of `data/cells/c<N>.jsonl`, a JSON object written by Python's `json.dumps` with the keys
`ztree`, `wtree`, `argmin`, `x`, `hz`, `hw`, `slack`, `sumx`. Corollary 5.8 needs only the value of `argmin`: a list
of pairs `[name, labels]`, one for each base identity, with the labels of the terms in its argmin set. These values
are nested arrays of strings (without escapes) and natural numbers. This file reads such values from the bytes of a
line (`parseVal`) and writes them back in the layout of `json.dumps` (`render`: `", "` between the elements of an
array). The checks of `L6F5.Census` require that the rendered value is, byte for byte, the text between
`"argmin": ` and `, "x": ` of the line, so the parsed value is exactly what the file says, whatever the details of
the parser.
-/

namespace L6F5

/-- A JSON value built from arrays, strings without escapes and natural numbers. -/
inductive JV where
  | num (k : Nat)
  | str (s : String)
  | arr (xs : List JV)
  deriving Inhabited

mutual
/-- The text of a value in the layout of `json.dumps`. -/
def render : JV → String
  | .num k => toString k
  | .str s => "\"" ++ s ++ "\""
  | .arr xs => "[" ++ renderElems xs ++ "]"

/-- The elements of an array, separated by `", "`. -/
def renderElems : List JV → String
  | [] => ""
  | [x] => render x
  | x :: y :: ys => render x ++ ", " ++ renderElems (y :: ys)
end

/-- The byte at the position `i` of `b`, and `0` past the end. -/
@[inline] def byteAt (b : ByteArray) (i : Nat) : UInt8 := if h : i < b.size then b[i] else 0

/-- The decimal digits of `b` from the position `i` (at most `fuel` of them), added to `acc`: the number and the
position after the digits. -/
def parseNat (b : ByteArray) : Nat → Nat → Nat → Nat × Nat
  | 0, i, acc => (acc, i)
  | fuel + 1, i, acc =>
    let c := byteAt b i
    if 48 ≤ c && c ≤ 57 then parseNat b fuel (i + 1) (acc * 10 + (c.toNat - 48)) else (acc, i)

/-- The printable ASCII bytes of `b` from the position `i` up to the closing `"` (at most `fuel` of them), appended
to `acc`: the string and the position after the quote. A backslash or any other byte gives `none`. -/
def parseStrBody (b : ByteArray) : Nat → Nat → String → Option (String × Nat)
  | 0, _, _ => none
  | fuel + 1, i, acc =>
    let c := byteAt b i
    if c == 34 then some (acc, i + 1)
    else if 32 ≤ c && c < 127 && c != 92 then parseStrBody b fuel (i + 1) (acc.push (Char.ofNat c.toNat))
    else none

mutual
/-- The value of `b` at the position `i` and the position after it (within `fuel` steps). -/
def parseVal (b : ByteArray) : Nat → Nat → Option (JV × Nat)
  | 0, _ => none
  | fuel + 1, i =>
    let c := byteAt b i
    if c == 91 then
      if byteAt b (i + 1) == 93 then some (.arr [], i + 2) else parseElems b fuel (i + 1) []
    else if c == 34 then
      match parseStrBody b fuel (i + 1) "" with
      | some (s, j) => some (.str s, j)
      | none => none
    else if 48 ≤ c && c ≤ 57 then
      let r := parseNat b fuel i 0
      some (.num r.1, r.2)
    else none

/-- The elements of an array from the position `i` (after `[`), the elements read so far being `acc` (reversed):
the array and the position after `]`. -/
def parseElems (b : ByteArray) : Nat → Nat → List JV → Option (JV × Nat)
  | 0, _, _ => none
  | fuel + 1, i, acc =>
    match parseVal b fuel i with
    | none => none
    | some (v, j) =>
      if byteAt b j == 44 && byteAt b (j + 1) == 32 then parseElems b fuel (j + 2) (v :: acc)
      else if byteAt b j == 93 then some (.arr (v :: acc).reverse, j + 1)
      else none
end

/-- The bytes of `b` from the position `i` on begin with the bytes of `p`. -/
def matchAt (b p : ByteArray) (i : Nat) : Bool := go p.size 0
where
  /-- The bytes `k, k + 1, …` of `p` (at most `fuel` of them) agree. -/
  go : Nat → Nat → Bool
    | 0, _ => true
    | fuel + 1, k => if k < p.size then byteAt b (i + k) == byteAt p k && go fuel (k + 1) else true

/-- The first position `j` with `i ≤ j` and `j + p.size ≤ stop` at which the bytes of `p` occur in `b`. -/
def findFrom (b p : ByteArray) (i stop : Nat) : Option Nat := go (stop + 1 - i) i
where
  /-- The search from the position `j`, within `fuel` steps. -/
  go : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, j => if j + p.size > stop then none else if matchAt b p j then some j else go fuel (j + 1)

end L6F5
