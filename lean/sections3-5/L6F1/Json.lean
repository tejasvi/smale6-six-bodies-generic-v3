import L6F1.Rules

/-!
# The class files `n4.json`, `n5.json`, `n6.json`

Each file lists the classes of labelled diagrams on `n` bodies: for each class a representative (its edges, as a map
from the pair `"ab"` to the kind, its `z`- and `w`-circled bodies) and the number of labelled diagrams in the class.
`parseFile` reads a file into `(n, total, classes)` with each class as `(representative, count)`. The reading is
checked by `renderFile`, which writes `(n, total, classes)` back in the layout of the files (JSON with an indentation
of one space per level, the keys in the order `edges`, `zcircles`, `wcircles`, `labelled`, the edges in the order of
the positions): the checks require `renderFile n total classes = file`, byte for byte, so the parsed data are
exactly what the file says, whatever the details of the parser.
-/

namespace L6F1

/-! ## Writing -/

/-- The bodies `< n` circled in the mask `c`, increasing. -/
def bodiesOf (n c : Nat) : List Nat := (List.range n).filter (circled c)

/-- A list of bodies at the indentation of the class fields: `[]`, or one entry per line. -/
def renderList (ks : List Nat) : String :=
  if ks.isEmpty then "[]" else "[\n" ++ ",\n".intercalate (ks.map fun k => "    " ++ toString k) ++ "\n   ]"

/-- The edges of the edge code `e` on `n` bodies: one line `"ab": kind` per pair `(a, b)` with a nonzero kind, in the
order of the positions. -/
def renderEdges (n e : Nat) : String :=
  let es := (pairs n).filter fun p => kind e p.1 p.2 != 0
  if es.isEmpty then "{}" else
    "{\n" ++ ",\n".intercalate (es.map fun p =>
      "    \"" ++ toString p.1 ++ toString p.2 ++ "\": " ++ toString (kind e p.1 p.2)) ++ "\n   }"

/-- One class: the representative `x.1` and the number `x.2` of labelled diagrams. -/
def renderClass (n : Nat) (x : Diagram × Nat) : String :=
  "  {\n   \"edges\": " ++ renderEdges n x.1.e ++ ",\n   \"zcircles\": " ++ renderList (bodiesOf n x.1.zc) ++
    ",\n   \"wcircles\": " ++ renderList (bodiesOf n x.1.wc) ++ ",\n   \"labelled\": " ++ toString x.2 ++ "\n  }"

/-- **The file** with the number of bodies `n`, the total `total` and the classes `cls`. -/
def renderFile (n total : Nat) (cls : List (Diagram × Nat)) : String :=
  "{\n \"n\": " ++ toString n ++ ",\n \"labelled\": " ++ toString total ++ ",\n \"classes\": [\n" ++
    ",\n".intercalate (cls.map (renderClass n)) ++ "\n ]\n}"

/-! ## Reading -/

/-- The tokens of the files. -/
inductive Tok where
  | lbrace | rbrace | lbrack | rbrack | colon | comma
  | num (k : Nat)
  | str (s : String)
  | bad
  deriving Repr, BEq, Inhabited

/-- The tokens of a string: braces, brackets, colons, commas, decimal numbers and strings without escapes; spaces and
line breaks are skipped, and any other byte gives `bad`. -/
def tokenize (s : String) : Array Tok := Id.run do
  let b := s.toUTF8
  let mut toks : Array Tok := #[]
  let mut num : Option Nat := none
  let mut str : Option String := none
  for i in [0:b.size] do
    let c := b[i]!
    match str with
    | some acc =>
      if c == 34 then
        toks := toks.push (.str acc)
        str := none
      else if c < 128 then
        str := some (acc.push (Char.ofNat c.toNat))
      else
        toks := toks.push .bad
    | none =>
      if 48 ≤ c && c ≤ 57 then
        num := some (num.getD 0 * 10 + (c.toNat - 48))
      else
        if let some k := num then
          toks := toks.push (.num k)
          num := none
        if c == 34 then str := some ""
        else if c == 123 then toks := toks.push .lbrace
        else if c == 125 then toks := toks.push .rbrace
        else if c == 91 then toks := toks.push .lbrack
        else if c == 93 then toks := toks.push .rbrack
        else if c == 58 then toks := toks.push .colon
        else if c == 44 then toks := toks.push .comma
        else if c == 32 || c == 10 || c == 13 || c == 9 then pure ()
        else toks := toks.push .bad
  if let some k := num then toks := toks.push (.num k)
  if str.isSome then toks := toks.push .bad
  return toks

/-- `k, …, k ]`. -/
def parseNums : List Tok → Option (List Nat × List Tok)
  | .num k :: .comma :: ts => (parseNums ts).map fun r => (k :: r.1, r.2)
  | .num k :: .rbrack :: ts => some ([k], ts)
  | _ => none

/-- `[]` or `[ k, …, k ]`. -/
def parseNumList : List Tok → Option (List Nat × List Tok)
  | .lbrack :: .rbrack :: ts => some ([], ts)
  | .lbrack :: ts => parseNums ts
  | _ => none

/-- `"key": v, …, "key": v }`. -/
def parseEntries : List Tok → Option (List (String × Nat) × List Tok)
  | .str key :: .colon :: .num v :: .comma :: ts => (parseEntries ts).map fun r => ((key, v) :: r.1, r.2)
  | .str key :: .colon :: .num v :: .rbrace :: ts => some ([(key, v)], ts)
  | _ => none

/-- The edge code with the kinds `v` of the entries `"ab": v` (`a`, `b` single digits). -/
def edgeCodeOf (es : List (String × Nat)) : Nat :=
  (es.map fun x =>
    match x.1.toList with
    | [ca, cb] => x.2 * 4 ^ ppos (ca.toNat - 48) (cb.toNat - 48)
    | _ => 0).sum

/-- The circle mask of a list of bodies. -/
def maskOfList (ks : List Nat) : Nat := (ks.map fun k => 2 ^ k).sum

/-- One class `{ "edges": {…}, "zcircles": […], "wcircles": […], "labelled": k }`. -/
def parseClass (ts : List Tok) : Option ((Diagram × Nat) × List Tok) :=
  match ts with
  | .lbrace :: .str "edges" :: .colon :: .lbrace :: ts => do
    let (es, ts) ← parseEntries ts
    match ts with
    | .comma :: .str "zcircles" :: .colon :: ts => do
      let (zs, ts) ← parseNumList ts
      match ts with
      | .comma :: .str "wcircles" :: .colon :: ts => do
        let (ws, ts) ← parseNumList ts
        match ts with
        | .comma :: .str "labelled" :: .colon :: .num k :: .rbrace :: ts =>
          some ((⟨edgeCodeOf es, maskOfList zs, maskOfList ws⟩, k), ts)
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- The classes `c, …, c ]` (at most `fuel` of them). -/
def parseClassList : Nat → List Tok → Option (List (Diagram × Nat) × List Tok)
  | 0, _ => none
  | fuel + 1, ts =>
    match parseClass ts with
    | some (x, .comma :: ts) => (parseClassList fuel ts).map fun r => (x :: r.1, r.2)
    | some (x, .rbrack :: ts) => some ([x], ts)
    | _ => none

/-- **Reads a class file**: `(n, total, classes)`. -/
def parseFile (s : String) : Option (Nat × Nat × List (Diagram × Nat)) :=
  match (tokenize s).toList with
  | .lbrace :: .str "n" :: .colon :: .num n :: .comma :: .str "labelled" :: .colon :: .num total :: .comma ::
      .str "classes" :: .colon :: .lbrack :: ts =>
    match parseClassList ts.length ts with
    | some (cls, [.rbrace]) => some (n, total, cls)
    | _ => none
  | _ => none

end L6F1
