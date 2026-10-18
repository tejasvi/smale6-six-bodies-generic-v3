import L6F1.Search

/-!
# The 117 diagrams of Chang and Chen

The file `data/f1/chang_chen_117.txt` lists the 117 six-body diagrams of Chang and Chen (arXiv:2303.02853v1,
Figs. 3–6), one per line: `<number> <z-strokes> <w-strokes> <z-circled> <w-circled>`, with the bodies `1, …, 6` of their
figures, strokes as comma-separated pairs `ab` (`a < b`), circled bodies as a string of digits, and `-` for an empty
list. `parseCC` reads it; `renderCCLine` writes a diagram back, and `checkCC` requires the file (without its comment
lines) to be written back identically, so the parsed data are exactly those of the file.

`checkCC` also checks that the diagrams are numbered `1, …, 117`, well formed, satisfy the rules (`okRules 6`, after
renaming the body `k` to `k - 1`, `ccToDiagram`), and have pairwise distinct canonical keys (`canonKey 6 false`); since
the canonical key is constant on orbits, they lie in 117 distinct orbits.
-/

namespace L6F1

/-- A diagram of the list: its number, `z`-strokes, `w`-strokes (pairs `(a, b)`, `1 ≤ a < b ≤ 6`), and its `z`- and
`w`-circled bodies (in `1, …, 6`). -/
structure CCDiagram where
  /-- The number of the diagram in the figures of Chang and Chen. -/
  num : Nat
  /-- The `z`-strokes. -/
  zs : List (Nat × Nat)
  /-- The `w`-strokes. -/
  ws : List (Nat × Nat)
  /-- The `z`-circled bodies. -/
  zc : List Nat
  /-- The `w`-circled bodies. -/
  wc : List Nat
  deriving Repr, Inhabited

/-- The labelled diagram on the bodies `0, …, 5` (the body `k` of the figures becomes `k - 1`). -/
def ccToDiagram (x : CCDiagram) : Diagram :=
  ⟨codeOf 6 (fun a b => (if (a + 1, b + 1) ∈ x.zs then 1 else 0) + (if (a + 1, b + 1) ∈ x.ws then 2 else 0)),
    maskOf 6 (fun k => k + 1 ∈ x.zc), maskOf 6 (fun k => k + 1 ∈ x.wc)⟩

/-- The pairs `1 ≤ a < b ≤ 6` and the bodies `1 ≤ k ≤ 6` of the diagram are valid. -/
def ccWellFormed (x : CCDiagram) : Bool :=
  (x.zs ++ x.ws).all (fun p => 1 ≤ p.1 && p.1 < p.2 && p.2 ≤ 6) && (x.zc ++ x.wc).all (fun k => 1 ≤ k && k ≤ 6)

/-- Pairs `ab` separated by commas, or `-`. -/
def renderPairsCC (ps : List (Nat × Nat)) : String :=
  if ps.isEmpty then "-" else ",".intercalate (ps.map fun p => toString p.1 ++ toString p.2)

/-- Bodies as a string of digits, or `-`. -/
def renderBodiesCC (ks : List Nat) : String :=
  if ks.isEmpty then "-" else String.join (ks.map toString)

/-- **One line of the file.** -/
def renderCCLine (x : CCDiagram) : String :=
  toString x.num ++ " " ++ renderPairsCC x.zs ++ " " ++ renderPairsCC x.ws ++ " " ++ renderBodiesCC x.zc ++ " " ++
    renderBodiesCC x.wc

/-- The data lines of the file (not empty, not starting with `#`). -/
def ccLines (s : String) : List String :=
  (s.splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "#"

/-- The value of a decimal digit. -/
def digitVal (c : Char) : Nat := c.toNat - 48

/-- Reads `ab,cd,…` or `-`. -/
def parsePairsCC (f : String) : List (Nat × Nat) :=
  if f == "-" then [] else
    (f.splitOn ",").map fun p =>
      match p.toList with
      | [a, b] => (digitVal a, digitVal b)
      | _ => (0, 0)

/-- Reads a string of digits or `-`. -/
def parseBodiesCC (f : String) : List Nat := if f == "-" then [] else f.toList.map digitVal

/-- Reads one line. -/
def parseCCLine (l : String) : Option CCDiagram :=
  match l.splitOn " " with
  | [a, b, c, d, e] => some ⟨a.toNat?.getD 0, parsePairsCC b, parsePairsCC c, parseBodiesCC d, parseBodiesCC e⟩
  | _ => none

/-- **Reads the file.** -/
def parseCC (s : String) : Option (List CCDiagram) := (ccLines s).mapM parseCCLine

/-- **The checks of the list of Chang and Chen.** -/
def checkCC (s : String) : Bool :=
  match parseCC s with
  | none => false
  | some xs =>
    xs.map renderCCLine == ccLines s && xs.length == 117 && xs.map (·.num) == (List.range 117).map (· + 1) &&
      xs.all ccWellFormed && xs.all (fun x => inRange 6 (ccToDiagram x) && okRules 6 (ccToDiagram x)) &&
      strictSorted (sortNat (xs.map fun x => canonKey 6 false (ccToDiagram x)))

end L6F1
