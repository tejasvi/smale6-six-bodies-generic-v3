import L6F1.Json
import L6F1.Data
import L6Common.SHA256
import L6F2.Search

/-!
# The checks of Proposition 4.5 against the stored cell lists

The stored list of class `k` (`data/cells/c<k>.jsonl`, the file `cells.jsonl` of the engine's run) is the
concatenation of the outputs of the 384 parts of the search in the byte order of their file names `p<part>.jsonl`
(`p0, p1, p10, p100, …`). A *chunk* is a run of consecutive parts in that order, with the line offset of its first
cell, its number of cells and the counters of the engine's run (number of linear programs, number of prunes).

`checkChunk text c` runs the parts of the chunk `c` with `runPart` and checks that the cells it writes are, in order,
the beginnings (up to `"x": `) of the lines `c.off, c.off + 1, …` of `text`, that there are exactly `c.cells` of
them, that no linear program failed (every float prune had an accepted certificate), that every cell written has an
exact point with `s > 0` satisfying all its rows and `ℓ(x) ≤ 0` (`leafCertified`), and that the counters are those
of the engine (in total and part by part). `tilingOk text cs k` checks that the chunks `cs` of class `k` cover the 384 parts once, in the byte
order of their names, with consecutive offsets that end at the number of lines of `text`.
-/

namespace L6.F2

/-- The 191 class representatives of `n6.json` (read by `L6F1.parseFile`; `L6F1` proves the reading exact). -/
def classes6 : Array L6F1.Diagram :=
  match L6F1.parseFile L6F1.n6json with
  | some (_, _, cls) => (cls.map (·.1)).toArray
  | none => #[]

/-- The diagram of class `k`. -/
def diagOf (k : Nat) : Diag := Diag.ofF1 classes6[k]!

/-- The lines of a text (a final newline does not start a line). -/
def linesOf (text : String) : Array String :=
  let ls := (text.splitOn "\n").toArray
  if ls.size > 0 && ls[ls.size - 1]! == "" then ls.pop else ls

/-- The parts `0 … 383` in the byte order of their file names `p<part>.jsonl`. -/
def lexParts : List Nat :=
  (List.range 384).mergeSort fun a b => decide (s!"p{a}.jsonl" ≤ s!"p{b}.jsonl")

/-- A chunk: class, parts (in order), offset of the first line, number of cells, engine counters (totals, and per
part the number of cells, of linear programs and of prunes). -/
structure Chunk where
  cls : Nat
  parts : List Nat
  off : Nat
  cells : Nat
  lp : Nat
  pruned : Nat
  perPart : List (Nat × Nat × Nat)
  deriving Inhabited, Repr

/-- The result of running the parts of a chunk: the counters and the cells, in order, and the counters of each part. -/
def runChunk (c : Chunk) : St × List (Nat × Nat × Nat) :=
  let D := diagOf c.cls
  let (acc, pp) := c.parts.foldl (fun (acc, pp) p =>
    let r := runPart D p 384
    ({ acc with lp := acc.lp + r.lp, pruned := acc.pruned + r.pruned, fail := acc.fail + r.fail,
                leafFail := acc.leafFail + r.leafFail, cells := acc.cells ++ r.cells },
     (r.cells.size, r.lp, r.pruned) :: pp)) (({} : St), [])
  (acc, pp.reverse)

/-- The check of one chunk against the stored text of its class. -/
def checkChunk (text : String) (c : Chunk) : Bool :=
  let (r, pp) := runChunk c
  let lines := linesOf text
  r.fail == 0 && r.leafFail == 0 && r.lp == c.lp && r.pruned == c.pruned && r.cells.size == c.cells &&
    pp == c.perPart &&
    decide (c.off + c.cells ≤ lines.size) &&
    (List.range c.cells).all fun i => (lines[c.off + i]!).startsWith r.cells[i]!

/-- The chunks of class `k` tile its stored text. -/
def tilingOk (text : String) (cs : List Chunk) (k : Nat) : Bool :=
  let ends := cs.foldl (fun (acc : Option Nat) c =>
    match acc with
    | some o => if c.off == o then some (o + c.cells) else none
    | none => none) (some 0)
  cs.all (·.cls == k) && (cs.flatMap (·.parts)) == lexParts && ends == some (linesOf text).size

/-- Totals of a list of chunks: cells, linear programs, prunes. -/
def totals (cs : List Chunk) : Nat × Nat × Nat :=
  cs.foldl (fun (a, b, c) ch => (a + ch.cells, b + ch.lp, c + ch.pruned)) (0, 0, 0)

end L6.F2
