import L6F5
import L6F1.Data
import L6Check.F5.Data

/-!
# Proposition 5.9: the clique census

The theorems of the family F5, about the embedded data of `L6Check.F5.Data` (the stored cells of the 191 classes,
`n6.json`, `open43.tsv`; their digests are checked in `L6Check.F5.Sha`):

* `census_table`: the census `L6F5.census` (for each class the `Tally`: the numbers of cells, of cells with a clique
  as in Corollary 5.8, with one of three bodies, with one of four bodies, and of cells whose forced argmin sets are
  those of the diagram) is the explicit table `table`;
* `F5_main` (Proposition 5.9): 91,273 cells, of which 86,938 have a clique as in Corollary 5.8 and 4,335 do not; all
  cells of 18 classes have one, among them the 44,247 cells of class 3 and the 32,864 cells of class 128;
* `F5_three_four`: 86,842 cells have a clique of three bodies, 96 cells have a clique of four bodies, and no cell has
  both;
* `F5_forced`: in every stored cell the argmin set of each equation of a body with a stroke or a circle in its
  colour is the set of terms forced by the diagram;
* `F5_open`: of the 43 open cells of Proposition 5.3, the 11 cells of class 124 have a clique, of four bodies, and the
  other 32 have none;
* `F5_singular`: of the ten cells whose cores rest on Singular alone, the cell 122 of class 30 has no clique and the
  other nine have one;
* `F5_cc`: the classes 3, 128, 14, 30, 124, 143, 127, 31, 132, 147, 133 contain the diagrams 7, 11, 14, 16, 64, 66,
  88, 89, 93, 94, 98 of Chang and Chen, and the class of each open cell in `open43.tsv` contains the diagram listed
  with it;
* `rank_unit_vectors`: `rank` gives the dimension of the span of any set of vectors `e_t` together with, or without,
  the vector `𝟙` in `ℚ^3` and `ℚ^4`, the only vectors that occur in Corollary 5.8.
-/

namespace L6F5

open Data

/-- The census of the 191 classes, the class `c` at the position `c`: `⟨cells, clique, three, four, forced⟩`. -/
def table : List Tally :=
  [⟨17, 0, 0, 0, 17⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨44247, 44247, 44247, 0, 44247⟩, ⟨177, 177, 177, 0, 177⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0⟩, ⟨10, 0, 0, 0, 10⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1⟩, ⟨865, 715, 715, 0, 865⟩, ⟨42, 0, 0, 0, 42⟩, ⟨28, 0, 0, 0, 28⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨13, 0, 0, 0, 13⟩, ⟨0, 0, 0, 0, 0⟩, ⟨2, 0, 0, 0, 2⟩,
   ⟨239, 0, 0, 0, 239⟩, ⟨72, 0, 0, 0, 72⟩, ⟨88, 0, 0, 0, 88⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨3, 0, 0, 0, 3⟩,
   ⟨1866, 0, 0, 0, 1866⟩, ⟨273, 0, 0, 0, 273⟩, ⟨49, 0, 0, 0, 49⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 1⟩,
   ⟨1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨394, 394, 394, 0, 394⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨20, 20, 20, 0, 20⟩, ⟨0, 0, 0, 0, 0⟩, ⟨154, 154, 154, 0, 154⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨497, 497, 497, 0, 497⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨3, 3, 3, 0, 3⟩, ⟨0, 0, 0, 0, 0⟩, ⟨24, 24, 24, 0, 24⟩, ⟨37, 0, 0, 0, 37⟩, ⟨2, 0, 0, 0, 2⟩, ⟨2, 0, 0, 0, 2⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨14, 0, 0, 0, 14⟩, ⟨7, 0, 0, 0, 7⟩, ⟨162, 0, 0, 0, 162⟩,
   ⟨1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1⟩, ⟨2, 0, 0, 0, 2⟩, ⟨0, 0, 0, 0, 0⟩, ⟨2, 0, 0, 0, 2⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨1, 1, 0, 1, 1⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨21, 0, 0, 0, 21⟩, ⟨2, 0, 0, 0, 2⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨1, 0, 0, 0, 1⟩, ⟨2, 0, 0, 0, 2⟩, ⟨1, 0, 0, 0, 1⟩, ⟨10, 0, 0, 0, 10⟩, ⟨1, 0, 0, 0, 1⟩, ⟨143, 95, 0, 95, 143⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨27, 0, 0, 0, 27⟩, ⟨9, 0, 0, 0, 9⟩, ⟨32864, 32864, 32864, 0, 32864⟩, ⟨1449, 1449, 1449, 0, 1449⟩,
   ⟨630, 441, 441, 0, 630⟩, ⟨196, 0, 0, 0, 196⟩, ⟨147, 0, 0, 0, 147⟩, ⟨49, 0, 0, 0, 49⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨297, 0, 0, 0, 297⟩, ⟨77, 0, 0, 0, 77⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨81, 0, 0, 0, 81⟩,
   ⟨63, 0, 0, 0, 63⟩, ⟨4777, 4777, 4777, 0, 4777⟩, ⟨756, 756, 756, 0, 756⟩, ⟨224, 224, 224, 0, 224⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨72, 72, 72, 0, 72⟩, ⟨0, 0, 0, 0, 0⟩, ⟨18, 18, 18, 0, 18⟩,
   ⟨9, 9, 9, 0, 9⟩, ⟨19, 0, 0, 0, 19⟩, ⟨6, 0, 0, 0, 6⟩, ⟨1, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨1, 1, 1, 0, 1⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
   ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩]

set_option profiler true in
/-- **The census of the stored cells is `table`.** -/
theorem census_table : census n6 files = some table := by native_decide

/-- The classes with at least one cell, all of whose cells have a clique as in Corollary 5.8. -/
def fullClasses (t : List Tally) : List Nat :=
  (List.range t.length).filter fun c =>
    0 < (t.getD c default).cells && (t.getD c default).clique == (t.getD c default).cells

/-- **Proposition 5.9.** Of the 91,273 stored cells of the 191 classes, 86,938 have a clique as in Corollary 5.8 and
4,335 do not. All cells of 18 classes have one, among them all 44,247 cells of class 3 (diagram 7 of Chang and Chen,
`F5_cc`) and all 32,864 cells of class 128 (diagram 11). -/
theorem F5_main :
    ∃ t : List Tally, census n6 files = some t ∧ t.length = 191 ∧
      (t.map (·.cells)).sum = 91273 ∧ (t.map (·.clique)).sum = 86938 ∧
      (t.map fun r => r.cells - r.clique).sum = 4335 ∧
      fullClasses t = [3, 4, 40, 42, 44, 47, 53, 55, 84, 128, 129, 148, 149, 150, 167, 169, 170, 183] ∧
      (t.getD 3 default).cells = 44247 ∧ (t.getD 3 default).clique = 44247 ∧
      (t.getD 128 default).cells = 32864 ∧ (t.getD 128 default).clique = 32864 :=
  ⟨table, census_table, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The cells with a clique of three bodies and with a clique of four bodies: 86,842 and 96, and no cell has both,
so that 96 cells have a clique of four bodies only. Also: 69 classes have cells. -/
theorem F5_three_four :
    ∃ t : List Tally, census n6 files = some t ∧
      (t.map (·.three)).sum = 86842 ∧ (t.map (·.four)).sum = 96 ∧
      t.all (fun r => r.clique == r.three + r.four) = true ∧ (t.filter (0 < ·.cells)).length = 69 :=
  ⟨table, census_table, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- In every stored cell, the argmin set of each equation of a body with a stroke or a circle in its colour is the
set of terms forced by the diagram (`forcedOK`). -/
theorem F5_forced :
    ∃ t : List Tally, census n6 files = some t ∧ t.all (fun r => r.forced == r.cells) = true :=
  ⟨table, census_table, by decide +kernel⟩

/-- The status of the 43 open cells of `open43.tsv`: (class, diagram of Chang and Chen, cell, status). -/
def openTable : List (Nat × Nat × Nat × Status) :=
  [(31, 89, 22, ⟨false, false, false⟩), (124, 64, 0, ⟨true, false, true⟩), (124, 64, 16, ⟨true, false, true⟩),
   (124, 64, 17, ⟨true, false, true⟩), (124, 64, 30, ⟨true, false, true⟩), (124, 64, 46, ⟨true, false, true⟩),
   (124, 64, 83, ⟨true, false, true⟩), (124, 64, 105, ⟨true, false, true⟩), (124, 64, 109, ⟨true, false, true⟩),
   (124, 64, 110, ⟨true, false, true⟩), (124, 64, 111, ⟨true, false, true⟩), (124, 64, 121, ⟨true, false, true⟩),
   (132, 93, 53, ⟨false, false, false⟩), (133, 98, 17, ⟨false, false, false⟩), (127, 88, 0, ⟨false, false, false⟩),
   (127, 88, 1, ⟨false, false, false⟩), (127, 88, 2, ⟨false, false, false⟩), (127, 88, 3, ⟨false, false, false⟩),
   (127, 88, 4, ⟨false, false, false⟩), (127, 88, 5, ⟨false, false, false⟩), (127, 88, 6, ⟨false, false, false⟩),
   (127, 88, 7, ⟨false, false, false⟩), (127, 88, 8, ⟨false, false, false⟩), (147, 94, 5, ⟨false, false, false⟩),
   (147, 94, 11, ⟨false, false, false⟩), (147, 94, 17, ⟨false, false, false⟩), (147, 94, 23, ⟨false, false, false⟩),
   (147, 94, 29, ⟨false, false, false⟩), (147, 94, 35, ⟨false, false, false⟩), (147, 94, 41, ⟨false, false, false⟩),
   (147, 94, 47, ⟨false, false, false⟩), (147, 94, 53, ⟨false, false, false⟩), (143, 66, 3, ⟨false, false, false⟩),
   (143, 66, 13, ⟨false, false, false⟩), (143, 66, 14, ⟨false, false, false⟩), (143, 66, 23, ⟨false, false, false⟩),
   (143, 66, 29, ⟨false, false, false⟩), (143, 66, 35, ⟨false, false, false⟩), (143, 66, 47, ⟨false, false, false⟩),
   (143, 66, 53, ⟨false, false, false⟩), (143, 66, 59, ⟨false, false, false⟩), (143, 66, 65, ⟨false, false, false⟩),
   (143, 66, 71, ⟨false, false, false⟩)]

set_option profiler true in
/-- **The status of the open cells is `openTable`.** -/
theorem open_status : openStatus n6 files open43 = some openTable := by native_decide

/-- **The open cells.** Of the 43 cells of `open43.tsv` (Proposition 5.3), the 11 cells of class 124 (diagram 64)
have a clique as in Corollary 5.8, each one of four bodies, and the other 32 have none. -/
theorem F5_open :
    ∃ t : List (Nat × Nat × Nat × Status), openStatus n6 files open43 = some t ∧ t.length = 43 ∧
      (t.filter (·.2.2.2.clique)).map (fun r => (r.1, r.2.1, r.2.2.1)) =
        [(124, 64, 0), (124, 64, 16), (124, 64, 17), (124, 64, 30), (124, 64, 46), (124, 64, 83), (124, 64, 105),
          (124, 64, 109), (124, 64, 110), (124, 64, 111), (124, 64, 121)] ∧
      (t.filter (·.2.2.2.clique)).all (·.2.2.2.four) = true ∧ (t.filter fun r => !r.2.2.2.clique).length = 32 :=
  ⟨openTable, open_status, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The ten cells whose cores rest on Singular alone (Section 9 of the paper): the cells 8722, 13414, 17222, 24695,
31349, 41091, 41143 and 41569 of class 3 (diagram 7), the cell 218 of class 14 (diagram 14) and the cell 122 of
class 30 (diagram 16). -/
def singularOnly : List (Nat × Nat) :=
  [(3, 8722), (3, 13414), (3, 17222), (3, 24695), (3, 31349), (3, 41091), (3, 41143), (3, 41569), (14, 218), (30, 122)]

set_option profiler true in
/-- **The cells whose cores rest on Singular alone.** The cell 122 of class 30 has no clique as in Corollary 5.8;
the other nine have one, of three bodies. -/
theorem F5_singular :
    singularOnly.map (fun q => cellStatus n6 files q.1 q.2) =
      [some ⟨true, true, false⟩, some ⟨true, true, false⟩, some ⟨true, true, false⟩, some ⟨true, true, false⟩,
        some ⟨true, true, false⟩, some ⟨true, true, false⟩, some ⟨true, true, false⟩, some ⟨true, true, false⟩,
        some ⟨true, true, false⟩, some ⟨false, false, false⟩] := by native_decide

set_option profiler true in
/-- **The numbering of Chang and Chen.** The diagrams 7, 11, 14, 16, 64, 66, 88, 89, 93, 94 and 98 of Chang and Chen
(`data/f1/chang_chen_117.txt`, as read by the family F1) lie in the orbits of the representatives of the classes 3,
128, 14, 30, 124, 143, 127, 31, 132, 147 and 133, and the diagram listed with each open cell in `open43.tsv` lies in
the orbit of its class. -/
theorem F5_cc :
    [(7, 3), (11, 128), (14, 14), (16, 30), (64, 124), (66, 143), (88, 127), (89, 31), (93, 132), (94, 147),
      (98, 133)].all (fun p => ccInClass L6F1.ccData n6 p.1 p.2) = true ∧
    openTable.all (fun r => ccInClass L6F1.ccData n6 r.2.1 r.1) = true := by native_decide

/-- The subsets of `0, …, k - 1`, as increasing lists. -/
def allSubsets (k : Nat) : List (List Nat) := (List.range (k + 1)).flatMap fun j => choose j (List.range k)

/-- **The rank of the vectors of Corollary 5.8.** For `k = 3, 4`, every set `F` of coordinates and both values of
`one`, the rank of the vectors `e_t` (`t ∈ F`) of `ℚ^k`, together with `𝟙` if `one`, is `k` if `one` and `F` is
everything, and `|F| + [one]` otherwise; these are the dimensions of the spans of these vectors. -/
theorem rank_unit_vectors :
    [3, 4].all (fun k => (allSubsets k).all fun F => [false, true].all fun one =>
      rank k ((F.map (unitVec (List.range k))) ++ (if one then [(List.range k).map fun _ => 1] else [])) ==
        (if one && F.length == k then k else F.length + (if one then 1 else 0))) = true := by decide +kernel

end L6F5
