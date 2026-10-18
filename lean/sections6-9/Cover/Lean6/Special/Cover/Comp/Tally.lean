import Lean6.Special.Cover.Comp.Every
import Lean6.Special.Cover.Comp.Generic
import Lean6.Special.Cover.Comp.Lines

/-!
# Proposition 9.23: the first group of (b) and the lemmas at every positive mass

For each stored cell, the tests of the lemmas of the first group of Proposition 9.23(b), in this order:

| index | test | statement |
|---|---|---|
| 0–5 | `Every.lemT`, `lemP`, `lemC`, `lemB0`, `lemK`, `lemL` | Lemmas 9.2–9.7 (every positive mass) |
| 6 | `Generic.lemE` | the class-level case after Corollary 9.10 |
| 7 | `Generic.lemE1` | Corollary 9.10 |
| 8, 9 | `Generic.lemRa`, `lemRb` | Lemma 9.11 (a), (b) |
| 10 | `Generic.lemR6` | Lemma 9.12 |
| 11, 12 | `Lines.lemW3`, `lemEQ2` | Lemmas 9.13, 9.14 |
| 13 | `Generic.lemQ` | Lemma 9.15 |
| 14 | `Generic.lemClique3` | Corollary 9.18 for a clique of three bodies |

`tally` counts, over all stored cells: the cells; those with one of Lemmas 9.2–9.7 (Proposition 9.23(a): "70,233 by
Lemmas 9.2–9.7"); those with one of the first group of (b); the same without Corollary 9.18; the cells that Corollary
9.18 adds, by class; the cells in which Lemma 9.13, resp. 9.14, is the only test of the first group that holds, and
whether in each of them the polynomial of the lemma (`H_W`, resp. `m_a² M_A⁴ − m_b² M_B⁴`) and `g` are nonzero at
`m = (1, …, 6)` (`Lines.w3NonzeroAtM0`, `Lines.eq2NonzeroAtM0`); and the number of cells for each test.
-/

namespace Lean6.Special.Cover

open L6.F34

/-- The tests of the first group of Proposition 9.23(b) in a cell (order of the table above). -/
def firstFlags (c : CCell) : List Bool :=
  [Every.lemT c.x, Every.lemP c.x c.d, Every.lemC c.x, Every.lemB0 c.x, Every.lemK c.x, Every.lemL c.x,
   Generic.lemE c.d, Generic.lemE1 c.x, Generic.lemRa c.x, Generic.lemRb c.x, Generic.lemR6 c.x,
   Lines.lemW3 c.x, Lines.lemEQ2 c.x, Generic.lemQ c.x, Generic.lemClique3 c.x c.d]

/-- The counts of Proposition 9.23 about the first group of (b). -/
structure Tally where
  /-- the stored cells -/
  cells : Nat
  /-- the cells with one of Lemmas 9.2–9.7 -/
  every : Nat
  /-- the cells with one of the tests of the first group -/
  first : Nat
  /-- the cells with one of the tests of the first group other than Corollary 9.18 -/
  firstNoClique : Nat
  /-- the cells in which Corollary 9.18 is the only test of the first group that holds: `(class, number)` -/
  cliqueOnly : List (Nat × Nat)
  /-- the cells in which Lemma 9.13 is the only test of the first group that holds -/
  w3Only : Nat
  /-- the cells in which Lemma 9.14 is the only test of the first group that holds -/
  eq2Only : Nat
  /-- in each of the cells of `w3Only`, `g` and `H_W` are nonzero at `m = (1, …, 6)` at every instance -/
  w3OnlyNonzero : Bool
  /-- in each of the cells of `eq2Only`, `g` and `m_a² M_A⁴ − m_b² M_B⁴` are nonzero at `m = (1, …, 6)` -/
  eq2OnlyNonzero : Bool
  /-- the number of cells in which each test holds (order of the table above) -/
  perTest : List Nat
  deriving DecidableEq, Repr

/-- The cells of `l` with the class `c`, counted, for the classes that occur (increasing). -/
def byClass (l : List Nat) : List (Nat × Nat) :=
  (l.eraseDups.mergeSort (· ≤ ·)).map fun c => (c, (l.filter (· == c)).length)

/-- The only test that holds is the one at index `i`. -/
def onlyAt (f : List Bool) (i : Nat) : Bool :=
  f.getD i false && ((List.range f.length).all fun j => j == i || !f.getD j false)

/-- **The counts of Proposition 9.23 about the first group of (b).** -/
def tally (cs : Array CCell) : Tally :=
  let fl := cs.toList.map fun c => (c, firstFlags c)
  let w3o := fl.filter fun (_, f) => onlyAt f 11
  let eq2o := fl.filter fun (_, f) => onlyAt f 12
  { cells := fl.length
    every := (fl.filter fun (_, f) => (f.take 6).any id).length
    first := (fl.filter fun (_, f) => f.any id).length
    firstNoClique := (fl.filter fun (_, f) => (f.take 14).any id).length
    cliqueOnly := byClass ((fl.filter fun (_, f) => onlyAt f 14).map (·.1.cls))
    w3Only := w3o.length
    eq2Only := eq2o.length
    w3OnlyNonzero := w3o.all fun (c, _) => Lines.w3NonzeroAtM0 c.x
    eq2OnlyNonzero := eq2o.all fun (c, _) => Lines.eq2NonzeroAtM0 c.x
    perTest := (List.range 15).map fun i => (fl.filter fun (_, f) => f.getD i false).length }

end Lean6.Special.Cover
