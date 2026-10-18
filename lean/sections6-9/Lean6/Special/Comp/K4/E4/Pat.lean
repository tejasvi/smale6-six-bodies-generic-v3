import Lean6.Special.Comp.K4.E4.Mac

/-!
# The finite checks in the proof of Lemma 7.7 (no Mathlib)

Patterns `ε_{kl} = j^{e_{kl}}` are lists `v` of the six exponents `e ∈ ℤ/3` on the pairs `01, 02, 03, 12, 13, 23`
(`patsF`); sign patterns `σ` are lists `w` of the six signs `σ_{kl}`, `k < l` (`patsG`). Each theorem is a check run by
`native_decide`:

* `free`, `orbit_size`, `inv_invariant`, `inv_separates`, `nine_values`: the substitutions
  `e′_{kl} = e_{kl} − c_k − c_l` (`act`) act freely, each orbit has 81 patterns, and the triple
  `(e₁₂ + e₃₄, e₁₃ + e₂₄, e₁₄ + e₂₃)` modulo `(1, 1, 1)` (`inv`) is constant on orbits, separates them and takes 9
  values, so there are 9 orbits;
* `relabel_triple`, `conj_triple`: a relabelling of the bodies permutes the entries of the triple (the same
  permutation for every pattern) and `e ↦ −e` negates it;
* `reduction`: every pattern is carried by a substitution, a relabelling and possibly `e ↦ −e` to one of the three
  patterns of types (I), (II), (III), whose triples are `(0,0,0)`, `(0,0,1)`, `(0,1,2)` (`rep_triples`);
* `score_counts`, `score_determines`, `reduce_tournaments`, `rep_scores`: the 64 tournaments have the score
  sequences `(3,2,1,0)`, `(3,1,1,1)`, `(2,2,2,0)`, `(2,2,1,1)` with 24, 8, 8, 24 members; two tournaments with the
  same score sequence differ by a relabelling; up to relabelling and `σ ↦ −σ` every tournament is `T1`, `T2` or `T3`.
-/

namespace Lean6.Special.Comp.E4

/-- The bodies of the pair with index `i` (order `01, 02, 03, 12, 13, 23`). -/
def pairFst (i : Nat) : Nat := if i < 3 then 0 else if i < 5 then 1 else 2

def pairSnd (i : Nat) : Nat := if i < 3 then i + 1 else if i < 5 then i - 1 else 3

/-- All 81 substitutions `c ∈ (ℤ/3)^4`. -/
def subs : List (List Nat) := (List.range 81).map fun c => (List.range 4).map fun i => c / 3 ^ i % 3

/-- All 24 relabellings, as lists of images. -/
def perms : List (List Nat) :=
  ((List.range 256).map fun c => (List.range 4).map fun i => c / 4 ^ i % 4).filter fun π =>
    (List.range 4).all fun k => π.contains k

/-- The 6 permutations of `{0, 1, 2}`. -/
def perms3 : List (List Nat) := [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

/-- The substitution `e′_{kl} = e_{kl} − c_k − c_l`. -/
def act (c v : List Nat) : List Nat :=
  (List.range 6).map fun i => (v.getD i 0 + 6 - c.getD (pairFst i) 0 - c.getD (pairSnd i) 0) % 3

/-- The pattern `e ↦ s e` (`s = 2` is `e ↦ −e`). -/
def scale (s : Nat) (v : List Nat) : List Nat := v.map fun x => s * x % 3

/-- The relabelled pattern `e′_{kl} = e_{π k, π l}`. -/
def relabel (π v : List Nat) : List Nat :=
  (List.range 6).map fun i => v.getD (pairIdx (π.getD (pairFst i) 0) (π.getD (pairSnd i) 0)) 0

/-- The triple `(e₁₂ + e₃₄, e₁₃ + e₂₄, e₁₄ + e₂₃)`. -/
def triple (v : List Nat) : List Nat := [(v.getD 0 0 + v.getD 5 0) % 3, (v.getD 1 0 + v.getD 4 0) % 3,
  (v.getD 2 0 + v.getD 3 0) % 3]

/-- The triple modulo `(1, 1, 1)`. -/
def inv (v : List Nat) : List Nat := let t := triple v; t.map fun x => (x + 3 - t.getD 0 0) % 3

/-- The patterns of types (I), (II), (III) of the paper. -/
def repI : List Nat := [0, 0, 0, 0, 0, 0]
def repII : List Nat := [0, 0, 1, 0, 0, 0]
def repIII : List Nat := [0, 2, 1, 1, 2, 0]

theorem free : patsF.all (fun v => subs.all fun c => act c v != v || c == [0, 0, 0, 0]) = true := by native_decide

theorem orbit_size : patsF.all (fun v => (subs.map (act · v)).eraseDups.length == 81) = true := by native_decide

theorem inv_invariant : patsF.all (fun v => subs.all fun c => inv (act c v) == inv v) = true := by native_decide

theorem inv_separates :
    patsF.all (fun v => patsF.all fun v' => inv v != inv v' || subs.any fun c => act c v == v') = true := by
  native_decide

theorem nine_values : (patsF.map inv).eraseDups.length = 9 := by native_decide

theorem perms_count : perms.length = 24 := by native_decide

/-- For each relabelling one permutation `τ` of the three entries with `triple (relabel π v) = τ (triple v)`. -/
theorem relabel_triple : perms.all (fun π => perms3.any fun τ =>
    patsF.all fun v => triple (relabel π v) == (List.range 3).map fun i => (triple v).getD (τ.getD i 0) 0) = true := by
  native_decide

theorem conj_triple : patsF.all (fun v => triple (scale 2 v) == (triple v).map fun x => 2 * x % 3) = true := by
  native_decide

theorem rep_triples : triple repI = [0, 0, 0] ∧ triple repII = [0, 0, 1] ∧ triple repIII = [0, 1, 2] := by decide

theorem reduction : patsF.all (fun v => perms.any fun π => [1, 2].any fun s => subs.any fun c =>
    [repI, repII, repIII].contains (act c (scale s (relabel π v)))) = true := by native_decide

/-! ## Tournaments -/

/-- The out-degrees, sorted decreasingly. -/
def scoreSeq (w : List Int) : List Nat :=
  ((List.range 4).map fun k => ((List.range 4).filter fun l => l != k && sigmaOf w k l == 1).length).mergeSort
    fun a b => b ≤ a

/-- The relabelled sign pattern `σ′_{kl} = σ_{π k, π l}`. -/
def relabelG (π : List Nat) (w : List Int) : List Int :=
  (List.range 6).map fun i => sigmaOf w (π.getD (pairFst i) 0) (π.getD (pairSnd i) 0)

/-- `T1`, `T2` (`σ₂₄ = −1`), `T3` (`σ₁₄ = −1`). -/
def wT1 : List Int := [1, 1, 1, 1, 1, 1]
def wT2 : List Int := [1, 1, 1, 1, -1, 1]
def wT3 : List Int := [1, 1, -1, 1, 1, 1]

theorem score_counts :
    ([[3, 2, 1, 0], [3, 1, 1, 1], [2, 2, 2, 0], [2, 2, 1, 1]].map fun sc => (patsG.filter (scoreSeq · == sc)).length) =
      [24, 8, 8, 24] := by native_decide

theorem score_determines : patsG.all (fun w => patsG.all fun w' =>
    scoreSeq w != scoreSeq w' || perms.any fun π => relabelG π w == w') = true := by native_decide

theorem reduce_tournaments : patsG.all (fun w => perms.any fun π => [1, -1].any fun s =>
    [wT1, wT2, wT3].contains ((relabelG π w).map (s * ·))) = true := by native_decide

theorem rep_scores : scoreSeq wT1 = [3, 2, 1, 0] ∧ scoreSeq wT2 = [3, 1, 1, 1] ∧ scoreSeq wT3 = [2, 2, 1, 1] := by
  native_decide

end Lean6.Special.Comp.E4
