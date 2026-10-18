import Lean6.Special.K4.C4.Defs
import Lean6.Special.K4.C4.GBSound
import Lean6.Special.Comp.K4.C4.Run.M0P32003
import Lean6.Special.Comp.K4.C4.Run.M0P1073741789
import Lean6.Special.Comp.K4.C4.Run.M1P32003
import Lean6.Special.Comp.K4.C4.Run.M1P1073741789
import Lean6.Special.Comp.K4.C4.Prime
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Lemma 7.9 and the computation of §7.4: the compact model of `C₄` on the fourteen charts

The equations of `Z(μ)` (Section 7.3), written as in the paper over any commutative ring (`eqsZ`): with
`ξ = (μ₃ s, μ₃ t, −(μ₁ s + μ₂ t), 0)` (bodies `0, 1, 2, 3` for the paper's `1, 2, 3, 4`) and the symmetric `P_kl`,

* (I) `Σ_{l ≠ k} μ_l P_kl³ (ξ_k − ξ_l)`, `k = 1, …, 4`;
* (II) `Σ_{l ≠ k} μ_l P_kl Π_{j ≠ k, l} (ξ_k − ξ_j) − c Π_{l ≠ k} (ξ_k − ξ_l)`, `k = 1, 2, 3`;
* (III) `a_ln a_nk + a_kl a_nk + a_kl a_ln`, `a_kl = P_kl² (ξ_k − ξ_l)`, for the triangles `123, 124, 134, 234`.

A point is `x : ℕ → R` with coordinates `s = x 0`, `t = x 1`, `P₁₂, P₁₃, P₁₄, P₂₃, P₂₄, P₃₄ = x 2, …, x 7`,
`c = x 8`; a chart `(a, b)` of `Comp.C4.charts` asks `x a = 1` (`a = 0` for `s`, `1` for `t`) and `x b = 1` (`b`
among `2, …, 8`).

**`lemma_7_9`**: at `μ₀ = (3, 5, 7, 11)` and `p = 32003`, and at `p = 1073741789`, on every chart the equations have
no common zero in any nontrivial commutative `ZMod p`-algebra, and they generate the unit ideal of the polynomial ring
over `ZMod p` (`lemma_7_9_span`). **`sec_7_4`**: the same at `μ = (1, 1, 1, 1)`. The computation is the Buchberger
engine of `Comp.K4.C4.GB` (`Comp.K4.C4.Run.*`, one `native_decide` per chart), proved sound in `GBSound`. The
transfer to `ℚ` (Lemma 7.10) is not formalized.
-/

namespace Lean6.Special.K4.C4

open Lean6.Special Lean6.Special.Comp Finset


section Bridge

variable {R : Type*} [CommRing R]

theorem intHom_f (a : ℤ) : (intHom R).f a = (a : R) := rfl

/-- The integer polynomials of `Comp.C4.eqs` evaluate to the equations of the paper. -/
theorem eval_eqs (μL : List ℤ) (x : ℕ → R) :
    (C4.eqs μL).map (Poly.eval (intHom R) x) = eqsAt (muOf μL) x := by
  simp only [C4.eqs, List.map_cons, List.map_nil, eqsAt, eqsZ, eqIZ, eqIIZ, eqIIIZ, aZ, xiZ, Pm, muOf]
  simp [C4.eqI, C4.eqII, C4.eqIII, C4.aa, C4.prodD, C4.dxi, C4.xi, C4.P, C4.V, C4.K, C4.mul, C4.sub,
    C4.others, C4.pIdx, Poly.eval_sum, Poly.eval_mul, Poly.eval_sub, Poly.eval_add, Poly.eval_const, Poly.eval_var,
    intHom_f, Finset.sum_filter, Finset.prod_filter, Fin.sum_univ_four, Fin.prod_univ_four, pairIdx, List.filter]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

end Bridge

section Charts

variable {R : Type*} [CommRing R]

theorem eval_chartSub (ch : ℕ × ℕ) (x : ℕ → R) (h1 : x ch.1 = 1) (h2 : x ch.2 = 1) :
    (fun j => Poly.eval (intHom R) x (C4.chartSub ch j)) = x := by
  funext j
  unfold C4.chartSub
  by_cases hj : (j == ch.1 || j == ch.2) = true
  · rw [if_pos hj, C4.K, Poly.eval_const, intHom_f, Int.cast_one]
    simp only [Bool.or_eq_true, beq_iff_eq] at hj
    rcases hj with rfl | rfl
    · exact h1.symm
    · exact h2.symm
  · rw [if_neg hj, C4.V, Poly.eval_var]

theorem toMod_cast (p : ℕ) [NeZero p] (a : ℤ) : (((a % (p : ℤ)).toNat : ℕ) : ZMod p) = (a : ZMod p) := by
  have hp : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have h0 : 0 ≤ a % (p : ℤ) := Int.emod_nonneg a hp.ne'
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0, ZMod.intCast_mod]

theorem eval_toMod (p : ℕ) [NeZero p] [Algebra (ZMod p) R] (x : ℕ → R) (f : Poly ℤ) :
    Poly.eval (algH p R) x (C4.toMod p f) = Poly.eval (intHom R) x f := by
  induction f with
  | nil => rfl
  | cons t f ih =>
    simp only [C4.toMod, Poly.mapC, List.map_cons, Poly.eval_cons] at ih ⊢
    rw [ih, algH_f, toMod_cast, map_intCast, intHom_f]

/-- **One chart**: if the engine succeeds on the chart `ch` (masses `μL`, prime `p`), the equations have no common
zero with `x ch.1 = x ch.2 = 1` in any nontrivial commutative `ZMod p`-algebra. -/
theorem chart_no_zero (μL : List ℤ) (p : ℕ) [Fact p.Prime] [NeZero p] (ch : ℕ × ℕ)
    (hok : C4.chartOK μL p ch = true) (R : Type*) [CommRing R] [Nontrivial R] [Algebra (ZMod p) R]
    (x : ℕ → R) (h1 : x ch.1 = 1) (h2 : x ch.2 = 1) : ¬ ∀ e ∈ eqsAt (muOf μL) x, e = 0 := by
  intro hz
  apply unitTest_sound p hok R x
  intro f hf
  simp only [C4.chartEqs, List.map_map, List.mem_map, Function.comp] at hf
  obtain ⟨e, he, rfl⟩ := hf
  rw [eval_toMod, Poly.eval_subst, eval_chartSub ch x h1 h2]
  apply hz
  rw [← eval_eqs]
  exact List.mem_map_of_mem he

/-- **One chart, as a unit ideal**: the eleven equations on the chart generate the unit ideal of the polynomial
ring over `ZMod p`. -/
theorem chart_span (μL : List ℤ) (p : ℕ) [Fact p.Prime] [NeZero p] (ch : ℕ × ℕ)
    (hok : C4.chartOK μL p ch = true) :
    (1 : MvPolynomial ℕ (ZMod p)) ∈ Ideal.span {e | e ∈ eqsAt (muOf μL) (chartPt p ch)} := by
  by_contra hI
  set I := Ideal.span {e | e ∈ eqsAt (muOf μL) (chartPt p ch)}
  have hne : I ≠ ⊤ := fun h => hI (h ▸ Submodule.mem_top)
  have : Nontrivial (MvPolynomial ℕ (ZMod p) ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  apply chart_no_zero μL p ch hok (MvPolynomial ℕ (ZMod p) ⧸ I) (fun j => Ideal.Quotient.mk I (chartPt p ch j))
  · simp [chartPt]
  · simp [chartPt]
  · rw [eqsAt_map]
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span he')

end Charts

section Final

theorem trialGo_sound (n : ℕ) : ∀ (fuel d : ℕ), C4.trialGo n d fuel = true → ∀ m, d ≤ m → m * m ≤ n → ¬ m ∣ n
  | 0, d, h => by simp [C4.trialGo] at h
  | fuel + 1, d, h => by
    intro m hdm hmm hdvd
    unfold C4.trialGo at h
    by_cases h1 : n < d * d
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [if_neg h1] at h
      by_cases h2 : (n % d == 0) = true
      · rw [if_pos h2] at h
        exact absurd h (by simp)
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
        · simp only [beq_iff_eq] at h2
          exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact trialGo_sound n fuel (d + 1) h m hlt hmm hdvd

theorem prime_of_trialPrime {n : ℕ} (h : C4.trialPrime n = true) : n.Prime := by
  simp only [C4.trialPrime, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hgo⟩ := h
  by_contra hp
  have hpos : 0 < n := by omega
  have hsq := Nat.minFac_sq_le_self hpos hp
  have hmin : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
  exact trialGo_sound n n 2 hgo n.minFac hmin (by nlinarith [hsq]) (Nat.minFac_dvd n)

instance fact_prime_32003 : Fact (Nat.Prime 32003) := ⟨prime_of_trialPrime C4.trialPrime_32003⟩

instance fact_prime_1073741789 : Fact (Nat.Prime 1073741789) := ⟨prime_of_trialPrime C4.trialPrime_1073741789⟩

theorem noZero_of (μL : List ℤ) (p : ℕ) [Fact p.Prime] [NeZero p] (h : ∀ ch ∈ C4.charts, C4.chartOK μL p ch = true) :
    NoZero μL p ∧ UnitIdeal μL p :=
  ⟨fun R _ _ _ ch hch x h1 h2 => chart_no_zero μL p ch (h ch hch) R x h1 h2,
   fun ch hch => chart_span μL p ch (h ch hch)⟩

/-- **Lemma 7.9** (`lem:C4cert`): at `μ₀ = (3, 5, 7, 11)`, on each of the fourteen charts the equations of `Z(μ₀)`
generate the unit ideal over `F_32003` and over `F_1073741789` (equivalently, they have no common zero in any
nontrivial commutative algebra over these fields). -/
theorem lemma_7_9 : (NoZero [3, 5, 7, 11] 32003 ∧ UnitIdeal [3, 5, 7, 11] 32003) ∧
    (NoZero [3, 5, 7, 11] 1073741789 ∧ UnitIdeal [3, 5, 7, 11] 1073741789) :=
  ⟨noZero_of _ _ Comp.C4.Run.M0P32003.all, noZero_of _ _ Comp.C4.Run.M0P1073741789.all⟩

/-- **§7.4**: the computation of Lemma 7.9 at `μ = (1, 1, 1, 1)`, over `F_32003` (the paper's claim) and over
`F_1073741789`. -/
theorem sec_7_4 : (NoZero [1, 1, 1, 1] 32003 ∧ UnitIdeal [1, 1, 1, 1] 32003) ∧
    (NoZero [1, 1, 1, 1] 1073741789 ∧ UnitIdeal [1, 1, 1, 1] 1073741789) :=
  ⟨noZero_of _ _ Comp.C4.Run.M1P32003.all, noZero_of _ _ Comp.C4.Run.M1P1073741789.all⟩

end Final

end Lean6.Special.K4.C4
