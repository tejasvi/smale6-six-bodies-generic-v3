import CC6Full.Curve.Places6
import CC6Full.Curve.FunctionField.Places
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# `U` is constant on every curve in `Y_m`, for all masses (Lemma 2.3 (b), `lem:U`)

Lemma 2.3 (`lem:U`) (b): `U = Σ_{k<l} m_k m_l p_kl` is constant on every irreducible curve `C ⊆ Y_m`. In the
coordinates `z, w, p` of `CC6Full.Curve.System` this holds for every mass vector (the paper's proof divides by
`M = Σ_k m_k` through `U = I`; here no division is needed).

The identity. Let `V = Σ_k m_k z_k w_k`. On `X_m`, by the equations of the bodies and the distance rows,
`2V = Σ_{k ≠ l} m_k m_l p_kl³ z_kl w_kl = Σ_{k ≠ l} m_k m_l p_kl = 2U` (Lemma 2.3 (a)). For a derivation `D`, the
distance row gives `2 D p_kl = −p_kl³ (D z_kl · w_kl + z_kl · D w_kl)`, and the equations of the bodies give
`2 Σ_k m_k (D z_k · w_k + z_k · D w_k) = Σ_{k ≠ l} m_k m_l p_kl³ (D z_kl · w_kl + z_kl · D w_kl)`. Hence
`2 D U = D(2V) = −2 D U`, so `D U = 0` (`Curve.deriv_U_core`, `Curve.deriv_U_eq_zero`).

The constancy (`Curve.U_const`), as in the five-body formalization (`CC5Full/Theory/ConstU.lean`): take a place `P`
centred on `C` (`exists_place_centred`) and an expansion `ι : ℂ(C) → ℂ((t))` (`Expansion_exists`). All coordinate
functions have order `≥ 0`, so `f ↦ ι(f)` is a `ℂ`-algebra map `ℂ[Coord] → ℂ⟦t⟧` (`Curve.psAlgHom`) that kills the
rows. With `D = d/dt`, `D ι(U) = 0`, so `ι(U)` is a constant `c`, and `U − c` vanishes on `C` since `ι` is injective.

* `Curve.sum_sum_erase_swap`, `Curve.two_mul_sum_sum_erase`, `Curve.sum_sum_erase_eq_sum_pair`,
  `Curve.sum_sum_erase_eq_two_mul_sum_pair`: double sums over the ordered pairs `k ≠ l` and sums over the pairs
  `k < l`.

The auxiliary lemmas are in the namespace `CC6Full.Curve`.
-/

namespace CC6Full

open Finset MvPolynomial

noncomputable section

namespace Curve

/-! ## Double sums over ordered pairs -/

section sums

variable {N : ℕ}

/-- Exchanging the two indices of a double sum over the ordered pairs `l ≠ k`. -/
theorem sum_sum_erase_swap {R : Type*} [AddCommGroup R] (f : Fin N → Fin N → R) :
    ∑ k, ∑ l ∈ univ.erase k, f l k = ∑ k, ∑ l ∈ univ.erase k, f k l := by
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

/-- Symmetrization of a double sum over the ordered pairs. -/
theorem two_mul_sum_sum_erase {R : Type*} [CommRing R] (f : Fin N → Fin N → R) :
    2 * ∑ k, ∑ l ∈ univ.erase k, f k l = ∑ k, ∑ l ∈ univ.erase k, (f k l + f l k) := by
  rw [two_mul]
  conv_lhs => arg 2; rw [← sum_sum_erase_swap f]
  simp only [← Finset.sum_add_distrib]

/-- A double sum over the ordered pairs `k ≠ l` as a sum over the pairs `k < l`. -/
theorem sum_sum_erase_eq_sum_pair {R : Type*} [AddCommMonoid R] (f : Fin N → Fin N → R) :
    ∑ k, ∑ l ∈ univ.erase k, f k l = ∑ e : Pair N, (f e.1.1 e.1.2 + f e.1.2 e.1.1) := by
  have h1 : ∀ g : Fin N → Fin N → R,
      ∑ e : Pair N, g e.1.1 e.1.2 = ∑ k, ∑ l, if k < l then g k l else 0 := by
    intro g
    rw [← Finset.sum_subtype (univ.filter fun x : Fin N × Fin N => x.1 < x.2) (by simp)
      (fun x => g x.1 x.2), Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_add_distrib, h1 f, h1 (fun k l => f l k),
    Finset.sum_comm (f := fun k l => if k < l then f l k else 0), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.add_sum_erase univ _ (Finset.mem_univ k)]
  simp only [lt_irrefl, ite_false, add_zero, zero_add]
  refine Finset.sum_congr rfl fun l hl => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with h | h
  · simp [h, not_lt.mpr h.le]
  · simp [h, not_lt.mpr h.le]

/-- For a symmetric `f`, the double sum over the ordered pairs is twice the sum over the pairs. -/
theorem sum_sum_erase_eq_two_mul_sum_pair {R : Type*} [CommSemiring R] (f : Fin N → Fin N → R)
    (hf : ∀ k l, f k l = f l k) : ∑ k, ∑ l ∈ univ.erase k, f k l = 2 * ∑ e : Pair N, f e.1.1 e.1.2 := by
  rw [sum_sum_erase_eq_sum_pair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hf e.1.2 e.1.1, two_mul]

end sums

/-! ## Lemma 2.3 (b) in derivation form -/

section deriv

variable {N : ℕ} {R : Type*} [CommRing R] [Algebra ℂ R]

theorem eq_zero_of_ofNat_mul_eq_zero (k : ℕ) [k.AtLeastTwo] {x : R} (h : (OfNat.ofNat k : R) * x = 0) : x = 0 := by
  have hk : (OfNat.ofNat k : ℂ) ≠ 0 := by simp
  have e : algebraMap ℂ R (OfNat.ofNat k)⁻¹ * ((OfNat.ofNat k : R) * x) = x := by
    rw [← mul_assoc, ← map_ofNat (algebraMap ℂ R) k, ← map_mul, inv_mul_cancel₀ hk, map_one, one_mul]
  rw [h, mul_zero] at e
  exact e.symm

/-- **The derivation identity behind Lemma 2.3 (b)**, for abstract `z_k`, `w_k`, `p_kl` satisfying the equations of the
bodies and the distance equations, and constants `μ_k` (`D μ_k = 0`): `D (Σ_{k ≠ l} μ_k μ_l p_kl) = 0`. -/
theorem deriv_U_core (d : Derivation ℂ R R) (μ z w : Fin N → R) (q : Fin N → Fin N → R)
    (hμ : ∀ k, d (μ k) = 0) (hq : ∀ k l, q k l = q l k)
    (hZ : ∀ k, z k = ∑ l ∈ univ.erase k, μ l * q k l ^ 3 * (z k - z l))
    (hW : ∀ k, w k = ∑ l ∈ univ.erase k, μ l * q k l ^ 3 * (w k - w l))
    (hD : ∀ k l, k ≠ l → q k l ^ 2 * (z k - z l) * (w k - w l) = 1) :
    d (∑ k, ∑ l ∈ univ.erase k, μ k * μ l * q k l) = 0 := by
  set S := ∑ k, ∑ l ∈ univ.erase k, μ k * μ l * q k l with hS
  -- the derivative of a distance row: `2 D p = −p³ (D z_kl · w_kl + z_kl · D w_kl)`
  have hdD : ∀ k l, k ≠ l → 2 * d (q k l) =
      -(q k l ^ 3 * ((d (z k) - d (z l)) * (w k - w l) + (z k - z l) * (d (w k) - d (w l)))) := by
    intro k l hkl
    have h0 : d (q k l ^ 2 * (z k - z l) * (w k - w l)) = 0 := by
      rw [hD k l hkl, Derivation.map_one_eq_zero]
    rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_sub] at h0
    simp only [smul_eq_mul, nsmul_eq_mul] at h0
    norm_num at h0
    linear_combination q k l * h0 - 2 * d (q k l) * hD k l hkl
  -- `2 Σ_k μ_k z_k w_k = S` (Lemma 2.3 (a))
  have hF : ∀ k, μ k * z k * w k = ∑ l ∈ univ.erase k, μ k * μ l * q k l ^ 3 * (z k - z l) * w k := by
    intro k
    conv_lhs => rw [hZ k]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hV : 2 * ∑ k, μ k * z k * w k = S := by
    rw [Finset.sum_congr rfl fun k _ => hF k, two_mul_sum_sum_erase]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l hl => ?_
    have hkl : k ≠ l := (Finset.ne_of_mem_erase hl).symm
    rw [hq l k]
    linear_combination μ k * μ l * q k l * hD k l hkl
  -- `Σ_k μ_k (D z_k · w_k + z_k · D w_k)` as a double sum
  have hG : ∀ k, μ k * (d (z k) * w k + z k * d (w k)) =
      ∑ l ∈ univ.erase k, μ k * μ l * q k l ^ 3 * ((w k - w l) * d (z k) + (z k - z l) * d (w k)) := by
    intro k
    have e1 : μ k * (d (z k) * w k + z k * d (w k)) =
        μ k * (d (z k) * (∑ l ∈ univ.erase k, μ l * q k l ^ 3 * (w k - w l)) +
          (∑ l ∈ univ.erase k, μ l * q k l ^ 3 * (z k - z l)) * d (w k)) := by
      rw [← hW k, ← hZ k]
    rw [e1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hdS : d S = ∑ k, ∑ l ∈ univ.erase k, μ k * μ l * d (q k l) := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Derivation.leibniz, Derivation.leibniz, hμ, hμ]
    simp only [smul_eq_mul]
    ring
  have hdV : 2 * ∑ k, μ k * (d (z k) * w k + z k * d (w k)) = -(2 * d S) := by
    rw [Finset.sum_congr rfl fun k _ => hG k, two_mul_sum_sum_erase, hdS, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hkl : k ≠ l := (Finset.ne_of_mem_erase hl).symm
    rw [hq l k]
    linear_combination μ k * μ l * hdD k l hkl
  have hdsum : d (∑ k, μ k * z k * w k) = ∑ k, μ k * (d (z k) * w k + z k * d (w k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.leibniz, Derivation.leibniz, hμ]
    simp only [smul_eq_mul]
    ring
  have e2 : d S = 2 * d (∑ k, μ k * z k * w k) := by
    rw [← hV, two_mul, map_add, two_mul]
  rw [hdsum] at e2
  have h3 : (3 : R) * d S = 0 := by linear_combination e2 + hdV
  exact eq_zero_of_ofNat_mul_eq_zero 3 h3

/-- The distance row of an ordered pair `k ≠ l` is a row. -/
theorem exists_rowD_eq {k l : Fin N} (h : k ≠ l) :
    ∃ e : Pair N, rowD e = pP k l ^ 2 * (zP k - zP l) * (wP k - wP l) - 1 := by
  rcases lt_or_gt_of_ne h with h' | h'
  · exact ⟨⟨(k, l), h'⟩, by rw [pP_of_lt h']; rfl⟩
  · refine ⟨⟨(l, k), h'⟩, ?_⟩
    rw [pP_of_gt h']
    simp only [rowD]
    ring

/-- **Lemma 2.3 (b) in derivation form**: if a `ℂ`-algebra map `Ψ : ℂ[Coord] → R` kills the rows, then `D Ψ(U) = 0`
for every derivation `D` of `R`. No condition on the masses. -/
theorem deriv_U_eq_zero (d : Derivation ℂ R R) (Ψ : Poly N →ₐ[ℂ] R) (m : Fin N → ℝ)
    (hrows : ∀ f ∈ rows m, Ψ f = 0) : d (Ψ (Upoly m)) = 0 := by
  have hC : ∀ c : ℂ, Ψ (MvPolynomial.C c) = algebraMap ℂ R c := fun c => Ψ.commutes c
  have hZ : ∀ k, Ψ (zP k) = ∑ l ∈ univ.erase k,
      algebraMap ℂ R (m l) * Ψ (pP k l) ^ 3 * (Ψ (zP k) - Ψ (zP l)) := by
    intro k
    have h := hrows _ (rowZ_mem_rows m k)
    simp only [rowZ, map_sub, map_sum, map_mul, map_pow, hC] at h
    exact sub_eq_zero.mp h
  have hW : ∀ k, Ψ (wP k) = ∑ l ∈ univ.erase k,
      algebraMap ℂ R (m l) * Ψ (pP k l) ^ 3 * (Ψ (wP k) - Ψ (wP l)) := by
    intro k
    have h := hrows _ (rowW_mem_rows m k)
    simp only [rowW, map_sub, map_sum, map_mul, map_pow, hC] at h
    exact sub_eq_zero.mp h
  have hD : ∀ k l, k ≠ l → Ψ (pP k l) ^ 2 * (Ψ (zP k) - Ψ (zP l)) * (Ψ (wP k) - Ψ (wP l)) = 1 := by
    intro k l hkl
    obtain ⟨e, he⟩ := exists_rowD_eq hkl
    have h := hrows _ (rowD_mem_rows m e)
    rw [he] at h
    simp only [map_sub, map_mul, map_pow, map_one] at h
    exact sub_eq_zero.mp h
  have hcore := deriv_U_core d (fun k => algebraMap ℂ R (m k)) (fun k => Ψ (zP k)) (fun k => Ψ (wP k))
    (fun k l => Ψ (pP k l)) (fun k => d.map_algebraMap _) (fun k l => by simp only [pP_comm k l]) hZ hW hD
  have hU : 2 * Ψ (Upoly m) =
      ∑ k, ∑ l ∈ univ.erase k, algebraMap ℂ R (m k) * algebraMap ℂ R (m l) * Ψ (pP k l) := by
    rw [sum_sum_erase_eq_two_mul_sum_pair _ (fun k l => by rw [pP_comm k l]; ring)]
    congr 1
    simp only [Upoly, map_sum, map_mul, hC, pP_pair, Complex.ofReal_mul]
  have h2 : (2 : R) * d (Ψ (Upoly m)) = 0 := by
    rw [two_mul, ← map_add, ← two_mul, hU]
    exact hcore
  exact eq_zero_of_ofNat_mul_eq_zero 2 h2

end deriv

/-! ## `U` is constant on every curve -/

/-- The power series of a Laurent series without negative terms. -/
def laurentToPS (x : LaurentSeries ℂ) : PowerSeries ℂ := PowerSeries.mk fun k => x.coeff k

theorem ofPowerSeries_laurentToPS {x : LaurentSeries ℂ} (hx : ∀ k : ℤ, k < 0 → x.coeff k = 0) :
    HahnSeries.ofPowerSeries ℤ ℂ (laurentToPS x) = x := by
  ext k
  rw [PowerSeries.coeff_coe]
  split_ifs with h
  · exact (hx k h).symm
  · simp only [laurentToPS, PowerSeries.coeff_mk]
    congr 1
    omega

/-- A ring hom `ℂ[σ] → ℂ((t))` without negative terms that is the identity on `ℂ`, as a `ℂ`-algebra map into
`ℂ⟦t⟧`. -/
def psAlgHom {σ : Type*} (L : MvPolynomial σ ℂ →+* LaurentSeries ℂ)
    (hneg : ∀ f, ∀ k : ℤ, k < 0 → (L f).coeff k = 0) (hC : ∀ c, L (MvPolynomial.C c) = HahnSeries.C c) :
    MvPolynomial σ ℂ →ₐ[ℂ] PowerSeries ℂ where
  toFun f := laurentToPS (L f)
  map_one' := HahnSeries.ofPowerSeries_injective (by
    rw [ofPowerSeries_laurentToPS (hneg 1), map_one, map_one])
  map_mul' f g := HahnSeries.ofPowerSeries_injective (by
    rw [ofPowerSeries_laurentToPS (hneg _), map_mul, map_mul, ofPowerSeries_laurentToPS (hneg _),
      ofPowerSeries_laurentToPS (hneg _)])
  map_zero' := HahnSeries.ofPowerSeries_injective (by
    rw [ofPowerSeries_laurentToPS (hneg 0), map_zero, map_zero])
  map_add' f g := HahnSeries.ofPowerSeries_injective (by
    rw [ofPowerSeries_laurentToPS (hneg _), map_add, map_add, ofPowerSeries_laurentToPS (hneg _),
      ofPowerSeries_laurentToPS (hneg _)])
  commutes' c := HahnSeries.ofPowerSeries_injective (by
    rw [ofPowerSeries_laurentToPS (hneg _), MvPolynomial.algebraMap_eq, hC, PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C])

theorem ofPowerSeries_psAlgHom {σ : Type*} (L : MvPolynomial σ ℂ →+* LaurentSeries ℂ)
    (hneg : ∀ f, ∀ k : ℤ, k < 0 → (L f).coeff k = 0) (hC : ∀ c, L (MvPolynomial.C c) = HahnSeries.C c)
    (f : MvPolynomial σ ℂ) : HahnSeries.ofPowerSeries ℤ ℂ (psAlgHom L hneg hC f) = L f :=
  ofPowerSeries_laurentToPS (hneg f)

end Curve

open Curve

variable {n : ℕ} {m : Fin (n + 2) → ℝ}

/-- **Lemma 2.3 (b)** (`lem:U`): `U` is constant on every irreducible curve `C ⊆ Y_m`, for every mass vector `m`. -/
theorem Curve.U_const (C : Curve n m) : C.IsConst (Upoly m) := by
  obtain ⟨P, hP⟩ := exists_place_centred C.toACurve
  obtain ⟨E⟩ := Expansion_exists P
  set L : Poly (n + 2) →+* LaurentSeries ℂ := E.ι.comp C.fnHom with hL
  have hLf : ∀ f, L f = E.ι (C.fn f) := fun f => rfl
  have hneg : ∀ f, ∀ k : ℤ, k < 0 → (L f).coeff k = 0 := fun f k hk =>
    HahnSeries.coeff_eq_zero_of_lt_orderTop (by
      rw [hLf, E.orderTop_eq]
      exact lt_of_lt_of_le (by exact_mod_cast hk) (hP f))
  have hLC : ∀ c, L (MvPolynomial.C c) = HahnSeries.C c := fun c => by rw [hLf, E.map_const]
  set Ψ := psAlgHom L hneg hLC with hΨdef
  have hΨ : ∀ f, HahnSeries.ofPowerSeries ℤ ℂ (Ψ f) = L f := ofPowerSeries_psAlgHom L hneg hLC
  have hzero : ∀ f ∈ rows m, Ψ f = 0 := fun f hf => HahnSeries.ofPowerSeries_injective (by
    rw [hΨ, map_zero, hLf, ACurve.fn_eq_zero_iff.mpr (C.rows_mem hf), map_zero])
  have hd := deriv_U_eq_zero (PowerSeries.derivative (R := ℂ)) Ψ m hzero
  set c₀ := PowerSeries.constantCoeff (Ψ (Upoly m)) with hc₀
  have hconst : Ψ (Upoly m) = PowerSeries.C c₀ :=
    PowerSeries.derivative.ext (by rw [hd, PowerSeries.derivative_C]) (by rw [hc₀, PowerSeries.constantCoeff_C])
  refine ⟨c₀, ?_⟩
  rw [← ACurve.fn_eq_zero_iff]
  apply E.ι.injective
  rw [map_zero, ← hLf, map_sub, ← hΨ, hconst, HahnSeries.ofPowerSeries_C, hLC, sub_self]

end

end CC6Full
