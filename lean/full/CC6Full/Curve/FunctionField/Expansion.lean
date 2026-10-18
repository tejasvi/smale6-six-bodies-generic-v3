import CC6Full.Curve.FunctionField.Residue
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Formal expansions at a place: `Expansion_exists` (`lem:place`, last statement)

For a field `K ⊇ ℂ` with a valuation `v : K → WithTop ℤ` that is trivial on `ℂ*`, has residue field `ℂ`
(`hres`) and a uniformizer `t` (`v t = 1`):

* `digit`, `remSeq`: `f = Σ_{i<n} digit_i tⁱ + tⁿ rem_n` (`expansion_identity`), with `v(rem_n) ≥ 0` when
  `v(f) ≥ 0`.
* `IsExp f s`: `v(f − s_{<n}(t)) ≥ n` for every `n`; expansions are unique (`isExp_unique`), additive and
  multiplicative (`isExp_add`, `isExp_mul`), so `f ↦ Σ digit_i Xⁱ` is an injective ring hom `O_v → ℂ⟦X⟧` preserving
  the order (`serHom`, `orderTop_serHom`).
* `exists_expansion_hom`: its extension `K = Frac(O_v) → ℂ((X))` is the identity on `ℂ` and turns `v` into the
  `X`-adic order.
* `Expansion_exists`: every place `P` of an irreducible curve `C ⊆ ℂ^σ` (`σ` finite) has a formal expansion
  `ℂ(C) → ℂ((t))` (the residue field is `ℂ` by `exists_residue_place`).

Ported from the five-body formalization (`CC5Full/Theory/FunctionField/Expansion.lean`), with the curves `C ⊆ Y_m`
replaced by the affine curves `ACurve σ`.
-/

namespace CC6Full

open Polynomial

noncomputable section

section general

variable {K : Type*} [Field K] [Algebra ℂ K] (v : AddValuation K (WithTop ℤ))

theorem one_le_of_pos_withTop {x : WithTop ℤ} (h : 0 < x) : 1 ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    have : (0 : ℤ) < n := by exact_mod_cast h
    exact_mod_cast (show (1 : ℤ) ≤ n by omega)

theorem nonneg_of_one_add {y : WithTop ℤ} (h : (1 : WithTop ℤ) ≤ 1 + y) : 0 ≤ y := by
  induction y using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    have : (1 : ℤ) ≤ 1 + n := by exact_mod_cast h
    exact_mod_cast (show (0 : ℤ) ≤ n by omega)

variable (hconst : ∀ c : ℂ, c ≠ 0 → v (algebraMap ℂ K c) = 0)
  (hres : ∀ f : K, 0 ≤ v f → ∃ c : ℂ, 0 < v (f - algebraMap ℂ K c)) {t : K} (ht : v t = 1)

omit [Algebra ℂ K] in
include ht in
theorem ne_zero_of_val_one : t ≠ 0 := by
  rintro rfl
  rw [AddValuation.map_zero] at ht
  exact WithTop.top_ne_coe ht

/-- The residue of `f` (a constant `c` with `v(f − c) > 0`, when `v(f) ≥ 0`). -/
def resC (f : K) : ℂ := by
  classical
  exact if h : 0 ≤ v f then Classical.choose (hres f h) else 0

include hres in
theorem resC_spec {f : K} (hf : 0 ≤ v f) : 0 < v (f - algebraMap ℂ K (resC v hres f)) := by
  classical
  unfold resC
  simp only [hf, ↓reduceDIte]
  exact Classical.choose_spec (hres f hf)

/-- The remainders `rem_{n+1} = (rem_n − res(rem_n)) / t`. -/
def remSeq (f : K) : ℕ → K
  | 0 => f
  | n + 1 => (remSeq f n - algebraMap ℂ K (resC v hres (remSeq f n))) * t⁻¹

/-- The digits of the expansion. -/
def digit (f : K) (n : ℕ) : ℂ := resC v hres (remSeq v hres (t := t) f n)

include ht in
theorem remSeq_nonneg {f : K} (hf : 0 ≤ v f) (n : ℕ) : 0 ≤ v (remSeq v hres (t := t) f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    have hspec := one_le_of_pos_withTop (resC_spec v hres ih)
    have ht0 := ne_zero_of_val_one v ht
    have hmul : remSeq v hres (t := t) f n - algebraMap ℂ K (resC v hres (remSeq v hres (t := t) f n)) =
        t * remSeq v hres (t := t) f (n + 1) := by
      simp only [remSeq]; field_simp
    rw [hmul, AddValuation.map_mul, ht] at hspec
    exact nonneg_of_one_add hspec

include ht in
/-- `f = Σ_{i<n} digit_i tⁱ + tⁿ rem_n`. -/
theorem expansion_identity (f : K) (n : ℕ) :
    f = Polynomial.aeval t (PowerSeries.trunc n (PowerSeries.mk (digit v hres (t := t) f))) +
      t ^ n * remSeq v hres (t := t) f n := by
  have ht0 := ne_zero_of_val_one v ht
  induction n with
  | zero => simp [remSeq]
  | succ n ih =>
    rw [PowerSeries.trunc_succ, map_add, Polynomial.aeval_monomial, PowerSeries.coeff_mk]
    conv_lhs => rw [ih]
    simp only [remSeq, digit]
    field_simp
    ring

/-- `s` is an expansion of `f`. -/
def IsExp (t f : K) (s : PowerSeries ℂ) : Prop :=
  ∀ n : ℕ, (n : WithTop ℤ) ≤ v (f - Polynomial.aeval t (PowerSeries.trunc n s))

include hconst in
theorem hconst_nonneg' (c : ℂ) : 0 ≤ v (algebraMap ℂ K c) := hconst_nonneg v hconst c

include ht in
theorem isExp_digits {f : K} (hf : 0 ≤ v f) :
    IsExp v t f (PowerSeries.mk (digit v hres (t := t) f)) := by
  intro n
  have h := expansion_identity v hres ht f n
  have : f - Polynomial.aeval t (PowerSeries.trunc n (PowerSeries.mk (digit v hres (t := t) f))) =
      t ^ n * remSeq v hres (t := t) f n := by
    linear_combination h
  rw [this, AddValuation.map_mul, AddValuation.map_pow, ht]
  have h2 := remSeq_nonneg v hres ht hf n
  calc (n : WithTop ℤ) = n • (1 : WithTop ℤ) := by simp
    _ ≤ n • (1 : WithTop ℤ) + v (remSeq v hres (t := t) f n) := le_add_of_nonneg_right h2

include ht hconst in
theorem val_aeval_t_nonneg (p : Polynomial ℂ) : 0 ≤ v (Polynomial.aeval t p) :=
  val_aeval_nonneg v (hconst_nonneg v hconst) (by rw [ht]; exact zero_le_one) p

include ht hconst in
/-- A polynomial divisible by `Xⁿ` has order `≥ n` at `t`. -/
theorem val_aeval_t_of_coeff {p : Polynomial ℂ} {n : ℕ} (hp : ∀ d < n, p.coeff d = 0) :
    (n : WithTop ℤ) ≤ v (Polynomial.aeval t p) := by
  obtain ⟨q, rfl⟩ := Polynomial.X_pow_dvd_iff.mpr hp
  rw [map_mul, map_pow, Polynomial.aeval_X, AddValuation.map_mul, AddValuation.map_pow, ht]
  have := val_aeval_t_nonneg v hconst ht q
  calc (n : WithTop ℤ) = n • (1 : WithTop ℤ) := by simp
    _ ≤ n • (1 : WithTop ℤ) + v (Polynomial.aeval t q) := le_add_of_nonneg_right this

include ht hconst in
/-- **Expansions are unique.** -/
theorem isExp_unique {f : K} {s s' : PowerSeries ℂ} (hs : IsExp v t f s) (hs' : IsExp v t f s') : s = s' := by
  classical
  by_contra hne
  have hex : ∃ k, PowerSeries.coeff k s ≠ PowerSeries.coeff k s' := by
    by_contra h; push Not at h; exact hne (PowerSeries.ext h)
  set k := Nat.find hex
  have hk : PowerSeries.coeff k s ≠ PowerSeries.coeff k s' := Nat.find_spec hex
  have hlt : ∀ j < k, PowerSeries.coeff j s = PowerSeries.coeff j s' := fun j hj => by
    by_contra h; exact Nat.find_min hex hj h
  have hdiff : PowerSeries.trunc (k + 1) s - PowerSeries.trunc (k + 1) s' =
      Polynomial.monomial k (PowerSeries.coeff k s - PowerSeries.coeff k s') := by
    ext d
    simp only [Polynomial.coeff_sub, PowerSeries.coeff_trunc, Polynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · subst h2; rfl
    · rw [hlt d (by omega), sub_self]
    · omega
    · rw [sub_self]
  have h1 := hs (k + 1)
  have h2 := hs' (k + 1)
  have h3 : ((k + 1 : ℕ) : WithTop ℤ) ≤ v (Polynomial.aeval t (PowerSeries.trunc (k + 1) s) -
      Polynomial.aeval t (PowerSeries.trunc (k + 1) s')) := by
    have : Polynomial.aeval t (PowerSeries.trunc (k + 1) s) - Polynomial.aeval t (PowerSeries.trunc (k + 1) s') =
        (f - Polynomial.aeval t (PowerSeries.trunc (k + 1) s')) - (f - Polynomial.aeval t (PowerSeries.trunc (k + 1) s)) := by
      ring
    rw [this]
    exact AddValuation.map_le_sub v h2 h1
  rw [← map_sub, hdiff, Polynomial.aeval_monomial, AddValuation.map_mul, AddValuation.map_pow, ht,
    hconst _ (sub_ne_zero.mpr hk), zero_add] at h3
  have : ((k + 1 : ℕ) : WithTop ℤ) ≤ ((k : ℕ) : WithTop ℤ) := by simpa using h3
  have : k + 1 ≤ k := by exact_mod_cast this
  omega

theorem isExp_add {f g : K} {s s' : PowerSeries ℂ} (hs : IsExp v t f s) (hs' : IsExp v t g s') :
    IsExp v t (f + g) (s + s') := by
  intro n
  have : f + g - Polynomial.aeval t (PowerSeries.trunc n (s + s')) =
      (f - Polynomial.aeval t (PowerSeries.trunc n s)) + (g - Polynomial.aeval t (PowerSeries.trunc n s')) := by
    rw [map_add, map_add]; ring
  rw [this]
  exact AddValuation.map_le_add v (hs n) (hs' n)

include ht hconst in
theorem isExp_mul {f g : K} {s s' : PowerSeries ℂ} (hs : IsExp v t f s) (hs' : IsExp v t g s') :
    IsExp v t (f * g) (s * s') := by
  intro n
  set A := Polynomial.aeval t (PowerSeries.trunc n s)
  set B := Polynomial.aeval t (PowerSeries.trunc n s')
  have hA := val_aeval_t_nonneg v hconst ht (PowerSeries.trunc n s)
  have hB := val_aeval_t_nonneg v hconst ht (PowerSeries.trunc n s')
  -- the truncated product
  have hP : (n : WithTop ℤ) ≤ v (A * B - Polynomial.aeval t (PowerSeries.trunc n (s * s'))) := by
    rw [← map_mul, ← map_sub]
    refine val_aeval_t_of_coeff v hconst ht fun d hd => ?_
    have h := congrArg (fun p : Polynomial ℂ => p.coeff d)
      (PowerSeries.trunc_trunc_mul_trunc (n := n) s s')
    simp only [PowerSeries.coeff_trunc, hd, ↓reduceIte] at h
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc]
    simp only [hd, ↓reduceIte]
    rw [← h, ← Polynomial.coeff_coe, Polynomial.coe_mul, sub_self]
  have key : f * g - Polynomial.aeval t (PowerSeries.trunc n (s * s')) =
      (A * B - Polynomial.aeval t (PowerSeries.trunc n (s * s'))) + A * (g - B) + (f - A) * B + (f - A) * (g - B) := by
    ring
  rw [key]
  have hn0 : (0 : WithTop ℤ) ≤ (n : WithTop ℤ) := by exact_mod_cast Nat.zero_le n
  have h2 : (n : WithTop ℤ) ≤ v (A * (g - B)) := by
    rw [AddValuation.map_mul]
    simpa using add_le_add hA (hs' n)
  have h3 : (n : WithTop ℤ) ≤ v ((f - A) * B) := by
    rw [AddValuation.map_mul]
    simpa using add_le_add (hs n) hB
  have h4 : (n : WithTop ℤ) ≤ v ((f - A) * (g - B)) := by
    rw [AddValuation.map_mul]
    calc (n : WithTop ℤ) = n + 0 := by simp
      _ ≤ v (f - A) + v (g - B) := add_le_add (hs n) (hn0.trans (hs' n))
  exact AddValuation.map_le_add v (AddValuation.map_le_add v (AddValuation.map_le_add v hP h2) h3) h4

theorem isExp_C (c : ℂ) (hc : 0 ≤ v (algebraMap ℂ K c)) : IsExp v t (algebraMap ℂ K c) (PowerSeries.C c) := by
  intro n
  cases n with
  | zero => simpa using hc
  | succ n => simp

include ht in
theorem isExp_X : IsExp v t t PowerSeries.X := by
  intro n
  match n with
  | 0 => simp [ht]
  | 1 =>
    have : PowerSeries.trunc 1 (PowerSeries.X : PowerSeries ℂ) = 0 := by
      ext d; simp [PowerSeries.coeff_X]
    rw [this, map_zero, sub_zero, ht]; rfl
  | n + 2 => simp

/-- The valuation ring `{f | v f ≥ 0}`. -/
def valSubring : ValuationSubring K where
  carrier := {f | 0 ≤ v f}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [AddValuation.map_mul]; exact add_nonneg ha hb
  one_mem' := by simp [AddValuation.map_one]
  add_mem' {a b} ha hb := AddValuation.map_le_add v ha hb
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, AddValuation.map_neg] at *; exact ha
  mem_or_inv_mem' x := by
    by_cases hx : x = 0
    · left; simp [hx]
    rcases le_total 0 (v x) with h | h
    · left; exact h
    · right
      show 0 ≤ v x⁻¹
      have h1 : v x⁻¹ + v x = 0 := by rw [← AddValuation.map_mul, inv_mul_cancel₀ hx, AddValuation.map_one]
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hx)
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr (inv_ne_zero hx))
      rw [← hn] at h h1
      rw [← hk] at h1 ⊢
      have h' : n ≤ 0 := by exact_mod_cast h
      have h1' : k + n = 0 := by exact_mod_cast h1
      exact_mod_cast (show (0 : ℤ) ≤ k by omega)

omit [Algebra ℂ K] in
theorem mem_valSubring {f : K} : f ∈ valSubring v ↔ 0 ≤ v f := Iff.rfl

/-- The expansion as a ring hom `O_v → ℂ⟦X⟧`. -/
def serHom : valSubring v →+* PowerSeries ℂ where
  toFun f := PowerSeries.mk (digit v hres (t := t) f.1)
  map_one' := by
    have h1 := isExp_digits v hres ht (f := 1) (by simp [AddValuation.map_one])
    have h2 := isExp_C v (t := t) 1 (by simp [AddValuation.map_one])
    rw [map_one, map_one] at h2
    exact isExp_unique v hconst ht h1 h2
  map_mul' f g := isExp_unique v hconst ht (isExp_digits v hres ht (f * g).2)
    (isExp_mul v hconst ht (isExp_digits v hres ht f.2) (isExp_digits v hres ht g.2))
  map_zero' := by
    have h1 := isExp_digits v hres ht (f := 0) (by simp)
    have h2 := isExp_C v (t := t) 0 (by simp)
    rw [map_zero, map_zero] at h2
    exact isExp_unique v hconst ht h1 h2
  map_add' f g := isExp_unique v hconst ht (isExp_digits v hres ht (f + g).2)
    (isExp_add v (isExp_digits v hres ht f.2) (isExp_digits v hres ht g.2))

theorem isExp_serHom (f : valSubring v) : IsExp v t f.1 (serHom v hconst hres ht f) :=
  isExp_digits v hres ht f.2

theorem serHom_eq_of_isExp {f : valSubring v} {s : PowerSeries ℂ} (hs : IsExp v t f.1 s) :
    serHom v hconst hres ht f = s :=
  isExp_unique v hconst ht (isExp_serHom v hconst hres ht f) hs

theorem serHom_injective : Function.Injective (serHom v hconst hres ht) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h := isExp_serHom v hconst hres ht f
  rw [hf] at h
  apply Subtype.ext
  show f.1 = 0
  by_contra hne
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hne)
  have := h (k.toNat + 1)
  simp only [map_zero, sub_zero, ← hk] at this
  have : ((k.toNat + 1 : ℕ) : ℤ) ≤ k := by exact_mod_cast this
  omega

/-- The constants expand to themselves. -/
theorem serHom_algebraMap (c : ℂ) :
    serHom v hconst hres ht ⟨algebraMap ℂ K c, hconst_nonneg v hconst c⟩ = PowerSeries.C c :=
  serHom_eq_of_isExp v hconst hres ht (isExp_C v c (hconst_nonneg v hconst c))

/-- A Laurent series with nonzero constant term and no negative terms has order `0`. -/
theorem orderTop_ofPowerSeries_eq_zero {s : PowerSeries ℂ} (hs : PowerSeries.constantCoeff s ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ ℂ s).orderTop = 0 := by
  apply HahnSeries.orderTop_eq_of_le
  · rw [HahnSeries.mem_support]
    have := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) s 0
    simp only [Nat.cast_zero] at this
    rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hs
  · intro g hg
    by_contra hneg
    push Not at hneg
    rw [HahnSeries.mem_support, PowerSeries.coeff_coe] at hg
    simp [hneg] at hg

/-- **The expansion preserves the order.** -/
theorem orderTop_serHom (f : valSubring v) :
    (HahnSeries.ofPowerSeries ℤ ℂ (serHom v hconst hres ht f)).orderTop = v f.1 := by
  by_cases hf0 : f.1 = 0
  · have : f = 0 := Subtype.ext hf0
    rw [this, map_zero, map_zero, HahnSeries.orderTop_zero, ZeroMemClass.coe_zero, AddValuation.map_zero]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hf0)
  have hk0 : 0 ≤ k := by have := f.2; rw [mem_valSubring, ← hk] at this; exact_mod_cast this
  have ht0 := ne_zero_of_val_one v ht
  -- `f = t^k u` with `v(u) = 0`
  set u : K := f.1 * (t ^ k.toNat)⁻¹
  have hvt : v (t ^ k.toNat) = (k : WithTop ℤ) := by
    rw [AddValuation.map_pow, ht, nsmul_one, ← WithTop.coe_natCast, Int.toNat_of_nonneg hk0]
  have hu : v u = 0 := by
    have h1 : v u + v (t ^ k.toNat) = v f.1 := by
      rw [← AddValuation.map_mul]; simp only [u]; rw [inv_mul_cancel_right₀ (pow_ne_zero _ ht0)]
    rw [hvt, ← hk] at h1
    have hu0 : u ≠ 0 := mul_ne_zero hf0 (inv_ne_zero (pow_ne_zero _ ht0))
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hu0)
    rw [← hj] at h1 ⊢
    have : j + k = k := by exact_mod_cast h1
    have : j = 0 := by omega
    rw [this]; rfl
  have huO : u ∈ valSubring v := by rw [mem_valSubring, hu]
  have htO : t ∈ valSubring v := by rw [mem_valSubring, ht]; exact zero_le_one
  have hfu : f = ⟨t, htO⟩ ^ k.toNat * ⟨u, huO⟩ := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul, u]
    field_simp
  have hst : serHom v hconst hres ht ⟨t, htO⟩ = PowerSeries.X := serHom_eq_of_isExp v hconst hres ht (isExp_X v ht)
  have hcu : PowerSeries.constantCoeff (serHom v hconst hres ht ⟨u, huO⟩) ≠ 0 := by
    show PowerSeries.constantCoeff (PowerSeries.mk (digit v hres (t := t) u)) ≠ 0
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    intro h0
    have hspec := resC_spec v hres (f := u) (by rw [hu])
    simp only [digit, remSeq] at h0
    rw [h0, map_zero, sub_zero, hu] at hspec
    exact lt_irrefl _ hspec
  conv_lhs => rw [hfu, map_mul, map_pow, hst, map_mul, map_pow, HahnSeries.ofPowerSeries_X,
    HahnSeries.orderTop_mul, orderTop_ofPowerSeries_eq_zero hcu, add_zero, HahnSeries.single_pow, one_pow,
    HahnSeries.orderTop_single one_ne_zero]
  rw [← hk]
  congr 1
  simp [Int.toNat_of_nonneg hk0]

include hconst hres ht in
/-- **The expansion homomorphism**: a ring hom `K → ℂ((X))`, the identity on `ℂ`, turning `v` into the order. -/
theorem exists_expansion_hom : ∃ ι : K →+* LaurentSeries ℂ, (∀ c : ℂ, ι (algebraMap ℂ K c) = HahnSeries.C c) ∧
    ∀ f : K, (ι f).orderTop = v f := by
  set ψ : valSubring v →+* LaurentSeries ℂ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (serHom v hconst hres ht)
  have hψ : Function.Injective ψ :=
    HahnSeries.ofPowerSeries_injective.comp (serHom_injective v hconst hres ht)
  set ι := IsFractionRing.lift (K := K) hψ
  refine ⟨ι, fun c => ?_, fun f => ?_⟩
  · have : algebraMap ℂ K c = algebraMap (valSubring v) K ⟨algebraMap ℂ K c, hconst_nonneg v hconst c⟩ := rfl
    rw [this, IsFractionRing.lift_algebraMap]
    simp only [ψ, RingHom.comp_apply, serHom_algebraMap, HahnSeries.ofPowerSeries_C]
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := valSubring v) f
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (valSubring v) K b ≠ 0 := by
      intro h; exact hb0 (IsFractionRing.injective (valSubring v) K (h.trans (map_zero _).symm))
    have hψb : ψ b ≠ 0 := fun h => hb0 (hψ (h.trans (map_zero _).symm))
    rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    have hoa : (ψ a).orderTop = v a.1 := orderTop_serHom v hconst hres ht a
    have hob : (ψ b).orderTop = v b.1 := orderTop_serHom v hconst hres ht b
    have h1 : (ψ a / ψ b).orderTop + (ψ b).orderTop = (ψ a).orderTop := by
      rw [← HahnSeries.orderTop_mul, div_mul_cancel₀ _ hψb]
    have h2 : v (algebraMap (valSubring v) K a / algebraMap (valSubring v) K b) +
        v (algebraMap (valSubring v) K b) = v (algebraMap (valSubring v) K a) := by
      rw [← AddValuation.map_mul, div_mul_cancel₀ _ hbK]
    have hoa' : (ψ a).orderTop = v (algebraMap (valSubring v) K a) := hoa
    have hob' : (ψ b).orderTop = v (algebraMap (valSubring v) K b) := hob
    rw [hoa', hob', ← h2] at h1
    have hbtop : v (algebraMap (valSubring v) K b) ≠ ⊤ := (AddValuation.ne_top_iff v).mpr hbK
    exact WithTop.add_right_cancel hbtop h1

end general

/-- **Every place has a formal expansion** (`lem:place`, last statement): a ring embedding `ℂ(C) → ℂ((t))`, the
identity on `ℂ`, turning `ord_P` into the `t`-adic order. -/
theorem Expansion_exists {σ : Type*} [Finite σ] {C : ACurve σ} (P : Place C) : Nonempty P.Expansion := by
  obtain ⟨u, hu⟩ := P.exists_ord_eq_one
  obtain ⟨ι, hι1, hι2⟩ := exists_expansion_hom P.ord (ord_algebraMap P) (fun f hf => exists_residue_place P hf) hu
  exact ⟨⟨ι, fun c => by rw [fn_C_eq_algebraMap]; exact hι1 c, hι2⟩⟩

end

end CC6Full
