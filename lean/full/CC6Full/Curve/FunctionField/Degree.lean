import CC6Full.Curve.FunctionField.ValLemmas
import CC6Full.Curve.FunctionField.Places
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Degree of a transcendental function: `Σ_{ord_P x > 0} ord_P x = [K : ℂ(x)]`

For a field `K ⊇ ℂ` and `x ∈ K` transcendental over `ℂ` with `K` finite over `ℂ⟮x⟯`:

* the normalized discrete valuations `w` of `K` trivial on `ℂ` with `w(x) > 0` are exactly the adic valuations of
  the primes `𝔓` over `(x)` of the integral closure `B` of `R = ℂ[x]` in `K` (a Dedekind domain): `B ⊆ O_w` since
  valuation rings are integrally closed, `𝔓 = {b ∈ B : w(b) > 0}`, and `w` equals the `𝔓`-adic valuation by
  `addVal_eq_of_nonneg_imp`;
* `w_𝔓(x) = e(𝔓 | x)` and the residue degrees are `1` (`R/(x) ≅ ℂ` is algebraically closed), so
  `Σ_𝔓 w_𝔓(x) = Σ e f = rank_R B = [K : ℂ⟮x⟯]` (`Ideal.sum_ramification_inertia_eq_finrank`,
  `IsIntegralClosure.rank`).

Main result: `degree_pos_places`.

Ported from the five-body formalization (`CC5Full/Theory/FunctionField/Degree.lean`), for fields `K` in any universe.
-/

open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField IsDedekindDomain

namespace CC6Full

noncomputable section

local notation "Zm0" => WithZero (Multiplicative ℤ)

variable {K : Type*} [Field K]

theorem ordOfVal_nonneg_iff (val : Valuation K Zm0) (y : K) : 0 ≤ ordOfVal val y ↔ val y ≤ 1 := by
  refine ⟨fun h => ?_, ordOfVal_nonneg val⟩
  rw [ordOfVal_apply] at h
  by_cases hy : val y = 0
  · rw [hy]; exact zero_le
  rw [ordFun_of_ne val hy] at h
  have h2 : Multiplicative.toAdd (WithZero.unzero hy) ≤ 0 := by
    have : (0 : ℤ) ≤ -Multiplicative.toAdd (WithZero.unzero hy) := by exact_mod_cast h
    linarith
  have h3 : WithZero.unzero hy ≤ 1 := Multiplicative.toAdd_le.mp (by simpa using h2)
  rw [← WithZero.coe_unzero hy]
  exact_mod_cast h3

theorem ordOfVal_pos_iff (val : Valuation K Zm0) (y : K) : 0 < ordOfVal val y ↔ val y < 1 := by
  rw [ordOfVal_apply]
  by_cases hy : val y = 0
  · rw [hy]; unfold ordFun; simp [hy]
  rw [ordFun_of_ne val hy]
  constructor
  · intro h
    have h2 : Multiplicative.toAdd (WithZero.unzero hy) < 0 := by
      have : (0 : ℤ) < -Multiplicative.toAdd (WithZero.unzero hy) := by exact_mod_cast h
      linarith
    have h3 : WithZero.unzero hy < 1 := Multiplicative.toAdd_lt.mp (by simpa using h2)
    rw [← WithZero.coe_unzero hy]
    exact_mod_cast h3
  · intro h
    rw [← WithZero.coe_unzero hy] at h
    have h3 : WithZero.unzero hy < 1 := by exact_mod_cast h
    have h2 : Multiplicative.toAdd (WithZero.unzero hy) < 0 := by
      simpa using Multiplicative.toAdd_lt.mpr h3
    have : (0 : ℤ) < -Multiplicative.toAdd (WithZero.unzero hy) := by linarith
    exact_mod_cast this

/-! ## Places of a Dedekind domain -/

section dedekind

variable {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]

/-- The place (additive normalized valuation) of a height-one prime. -/
def placeOf (v : HeightOneSpectrum B) : AddValuation K (WithTop ℤ) := ordOfVal (v.valuation K)

theorem placeOf_one (v : HeightOneSpectrum B) : ∃ f, placeOf (K := K) v f = 1 := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := K) v
  exact ⟨π, by rw [placeOf, ordOfVal_apply, ordFun_eq_coe _ (n := 1) hπ]; rfl⟩

theorem placeOf_algebraMap_nonneg (v : HeightOneSpectrum B) (b : B) : 0 ≤ placeOf v (algebraMap B K b) :=
  ordOfVal_nonneg _ (v.valuation_le_one b)

theorem placeOf_algebraMap_pos_iff (v : HeightOneSpectrum B) (b : B) :
    0 < placeOf v (algebraMap B K b) ↔ b ∈ v.asIdeal := by
  rw [placeOf, ordOfVal_pos_iff, v.valuation_lt_one_iff_mem]

theorem placeOf_injective : Function.Injective (placeOf (K := K) (B := B)) := by
  intro v v' h
  apply HeightOneSpectrum.ext
  ext b
  rw [← placeOf_algebraMap_pos_iff (K := K) v b, ← placeOf_algebraMap_pos_iff (K := K) v' b, h]

/-- The ideal of the elements of `B` of positive order. -/
def posIdeal (w : AddValuation K (WithTop ℤ)) (hB : ∀ b : B, 0 ≤ w (algebraMap B K b)) : Ideal B where
  carrier := {b | 0 < w (algebraMap B K b)}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add w _ _)
  zero_mem' := by simp
  smul_mem' := by
    intro c b hb
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hb ⊢
    exact lt_of_lt_of_le hb (le_add_of_nonneg_left (hB c))

omit [IsDedekindDomain B] [IsFractionRing B K] in
theorem mem_posIdeal (w : AddValuation K (WithTop ℤ)) (hB : ∀ b : B, 0 ≤ w (algebraMap B K b)) (b : B) :
    b ∈ posIdeal w hB ↔ 0 < w (algebraMap B K b) := Iff.rfl

omit [IsDedekindDomain B] [IsFractionRing B K] in
theorem posIdeal_isPrime (w : AddValuation K (WithTop ℤ)) (hB : ∀ b : B, 0 ≤ w (algebraMap B K b)) :
    (posIdeal w hB).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have h1 : (1 : B) ∈ posIdeal w hB := by rw [h]; trivial
    rw [mem_posIdeal, map_one, AddValuation.map_one] at h1
    exact lt_irrefl _ h1
  · rw [mem_posIdeal, map_mul, AddValuation.map_mul] at hab
    by_contra hn
    push Not at hn
    rw [mem_posIdeal, mem_posIdeal, not_lt, not_lt] at hn
    have ha := le_antisymm hn.1 (hB a)
    have hb := le_antisymm hn.2 (hB b)
    rw [ha, hb, add_zero] at hab
    exact lt_irrefl _ hab

/-- The height-one prime of a place that is nonnegative on `B`. -/
def posPrime (w : AddValuation K (WithTop ℤ)) (hB : ∀ b : B, 0 ≤ w (algebraMap B K b))
    (hne : posIdeal w hB ≠ ⊥) : HeightOneSpectrum B :=
  ⟨posIdeal w hB, posIdeal_isPrime w hB, hne⟩

/-- **A place nonnegative on `B` is the adic valuation of its centre.** -/
theorem eq_placeOf_posPrime (w : AddValuation K (WithTop ℤ)) (hw : ∃ f, w f = 1)
    (hB : ∀ b : B, 0 ≤ w (algebraMap B K b)) (hne : posIdeal w hB ≠ ⊥) :
    w = placeOf (posPrime w hB hne) := by
  refine addVal_eq_of_nonneg_imp w _ hw (placeOf_one _) fun y hy => ?_
  rw [placeOf, ordOfVal_nonneg_iff] at hy
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (posPrime w hB hne) y hy
  have hd : w (algebraMap B K d) = 0 := by
    have h1 := d.2
    have h2 : ¬ (0 < w (algebraMap B K d)) := h1
    exact le_antisymm (not_lt.mp h2) (hB d)
  have h3 := congrArg w hnd
  rw [AddValuation.map_mul, hd, add_zero] at h3
  rw [h3]
  exact hB n

/-- The order of an element of `B` is the multiplicity of the prime in its principal ideal. -/
theorem placeOf_algebraMap_eq (v : HeightOneSpectrum B) {b : B} (hb : b ≠ 0) :
    placeOf v (algebraMap B K b) = ((multiplicity v.asIdeal (Ideal.span {b}) : ℕ) : WithTop ℤ) := by
  have hv : v.valuation K (algebraMap B K b) =
      ((Multiplicative.ofAdd (-((multiplicity v.asIdeal (Ideal.span {b}) : ℕ) : ℤ)) : Multiplicative ℤ) : Zm0) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hb]
    rfl
  rw [placeOf, ordOfVal_apply, ordFun_eq_coe _ hv]
  rfl

/-- Units of `B` have order `0`. -/
theorem placeOf_unit (v : HeightOneSpectrum B) {b : B} (hb : IsUnit b) : placeOf v (algebraMap B K b) = 0 := by
  have h1 : v.valuation K (algebraMap B K b) =
      ((Multiplicative.ofAdd (-(0 : ℤ)) : Multiplicative ℤ) : Zm0) := by
    have h2 : v.valuation K (algebraMap B K b) = 1 := by
      rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
      exact fun hmem => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hb)
    rw [h2]
    rfl
  rw [placeOf, ordOfVal_apply, ordFun_eq_coe _ h1]
  rfl

end dedekind

/-- Algebraic closedness transfers along a ring isomorphism (the fields may lie in different universes). -/
theorem isAlgClosed_of_ringEquiv {k k' : Type*} [Field k] [Field k'] (e : k ≃+* k') [IsAlgClosed k] :
    IsAlgClosed k' := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : Polynomial.degree (p.map e.symm.toRingHom) ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (k := k) (p.map e.symm.toRingHom) hpe
  refine ⟨e y, ?_⟩
  rw [Polynomial.IsRoot] at hy
  apply e.symm.injective
  rw [map_zero, ← hy]
  clear hy hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

/-! ## The integral closure of `ℂ[x]` -/

section degree

variable {L : Type*} [Field L] [Algebra ℂ L]

/-- A normalized discrete valuation of `L` trivial on `ℂ`. -/
structure IsNormPlace (w : AddValuation L (WithTop ℤ)) : Prop where
  const : ∀ c : ℂ, c ≠ 0 → w (algebraMap ℂ L c) = 0
  one : ∃ f, w f = 1

/-- `ℂ[x] ⊆ L`. -/
abbrev Rx (x : L) : Subalgebra ℂ L := Algebra.adjoin ℂ {x}

/-- The integral closure of `ℂ[x]` in `L`. -/
abbrev Bx (x : L) : Subalgebra (Rx x) L := integralClosure (Rx x) L

/-- The generator `x ∈ ℂ[x]`. -/
def genR (x : L) : Rx x := ⟨x, Algebra.self_mem_adjoin_singleton ℂ x⟩

/-- The ideal `(x)` of `ℂ[x]`. -/
def xIdeal (x : L) : Ideal (Rx x) := Ideal.span {genR x}

variable (x : L) (hx : Transcendental ℂ x)
include hx

theorem isPIR_Rx : IsPrincipalIdealRing (Rx x) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental ℂ x hx).toRingHom
    (Polynomial.algEquivOfTranscendental ℂ x hx).surjective

theorem algEquiv_X : Polynomial.algEquivOfTranscendental ℂ x hx Polynomial.X = genR x := by
  apply Subtype.ext
  simp [genR]

theorem genR_ne_zero : genR x ≠ 0 := by
  intro h
  have h1 := congrArg Subtype.val h
  simp only [genR, ZeroMemClass.coe_zero] at h1
  exact hx (by rw [h1]; exact isAlgebraic_zero)

theorem xIdeal_isMaximal : (xIdeal x).IsMaximal := by
  have hpe : xIdeal x = Ideal.map (Polynomial.algEquivOfTranscendental ℂ x hx) (Ideal.span {Polynomial.X}) := by
    rw [Ideal.map_span, Set.image_singleton, algEquiv_X x hx]; rfl
  have hXmax : (Ideal.span {(Polynomial.X : Polynomial ℂ)}).IsMaximal := by
    have h1 := Polynomial.ker_evalRingHom (0 : ℂ)
    rw [map_zero, sub_zero] at h1
    rw [← h1]
    exact RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨Polynomial.C c, by simp⟩)
  rw [hpe]
  exact Ideal.map_isMaximal_of_equiv _

theorem xIdeal_ne_bot : xIdeal x ≠ ⊥ := by
  rw [xIdeal, Ne, Ideal.span_singleton_eq_bot]
  exact genR_ne_zero x hx

/-- `ℂ[x]/(x) = ℂ`. -/
theorem algebraMap_quot_xIdeal_surjective : Function.Surjective (algebraMap ℂ (Rx x ⧸ xIdeal x)) := by
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨f, rfl⟩ := (Polynomial.algEquivOfTranscendental ℂ x hx).surjective r
  refine ⟨f.coeff 0, ?_⟩
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
  obtain ⟨g, hg⟩ := Polynomial.X_dvd_sub_C (p := f)
  set e := Polynomial.algEquivOfTranscendental ℂ x hx
  have h1 : algebraMap ℂ (Rx x) (f.coeff 0) - e f = -(genR x * e g) := by
    rw [← e.commutes, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ← algEquiv_X x hx,
      ← map_mul, ← hg, map_sub]
    ring
  rw [h1]
  exact (xIdeal x).neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

variable [FiniteDimensional ℂ⟮x⟯ L]

theorem isDedekind_Bx : IsDedekindDomain (Bx x) := by
  have := isPIR_Rx x hx
  exact integralClosure.isDedekindDomain (Rx x) ℂ⟮x⟯ L

omit hx in
theorem isFractionRing_Bx : IsFractionRing (Bx x) L := by
  exact integralClosure.isFractionRing_of_finite_extension ℂ⟮x⟯ L

theorem finite_Bx : Module.Finite (Rx x) (Bx x) := by
  have := isPIR_Rx x hx
  exact IsIntegralClosure.finite (Rx x) ℂ⟮x⟯ L (Bx x)

theorem free_Bx : Module.Free (Rx x) (Bx x) := by
  have := isPIR_Rx x hx
  exact IsIntegralClosure.module_free (Rx x) ℂ⟮x⟯ L (Bx x)

theorem finrank_Bx : Module.finrank (Rx x) (Bx x) = Module.finrank ℂ⟮x⟯ L := by
  have := isPIR_Rx x hx
  exact IsIntegralClosure.rank (Rx x) ℂ⟮x⟯ L (Bx x)

omit hx [FiniteDimensional ℂ⟮x⟯ L] in
theorem algebraMap_Rx_Bx_injective : Function.Injective (algebraMap (Rx x) (Bx x)) := by
  intro a b hab
  have h1 := congrArg (algebraMap (Bx x) L) hab
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
  exact Subtype.ext h1

omit [FiniteDimensional ℂ⟮x⟯ L] in
/-- The primes over `(x)` are nonzero. -/
theorem primesOver_ne_bot (q : (xIdeal x).primesOver (Bx x)) : q.1 ≠ ⊥ := by
  intro hq
  have h1 := q.2.2.over
  rw [hq] at h1
  apply xIdeal_ne_bot x hx
  rw [h1, Ideal.under, Ideal.comap_bot_of_injective _ (algebraMap_Rx_Bx_injective x)]

/-- **The residue degrees over `(x)` are `1`.** -/
theorem inertiaDeg_eq_one (q : (xIdeal x).primesOver (Bx x)) : q.1.inertiaDeg (Rx x) = 1 := by
  have := isDedekind_Bx x hx
  have := finite_Bx x hx
  have := xIdeal_isMaximal x hx
  have hqp : q.1.IsPrime := q.2.1
  have : q.1.LiesOver (xIdeal x) := q.2.2
  have : q.1.IsMaximal := Ideal.IsPrime.isMaximal hqp (primesOver_ne_bot x hx q)
  let _ : Field (Rx x ⧸ xIdeal x) := Ideal.Quotient.field _
  have hbij : Function.Bijective (algebraMap ℂ (Rx x ⧸ xIdeal x)) :=
    ⟨(algebraMap ℂ (Rx x ⧸ xIdeal x)).injective, algebraMap_quot_xIdeal_surjective x hx⟩
  have : IsAlgClosed (Rx x ⧸ xIdeal x) := isAlgClosed_of_ringEquiv (RingEquiv.ofBijective _ hbij)
  rw [Ideal.inertiaDeg_eq_of_isMaximal (xIdeal x) q.1]
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Rx x ⧸ xIdeal x) (K := Bx x ⧸ q.1)
  apply Subalgebra.bot_eq_top_iff_finrank_eq_one.mp
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, rfl⟩ := hb.2 y
  exact Subalgebra.algebraMap_mem _ z

omit hx [FiniteDimensional ℂ⟮x⟯ L] in
/-- Elements of `ℂ[x]` have nonnegative order where `x` has. -/
theorem nonneg_on_Rx (w : AddValuation L (WithTop ℤ)) (hw : IsNormPlace w) (hwx : 0 ≤ w x) (r : Rx x) :
    0 ≤ w (algebraMap (Rx x) L r) := by
  obtain ⟨r, hr⟩ := r
  show 0 ≤ w r
  induction hr using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hwx
  | algebraMap c =>
    by_cases hc : c = 0
    · simp [hc]
    · rw [hw.const c hc]
  | add y z _ _ hy hz => exact le_trans (le_min hy hz) (AddValuation.map_add w _ _)
  | mul y z _ _ hy hz => rw [AddValuation.map_mul]; exact add_nonneg hy hz

omit hx [FiniteDimensional ℂ⟮x⟯ L] in
/-- Elements of the integral closure of `ℂ[x]` have nonnegative order where `x` has. -/
theorem nonneg_on_Bx (w : AddValuation L (WithTop ℤ)) (hw : IsNormPlace w) (hwx : 0 ≤ w x) (b : Bx x) :
    0 ≤ w (algebraMap (Bx x) L b) :=
  addVal_nonneg_of_isIntegral w (nonneg_on_Rx x w hw hwx) b.2

/-- **Degree of a transcendental function**: the normalized places `w` of `L` trivial on `ℂ` with `w(x) > 0` form
a finite set, and `Σ_w w(x) = [L : ℂ⟮x⟯]`. -/
theorem degree_pos_places :
    ∃ S : Finset (AddValuation L (WithTop ℤ)), (∀ w, w ∈ S ↔ IsNormPlace w ∧ 0 < w x) ∧
      ∑ w ∈ S, w x = (Module.finrank ℂ⟮x⟯ L : WithTop ℤ) := by
  classical
  have := isPIR_Rx x hx
  have := isDedekind_Bx x hx
  have := isFractionRing_Bx x
  have := finite_Bx x hx
  have := free_Bx x hx
  have hmax := xIdeal_isMaximal x hx
  have : Fintype ((xIdeal x).primesOver (Bx x)) := (Algebra.QuasiFinite.finite_primesOver (xIdeal x)).fintype
  let hts : (xIdeal x).primesOver (Bx x) → HeightOneSpectrum (Bx x) :=
    fun q => ⟨q.1, q.2.1, primesOver_ne_bot x hx q⟩
  set xB : Bx x := algebraMap (Rx x) (Bx x) (genR x) with hxB_def
  have hxB : algebraMap (Bx x) L xB = x := by
    rw [hxB_def, ← IsScalarTower.algebraMap_apply]; rfl
  have hxB0 : xB ≠ 0 := fun h => genR_ne_zero x hx (algebraMap_Rx_Bx_injective x (by rw [map_zero]; exact h))
  have hpmap : (xIdeal x).map (algebraMap (Rx x) (Bx x)) = Ideal.span {xB} := by
    rw [xIdeal, Ideal.map_span, Set.image_singleton]
  have hne : (xIdeal x).map (algebraMap (Rx x) (Bx x)) ≠ ⊥ := by
    rw [hpmap, Ne, Ideal.span_singleton_eq_bot]; exact hxB0
  have hx' : ∀ q, placeOf (K := L) (hts q) x = placeOf (hts q) (algebraMap (Bx x) L xB) := fun q => by
    rw [hxB]
  have hram : ∀ q, placeOf (K := L) (hts q) x = (q.1.ramificationIdx (Rx x) : WithTop ℤ) := by
    intro q
    have : q.1.IsPrime := q.2.1
    have : q.1.LiesOver (xIdeal x) := q.2.2
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (xIdeal x) q.1 hne, hpmap, hx',
      placeOf_algebraMap_eq _ hxB0]
  have hxBq : ∀ q : (xIdeal x).primesOver (Bx x), xB ∈ q.1 := by
    intro q
    have h1 : genR x ∈ q.1.under (Rx x) := by
      rw [← q.2.2.over]; exact Ideal.subset_span rfl
    exact h1
  have hunit : ∀ c : ℂ, c ≠ 0 → ∃ b : Bx x, IsUnit b ∧ algebraMap (Bx x) L b = algebraMap ℂ L c := by
    intro c hc
    refine ⟨algebraMap (Rx x) (Bx x) (algebraMap ℂ (Rx x) c), ((Ne.isUnit hc).map _).map _, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have hnorm : ∀ q, IsNormPlace (placeOf (K := L) (hts q)) := fun q =>
    ⟨fun c hc => by obtain ⟨b, hb, hbc⟩ := hunit c hc; rw [← hbc]; exact placeOf_unit _ hb, placeOf_one _⟩
  have hinj : Function.Injective (fun q => placeOf (K := L) (hts q)) := by
    intro q q' h
    have h1 := placeOf_injective h
    exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal h1)
  refine ⟨Finset.univ.image (fun q => placeOf (K := L) (hts q)), fun w => ⟨?_, ?_⟩, ?_⟩
  · intro hw
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨hnorm q, ?_⟩
    rw [hx', placeOf_algebraMap_pos_iff]
    exact hxBq q
  · rintro ⟨hw, hwx⟩
    have hB := nonneg_on_Bx x w hw hwx.le
    have hxBQ : xB ∈ posIdeal w hB := by rw [mem_posIdeal, hxB]; exact hwx
    have hQne : posIdeal w hB ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hxBQ
      exact hxB0 hxBQ
    have hQprime := posIdeal_isPrime w hB
    have hover : xIdeal x = (posIdeal w hB).under (Rx x) := by
      refine hmax.eq_of_le (Ideal.IsPrime.under (Rx x) (posIdeal w hB)).ne_top ?_
      rw [xIdeal, Ideal.span_le, Set.singleton_subset_iff]
      exact hxBQ
    have hQ : posIdeal w hB ∈ (xIdeal x).primesOver (Bx x) := ⟨hQprime, ⟨hover⟩⟩
    refine Finset.mem_image.mpr ⟨⟨posIdeal w hB, hQ⟩, Finset.mem_univ _, ?_⟩
    exact (eq_placeOf_posPrime w hw.one hB hQne).symm
  · rw [Finset.sum_image (fun q _ q' _ h => hinj h)]
    simp only [hram]
    have hsum := Ideal.sum_ramification_inertia_eq_finrank (xIdeal x) (Bx x)
    simp only [inertiaDeg_eq_one x hx, mul_one] at hsum
    rw [finrank_Bx x hx] at hsum
    rw [← hsum, Nat.cast_sum]

end degree

end

end CC6Full
