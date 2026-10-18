import CC6Full.Curve.FunctionField.Dim
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Algebraic relations over `ℂ[x]` and residues of valuations trivial on `ℂ`

For a field `K ⊇ ℂ` and an additive valuation `v` of `K` with values in `WithTop ℤ`, trivial on `ℂ*`:

* `AlgRel x f`: `f` is a root of a nonzero polynomial with coefficients in `ℂ[x]`.
* `algRel_shift`, `algRel_inv`: relations over `ℂ[x]` give relations over `ℂ[x − c]` and `ℂ[x⁻¹]`.
* `val_aeval_eq_sum_roots`: `v(q(y)) = Σ_{q(c) = 0} v(y − c)` (`q` splits over `ℂ`).
* `val_eq_zero_of_algRel`: if `v` vanishes on `ℂ[x] ∖ 0`, it vanishes on every nonzero `f` algebraic over `ℂ[x]`
  (the term of least order of a relation would be alone).
* `exists_residue`: if `v(x) > 0` and `f` with `v(f) ≥ 0` is algebraic over `ℂ[x]`, then `v(f − c) > 0` for some
  `c ∈ ℂ` (reduce a normalized relation modulo `x`: `f` is a root of a nonzero `p ∈ ℂ[T]` up to positive order,
  and `p` splits).

Ported unchanged from the five-body formalization (`CC5Full/Theory/FunctionField/AlgRel.lean`).
-/

namespace CC6Full

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- `f` is a root of a nonzero polynomial with coefficients in `ℂ[x]`. -/
def AlgRel (x f : K) : Prop :=
  ∃ Q : Polynomial (Polynomial ℂ), Q ≠ 0 ∧ Q.eval₂ (Polynomial.aeval (R := ℂ) x).toRingHom f = 0

/-- Relations over `ℂ[x]` give relations over `ℂ[x − c]`. -/
theorem algRel_shift {x f : K} (h : AlgRel x f) (c : ℂ) : AlgRel (x - algebraMap ℂ K c) f := by
  obtain ⟨Q, hQ, hQf⟩ := h
  set ρ : Polynomial ℂ →+* Polynomial ℂ := Polynomial.compRingHom (Polynomial.X + Polynomial.C c)
  have hρ : Function.Injective ρ := by
    have hleft : ∀ q, (ρ q).comp (Polynomial.X - Polynomial.C c) = q := by
      intro q
      simp only [ρ, Polynomial.coe_compRingHom_apply, Polynomial.comp_assoc]
      simp
    exact Function.LeftInverse.injective hleft
  have hcomp : ((Polynomial.aeval (R := ℂ) (x - algebraMap ℂ K c)).toRingHom).comp ρ =
      (Polynomial.aeval (R := ℂ) x).toRingHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [ρ]
    · show Polynomial.aeval (x - algebraMap ℂ K c) (Polynomial.X.comp (Polynomial.X + Polynomial.C c)) =
        Polynomial.aeval x Polynomial.X
      simp
  refine ⟨Q.map ρ, (Polynomial.map_ne_zero_iff hρ).mpr hQ, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  exact hQf

/-- Relations over `ℂ[x]` give relations over `ℂ[x⁻¹]` (multiply by `x^D`, `D` a bound of the degrees). -/
theorem algRel_inv {x f : K} (hx : x ≠ 0) (h : AlgRel x f) : AlgRel x⁻¹ f := by
  classical
  obtain ⟨Q, hQ, hQf⟩ := h
  set D : ℕ := Q.support.sup fun i => (Q.coeff i).natDegree
  have hD : ∀ i, (Q.coeff i).natDegree ≤ D := by
    intro i
    by_cases hi : i ∈ Q.support
    · exact Finset.le_sup (f := fun i => (Q.coeff i).natDegree) hi
    · rw [Polynomial.notMem_support_iff.mp hi]; simp
  set Q' : Polynomial (Polynomial ℂ) := ∑ i ∈ Q.support, Polynomial.monomial i (Polynomial.reflect D (Q.coeff i))
  have hcoeff : ∀ i, Q'.coeff i = Polynomial.reflect D (Q.coeff i) := by
    intro i
    simp only [Q', Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · intro hi; rw [Polynomial.notMem_support_iff.mp hi]; simp
  have hQ' : Q' ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, Q.coeff i ≠ 0 := by
      by_contra hall; push Not at hall; exact hQ (Polynomial.ext fun i => by simp [hall i])
    intro h0
    have := hcoeff i
    rw [h0, Polynomial.coeff_zero] at this
    exact hi (Polynomial.reflect_eq_zero_iff.mp this.symm)
  refine ⟨Q', hQ', ?_⟩
  have _ : Invertible x := invertibleOfNonzero hx
  -- `x^D · Q'(x⁻¹, f) = Q(x, f)`
  have key : Q'.eval₂ (Polynomial.aeval (R := ℂ) x⁻¹).toRingHom f * x ^ D =
      Q.eval₂ (Polynomial.aeval (R := ℂ) x).toRingHom f := by
    rw [Polynomial.eval₂_eq_sum_range' _ (n := Q'.natDegree + Q.natDegree + 1) (by omega),
      Polynomial.eval₂_eq_sum_range' _ (n := Q'.natDegree + Q.natDegree + 1) (by omega), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoeff i]
    have hr := Polynomial.eval₂_reflect_mul_pow (algebraMap ℂ K) x D (Q.coeff i) (hD i)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_def]
    rw [invOf_eq_inv] at hr
    rw [mul_right_comm, hr]
  rw [hQf] at key
  exact (mul_eq_zero.mp key).resolve_right (pow_ne_zero _ hx)

section val

variable (v : AddValuation K (WithTop ℤ)) (hconst : ∀ c : ℂ, c ≠ 0 → v (algebraMap ℂ K c) = 0)
include hconst

omit hconst [Algebra ℂ K] in
/-- The valuation of a product over a multiset. -/
theorem val_multiset_prod (s : Multiset ℂ) (g : ℂ → K) : v (s.map g).prod = (s.map fun c => v (g c)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [AddValuation.map_one]
  | cons a s ih => rw [Multiset.map_cons, Multiset.prod_cons, AddValuation.map_mul, ih]; simp

/-- **`v(q(y)) = Σ_{q(c)=0} v(y − c)`** for a nonzero `q ∈ ℂ[X]`. -/
theorem val_aeval_eq_sum_roots {q : Polynomial ℂ} (hq : q ≠ 0) (y : K) :
    v (Polynomial.aeval y q) = (q.roots.map fun c => v (y - algebraMap ℂ K c)).sum := by
  have hfact := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := q))
  conv_lhs => rw [← hfact]
  rw [map_mul, Polynomial.aeval_C, map_multiset_prod, Multiset.map_map, AddValuation.map_mul,
    hconst _ (Polynomial.leadingCoeff_ne_zero.mpr hq), zero_add]
  have : (q.roots.map ((Polynomial.aeval y) ∘ fun a => Polynomial.X - Polynomial.C a)) =
      q.roots.map fun c => y - algebraMap ℂ K c := by
    refine Multiset.map_congr rfl fun c _ => ?_
    simp
  rw [this, val_multiset_prod v]

omit hconst in
/-- The valuation of a polynomial in `x` is nonnegative when `v(x) ≥ 0`. -/
theorem val_aeval_nonneg (hconst' : ∀ c : ℂ, 0 ≤ v (algebraMap ℂ K c)) {x : K} (hx : 0 ≤ v x) (q : Polynomial ℂ) :
    0 ≤ v (Polynomial.aeval x q) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact AddValuation.map_le_add v hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, AddValuation.map_mul, AddValuation.map_pow]
    exact add_nonneg (hconst' a) (nsmul_nonneg hx n)

theorem hconst_nonneg (c : ℂ) : 0 ≤ v (algebraMap ℂ K c) := by
  by_cases hc : c = 0
  · subst hc; simp
  · rw [hconst c hc]

omit hconst in
/-- **Dominance**: if `v` vanishes on `ℂ[x] ∖ 0`, it vanishes on every nonzero `f` algebraic over `ℂ[x]`. -/
theorem val_eq_zero_of_algRel {x f : K} (hf : f ≠ 0) (hrel : AlgRel x f)
    (hv : ∀ q : Polynomial ℂ, q ≠ 0 → v (Polynomial.aeval x q) = 0) : v f = 0 := by
  classical
  obtain ⟨Q, hQ, hQf⟩ := hrel
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hf)
  set ψ := (Polynomial.aeval (R := ℂ) x).toRingHom
  have hterm : ∀ i, Q.coeff i ≠ 0 → v (ψ (Q.coeff i) * f ^ i) = ((i : ℤ) * r : ℤ) := by
    intro i hi
    rw [AddValuation.map_mul, AddValuation.map_pow, ← hr]
    have : v (ψ (Q.coeff i)) = 0 := hv _ hi
    rw [this, zero_add]
    norm_cast
  have hsum : Q.eval₂ ψ f = ∑ i ∈ Q.support, ψ (Q.coeff i) * f ^ i := by
    rw [Polynomial.eval₂_eq_sum]; rfl
  by_contra hne
  have hr0 : r ≠ 0 := by
    intro h0; apply hne; rw [← hr, h0]; rfl
  -- the index whose term has the least order
  obtain ⟨j, hjS, hjmin⟩ : ∃ j ∈ Q.support, ∀ i ∈ Q.support, i ≠ j → (j : ℤ) * r < (i : ℤ) * r := by
    rcases lt_or_gt_of_ne hr0 with hneg | hpos
    · refine ⟨Q.natDegree, Polynomial.natDegree_mem_support_of_nonzero hQ, fun i hi hij => ?_⟩
      have : i < Q.natDegree := lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp i hi) hij
      have : (i : ℤ) < Q.natDegree := by exact_mod_cast this
      nlinarith
    · refine ⟨Q.natTrailingDegree, Polynomial.natTrailingDegree_mem_support_of_nonzero hQ, fun i hi hij => ?_⟩
      have : Q.natTrailingDegree < i :=
        lt_of_le_of_ne (Polynomial.natTrailingDegree_le_of_mem_supp i hi) (Ne.symm hij)
      have : (Q.natTrailingDegree : ℤ) < i := by exact_mod_cast this
      nlinarith
  have hsplit : Q.eval₂ ψ f = ψ (Q.coeff j) * f ^ j + ∑ i ∈ Q.support.erase j, ψ (Q.coeff i) * f ^ i := by
    rw [hsum, ← Finset.add_sum_erase _ _ hjS]
  have hrest : (((j : ℤ) * r : ℤ) : WithTop ℤ) < v (∑ i ∈ Q.support.erase j, ψ (Q.coeff i) * f ^ i) := by
    refine AddValuation.map_lt_sum v WithTop.coe_ne_top fun i hi => ?_
    rw [hterm i (Polynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hi))]
    exact_mod_cast hjmin i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
  have hval : v (Q.eval₂ ψ f) = ((j : ℤ) * r : ℤ) := by
    rw [hsplit, AddValuation.map_add_eq_of_lt_left v (by rw [hterm j (Polynomial.mem_support_iff.mp hjS)]; exact hrest),
      hterm j (Polynomial.mem_support_iff.mp hjS)]
  rw [hQf, AddValuation.map_zero] at hval
  exact WithTop.top_ne_coe hval

omit hconst in
/-- A relation can be normalized so that its coefficients are not all divisible by `X`. -/
theorem normalize_algRel {x f : K} (hx : x ≠ 0) (hrel : AlgRel x f) :
    ∃ Q : Polynomial (Polynomial ℂ), Q.map (Polynomial.evalRingHom 0) ≠ 0 ∧
      Q.eval₂ (Polynomial.aeval (R := ℂ) x).toRingHom f = 0 := by
  classical
  obtain ⟨Q, hQ, hQf⟩ := hrel
  obtain ⟨i₀, hi₀⟩ : ∃ i, Q.coeff i ≠ 0 := by
    by_contra hall; push Not at hall; exact hQ (Polynomial.ext fun i => by simp [hall i])
  -- induction on the degree of the coefficient `i₀`
  suffices H : ∀ n, ∀ Q : Polynomial (Polynomial ℂ), (Q.coeff i₀).natDegree = n → Q.coeff i₀ ≠ 0 →
      Q.eval₂ (Polynomial.aeval (R := ℂ) x).toRingHom f = 0 →
      ∃ Q' : Polynomial (Polynomial ℂ), Q'.map (Polynomial.evalRingHom 0) ≠ 0 ∧
        Q'.eval₂ (Polynomial.aeval (R := ℂ) x).toRingHom f = 0 from H _ Q rfl hi₀ hQf
  intro n
  induction n with
  | zero =>
    intro Q hn hQ0 hQf
    refine ⟨Q, ?_, hQf⟩
    intro h0
    have := congrArg (fun p => Polynomial.coeff p i₀) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, Polynomial.coe_evalRingHom] at this
    rw [Polynomial.eq_C_of_natDegree_eq_zero hn, Polynomial.eval_C] at this
    exact hQ0 (by rw [Polynomial.eq_C_of_natDegree_eq_zero hn, this, map_zero])
  | succ n ih =>
    intro Q hn hQ0 hQf
    by_cases hmap : Q.map (Polynomial.evalRingHom 0) = 0
    · -- every coefficient is divisible by `X`: divide
      have hdiv : ∀ i, (Q.coeff i).coeff 0 = 0 := by
        intro i
        have := congrArg (fun p => Polynomial.coeff p i) hmap
        simpa [Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero] using this
      set Q₁ : Polynomial (Polynomial ℂ) := ∑ i ∈ Q.support, Polynomial.monomial i (Polynomial.divX (Q.coeff i))
      have hcoeff₁ : ∀ i, Q₁.coeff i = Polynomial.divX (Q.coeff i) := by
        intro i
        simp only [Q₁, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; simp [hji]
        · intro hi; rw [Polynomial.notMem_support_iff.mp hi]; simp
      have hQeq : Q = Polynomial.C Polynomial.X * Q₁ := by
        ext1 i
        rw [Polynomial.coeff_C_mul, hcoeff₁]
        have := Polynomial.X_mul_divX_add (Q.coeff i)
        rw [hdiv i, map_zero, add_zero] at this
        exact this.symm
      refine ih Q₁ ?_ ?_ ?_
      · rw [hcoeff₁, Polynomial.natDegree_divX_eq_natDegree_tsub_one, hn]; rfl
      · intro h0
        apply hQ0
        rw [hQeq, Polynomial.coeff_C_mul, h0, mul_zero]
      · rw [hQeq, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hQf
        have hxX : (Polynomial.aeval (R := ℂ) x).toRingHom Polynomial.X = x := by simp
        rw [hxX] at hQf
        exact (mul_eq_zero.mp hQf).resolve_left hx
    · exact ⟨Q, hmap, hQf⟩

/-- **The residue of `f` is a constant**: if `v(x) > 0` and `f`, with `v(f) ≥ 0`, is algebraic over `ℂ[x]`, then
`v(f − c) > 0` for some `c ∈ ℂ`. -/
theorem exists_residue {x f : K} (hx0 : x ≠ 0) (hx : 0 < v x) (hf : 0 ≤ v f) (hrel : AlgRel x f) :
    ∃ c : ℂ, 0 < v (f - algebraMap ℂ K c) := by
  classical
  obtain ⟨Q, hQ0, hQf⟩ := normalize_algRel hx0 hrel
  set p : Polynomial ℂ := Q.map (Polynomial.evalRingHom 0)
  set ψ := (Polynomial.aeval (R := ℂ) x).toRingHom
  -- `v(p(f)) > 0`
  have hpf : 0 < v (Polynomial.aeval f p) := by
    have hdiff : Polynomial.aeval f p = -(Q.eval₂ ψ f - Polynomial.aeval f p) := by rw [hQf]; ring
    have hexp : Q.eval₂ ψ f - Polynomial.aeval f p =
        ∑ i ∈ Q.support, (ψ (Q.coeff i) - algebraMap ℂ K ((Q.coeff i).eval 0)) * f ^ i := by
      rw [Polynomial.eval₂_eq_sum, Polynomial.aeval_def, Polynomial.eval₂_eq_sum,
        Polynomial.sum_over_range' _ (fun n => by simp) (Q.natDegree + 1) (by omega),
        Polynomial.sum_over_range' _ (fun n => by simp) (Q.natDegree + 1)
          ((Polynomial.natDegree_map_le).trans_lt (by omega)),
        ← Finset.sum_sub_distrib]
      rw [← Finset.sum_subset (Polynomial.supp_subset_range (Nat.lt_succ_self Q.natDegree))]
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp [Polynomial.coeff_map, sub_mul]
      · intro i _ hi
        simp [Polynomial.notMem_support_iff.mp hi]
    rw [hdiff, AddValuation.map_neg, hexp]
    refine AddValuation.map_lt_sum v (WithTop.coe_ne_top) fun i _ => ?_
    -- `ψ(q) − q(0) = x · ψ(q.divX)`
    have hq : ψ (Q.coeff i) - algebraMap ℂ K ((Q.coeff i).eval 0) =
        x * Polynomial.aeval x (Polynomial.divX (Q.coeff i)) := by
      have h := Polynomial.X_mul_divX_add (Q.coeff i)
      have h3 : Polynomial.aeval x (Q.coeff i) =
          x * Polynomial.aeval x (Polynomial.divX (Q.coeff i)) + algebraMap ℂ K ((Q.coeff i).coeff 0) := by
        conv_lhs => rw [← h]
        rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [show ψ (Q.coeff i) = Polynomial.aeval x (Q.coeff i) from rfl, h3,
        Polynomial.coeff_zero_eq_eval_zero]
      ring
    rw [hq, AddValuation.map_mul, AddValuation.map_mul]
    have h1 := val_aeval_nonneg v (hconst_nonneg v hconst) hx.le (Polynomial.divX (Q.coeff i))
    have h2 : 0 ≤ v (f ^ i) := by rw [AddValuation.map_pow]; exact nsmul_nonneg hf i
    calc (0 : WithTop ℤ) < v x := hx
      _ ≤ v x + v (Polynomial.aeval x (Polynomial.divX (Q.coeff i))) := le_add_of_nonneg_right h1
      _ ≤ v x + v (Polynomial.aeval x (Polynomial.divX (Q.coeff i))) + v (f ^ i) := le_add_of_nonneg_right h2
  -- factor `p`
  rw [val_aeval_eq_sum_roots v hconst hQ0 f] at hpf
  by_contra hall
  push Not at hall
  have hzero : ∀ c ∈ p.roots, v (f - algebraMap ℂ K c) = 0 := by
    intro c _
    refine le_antisymm (hall c) ?_
    exact le_trans (le_min hf (hconst_nonneg v hconst c)) (AddValuation.map_sub v _ _)
  rw [Multiset.map_congr rfl hzero, Multiset.map_const', Multiset.sum_replicate, nsmul_zero] at hpf
  exact lt_irrefl _ hpf

end val

end

end CC6Full
