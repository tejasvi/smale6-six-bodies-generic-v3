import CC6Full.Six.Common
import CC6Full.Six.K4Aux

/-!
# Diagram 98: the leading data (Lemmas 6.10 and 6.11)

§6.5 of the paper (`ss:d98`). At a singular place with diagram `98` (Table 1, `Diagram.d98`), `A = {4, 5, 6}` is the
`z`-circled triangle of `z`-strokes and `B = {1, 2, 3}` the `w`-circled triangle of `w`-strokes. In Lean body `k` of
the paper is `k − 1`: `A = {3, 4, 5}` and `B = {0, 1, 2}`. Everything is stated for a germ `G : Germ 6 m` with
positive masses (`hm : ∀ i, 0 < m i`) and `G.HasDiagram Diagram.d98`.

* `Six.triA`, `Six.triB : Fin 3 → Fin 6`: the order-preserving embeddings of `A` and `B`.
* `Six.Tri.lead_z`, `Six.Tri.lead_w`: the leading system of a cluster of bodies whose pairs have `ζ = −2`, `ω = 2`
  and whose cross pairs have `ζ = −2`, `ω < 2` (colour `z`; for the colour `w`, `ζ` and `ω` exchanged): it solves
  `N(μ)` (`IsNSys`), with the proof of Lemma 6.11 (a). `Six.Tri.torque_coeff`: the coefficients of the torque `T_A`
  as a sum over the pairs between `A` and `B`. Both are shared with `D93Lead.lean` (Theorem 6.15, `thm:d93`).
* `Six.d98type_a`, `Six.d98type_b`, `Six.d98type_c`: Lemma 6.10 (`lem:d98type`) (a)–(c).
* `Six.d98lead_a`, `Six.d98lead_b`, `Six.d98lead_c`, `Six.d98lead_d`: Lemma 6.11 (`lem:d98lead`) (a)–(d), and
  `Six.d98_lead`, the four parts in one statement, with the leading data as explicit functions `Fin 3 → ℂ` on the
  renumbered triangles: `ẑ_j = [z_j]_{−2}`, `w̃_j = [w_j]_2`, `p̂_jj' = [p_jj']_0` on `A`, `ŵ_l = [w_l]_{−2}`,
  `z̃_l = [z_l]_2`, `p̂_ll' = [p_ll']_0` on `B`, and `p̂_jl = [p_jl]_2` for `j ∈ A`, `l ∈ B`.

The proofs are the paper's. In (a), the cross terms are handled through the general `Six.Tri.lead_z`: a cross pair
`jl` with `ζ_jl = −2` and `ω_jl < 2` has `e(Z_jl) = 1 − 3ω_jl/2 > −2` and `e(W_jl) = 3 − ω_jl/2 > 2`; at diagram `98`,
`ω_jl < 2` because `jl` is not a `z`-stroke ((O1) and (O6) of Lemma 2.8, `lem:orders`).
-/

namespace CC6Full

open Finset

noncomputable section

namespace Six

/-! ## The two triangles -/

/-- The order-preserving embedding of the triangle `A = {4, 5, 6}` of the paper (`{3, 4, 5}` in Lean):
`j ↦ j + 3`. -/
def triA (j : Fin 3) : Fin 6 := ⟨j.val + 3, by omega⟩

/-- The order-preserving embedding of the triangle `B = {1, 2, 3}` of the paper (`{0, 1, 2}` in Lean). -/
def triB (l : Fin 3) : Fin 6 := ⟨l.val, by omega⟩

theorem triA_val (j : Fin 3) : (triA j).val = j.val + 3 := rfl

theorem triB_val (l : Fin 3) : (triB l).val = l.val := rfl

theorem triA_zero : triA 0 = 3 := rfl
theorem triA_one : triA 1 = 4 := rfl
theorem triA_two : triA 2 = 5 := rfl
theorem triB_zero : triB 0 = 0 := rfl
theorem triB_one : triB 1 = 1 := rfl
theorem triB_two : triB 2 = 2 := rfl

theorem three_le_triA (j : Fin 3) : 3 ≤ (triA j).val := by
  rw [triA_val]
  omega

theorem triB_lt_three (l : Fin 3) : (triB l).val < 3 := l.isLt

theorem triA_injective : Function.Injective triA := fun j j' h => by
  have := congrArg Fin.val h
  rw [triA_val, triA_val] at this
  exact Fin.ext (by omega)

theorem triB_injective : Function.Injective triB := fun l l' h => by
  have := congrArg Fin.val h
  rw [triB_val, triB_val] at this
  exact Fin.ext this

theorem triA_ne_triB (j l : Fin 3) : triA j ≠ triB l := fun h => by
  have := congrArg Fin.val h
  rw [triA_val, triB_val] at this
  omega

/-- `k ∈ A` iff `k ≥ 3` in Lean's numbering. -/
theorem mem_image_triA (k : Fin 6) : k ∈ univ.image triA ↔ 3 ≤ k.val := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact three_le_triA j
  · intro h
    exact ⟨⟨k.val - 3, by omega⟩, Fin.ext (show k.val - 3 + 3 = k.val by omega)⟩

/-- `l ∈ B` iff `l < 3` in Lean's numbering. -/
theorem mem_image_triB (k : Fin 6) : k ∈ univ.image triB ↔ k.val < 3 := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨l, rfl⟩
    exact triB_lt_three l
  · intro h
    exact ⟨⟨k.val, h⟩, Fin.ext rfl⟩

/-- `B` is the complement of `A`. -/
theorem compl_image_triA : (univ.image triA)ᶜ = univ.image triB := by
  ext k
  rw [Finset.mem_compl, mem_image_triA, mem_image_triB]
  constructor <;> intro h <;> omega

/-! ## Tools: sums along an embedding, leading systems of clusters, the torque of `A` -/

namespace Tri

variable {n : ℕ} {m : Fin n → ℝ}

/-- A sum over the image of an injective map `e : Fin N → Fin n`, as a sum over `Fin N`. -/
theorem sum_image_emb {M : Type*} [AddCommMonoid M] {N : ℕ} {e : Fin N → Fin n} (he : Function.Injective e)
    (f : Fin n → M) : ∑ l ∈ univ.image e, f l = ∑ k, f (e k) :=
  Finset.sum_image he.injOn

/-- A sum over all bodies, split along an injective map `e : Fin N → Fin n`: the bodies `e k` and the others. -/
theorem sum_univ_image {M : Type*} [AddCommMonoid M] {N : ℕ} {e : Fin N → Fin n} (he : Function.Injective e)
    (f : Fin n → M) : ∑ l, f l = ∑ k, f (e k) + ∑ l ∈ (univ.image e)ᶜ, f l := by
  rw [← Finset.sum_add_sum_compl (univ.image e) f, sum_image_emb he]

/-- The coefficient form of the equation of the body `e k` in the colour `h`, split along an injective map `e`:
`[h_{e k}]_c = Σ_{k'} m_{e k'} [H_{e k, e k'}]_c + Σ_{l ∉ e(Fin N)} m_l [H_{e k, l}]_c`. -/
theorem coeff_body_image {p : Fin n → Fin n → Ser} {h h' : Fin n → Ser} (H : Colour.Pair m p h h') {N : ℕ}
    {e : Fin N → Fin n} (he : Function.Injective e) (k : Fin N) (c : ℚ) :
    (h (e k)).coeff c = ∑ k', (m (e k') : ℂ) * (termZ p h (e k) (e k')).coeff c +
      ∑ l ∈ (univ.image e)ᶜ, (m l : ℂ) * (termZ p h (e k) l).coeff c := by
  rw [H.coeff_body (e k) c, Finset.sum_erase _ (by simp [Germ.termZ_self]), sum_univ_image he]

/-- `ζ_kl < 2` if `kl` is not a `w`-stroke: `ζ_kl ≤ 2` by (O1), and `ζ_kl = 2` makes `kl` a `w`-stroke by (O6)
(Lemma 2.8, `lem:orders`). -/
theorem zeta_lt_two (G : Germ n m) {k l : Fin n} (hkl : k ≠ l) (hs : ¬ G.wStroke k l) : G.zeta k l < 2 :=
  lt_of_le_of_ne (G.O1_le hkl).1 fun h => hs (G.O6_z' h).2

/-- `ω_kl < 2` if `kl` is not a `z`-stroke ((O1) and (O6) of Lemma 2.8, `lem:orders`). -/
theorem omega_lt_two (G : Germ n m) {k l : Fin n} (hkl : k ≠ l) (hs : ¬ G.zStroke k l) : G.omega k l < 2 :=
  lt_of_le_of_ne (G.O1_le hkl).2.1 fun h => hs (G.O6_w' h).2

/-- A finite exponent below `c`. -/
theorem exists_coe_of_lt {u : WithTop ℚ} {c : ℚ} (h : u < c) : ∃ A : ℚ, u = A ∧ A < c := by
  induction u using WithTop.recTopCoe with
  | top => exact absurd h not_top_lt
  | coe A => exact ⟨A, rfl, WithTop.coe_lt_coe.mp h⟩

/-- **The leading system of a cluster**, colour `z` (the proof of Lemma 6.11 (a), `lem:d98lead`). Let
`e : Fin N → Fin n` be injective, such that `ζ = −2` and `ω = 2` on the pairs `e k, e k'` of the cluster, and
`ζ_{e k, l} = −2`, `ω_{e k, l} < 2` for the bodies `l` outside it. Then `(ẑ, w̃, p̂)` with `ẑ_k = [z_{e k}]_{−2}`,
`w̃_k = [w_{e k}]_2` and `p̂_kk' = [p_{e k, e k'}]_0` solves `N(m ∘ e)`: in the `z`-equation of `e k` the terms
`Z_{e k, e k'}` have exponent `−2`, with coefficient `p̂_kk'³ (ẑ_k − ẑ_k')` there, and the terms `Z_{e k, l}` have
exponent `1 − 3ω_{e k, l}/2 > −2`; in the `w`-equation the terms `W_{e k, e k'}` have exponent `2` and the terms
`W_{e k, l}` exponent `3 − ω_{e k, l}/2 > 2`; and the distance equation of the pair `e k, e k'` at exponent `0` gives
`p̂_kk'² (ẑ_k − ẑ_k')(w̃_k − w̃_k') = 1`. -/
theorem lead_z (G : Germ n m) {N : ℕ} {e : Fin N → Fin n} (he : Function.Injective e)
    (hin : ∀ k k', k ≠ k' → G.zeta (e k) (e k') = -2 ∧ G.omega (e k) (e k') = 2)
    (hout : ∀ k, ∀ l ∉ univ.image e, G.zeta (e k) l = -2 ∧ G.omega (e k) l < 2) :
    IsNSys (fun k => (m (e k) : ℂ)) (fun k => (G.z (e k)).coeff (-2)) (fun k => (G.w (e k)).coeff 2)
      (fun k k' => (G.p (e k) (e k')).coeff 0) := by
  have hne : ∀ {k k' : Fin N}, k ≠ k' → e k ≠ e k' := fun h h' => h (he h')
  have hne' : ∀ k, ∀ l ∉ univ.image e, e k ≠ l := fun k l hl h =>
    hl (h ▸ Finset.mem_image_of_mem e (Finset.mem_univ k))
  -- the exponents on the pairs of the cluster: `e(p) = 0`, `ζ = −2`, `ω = 2`
  have hp : ∀ k k', k ≠ k' → (G.p (e k) (e k')).orderTop = ((0 : ℚ) : WithTop ℚ) := fun k k' h => by
    rw [G.orderTop_p (hne h), G.x_eq (hne h), (hin k k' h).1, (hin k k' h).2]
    norm_num
  have hz : ∀ k k', k ≠ k' → (G.z (e k) - G.z (e k')).orderTop = ((-2 : ℚ) : WithTop ℚ) := fun k k' h => by
    rw [G.orderTop_z_sub (hne h), (hin k k' h).1]
  have hw : ∀ k k', k ≠ k' → (G.w (e k) - G.w (e k')).orderTop = ((2 : ℚ) : WithTop ℚ) := fun k k' h => by
    rw [G.orderTop_w_sub (hne h), (hin k k' h).2]
  refine ⟨fun k k' => ?_, fun k => ?_, fun k => ?_, fun k k' h => ?_⟩
  · show (G.p (e k) (e k')).coeff 0 = (G.p (e k') (e k)).coeff 0
    rw [G.p_symm]
  · -- the `z`-equation of `e k` at exponent `−2`
    show (G.z (e k)).coeff (-2) = force _ _ _ k
    have hcross : ∑ l ∈ (univ.image e)ᶜ, (m l : ℂ) * (termZ G.p G.z (e k) l).coeff (-2) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have hl' := Finset.mem_compl.mp hl
      have hlt : ((-2 : ℚ) : WithTop ℚ) < (termZ G.p G.z (e k) l).orderTop := by
        rw [G.orderTop_termZ_z (hne' k l hl'), (hout k l hl').1]
        exact WithTop.coe_lt_coe.mpr (by linarith [(hout k l hl').2])
      rw [Ser.coeff_eq_zero_of_lt hlt, mul_zero]
    rw [coeff_body_image G.colZ he k (-2), hcross, add_zero, K4.force_eq_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    by_cases hkk : k = k'
    · subst hkk
      simp [Germ.termZ_self]
    · have c := K4.coeff_termZ (hp k k' hkk).ge (hz k k' hkk).ge
      rw [show 3 * (0 : ℚ) + -2 = -2 by norm_num, Ser.coeff_sub] at c
      rw [c]
      ring
  · -- the `w`-equation of `e k` at exponent `2`
    show (G.w (e k)).coeff 2 = force _ _ _ k
    have hcross : ∑ l ∈ (univ.image e)ᶜ, (m l : ℂ) * (termZ G.p G.w (e k) l).coeff 2 = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have hl' := Finset.mem_compl.mp hl
      have hlt : ((2 : ℚ) : WithTop ℚ) < (termZ G.p G.w (e k) l).orderTop := by
        rw [G.orderTop_termZ_w (hne' k l hl'), (hout k l hl').1]
        exact WithTop.coe_lt_coe.mpr (by linarith [(hout k l hl').2])
      rw [Ser.coeff_eq_zero_of_lt hlt, mul_zero]
    rw [coeff_body_image G.colW he k 2, hcross, add_zero, K4.force_eq_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    by_cases hkk : k = k'
    · subst hkk
      simp [Germ.termZ_self]
    · have c := K4.coeff_termZ (hp k k' hkk).ge (hw k k' hkk).ge
      rw [show 3 * (0 : ℚ) + 2 = 2 by norm_num, Ser.coeff_sub] at c
      rw [c]
      ring
  · -- the distance equation of `e k, e k'` at exponent `0`
    show (G.p (e k) (e k')).coeff 0 ^ 2 * ((G.z (e k)).coeff (-2) - (G.z (e k')).coeff (-2)) *
      ((G.w (e k)).coeff 2 - (G.w (e k')).coeff 2) = 1
    have d := K4.coeff_dist G (hne h) (hp k k' h).ge (hz k k' h).ge (hw k k' h).ge (by norm_num)
    rwa [Ser.coeff_sub, Ser.coeff_sub] at d

/-- **The leading system of a cluster**, colour `w` (`lead_z` with the colours exchanged, Lemma 2.9 (b),
`lem:symm`): if `ω = −2` and `ζ = 2` on the pairs of the cluster `e(Fin N)`, and `ω_{e k, l} = −2`,
`ζ_{e k, l} < 2` for the bodies `l` outside it, then `(ŵ, z̃, p̂)` with `ŵ_k = [w_{e k}]_{−2}`, `z̃_k = [z_{e k}]_2`
and `p̂_kk' = [p_{e k, e k'}]_0` solves `N(m ∘ e)`. -/
theorem lead_w (G : Germ n m) {N : ℕ} {e : Fin N → Fin n} (he : Function.Injective e)
    (hin : ∀ k k', k ≠ k' → G.omega (e k) (e k') = -2 ∧ G.zeta (e k) (e k') = 2)
    (hout : ∀ k, ∀ l ∉ univ.image e, G.omega (e k) l = -2 ∧ G.zeta (e k) l < 2) :
    IsNSys (fun k => (m (e k) : ℂ)) (fun k => (G.w (e k)).coeff (-2)) (fun k => (G.z (e k)).coeff 2)
      (fun k k' => (G.p (e k) (e k')).coeff 0) :=
  lead_z G.swap he hin hout

/-- The coefficient of exponent `c` of the torque `T_A = 0` of `A = {4, 5, 6}` (`Germ.torque`), as a sum over the
pairs `jl` with `j ∈ A`, `l ∈ B` (renumbered by `triA`, `triB`). -/
theorem torque_coeff {m : Fin 6 → ℝ} (G : Germ 6 m) (c : ℚ) :
    ∑ j : Fin 3, ∑ l : Fin 3, (cS (m (triA j)) * cS (m (triB l)) * (G.p (triA j) (triB l) ^ 3 *
      (G.z (triA j) * G.w (triB l) - G.z (triB l) * G.w (triA j)))).coeff c = 0 := by
  have hT := congrArg (fun f : Ser => f.coeff c) (G.torque (univ.image triA))
  simp only [HahnSeries.coeff_zero, Ser.coeff_sum] at hT
  rw [compl_image_triA] at hT
  simp only [sum_image_emb triA_injective, sum_image_emb triB_injective] at hT
  exact hT

end Tri

/-! ## The diagram -/

theorem d98_zS (k l : Fin 6) : Diagram.d98.zS k l ↔ (k ≠ l ∧ 3 ≤ k.val ∧ 3 ≤ l.val) := by
  revert k l
  unfold Diagram.zS
  decide

theorem d98_wS (k l : Fin 6) : Diagram.d98.wS k l ↔ (k ≠ l ∧ k.val < 3 ∧ l.val < 3) := by
  revert k l
  unfold Diagram.wS
  decide

theorem d98_zC (k : Fin 6) : k ∈ Diagram.d98.zCircles ↔ 3 ≤ k.val := by
  revert k
  decide

theorem d98_wC (k : Fin 6) : k ∈ Diagram.d98.wCircles ↔ k.val < 3 := by
  revert k
  decide

variable {m : Fin 6 → ℝ}

/-- The diagram `98` read on the germ: `z`-strokes on the pairs of `A`, `w`-strokes on the pairs of `B`, the
`z`-circles `A` and the `w`-circles `B`. -/
theorem d98_facts {G : Germ 6 m} (hD : G.HasDiagram Diagram.d98) :
    (∀ k l, G.zStroke k l ↔ (k ≠ l ∧ 3 ≤ k.val ∧ 3 ≤ l.val)) ∧
      (∀ k l, G.wStroke k l ↔ (k ≠ l ∧ k.val < 3 ∧ l.val < 3)) ∧ (∀ k, G.zCircle k ↔ 3 ≤ k.val) ∧
        (∀ k, G.wCircle k ↔ k.val < 3) :=
  ⟨fun k l => (hD.1 k l).trans (d98_zS k l), fun k l => (hD.2.1 k l).trans (d98_wS k l),
    fun k => (hD.2.2.1 k).trans (d98_zC k), fun k => (hD.2.2.2 k).trans (d98_wC k)⟩

/-- At diagram `98` the pairs of `A` are `z`-strokes. -/
theorem d98_zA {G : Germ 6 m} (hD : G.HasDiagram Diagram.d98) :
    ∀ k ∈ univ.image triA, ∀ l ∈ univ.image triA, k ≠ l → G.zStroke k l := fun k hk l hl hkl =>
  ((d98_facts hD).1 k l).mpr ⟨hkl, (mem_image_triA k).mp hk, (mem_image_triA l).mp hl⟩

/-- At diagram `98` the `z`-circled bodies lie in `A`. -/
theorem d98_zcA {G : Germ 6 m} (hD : G.HasDiagram Diagram.d98) :
    ∀ k, G.zCircle k → k ∈ univ.image triA := fun k hk =>
  (mem_image_triA k).mpr (((d98_facts hD).2.2.1 k).mp hk)

/-- At diagram `98` the pairs of `B` are `w`-strokes. -/
theorem d98_wB {G : Germ 6 m} (hD : G.HasDiagram Diagram.d98) :
    ∀ k ∈ univ.image triB, ∀ l ∈ univ.image triB, k ≠ l → G.wStroke k l := fun k hk l hl hkl =>
  ((d98_facts hD).2.1 k l).mpr ⟨hkl, (mem_image_triB k).mp hk, (mem_image_triB l).mp hl⟩

/-- At diagram `98` the `w`-circled bodies lie in `B`. -/
theorem d98_wcB {G : Germ 6 m} (hD : G.HasDiagram Diagram.d98) :
    ∀ k, G.wCircle k → k ∈ univ.image triB := fun k hk =>
  (mem_image_triB k).mpr (((d98_facts hD).2.2.2 k).mp hk)

/-! ## Lemma 6.10 -/

/-- **Lemma 6.10 (a)** (`lem:d98type`): at a singular place with diagram `98`, `ζ = −2`, `ω = 2`, `x = 0` on the
pairs of `A`, and `ω = −2`, `ζ = 2`, `x = 0` on the pairs of `B` ((F1) of Lemma 6.1, `lem:common`, in both
colours). Here `A = {3, 4, 5}` and `B = {0, 1, 2}` in Lean's numbering. -/
theorem d98type_a (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d98) :
    (∀ j j' : Fin 6, 3 ≤ j.val → 3 ≤ j'.val → j ≠ j' →
        G.zeta j j' = -2 ∧ G.omega j j' = 2 ∧ G.x j j' = 0) ∧
      ∀ l l' : Fin 6, l.val < 3 → l'.val < 3 → l ≠ l' →
        G.omega l l' = -2 ∧ G.zeta l l' = 2 ∧ G.x l l' = 0 := by
  obtain ⟨-, -, hzc, hwc⟩ := d98_facts hD
  refine ⟨fun j j' hj hj' hjj => ?_, fun l l' hl hl' hll => ?_⟩
  · exact F1_z hm G (d98_zA hD)
      ⟨triA 0, Finset.mem_image_of_mem _ (Finset.mem_univ _), (hzc _).mpr (three_le_triA 0)⟩ (d98_zcA hD)
      ((mem_image_triA j).mpr hj) ((mem_image_triA j').mpr hj') hjj
  · exact F1_w hm G (d98_wB hD)
      ⟨triB 0, Finset.mem_image_of_mem _ (Finset.mem_univ _), (hwc _).mpr (triB_lt_three 0)⟩ (d98_wcB hD)
      ((mem_image_triB l).mpr hl) ((mem_image_triB l').mpr hl') hll

/-- **Lemma 6.10 (b)** (`lem:d98type`): at a singular place with diagram `98`, `ζ = ω = −2` and `x = −2` on the nine
pairs `jl` with `j ∈ A`, `l ∈ B` ((O6) of Lemma 2.8, `lem:orders`, in both colours). -/
theorem d98type_b (G : Germ 6 m) (hD : G.HasDiagram Diagram.d98) :
    ∀ j l : Fin 6, 3 ≤ j.val → l.val < 3 →
      G.zeta j l = -2 ∧ G.omega j l = -2 ∧ G.x j l = -2 := by
  obtain ⟨-, -, hzc, hwc⟩ := d98_facts hD
  intro j l hj hl
  have hjl : j ≠ l := fun h => by
    rw [h] at hj
    omega
  have hζ : G.zeta j l = -2 :=
    G.O6_z ((hzc j).mpr hj) fun h => by
      have := (hzc l).mp h
      omega
  have hω : G.omega j l = -2 := by
    rw [G.omega_comm]
    exact G.O6_w ((hwc l).mpr hl) fun h => by
      have := (hwc j).mp h
      omega
  refine ⟨hζ, hω, ?_⟩
  rw [G.x_eq hjl, hζ, hω]
  norm_num

/-- **Lemma 6.10 (c)** (`lem:d98type`): at a singular place with diagram `98`, `a_j = −2` and `b_j ≥ 2` for `j ∈ A`,
and `b_l = −2` and `a_l ≥ 2` for `l ∈ B` ((F2) of Lemma 6.1, `lem:common`, in both colours). -/
theorem d98type_c (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d98) :
    (∀ j : Fin 6, 3 ≤ j.val →
        (G.z j).orderTop = ((-2 : ℚ) : WithTop ℚ) ∧ ((2 : ℚ) : WithTop ℚ) ≤ (G.w j).orderTop) ∧
      ∀ l : Fin 6, l.val < 3 →
        (G.w l).orderTop = ((-2 : ℚ) : WithTop ℚ) ∧ ((2 : ℚ) : WithTop ℚ) ≤ (G.z l).orderTop := by
  obtain ⟨-, -, hzc, hwc⟩ := d98_facts hD
  exact ⟨fun j hj => ⟨(hzc j).mpr hj, F2_z hm G (d98_zA hD) (d98_zcA hD) ((hzc j).mpr hj)⟩,
    fun l hl => ⟨(hwc l).mpr hl, F2_w hm G (d98_wB hD) (d98_wcB hD) ((hwc l).mpr hl)⟩⟩

/-! ## Lemma 6.11 -/

/-- **Lemma 6.11 (a)** (`lem:d98lead`): at a singular place with diagram `98`, `(ẑ_A, w̃_A, p̂_A)` with
`ẑ_j = [z_j]_{−2}`, `w̃_j = [w_j]_2` and `p̂_jj' = [p_jj']_0` (`A` renumbered by `triA`) is a solution of `N(m_A)`, and
`ẑ_j ≠ 0` for `j ∈ A`. In the `z`-equation of `j ∈ A` the terms `Z_jj'`, `j' ∈ A`, have exponent `−2` and the terms
`Z_jl`, `l ∈ B`, exponent `4`; in its `w`-equation the terms `W_jj'` have exponent `2` and the terms `W_jl` exponent
`4`; the distance equation of `jj'` is taken at exponent `0` (`Tri.lead_z`). -/
theorem d98lead_a (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d98) :
    IsNSys (fun j => (m (triA j) : ℂ)) (fun j => (G.z (triA j)).coeff (-2)) (fun j => (G.w (triA j)).coeff 2)
        (fun j j' => (G.p (triA j) (triA j')).coeff 0) ∧
      ∀ j, (G.z (triA j)).coeff (-2) ≠ 0 := by
  obtain ⟨hz, -, hzc, -⟩ := d98_facts hD
  obtain ⟨hA, -⟩ := d98type_a hm G hD
  refine ⟨Tri.lead_z G triA_injective (fun j j' h => ?_) (fun j l hl => ?_), fun j => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hA _ _ (three_le_triA j) (three_le_triA j') (triA_injective.ne h)
    exact ⟨h1, h2⟩
  · have hl3 : l.val < 3 := by
      rw [mem_image_triA] at hl
      omega
    have hj3 := three_le_triA j
    have hjl : triA j ≠ l := fun h => by
      rw [h] at hj3
      omega
    refine ⟨G.O6_z ((hzc _).mpr hj3) fun h => ?_, Tri.omega_lt_two G hjl fun h => ?_⟩
    · have := (hzc l).mp h
      omega
    · have := ((hz _ l).mp h).2.2
      omega
  · exact (G.colZ.circle_iff_coeff (triA j)).mp ((hzc _).mpr (three_le_triA j))

/-- **Lemma 6.11 (b)** (`lem:d98lead`): at a singular place with diagram `98`, `(ŵ_B, z̃_B, p̂_B)` with
`ŵ_l = [w_l]_{−2}`, `z̃_l = [z_l]_2` and `p̂_ll' = [p_ll']_0` (`B` renumbered by `triB`) is a solution of `N(m_B)`, and
`ŵ_l ≠ 0` for `l ∈ B`: (a) with the colours exchanged (`Tri.lead_w`). -/
theorem d98lead_b (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d98) :
    IsNSys (fun l => (m (triB l) : ℂ)) (fun l => (G.w (triB l)).coeff (-2)) (fun l => (G.z (triB l)).coeff 2)
        (fun l l' => (G.p (triB l) (triB l')).coeff 0) ∧
      ∀ l, (G.w (triB l)).coeff (-2) ≠ 0 := by
  obtain ⟨-, hw, -, hwc⟩ := d98_facts hD
  obtain ⟨-, hB⟩ := d98type_a hm G hD
  refine ⟨Tri.lead_w G triB_injective (fun l l' h => ?_) (fun l j hj => ?_), fun l => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hB _ _ (triB_lt_three l) (triB_lt_three l') (triB_injective.ne h)
    exact ⟨h1, h2⟩
  · have hj3 : 3 ≤ j.val := by
      rw [mem_image_triB] at hj
      omega
    have hl3 := triB_lt_three l
    have hlj : triB l ≠ j := fun h => by
      rw [h] at hl3
      omega
    refine ⟨G.O6_w ((hwc _).mpr hl3) fun h => ?_, Tri.zeta_lt_two G hlj fun h => ?_⟩
    · have := (hwc j).mp h
      omega
    · have := ((hw _ j).mp h).2.2
      omega
  · exact (G.colW.circle_iff_coeff (triB l)).mp ((hwc _).mpr (triB_lt_three l))

/-- **Lemma 6.11 (c)** (`lem:d98lead`): at a singular place with diagram `98`, `p̂_jl² ẑ_j ŵ_l = −1` for `j ∈ A`,
`l ∈ B`, with `p̂_jl = [p_jl]_2`, `ẑ_j = [z_j]_{−2}` and `ŵ_l = [w_l]_{−2}` ((F4) of Lemma 6.1, `lem:common`). -/
theorem d98lead_c (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d98) :
    ∀ j l : Fin 3,
      (G.p (triA j) (triB l)).coeff 2 ^ 2 * (G.z (triA j)).coeff (-2) * (G.w (triB l)).coeff (-2) = -1 := by
  obtain ⟨hA, hB⟩ := d98type_c hm G hD
  intro j l
  obtain ⟨hzj, hwj⟩ := hA _ (three_le_triA j)
  obtain ⟨hwl, hzl⟩ := hB _ (triB_lt_three l)
  have h := (K4.f4 G (triA_ne_triB j l) hzj hwl
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hzl)
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hwj)).2.2.2
  rw [show (-((-2 + -2) / 2) : ℚ) = 2 by norm_num] at h
  exact h

/-- **Lemma 6.11 (d)** (`lem:d98lead`): at a singular place with diagram `98`, `Σ_{j∈A, l∈B} m_j m_l p̂_jl = 0`. In the
torque `T_A` all terms have exponent at least `2` by (F4), and the coefficient of exponent `2` is
`−Σ m_j m_l p̂_jl`. -/
theorem d98lead_d (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d98) :
    ∑ j : Fin 3, ∑ l : Fin 3, (m (triA j) : ℂ) * (m (triB l) : ℂ) * (G.p (triA j) (triB l)).coeff 2 = 0 := by
  obtain ⟨hA, hB⟩ := d98type_c hm G hD
  have hterm : ∀ j l : Fin 3, (cS (m (triA j)) * cS (m (triB l)) * (G.p (triA j) (triB l) ^ 3 *
      (G.z (triA j) * G.w (triB l) - G.z (triB l) * G.w (triA j)))).coeff 2 =
        -((m (triA j) : ℂ) * (m (triB l) : ℂ) * (G.p (triA j) (triB l)).coeff 2) := by
    intro j l
    obtain ⟨hzj, hwj⟩ := hA _ (three_le_triA j)
    obtain ⟨hwl, hzl⟩ := hB _ (triB_lt_three l)
    have hal : ((-2 : ℚ) : WithTop ℚ) < (G.z (triB l)).orderTop :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hzl
    have hbj : ((-2 : ℚ) : WithTop ℚ) < (G.w (triA j)).orderTop :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hwj
    have hc := (K4.f4_term G (triA_ne_triB j l) hzj hwl hal hbj (K4.coe_add_lt hal.le hbj)).2
    rw [show (-((-2 + -2) / 2) : ℚ) = 2 by norm_num] at hc
    rw [← cS_mul, Ser.coeff_cS_mul, hc]
    ring
  have hT := Tri.torque_coeff G 2
  simp only [hterm, Finset.sum_neg_distrib, neg_eq_zero] at hT
  exact hT

/-- **Lemma 6.11** (`lem:d98lead`), parts (a)–(d) in one statement. At a singular place with diagram `98`
(`A = {4, 5, 6}` and `B = {1, 2, 3}` of the paper, renumbered `0, 1, 2` in increasing order by `triA`, `triB`), with
`ẑ_j = [z_j]_{−2}`, `w̃_j = [w_j]_2`, `p̂_jj' = [p_jj']_0` for `j, j' ∈ A`, `ŵ_l = [w_l]_{−2}`, `z̃_l = [z_l]_2`,
`p̂_ll' = [p_ll']_0` for `l, l' ∈ B`, and `p̂_jl = [p_jl]_2`:
(a) `(ẑ_A, w̃_A, p̂_A)` solves `N(m_A)` and `ẑ_j ≠ 0`; (b) `(ŵ_B, z̃_B, p̂_B)` solves `N(m_B)` and `ŵ_l ≠ 0`;
(c) `p̂_jl² ẑ_j ŵ_l = −1`; (d) `Σ_{j∈A, l∈B} m_j m_l p̂_jl = 0`. -/
theorem d98_lead (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d98) :
    (IsNSys (fun j => (m (triA j) : ℂ)) (fun j => (G.z (triA j)).coeff (-2))
        (fun j => (G.w (triA j)).coeff 2) (fun j j' => (G.p (triA j) (triA j')).coeff 0) ∧
      ∀ j, (G.z (triA j)).coeff (-2) ≠ 0) ∧
    (IsNSys (fun l => (m (triB l) : ℂ)) (fun l => (G.w (triB l)).coeff (-2))
        (fun l => (G.z (triB l)).coeff 2) (fun l l' => (G.p (triB l) (triB l')).coeff 0) ∧
      ∀ l, (G.w (triB l)).coeff (-2) ≠ 0) ∧
    (∀ j l : Fin 3,
      (G.p (triA j) (triB l)).coeff 2 ^ 2 * (G.z (triA j)).coeff (-2) * (G.w (triB l)).coeff (-2) = -1) ∧
    ∑ j : Fin 3, ∑ l : Fin 3, (m (triA j) : ℂ) * (m (triB l) : ℂ) * (G.p (triA j) (triB l)).coeff 2 = 0 :=
  ⟨d98lead_a hm G hD, d98lead_b hm G hD, d98lead_c hm G hD, d98lead_d hm G hD⟩

end Six

end

end CC6Full
