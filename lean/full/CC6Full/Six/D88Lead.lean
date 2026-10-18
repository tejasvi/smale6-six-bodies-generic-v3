import CC6Full.Six.D98Lead

/-!
# Diagrams 88 and 94: the leading data (Lemmas 6.16 and 6.17)

§6.7 of the paper (`ss:d88`). In diagram `88` (Table 1, `Diagram.d88`) the binary `{5, 6}` is `z`-circled and the
four bodies of `K = {1, 2, 3, 4}` are `w`-circled and pairwise joined by `w`-strokes. In diagram `94`
(`Diagram.d94`) the triangle `{4, 5, 6}` carries `z`-strokes with circles at `5`, `6`, and `Q = {1, 2, 3, 4}` carries
`w`-strokes on all pairs with circles at `1`, `2`, `3`. In Lean body `k` of the paper is `k − 1`: the binary is
`{4, 5}`, renumbered `0, 1` by `Six.bin`; `K = Q = {0, 1, 2, 3}`, renumbered by `Six.quad`; and the bodies `1, 2, 3`
of `Q` are renumbered by `Six.triB`. Everything about germs is stated for `G : Germ 6 m` with positive masses
(`hm : ∀ i, 0 < m i`).

* `Six.Quad.coeff_body_force`: the equation of a body `e k` of a cluster at an exponent `c` at which the terms of the
  pairs of the cluster have the coefficient `p̂³ (ĥ_k − ĥ_k')` and the cross terms vanish, as a force equation of the
  leading data. `Six.Quad.lead_dist`: the distance equations of the leading data of a cluster of `w`-strokes.
* `Six.d88_exps`, `Six.d88_lead`: the exponents in the proof of Lemma 6.16 (a) (`lem:d88lead`), and Lemma 6.16 (a)
  itself, with the leading data as explicit functions on `Fin 2` (the binary) and `Fin 4` (the cluster `K`).
* `Six.d94_exps`, `Six.d94_lead`: the same for Lemma 6.16 (b); the sums over `l ≤ 3` are over `Fin 3`.
* `Six.Ttest_a`, `Six.Ttest_b`: Lemma 6.17 (`lem:Ttest`) (a) and (b), as statements about complex numbers, and
  `Six.d88_Ttest`, `Six.d94_Ttest`: their application to the leading data of Lemma 6.16.

The proofs are the paper's. In (b) of Lemma 6.16 the pairs `(j, 4)`, `j ∈ {5, 6}`, of the torque `T_{5,6}` are
handled by Lemma 6.2 (`lem:rewrite`) with `o = 4`: their contribution is `m_4 (w_4 B_z − z_4 B_w)`, of exponent at
least `4`.
-/

namespace CC6Full

open Finset

noncomputable section

namespace Six

/-! ## The binary and the cluster of four bodies -/

/-- The order-preserving embedding of the binary `{5, 6}` of the paper (`{4, 5}` in Lean): `j ↦ j + 4`. -/
def bin (j : Fin 2) : Fin 6 := ⟨j.val + 4, by omega⟩

/-- The order-preserving embedding of the cluster `K = Q = {1, 2, 3, 4}` of the paper (`{0, 1, 2, 3}` in Lean). -/
def quad (l : Fin 4) : Fin 6 := ⟨l.val, by omega⟩

theorem bin_val (j : Fin 2) : (bin j).val = j.val + 4 := rfl

theorem quad_val (l : Fin 4) : (quad l).val = l.val := rfl

theorem four_le_bin (j : Fin 2) : 4 ≤ (bin j).val := by
  rw [bin_val]
  omega

theorem quad_lt_four (l : Fin 4) : (quad l).val < 4 := l.isLt

theorem bin_injective : Function.Injective bin := fun j j' h => by
  have := congrArg Fin.val h
  rw [bin_val, bin_val] at this
  exact Fin.ext (by omega)

theorem quad_injective : Function.Injective quad := fun l l' h => by
  have := congrArg Fin.val h
  rw [quad_val, quad_val] at this
  exact Fin.ext this

theorem bin_ne_quad (j : Fin 2) (l : Fin 4) : bin j ≠ quad l := fun h => by
  have := congrArg Fin.val h
  rw [bin_val, quad_val] at this
  omega

theorem bin_ne_triB (j : Fin 2) (l : Fin 3) : bin j ≠ triB l := fun h => by
  have := congrArg Fin.val h
  rw [bin_val, triB_val] at this
  omega

/-- The bodies `1, 2, 3` of `Q` (`triB`) are the first three bodies of `quad`. -/
theorem quad_castSucc (l : Fin 3) : quad (Fin.castSucc l) = triB l := rfl

/-- The body `4` of `Q` is `3` in Lean. -/
theorem quad_last : quad (Fin.last 3) = 3 := rfl

/-- `k` is in the binary iff `k ≥ 4` in Lean's numbering. -/
theorem mem_image_bin (k : Fin 6) : k ∈ univ.image bin ↔ 4 ≤ k.val := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact four_le_bin j
  · intro h
    exact ⟨⟨k.val - 4, by omega⟩, Fin.ext (show k.val - 4 + 4 = k.val by omega)⟩

/-- `k` is in the cluster `K = Q` iff `k < 4` in Lean's numbering. -/
theorem mem_image_quad (k : Fin 6) : k ∈ univ.image quad ↔ k.val < 4 := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨l, rfl⟩
    exact quad_lt_four l
  · intro h
    exact ⟨⟨k.val, h⟩, Fin.ext rfl⟩

/-- The cluster `K = Q` is the complement of the binary. -/
theorem compl_image_bin : (univ.image bin)ᶜ = univ.image quad := by
  ext k
  rw [Finset.mem_compl, mem_image_bin, mem_image_quad]
  constructor <;> intro h <;> omega

/-! ## Tools: force equations and distance equations of the leading data of a cluster -/

namespace Quad

variable {n : ℕ} {m : Fin n → ℝ}

/-- The equation of a body of a cluster at one exponent, as a force equation of the leading data (the proof of
Lemma 6.16, `lem:d88lead`). Let `e : Fin N → Fin n` be injective, `h` a colour and `c` an exponent such that for the
pairs `e k, e k'` of the cluster `e(p_{e k, e k'}) ≥ 0` and `e(h_{e k} − h_{e k'}) ≥ c`, and such that the cross terms
`H_{e k, l}`, `l ∉ e(Fin N)`, vanish at exponent `c`. Then the equation of the body `e k` at exponent `c` reads
`ĥ_k = Σ_{k'} m_{e k'} p̂_kk'³ (ĥ_k − ĥ_k')` with `ĥ_k = [h_{e k}]_c` and `p̂_kk' = [p_{e k, e k'}]_0`. -/
theorem coeff_body_force {p : Fin n → Fin n → Ser} {h h' : Fin n → Ser} (H : Colour.Pair m p h h') {N : ℕ}
    {e : Fin N → Fin n} (he : Function.Injective e) (k : Fin N) (c : ℚ)
    (hin : ∀ k', k' ≠ k → ((0 : ℚ) : WithTop ℚ) ≤ (p (e k) (e k')).orderTop ∧
      (c : WithTop ℚ) ≤ (h (e k) - h (e k')).orderTop)
    (hout : ∀ l ∉ univ.image e, (termZ p h (e k) l).coeff c = 0) :
    (h (e k)).coeff c = force (fun k => (m (e k) : ℂ)) (fun k k' => (p (e k) (e k')).coeff 0)
      (fun k => (h (e k)).coeff c) k := by
  have hcross : ∑ l ∈ (univ.image e)ᶜ, (m l : ℂ) * (termZ p h (e k) l).coeff c = 0 :=
    Finset.sum_eq_zero fun l hl => by rw [hout l (Finset.mem_compl.mp hl), mul_zero]
  rw [Tri.coeff_body_image H he k c, hcross, add_zero, K4.force_eq_sum]
  refine Finset.sum_congr rfl fun k' _ => ?_
  by_cases hkk : k' = k
  · subst hkk
    simp [Germ.termZ_self]
  · have cc := K4.coeff_termZ (hin k' hkk).1 (hin k' hkk).2
    rw [show 3 * (0 : ℚ) + c = c by ring, Ser.coeff_sub] at cc
    rw [cc]
    ring

/-- The distance equations of the leading data of a cluster of `w`-strokes (the proof of Lemma 6.16,
`lem:d88lead`): if `ω = −2` and `ζ = 2` on the pairs `e k, e k'`, the distance equation of the pair at exponent `0`
gives `p̂_kk'² (X_k − X_k')(Y_k − Y_k') = 1` with `X_k = [w_{e k}]_{−2}`, `Y_k = [z_{e k}]_2` and
`p̂_kk' = [p_{e k, e k'}]_0`. -/
theorem lead_dist (G : Germ n m) {N : ℕ} {e : Fin N → Fin n} (he : Function.Injective e)
    (hin : ∀ k k', k ≠ k' → G.omega (e k) (e k') = -2 ∧ G.zeta (e k) (e k') = 2) :
    DistEqs (fun k k' => (G.p (e k) (e k')).coeff 0) (fun k => (G.w (e k)).coeff (-2))
      (fun k => (G.z (e k)).coeff 2) := by
  intro k k' h
  have hne : e k ≠ e k' := he.ne h
  obtain ⟨hω, hζ⟩ := hin k k' h
  have hp : (G.p (e k) (e k')).orderTop = ((0 : ℚ) : WithTop ℚ) := by
    rw [G.orderTop_p hne, G.x_eq hne, hζ, hω]
    norm_num
  have hz : (G.z (e k) - G.z (e k')).orderTop = ((2 : ℚ) : WithTop ℚ) := by
    rw [G.orderTop_z_sub hne, hζ]
  have hw : (G.w (e k) - G.w (e k')).orderTop = ((-2 : ℚ) : WithTop ℚ) := by
    rw [G.orderTop_w_sub hne, hω]
  have d := K4.coeff_dist G hne hp.ge hz.ge hw.ge (by norm_num)
  rw [Ser.coeff_sub, Ser.coeff_sub] at d
  show (G.p (e k) (e k')).coeff 0 ^ 2 * ((G.w (e k)).coeff (-2) - (G.w (e k')).coeff (-2)) *
    ((G.z (e k)).coeff 2 - (G.z (e k')).coeff 2) = 1
  linear_combination d

end Quad

/-! ## The diagrams -/

theorem d88_zS (k l : Fin 6) : Diagram.d88.zS k l ↔ (k ≠ l ∧ 4 ≤ k.val ∧ 4 ≤ l.val) := by
  revert k l
  unfold Diagram.zS
  decide

theorem d88_wS (k l : Fin 6) : Diagram.d88.wS k l ↔ (k ≠ l ∧ k.val < 4 ∧ l.val < 4) := by
  revert k l
  unfold Diagram.wS
  decide

theorem d88_zC (k : Fin 6) : k ∈ Diagram.d88.zCircles ↔ 4 ≤ k.val := by
  revert k
  decide

theorem d88_wC (k : Fin 6) : k ∈ Diagram.d88.wCircles ↔ k.val < 4 := by
  revert k
  decide

theorem d94_zS (k l : Fin 6) : Diagram.d94.zS k l ↔ (k ≠ l ∧ 3 ≤ k.val ∧ 3 ≤ l.val) := by
  revert k l
  unfold Diagram.zS
  decide

theorem d94_wS (k l : Fin 6) : Diagram.d94.wS k l ↔ (k ≠ l ∧ k.val < 4 ∧ l.val < 4) := by
  revert k l
  unfold Diagram.wS
  decide

theorem d94_zC (k : Fin 6) : k ∈ Diagram.d94.zCircles ↔ 4 ≤ k.val := by
  revert k
  decide

theorem d94_wC (k : Fin 6) : k ∈ Diagram.d94.wCircles ↔ k.val < 3 := by
  revert k
  decide

variable {m : Fin 6 → ℝ}

/-- The diagram `88` read on the germ: the `z`-stroke and the `z`-circles of the binary `{5, 6}` of the paper
(`{4, 5}` in Lean), the `w`-strokes on the pairs of `K` and the `w`-circles `K`. -/
theorem d88_facts {G : Germ 6 m} (hD : G.HasDiagram Diagram.d88) :
    (∀ k l, G.zStroke k l ↔ (k ≠ l ∧ 4 ≤ k.val ∧ 4 ≤ l.val)) ∧
      (∀ k l, G.wStroke k l ↔ (k ≠ l ∧ k.val < 4 ∧ l.val < 4)) ∧ (∀ k, G.zCircle k ↔ 4 ≤ k.val) ∧
        (∀ k, G.wCircle k ↔ k.val < 4) :=
  ⟨fun k l => (hD.1 k l).trans (d88_zS k l), fun k l => (hD.2.1 k l).trans (d88_wS k l),
    fun k => (hD.2.2.1 k).trans (d88_zC k), fun k => (hD.2.2.2 k).trans (d88_wC k)⟩

/-- The diagram `94` read on the germ: `z`-strokes on the pairs of the triangle `{4, 5, 6}` of the paper
(`{3, 4, 5}` in Lean), the `z`-circles `5, 6`, `w`-strokes on the pairs of `Q` and the `w`-circles `1, 2, 3`. -/
theorem d94_facts {G : Germ 6 m} (hD : G.HasDiagram Diagram.d94) :
    (∀ k l, G.zStroke k l ↔ (k ≠ l ∧ 3 ≤ k.val ∧ 3 ≤ l.val)) ∧
      (∀ k l, G.wStroke k l ↔ (k ≠ l ∧ k.val < 4 ∧ l.val < 4)) ∧ (∀ k, G.zCircle k ↔ 4 ≤ k.val) ∧
        (∀ k, G.wCircle k ↔ k.val < 3) :=
  ⟨fun k l => (hD.1 k l).trans (d94_zS k l), fun k l => (hD.2.1 k l).trans (d94_wS k l),
    fun k => (hD.2.2.1 k).trans (d94_zC k), fun k => (hD.2.2.2 k).trans (d94_wC k)⟩

/-- The binary `{5, 6}` when `5` and `6` are the only `z`-circled bodies (diagrams `88` and `94`):
`m_5 ẑ_5 + m_6 ẑ_6 = 0` with `ẑ_j = [z_j]_{−2}`, the coefficient of exponent `−2` in `Σ_k m_k z_k = 0` (Lemma 6.3,
`lem:binary`), and `ẑ_j ≠ 0`. -/
theorem bin_com (G : Germ 6 m) (hzc : ∀ k, G.zCircle k ↔ 4 ≤ k.val) :
    (m (bin 0) : ℂ) * (G.z (bin 0)).coeff (-2) + (m (bin 1) : ℂ) * (G.z (bin 1)).coeff (-2) = 0 ∧
      ∀ j, (G.z (bin j)).coeff (-2) ≠ 0 := by
  have h0 : G.zCircle (bin 0) := (hzc _).mpr (four_le_bin 0)
  have h1 : G.zCircle (bin 1) := (hzc _).mpr (four_le_bin 1)
  have honly : ∀ k, G.zCircle k → k = bin 0 ∨ k = bin 1 := fun k hk => by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ((mem_image_bin k).mpr ((hzc k).mp hk))
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨?_, fun j => (G.colZ.circle_iff_coeff (bin j)).mp ((hzc _).mpr (four_le_bin j))⟩
  have h := binary_com_z G (bin_injective.ne (by decide : (0 : Fin 2) ≠ 1)) h0 h1 honly
  rwa [← Ser.coeff_of_orderTop_eq h0, ← Ser.coeff_of_orderTop_eq h1] at h

/-- The coefficient of exponent `c` of the torque `T_{5,6} = 0` of the binary (`Germ.torque`), as a sum over the
pairs `jl` with `j ∈ {5, 6}`, `l ∈ K` (renumbered by `bin`, `quad`). -/
theorem torque_coeff_bin (G : Germ 6 m) (c : ℚ) :
    ∑ j : Fin 2, ∑ l : Fin 4, (cS (m (bin j)) * cS (m (quad l)) * (G.p (bin j) (quad l) ^ 3 *
      (G.z (bin j) * G.w (quad l) - G.z (quad l) * G.w (bin j)))).coeff c = 0 := by
  have hT := congrArg (fun f : Ser => f.coeff c) (G.torque (univ.image bin))
  simp only [HahnSeries.coeff_zero, Ser.coeff_sum] at hT
  rw [compl_image_bin] at hT
  simp only [Tri.sum_image_emb bin_injective, Tri.sum_image_emb quad_injective] at hT
  exact hT

/-! ## Lemma 6.16 (a): diagram 88 -/

/-- The exponents in the proof of **Lemma 6.16 (a)** (`lem:d88lead`), at a singular place with diagram `88`: by (F1)
of Lemma 6.1 (`lem:common`) in the colour `w`, `ω = −2`, `ζ = 2`, `x = 0` on the pairs of `K`; by (O6) of Lemma 2.8
(`lem:orders`), `ζ = ω = −2` on the eight pairs between `{5, 6}` and `K`; by (F2), `b_5, b_6 ≥ 2` and `a_l ≥ 2` for
`l ∈ K`; and `a_5 = a_6 = −2`, `b_l = −2` for `l ∈ K` (the circles). In Lean's numbering the binary is `{4, 5}` and
`K = {0, 1, 2, 3}`. -/
theorem d88_exps (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d88) :
    (∀ l l' : Fin 6, l.val < 4 → l'.val < 4 → l ≠ l' →
        G.omega l l' = -2 ∧ G.zeta l l' = 2 ∧ G.x l l' = 0) ∧
      (∀ j l : Fin 6, 4 ≤ j.val → l.val < 4 → G.zeta j l = -2 ∧ G.omega j l = -2) ∧
      (∀ j : Fin 6, 4 ≤ j.val →
        (G.z j).orderTop = ((-2 : ℚ) : WithTop ℚ) ∧ ((2 : ℚ) : WithTop ℚ) ≤ (G.w j).orderTop) ∧
      ∀ l : Fin 6, l.val < 4 →
        (G.w l).orderTop = ((-2 : ℚ) : WithTop ℚ) ∧ ((2 : ℚ) : WithTop ℚ) ≤ (G.z l).orderTop := by
  obtain ⟨hz, hw, hzc, hwc⟩ := d88_facts hD
  have hzA : ∀ k ∈ univ.image bin, ∀ l ∈ univ.image bin, k ≠ l → G.zStroke k l := fun k hk l hl hkl =>
    (hz k l).mpr ⟨hkl, (mem_image_bin k).mp hk, (mem_image_bin l).mp hl⟩
  have hcA : ∀ k, G.zCircle k → k ∈ univ.image bin := fun k hk => (mem_image_bin k).mpr ((hzc k).mp hk)
  have hwK : ∀ k ∈ univ.image quad, ∀ l ∈ univ.image quad, k ≠ l → G.wStroke k l := fun k hk l hl hkl =>
    (hw k l).mpr ⟨hkl, (mem_image_quad k).mp hk, (mem_image_quad l).mp hl⟩
  have hcK : ∀ k, G.wCircle k → k ∈ univ.image quad := fun k hk => (mem_image_quad k).mpr ((hwc k).mp hk)
  refine ⟨fun l l' hl hl' hll => ?_, fun j l hj hl => ?_, fun j hj => ?_, fun l hl => ?_⟩
  · exact F1_w hm G hwK ⟨0, (mem_image_quad 0).mpr (by decide), (hwc 0).mpr (by decide)⟩ hcK
      ((mem_image_quad l).mpr hl) ((mem_image_quad l').mpr hl') hll
  · refine ⟨G.O6_z ((hzc j).mpr hj) fun h => ?_, ?_⟩
    · have := (hzc l).mp h
      omega
    · rw [G.omega_comm]
      exact G.O6_w ((hwc l).mpr hl) fun h => by
        have := (hwc j).mp h
        omega
  · exact ⟨(hzc j).mpr hj, F2_z hm G hzA hcA ((hzc j).mpr hj)⟩
  · exact ⟨(hwc l).mpr hl, F2_w hm G hwK hcK ((hwc l).mpr hl)⟩

/-- **Lemma 6.16 (a)** (`lem:d88lead`), the leading system of `K`: at a singular place with diagram `88`,
`(X, Y, p̂_K)` with `X_l = [w_l]_{−2}`, `Y_l = [z_l]_2` and `p̂_ll' = [p_ll']_0` (`K` renumbered by `quad`) solves
`N₄(m_K)`, and `X_l ≠ 0`. The equations of the bodies of `K` at exponent `−2` in `w` and `2` in `z`, and their
distance equations at exponent `0`, form `N₄(m_K)`, since the cross terms have exponent `4` (`Tri.lead_w`). -/
theorem d88lead_N (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d88) :
    IsNSys (fun l => (m (quad l) : ℂ)) (fun l => (G.w (quad l)).coeff (-2)) (fun l => (G.z (quad l)).coeff 2)
        (fun l l' => (G.p (quad l) (quad l')).coeff 0) ∧
      ∀ l, (G.w (quad l)).coeff (-2) ≠ 0 := by
  obtain ⟨-, -, -, hwc⟩ := d88_facts hD
  obtain ⟨hK, hX, -, -⟩ := d88_exps hm G hD
  refine ⟨Tri.lead_w G quad_injective (fun l l' h => ?_) (fun l j hj => ?_), fun l => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hK _ _ (quad_lt_four l) (quad_lt_four l') (quad_injective.ne h)
    exact ⟨h1, h2⟩
  · have hj4 : 4 ≤ j.val := by
      rw [mem_image_quad] at hj
      omega
    obtain ⟨h1, h2⟩ := hX j (quad l) hj4 (quad_lt_four l)
    refine ⟨by rw [G.omega_comm]; exact h2, ?_⟩
    rw [G.zeta_comm, h1]
    norm_num
  · exact (G.colW.circle_iff_coeff (quad l)).mp ((hwc _).mpr (quad_lt_four l))

/-- **Lemma 6.16 (a)** (`lem:d88lead`), the cross relation: at a singular place with diagram `88`,
`p̂_jl² ẑ_j X_l = −1` for `j ∈ {5, 6}`, `l ∈ K`, with `p̂_jl = [p_jl]_2`, `ẑ_j = [z_j]_{−2}` and `X_l = [w_l]_{−2}`
((F4) of Lemma 6.1, `lem:common`: `a_j = −2 < 2 ≤ a_l` and `b_l = −2 < 2 ≤ b_j`). -/
theorem d88lead_cross (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d88) :
    ∀ j : Fin 2, ∀ l : Fin 4,
      (G.p (bin j) (quad l)).coeff 2 ^ 2 * (G.z (bin j)).coeff (-2) * (G.w (quad l)).coeff (-2) = -1 := by
  obtain ⟨-, -, hA, hB⟩ := d88_exps hm G hD
  intro j l
  obtain ⟨hzj, hwj⟩ := hA _ (four_le_bin j)
  obtain ⟨hwl, hzl⟩ := hB _ (quad_lt_four l)
  have h := (K4.f4 G (bin_ne_quad j l) hzj hwl
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hzl)
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hwj)).2.2.2
  rw [show (-((-2 + -2) / 2) : ℚ) = 2 by norm_num] at h
  exact h

/-- **Lemma 6.16 (a)** (`lem:d88lead`), the torque relation (eq:t88): at a singular place with diagram `88`,
`Σ_{j∈{5,6}, l∈K} m_j m_l p̂_jl = 0` with `p̂_jl = [p_jl]_2`. In the torque `T_{5,6}` all eight terms have exponent
`2` by (F4) of Lemma 6.1 (`lem:common`), with leading coefficient `−m_j m_l p̂_jl`. -/
theorem d88lead_torque (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d88) :
    ∑ j : Fin 2, ∑ l : Fin 4, (m (bin j) : ℂ) * (m (quad l) : ℂ) * (G.p (bin j) (quad l)).coeff 2 = 0 := by
  obtain ⟨-, -, hA, hB⟩ := d88_exps hm G hD
  have hterm : ∀ (j : Fin 2) (l : Fin 4), (cS (m (bin j)) * cS (m (quad l)) * (G.p (bin j) (quad l) ^ 3 *
      (G.z (bin j) * G.w (quad l) - G.z (quad l) * G.w (bin j)))).coeff 2 =
        -((m (bin j) : ℂ) * (m (quad l) : ℂ) * (G.p (bin j) (quad l)).coeff 2) := by
    intro j l
    obtain ⟨hzj, hwj⟩ := hA _ (four_le_bin j)
    obtain ⟨hwl, hzl⟩ := hB _ (quad_lt_four l)
    have hal : ((-2 : ℚ) : WithTop ℚ) < (G.z (quad l)).orderTop :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hzl
    have hbj : ((-2 : ℚ) : WithTop ℚ) < (G.w (bin j)).orderTop :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) hwj
    have hc := (K4.f4_term G (bin_ne_quad j l) hzj hwl hal hbj (K4.coe_add_lt hal.le hbj)).2
    rw [show (-((-2 + -2) / 2) : ℚ) = 2 by norm_num] at hc
    rw [← cS_mul, Ser.coeff_cS_mul, hc]
    ring
  have hT := torque_coeff_bin G 2
  simp only [hterm, Finset.sum_neg_distrib, neg_eq_zero] at hT
  exact hT

/-- **Lemma 6.16 (a)** (`lem:d88lead`), in one statement. At a singular place with diagram `88` (the binary `{5, 6}`
of the paper renumbered `0, 1` by `bin`, the cluster `K = {1, 2, 3, 4}` renumbered `0, 1, 2, 3` by `quad`), with
`ẑ_j = [z_j]_{−2}` for `j ∈ {5, 6}`, `X_l = [w_l]_{−2}`, `Y_l = [z_l]_2`, `p̂_ll' = [p_ll']_0` for `l, l' ∈ K` and
`p̂_jl = [p_jl]_2`: `m_5 ẑ_5 + m_6 ẑ_6 = 0`; `(X, Y, p̂_K)` solves `N₄(m_K)` (`IsNSys` for `N = 4`) with all `X_l ≠ 0`;
`p̂_jl² ẑ_j X_l = −1`; and `Σ_{j∈{5,6}, l∈K} m_j m_l p̂_jl = 0` (eq:t88). -/
theorem d88_lead (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d88) :
    (m (bin 0) : ℂ) * (G.z (bin 0)).coeff (-2) + (m (bin 1) : ℂ) * (G.z (bin 1)).coeff (-2) = 0 ∧
    IsNSys (fun l => (m (quad l) : ℂ)) (fun l => (G.w (quad l)).coeff (-2)) (fun l => (G.z (quad l)).coeff 2)
      (fun l l' => (G.p (quad l) (quad l')).coeff 0) ∧
    (∀ l, (G.w (quad l)).coeff (-2) ≠ 0) ∧
    (∀ j : Fin 2, ∀ l : Fin 4,
      (G.p (bin j) (quad l)).coeff 2 ^ 2 * (G.z (bin j)).coeff (-2) * (G.w (quad l)).coeff (-2) = -1) ∧
    ∑ j : Fin 2, ∑ l : Fin 4, (m (bin j) : ℂ) * (m (quad l) : ℂ) * (G.p (bin j) (quad l)).coeff 2 = 0 :=
  ⟨(bin_com G (d88_facts hD).2.2.1).1, (d88lead_N hm G hD).1, (d88lead_N hm G hD).2, d88lead_cross hm G hD,
    d88lead_torque hm G hD⟩

/-! ## Lemma 6.16 (b): diagram 94 -/

/-- The exponents in the proof of **Lemma 6.16 (b)** (`lem:d88lead`), at a singular place with diagram `94`: by (F1)
of Lemma 6.1 (`lem:common`), `ζ = −2`, `ω = 2`, `x = 0` on the pairs of the triangle `{4, 5, 6}`, and `ω = −2`,
`ζ = 2`, `x = 0` on the pairs of `Q`; by (O6) of Lemma 2.8 (`lem:orders`), `ζ_jl = −2` for `j ∈ {5, 6}`, `l ∈ Q`, and
`ω_jl = −2` for `j ∈ {4, 5, 6}`, `l ∈ {1, 2, 3}`; by (F2) and (F3), `b_j ≥ 2` for `j ∈ {4, 5, 6}` (`w_4 = w_5 − w_54`)
and `a_l ≥ 2` for `l ∈ Q` (`z_4 = z_1 − z_14`); and `a_5 = a_6 = −2`, `b_1 = b_2 = b_3 = −2` (the circles). In Lean's
numbering the triangle is `{3, 4, 5}`, `Q = {0, 1, 2, 3}` and body `4` of the paper is `3`. -/
theorem d94_exps (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d94) :
    (∀ j j' : Fin 6, 3 ≤ j.val → 3 ≤ j'.val → j ≠ j' →
        G.zeta j j' = -2 ∧ G.omega j j' = 2 ∧ G.x j j' = 0) ∧
      (∀ l l' : Fin 6, l.val < 4 → l'.val < 4 → l ≠ l' →
        G.omega l l' = -2 ∧ G.zeta l l' = 2 ∧ G.x l l' = 0) ∧
      (∀ j l : Fin 6, 4 ≤ j.val → l.val < 4 → G.zeta j l = -2) ∧
      (∀ j l : Fin 6, 3 ≤ j.val → l.val < 3 → G.omega j l = -2) ∧
      (∀ j : Fin 6, 3 ≤ j.val → ((2 : ℚ) : WithTop ℚ) ≤ (G.w j).orderTop) ∧
      (∀ l : Fin 6, l.val < 4 → ((2 : ℚ) : WithTop ℚ) ≤ (G.z l).orderTop) ∧
      (∀ j : Fin 6, 4 ≤ j.val → (G.z j).orderTop = ((-2 : ℚ) : WithTop ℚ)) ∧
      ∀ l : Fin 6, l.val < 3 → (G.w l).orderTop = ((-2 : ℚ) : WithTop ℚ) := by
  obtain ⟨hz, hw, hzc, hwc⟩ := d94_facts hD
  have hzA : ∀ k ∈ univ.image triA, ∀ l ∈ univ.image triA, k ≠ l → G.zStroke k l := fun k hk l hl hkl =>
    (hz k l).mpr ⟨hkl, (mem_image_triA k).mp hk, (mem_image_triA l).mp hl⟩
  have hcA : ∀ k, G.zCircle k → k ∈ univ.image triA := fun k hk => (mem_image_triA k).mpr (by
    have := (hzc k).mp hk
    omega)
  have hwQ : ∀ k ∈ univ.image quad, ∀ l ∈ univ.image quad, k ≠ l → G.wStroke k l := fun k hk l hl hkl =>
    (hw k l).mpr ⟨hkl, (mem_image_quad k).mp hk, (mem_image_quad l).mp hl⟩
  have hcQ : ∀ k, G.wCircle k → k ∈ univ.image quad := fun k hk => (mem_image_quad k).mpr (by
    have := (hwc k).mp hk
    omega)
  -- (F1) on the triangle and on `Q`
  have hA : ∀ j j' : Fin 6, 3 ≤ j.val → 3 ≤ j'.val → j ≠ j' →
      G.zeta j j' = -2 ∧ G.omega j j' = 2 ∧ G.x j j' = 0 := fun j j' hj hj' hjj =>
    F1_z hm G hzA ⟨4, (mem_image_triA 4).mpr (by decide), (hzc 4).mpr (by decide)⟩ hcA
      ((mem_image_triA j).mpr hj) ((mem_image_triA j').mpr hj') hjj
  have hQ : ∀ l l' : Fin 6, l.val < 4 → l'.val < 4 → l ≠ l' →
      G.omega l l' = -2 ∧ G.zeta l l' = 2 ∧ G.x l l' = 0 := fun l l' hl hl' hll =>
    F1_w hm G hwQ ⟨0, (mem_image_quad 0).mpr (by decide), (hwc 0).mpr (by decide)⟩ hcQ
      ((mem_image_quad l).mpr hl) ((mem_image_quad l').mpr hl') hll
  -- (O6) on the cross pairs
  have hζ : ∀ j l : Fin 6, 4 ≤ j.val → l.val < 4 → G.zeta j l = -2 := fun j l hj hl =>
    G.O6_z ((hzc j).mpr hj) fun h => by
      have := (hzc l).mp h
      omega
  have hω : ∀ j l : Fin 6, 3 ≤ j.val → l.val < 3 → G.omega j l = -2 := fun j l hj hl => by
    rw [G.omega_comm]
    exact G.O6_w ((hwc l).mpr hl) fun h => by
      have := (hwc j).mp h
      omega
  -- (F2): `b_5, b_6 ≥ 2`; (F3) on the `z`-stroke `45` with `x_45 = 0`: `b_4 ≥ min(b_5, 2) = 2`
  have hb56 : ∀ j : Fin 6, 4 ≤ j.val → ((2 : ℚ) : WithTop ℚ) ≤ (G.w j).orderTop := fun j hj =>
    F2_z hm G hzA hcA ((hzc j).mpr hj)
  have hbA : ∀ j : Fin 6, 3 ≤ j.val → ((2 : ℚ) : WithTop ℚ) ≤ (G.w j).orderTop := by
    intro j hj
    rcases Nat.lt_or_ge j.val 4 with h4 | h4
    · have hj3 : j = 3 := Fin.ext (show j.val = 3 by omega)
      subst hj3
      have h34 := F3_w G ((hz 3 4).mpr ⟨by decide, by decide, by decide⟩)
        (hA 3 4 (by decide) (by decide) (by decide)).2.2
      rw [min_eq_right (hb56 4 (by decide))] at h34
      exact h34
    · exact hb56 j h4
  -- (F2): `a_1, a_2, a_3 ≥ 2`; (F3) on the `w`-stroke `41` with `x_41 = 0`: `a_4 ≥ min(a_1, 2) = 2`
  have ha3 : ∀ l : Fin 6, l.val < 3 → ((2 : ℚ) : WithTop ℚ) ≤ (G.z l).orderTop := fun l hl =>
    F2_w hm G hwQ hcQ ((hwc l).mpr hl)
  have haQ : ∀ l : Fin 6, l.val < 4 → ((2 : ℚ) : WithTop ℚ) ≤ (G.z l).orderTop := by
    intro l hl
    rcases Nat.lt_or_ge l.val 3 with h3 | h3
    · exact ha3 l h3
    · have hl3 : l = 3 := Fin.ext (show l.val = 3 by omega)
      subst hl3
      have h30 := F3_z G ((hw 3 0).mpr ⟨by decide, by decide, by decide⟩)
        (hQ 3 0 (by decide) (by decide) (by decide)).2.2
      rw [min_eq_right (ha3 0 (by decide))] at h30
      exact h30
  exact ⟨hA, hQ, hζ, hω, hbA, haQ, fun j hj => (hzc j).mpr hj, fun l hl => (hwc l).mpr hl⟩

/-- **Lemma 6.16 (b)** (`lem:d88lead`), the centred system: at a singular place with diagram `94`, `(X, Y, p̂_Q)`
with `X_l = [w_l]_{−2}`, `Y_l = [z_l]_2` and `p̂_ll' = [p_ll']_0` (`Q` renumbered by `quad`) solves
`KC(m_1, …, m_4)` (`IsKC`). `X_4 = 0` since `b_4 ≥ 2`. The `w`-equations of `1, 2, 3` at exponent `−2` and their
`z`-equations at exponent `2` have the cross terms `W_lj`, `Z_lj`, `j = 5, 6`, of exponent `4`; the `w`-equation of
`4` at exponent `−2`, whose cross terms `W_4j` have exponent `2`, gives the equation of the centre; the distance
equations are taken at exponent `0`. -/
theorem d94lead_KC (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d94) :
    IsKC (fun l => (m (quad l) : ℂ)) (fun l => (G.w (quad l)).coeff (-2)) (fun l => (G.z (quad l)).coeff 2)
      (fun l l' => (G.p (quad l) (quad l')).coeff 0) := by
  obtain ⟨-, hQ, hζ, hω, hbA, -, -, -⟩ := d94_exps hm G hD
  have hne : ∀ {k k' : Fin 4}, k' ≠ k → quad k ≠ quad k' := fun h h' => h (quad_injective h').symm
  have hpair : ∀ k k' : Fin 4, k' ≠ k → G.omega (quad k) (quad k') = -2 ∧ G.zeta (quad k) (quad k') = 2 ∧
      G.x (quad k) (quad k') = 0 := fun k k' h =>
    hQ _ _ (quad_lt_four k) (quad_lt_four k') (hne h)
  have hp : ∀ k k' : Fin 4, k' ≠ k → ((0 : ℚ) : WithTop ℚ) ≤ (G.p (quad k) (quad k')).orderTop :=
    fun k k' h => by
      rw [G.orderTop_p (hne h), (hpair k k' h).2.2]
      norm_num
  have hout : ∀ l ∉ univ.image quad, 4 ≤ l.val := fun l hl => by
    rw [mem_image_quad] at hl
    omega
  have hql : ∀ (k : Fin 4) (l : Fin 6), 4 ≤ l.val → quad k ≠ l := fun k l hl h => by
    have := quad_lt_four k
    rw [h] at this
    omega
  -- the `w`-equations of the bodies of `Q` at exponent `−2`
  have hX : ∀ k : Fin 4, (G.w (quad k)).coeff (-2) = force (fun l => (m (quad l) : ℂ))
      (fun l l' => (G.p (quad l) (quad l')).coeff 0) (fun l => (G.w (quad l)).coeff (-2)) k := by
    intro k
    refine Quad.coeff_body_force G.colW quad_injective k (-2) (fun k' h => ⟨hp k k' h, ?_⟩) (fun l hl => ?_)
    · exact (show (G.w (quad k) - G.w (quad k')).orderTop = ((-2 : ℚ) : WithTop ℚ) by
        rw [G.orderTop_w_sub (hne h), (hpair k k' h).1]).ge
    · have hkl := hql k l (hout l hl)
      apply Ser.coeff_eq_zero_of_lt
      rw [G.orderTop_termZ_w hkl, G.zeta_comm, hζ l (quad k) (hout l hl) (quad_lt_four k)]
      exact WithTop.coe_lt_coe.mpr (by linarith [(G.O1_le hkl).2.1])
  -- the `z`-equations of the bodies `1, 2, 3` at exponent `2`
  have hY : ∀ k : Fin 4, k ≠ 3 → (G.z (quad k)).coeff 2 = force (fun l => (m (quad l) : ℂ))
      (fun l l' => (G.p (quad l) (quad l')).coeff 0) (fun l => (G.z (quad l)).coeff 2) k := by
    intro k hk3
    have hk : (quad k).val < 3 := by
      rw [quad_val]
      have h2 : k.val ≠ 3 := fun h => hk3 (Fin.ext h)
      omega
    refine Quad.coeff_body_force G.colZ quad_injective k 2 (fun k' h => ⟨hp k k' h, ?_⟩) (fun l hl => ?_)
    · exact (show (G.z (quad k) - G.z (quad k')).orderTop = ((2 : ℚ) : WithTop ℚ) by
        rw [G.orderTop_z_sub (hne h), (hpair k k' h).2.1]).ge
    · have hkl := hql k l (hout l hl)
      have hl3 : 3 ≤ l.val := by
        have := hout l hl
        omega
      apply Ser.coeff_eq_zero_of_lt
      rw [G.orderTop_termZ_z hkl, G.zeta_comm, hζ l (quad k) (hout l hl) (quad_lt_four k), G.omega_comm,
        hω l (quad k) hl3 hk]
      exact WithTop.coe_lt_coe.mpr (by norm_num)
  have hX3 : (G.w (quad 3)).coeff (-2) = 0 :=
    Ser.coeff_eq_zero_of_lt (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (hbA (quad 3) (by decide)))
  refine ⟨fun k l => ?_, hX3, fun k _ => hX k, (hX 3).symm.trans hX3, hY,
    Quad.lead_dist G quad_injective fun k k' h => ?_⟩
  · show (G.p (quad k) (quad l)).coeff 0 = (G.p (quad l) (quad k)).coeff 0
    rw [G.p_symm]
  · obtain ⟨h1, h2, -⟩ := hpair k k' (Ne.symm h)
    exact ⟨h1, h2⟩

/-- **Lemma 6.16 (b)** (`lem:d88lead`), the cross relation: at a singular place with diagram `94`,
`p̂_jl² ẑ_j X_l = −1` for `j ∈ {5, 6}`, `l ∈ {1, 2, 3}` (renumbered by `triB`), with `p̂_jl = [p_jl]_2`,
`ẑ_j = [z_j]_{−2}` and `X_l = [w_l]_{−2}` ((F4) of Lemma 6.1, `lem:common`). -/
theorem d94lead_cross (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d94) :
    ∀ j : Fin 2, ∀ l : Fin 3,
      (G.p (bin j) (triB l)).coeff 2 ^ 2 * (G.z (bin j)).coeff (-2) * (G.w (triB l)).coeff (-2) = -1 := by
  obtain ⟨-, -, -, -, hbA, haQ, hzc, hwc⟩ := d94_exps hm G hD
  intro j l
  have h := (K4.f4 G (bin_ne_triB j l) (hzc _ (four_le_bin j)) (hwc _ (triB_lt_three l))
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (haQ _ (by have := triB_lt_three l; omega)))
    (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (hbA _ (by have := four_le_bin j; omega)))).2.2.2
  rw [show (-((-2 + -2) / 2) : ℚ) = 2 by norm_num] at h
  exact h

/-- **Lemma 6.16 (b)** (`lem:d88lead`), the torque relation (eq:t94): at a singular place with diagram `94`,
`Σ_{j∈{5,6}, l≤3} m_j m_l p̂_jl = 0` with `p̂_jl = [p_jl]_2`. In `T_{5,6}` the pairs `(j, l)`, `l ≤ 3`, give exponent
`2` by (F4) of Lemma 6.1 (`lem:common`). By Lemma 6.2 (`lem:rewrite`) with `o = 4`, the pairs `(j, 4)` contribute
`m_4 (w_4 B_z − z_4 B_w)` with `B_z = Σ_{l≤3} m_l Z_4l` and `B_w = w_4 − A_w`, `A_w = Σ_{j=5,6} m_j W_4j`, both of
exponent at least `2`, although each `W_4l` has exponent `−2`; so this contribution has exponent at least `4`. -/
theorem d94lead_torque (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d94) :
    ∑ j : Fin 2, ∑ l : Fin 3, (m (bin j) : ℂ) * (m (triB l) : ℂ) * (G.p (bin j) (triB l)).coeff 2 = 0 := by
  obtain ⟨hA, hQ, -, -, hbA, haQ, hzc, hwc⟩ := d94_exps hm G hD
  -- the pairs `(j, l)`, `l ≤ 3`: (F4) at exponent `2`
  have hterm : ∀ (j : Fin 2) (l : Fin 3), (cS (m (bin j)) * cS (m (triB l)) * (G.p (bin j) (triB l) ^ 3 *
      (G.z (bin j) * G.w (triB l) - G.z (triB l) * G.w (bin j)))).coeff 2 =
        -((m (bin j) : ℂ) * (m (triB l) : ℂ) * (G.p (bin j) (triB l)).coeff 2) := by
    intro j l
    have hal : ((-2 : ℚ) : WithTop ℚ) < (G.z (triB l)).orderTop :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (haQ _ (by have := triB_lt_three l; omega))
    have hbj : ((-2 : ℚ) : WithTop ℚ) < (G.w (bin j)).orderTop :=
      lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (hbA _ (by have := four_le_bin j; omega))
    have hc := (K4.f4_term G (bin_ne_triB j l) (hzc _ (four_le_bin j)) (hwc _ (triB_lt_three l)) hal hbj
      (K4.coe_add_lt hal.le hbj)).2
    rw [show (-((-2 + -2) / 2) : ℚ) = 2 by norm_num] at hc
    rw [← cS_mul, Ser.coeff_cS_mul, hc]
    ring
  -- the pairs `(j, 4)`: by Lemma 6.2 with `o = 4`, `m_4 (w_4 B_z − z_4 B_w)`, of exponent at least `4`
  have hS : (3 : Fin 6) ∉ univ.image bin := by
    rw [mem_image_bin]
    decide
  obtain ⟨-, hBw⟩ := rewrite_B G (univ.image bin) hS
  obtain ⟨h1, h2⟩ := rewrite_sum G (univ.image bin) hS
  have hcompl : ∀ l ∈ (insert (3 : Fin 6) (univ.image bin))ᶜ, l.val < 3 := fun l hl => by
    rw [Finset.mem_compl, Finset.mem_insert, mem_image_bin, not_or] at hl
    have h1 : l.val ≠ 3 := fun h => hl.1 (Fin.ext h)
    have h2 := hl.2
    omega
  have hw3 : ((2 : ℚ) : WithTop ℚ) ≤ (G.w 3).orderTop := hbA 3 (by decide)
  have hz3 : ((2 : ℚ) : WithTop ℚ) ≤ (G.z 3).orderTop := haQ 3 (by decide)
  have hBz2 : ((2 : ℚ) : WithTop ℚ) ≤
      (∑ l ∈ (insert (3 : Fin 6) (univ.image bin))ᶜ, cS (m l) * termZ G.p G.z 3 l).orderTop := by
    refine K4.le_orderTop_sum _ _ fun l hl => le_trans ?_ (K4.le_orderTop_cS_mul _ _)
    have hl3 := hcompl l hl
    have h3l : (3 : Fin 6) ≠ l := fun h => by
      rw [← h] at hl3
      exact absurd hl3 (by decide)
    obtain ⟨hω, hζ, -⟩ := hQ 3 l (by decide) (by omega) h3l
    rw [G.orderTop_termZ_z h3l, hζ, hω]
    exact WithTop.coe_le_coe.mpr (by norm_num)
  have hBw2 : ((2 : ℚ) : WithTop ℚ) ≤
      (∑ l ∈ (insert (3 : Fin 6) (univ.image bin))ᶜ, cS (m l) * termZ G.p G.w 3 l).orderTop := by
    rw [← hBw]
    refine le_trans (le_min hw3 ?_) HahnSeries.min_orderTop_le_orderTop_sub
    refine K4.le_orderTop_sum _ _ fun j hj => le_trans ?_ (K4.le_orderTop_cS_mul _ _)
    have hj4 := (mem_image_bin j).mp hj
    have h3j : (3 : Fin 6) ≠ j := fun h => by
      rw [← h] at hj4
      exact absurd hj4 (by decide)
    obtain ⟨hζ, hω, -⟩ := hA 3 j (by decide) (by omega) h3j
    rw [G.orderTop_termZ_w h3j, hζ, hω]
    exact WithTop.coe_le_coe.mpr (by norm_num)
  have h3 : ∑ j : Fin 2, (cS (m (bin j)) * cS (m 3) * (G.p (bin j) 3 ^ 3 *
      (G.z (bin j) * G.w 3 - G.z 3 * G.w (bin j)))).coeff 2 = 0 := by
    have h3' : (∑ j ∈ univ.image bin, cS (m j) * cS (m 3) *
        (G.p j 3 ^ 3 * (G.z j * G.w 3 - G.z 3 * G.w j))).coeff 2 = 0 := by
      rw [h1, h2]
      apply Ser.coeff_eq_zero_of_lt
      refine lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (show (2 : ℚ) < 2 + 2 by norm_num)) ?_
      rw [WithTop.coe_add]
      refine le_trans ?_ (K4.le_orderTop_cS_mul _ _)
      refine le_trans (le_min ?_ ?_) HahnSeries.min_orderTop_le_orderTop_sub
      · rw [HahnSeries.orderTop_mul]
        exact add_le_add hw3 hBz2
      · rw [HahnSeries.orderTop_mul]
        exact add_le_add hz3 hBw2
    rwa [Tri.sum_image_emb bin_injective, Ser.coeff_sum] at h3'
  -- the torque `T_{5,6}` at exponent `2`
  have hsplit : ∀ j : Fin 2, ∑ l : Fin 4, (cS (m (bin j)) * cS (m (quad l)) * (G.p (bin j) (quad l) ^ 3 *
      (G.z (bin j) * G.w (quad l) - G.z (quad l) * G.w (bin j)))).coeff 2 =
      -∑ l : Fin 3, (m (bin j) : ℂ) * (m (triB l) : ℂ) * (G.p (bin j) (triB l)).coeff 2 +
        (cS (m (bin j)) * cS (m 3) * (G.p (bin j) 3 ^ 3 *
          (G.z (bin j) * G.w 3 - G.z 3 * G.w (bin j)))).coeff 2 := by
    intro j
    conv_lhs => rw [Fin.sum_univ_castSucc]
    simp only [quad_castSucc, quad_last, hterm, Finset.sum_neg_distrib]
  have hT := torque_coeff_bin G 2
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, h3, add_zero, Finset.sum_neg_distrib,
    neg_eq_zero] at hT
  exact hT

/-- **Lemma 6.16 (b)** (`lem:d88lead`), in one statement. At a singular place with diagram `94` (the binary `{5, 6}`
of the paper renumbered `0, 1` by `bin`, `Q = {1, 2, 3, 4}` renumbered `0, 1, 2, 3` by `quad`, its bodies `1, 2, 3`
renumbered by `triB`), with `ẑ_j = [z_j]_{−2}`, `X_l = [w_l]_{−2}`, `Y_l = [z_l]_2`, `p̂_ll' = [p_ll']_0` for
`l, l' ∈ Q` and `p̂_jl = [p_jl]_2`: `m_5 ẑ_5 + m_6 ẑ_6 = 0`; `(X, Y, p̂_Q)` solves `KC(m_1, …, m_4)` (`IsKC`) with
`X_1 X_2 X_3 ≠ 0`; `p̂_jl² ẑ_j X_l = −1` for `l ≤ 3`; and `Σ_{j∈{5,6}, l≤3} m_j m_l p̂_jl = 0` (eq:t94). -/
theorem d94_lead (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d94) :
    (m (bin 0) : ℂ) * (G.z (bin 0)).coeff (-2) + (m (bin 1) : ℂ) * (G.z (bin 1)).coeff (-2) = 0 ∧
    IsKC (fun l => (m (quad l) : ℂ)) (fun l => (G.w (quad l)).coeff (-2)) (fun l => (G.z (quad l)).coeff 2)
      (fun l l' => (G.p (quad l) (quad l')).coeff 0) ∧
    (∀ l : Fin 3, (G.w (triB l)).coeff (-2) ≠ 0) ∧
    (∀ j : Fin 2, ∀ l : Fin 3,
      (G.p (bin j) (triB l)).coeff 2 ^ 2 * (G.z (bin j)).coeff (-2) * (G.w (triB l)).coeff (-2) = -1) ∧
    ∑ j : Fin 2, ∑ l : Fin 3, (m (bin j) : ℂ) * (m (triB l) : ℂ) * (G.p (bin j) (triB l)).coeff 2 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hwc⟩ := d94_exps hm G hD
  exact ⟨(bin_com G (d94_facts hD).2.2.1).1, d94lead_KC hm G hD,
    fun l => (G.colW.circle_iff_coeff (triB l)).mp (hwc _ (triB_lt_three l)), d94lead_cross hm G hD,
    d94lead_torque hm G hD⟩

/-! ## Lemma 6.17 -/

namespace Ttest

/-- One group of the sums of **Lemma 6.17** (`lem:Ttest`), the computation of its proof. Let `m_5, m_6 > 0`, `c ≠ 0`,
and let `p̂_5`, `p̂_6` satisfy `p̂_5² (c m_6) X = −1` and `p̂_6² (−c m_5) X = −1` (`p̂_j² ẑ_j X = −1` with `ẑ_5 = c m_6`,
`ẑ_6 = −c m_5`). For any square roots `r` of `X` and `q` of `(−c m_6)⁻¹` there are signs `ε, s ∈ {±1}` with
`m_5 p̂_5 + m_6 p̂_6 = m_5 q (ε / r) (1 + i s ρ)`, `ρ = (m_6/m_5)^{3/2}`: `p̂_5 = ε q / r`, and
`p̂_6/p̂_5 = ±(ẑ_5/ẑ_6)^{1/2} = i s (m_6/m_5)^{1/2}`. -/
theorem group {m5 m6 : ℝ} (h5 : 0 < m5) (h6 : 0 < m6) {c X P5 P6 q r : ℂ} (hc : c ≠ 0)
    (hP5 : P5 ^ 2 * (c * m6) * X = -1) (hP6 : P6 ^ 2 * (-c * m5) * X = -1) (hq : q ^ 2 * (-c * m6) = 1)
    (hr : r ^ 2 = X) :
    ∃ ε s : ℂ, (ε = 1 ∨ ε = -1) ∧ (s = 1 ∨ s = -1) ∧
      (m5 : ℂ) * P5 + (m6 : ℂ) * P6 =
        (m5 : ℂ) * q * (ε / r) * (1 + Complex.I * s * (((m6 / m5) ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) := by
  have hm5 : (m5 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h5.ne'
  have hm6 : (m6 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h6.ne'
  have hX : X ≠ 0 := by
    intro h
    rw [h, mul_zero] at hP5
    norm_num at hP5
  have hr0 : r ≠ 0 := by
    intro h
    apply hX
    rw [← hr, h]
    ring
  -- `p̂_5 r = ε q`
  obtain ⟨ε, hε, hPr⟩ : ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ P5 * r = ε * q := by
    have h1 : (P5 * r - q) * (P5 * r + q) * (c * m6) = 0 := by
      linear_combination P5 ^ 2 * c * (m6 : ℂ) * hr + hP5 + hq
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact ⟨1, Or.inl rfl, by linear_combination h3⟩
      · exact ⟨-1, Or.inr rfl, by linear_combination h3⟩
    · exact absurd h2 (mul_ne_zero hc hm6)
  -- `p̂_6 = i s σ p̂_5` with `σ = (m_6/m_5)^{1/2}`
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = m6 / m5 := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]
    exact div_pos h6 h5
  have ham : (a : ℂ) * m5 = m6 := by
    rw [← Complex.ofReal_mul, ha, div_mul_cancel₀ _ h5.ne']
  have hσ2 : ((Real.sqrt a : ℝ) : ℂ) ^ 2 * m5 = m6 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ha0.le, ham]
  obtain ⟨s, hs, hP6'⟩ : ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ P6 = Complex.I * s * (Real.sqrt a : ℂ) * P5 := by
    have h1 : (P6 - Complex.I * (Real.sqrt a : ℂ) * P5) * (P6 + Complex.I * (Real.sqrt a : ℂ) * P5) *
        (c * X * m5) = 0 := by
      linear_combination -hP6 - Complex.I ^ 2 * P5 ^ 2 * c * X * hσ2 - Complex.I ^ 2 * hP5 + Complex.I_sq
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact ⟨1, Or.inl rfl, by linear_combination h3⟩
      · exact ⟨-1, Or.inr rfl, by linear_combination h3⟩
    · exact absurd h2 (mul_ne_zero (mul_ne_zero hc hX) hm5)
  -- `ρ = σ a`
  have hρ : (m6 / m5) ^ ((3 : ℝ) / 2) = Real.sqrt a * a := by
    rw [← ha, show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.rpow_add ha0, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hP5' : P5 = q * (ε / r) := by
    rw [mul_div_assoc', eq_div_iff hr0]
    linear_combination hPr
  refine ⟨ε, s, hε, hs, ?_⟩
  rw [hρ, Complex.ofReal_mul, hP6']
  linear_combination ((m5 : ℂ) + Complex.I * s * (Real.sqrt a : ℂ) * m5 * a) * hP5' -
    Complex.I * s * (Real.sqrt a : ℂ) * P5 * ham

/-- The decomposition of the sums of **Lemma 6.17** (`lem:Ttest`) into groups: with `ẑ_5 = c m_6`, `ẑ_6 = −c m_5`
(`c ≠ 0`, `m_5, m_6 > 0`), `p̂_jl² ẑ_j X_l = −1` and square roots `r_l` of `X_l`, there are `q ≠ 0` (a square root of
`(−c m_6)⁻¹`) and signs `ε_l, s_l ∈ {±1}` with `m_l (m_5 p̂_5l + m_6 p̂_6l) = m_5 q ε_l (m_l / r_l) (1 + i s_l ρ)`,
`ρ = (m_6/m_5)^{3/2}`. The binary is indexed by `Fin 2` (`m_5 = mb 0`, `m_6 = mb 1`, `ẑ_5 = zh 0`, `ẑ_6 = zh 1`). -/
theorem decomp {N : ℕ} {mb : Fin 2 → ℝ} (hmb : ∀ j, 0 < mb j) (μ : Fin N → ℝ) {c : ℂ} (hc : c ≠ 0)
    {zh : Fin 2 → ℂ} (hz0 : zh 0 = c * mb 1) (hz1 : zh 1 = -c * mb 0) {X : Fin N → ℂ}
    {P : Fin 2 → Fin N → ℂ} (hP : ∀ j l, P j l ^ 2 * zh j * X l = -1) {r : Fin N → ℂ}
    (hr : ∀ l, r l ^ 2 = X l) :
    ∃ q : ℂ, q ≠ 0 ∧ ∃ ε s : Fin N → ℂ, (∀ l, ε l = 1 ∨ ε l = -1) ∧ (∀ l, s l = 1 ∨ s l = -1) ∧
      ∀ l, (mb 0 : ℂ) * (μ l : ℂ) * P 0 l + (mb 1 : ℂ) * (μ l : ℂ) * P 1 l =
        (mb 0 : ℂ) * q * (ε l * ((μ l : ℂ) / r l) *
          (1 + Complex.I * s l * (((mb 1 / mb 0) ^ ((3 : ℝ) / 2) : ℝ) : ℂ))) := by
  have hu : -c * (mb 1 : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hc) (Complex.ofReal_ne_zero.mpr (hmb 1).ne')
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : ℂ, q₀ ^ 2 = -c * (mb 1 : ℂ) := ⟨_, Complex.cpow_nat_inv_pow _ two_ne_zero⟩
  have hq₀0 : q₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hq₀
    exact hu hq₀.symm
  have hq : q₀⁻¹ ^ 2 * (-c * (mb 1 : ℂ)) = 1 := by
    rw [← hq₀, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hq₀0)]
  have hg : ∀ l, ∃ ε s : ℂ, (ε = 1 ∨ ε = -1) ∧ (s = 1 ∨ s = -1) ∧
      (mb 0 : ℂ) * P 0 l + (mb 1 : ℂ) * P 1 l =
        (mb 0 : ℂ) * q₀⁻¹ * (ε / r l) * (1 + Complex.I * s * (((mb 1 / mb 0) ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) := by
    intro l
    have h0 := hP 0 l
    have h1 := hP 1 l
    rw [hz0] at h0
    rw [hz1] at h1
    exact group (hmb 0) (hmb 1) hc h0 h1 hq (hr l)
  choose ε s hε hs hgl using hg
  refine ⟨q₀⁻¹, inv_ne_zero hq₀0, ε, s, hε, hs, fun l => ?_⟩
  linear_combination (μ l : ℂ) * hgl l

/-- A sum of complex numbers with `‖g_l‖ = K a_l`, `K > 0`, does not vanish if `a_k > Σ_{l≠k} a_l` for some `k`:
the dominant term cannot be cancelled. -/
theorem sum_ne_zero_of_dominant {N : ℕ} (g : Fin N → ℂ) (a : Fin N → ℝ) {K : ℝ} (hK : 0 < K)
    (hg : ∀ l, ‖g l‖ = K * a l) {k : Fin N} (hk : ∑ l ∈ univ.erase k, a l < a k) : ∑ l, g l ≠ 0 := by
  intro hsum
  have h1 : g k = -∑ l ∈ univ.erase k, g l := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hsum
    linear_combination hsum
  have h2 : ‖g k‖ ≤ ∑ l ∈ univ.erase k, ‖g l‖ := by
    rw [h1, norm_neg]
    exact norm_sum_le _ _
  rw [hg k, Finset.sum_congr rfl fun l _ => hg l, ← Finset.mul_sum] at h2
  linarith [le_of_mul_le_mul_left h2 hK]

end Ttest

/-- **Lemma 6.17 (a)** (`lem:Ttest`), as a statement about complex numbers. Let `m_5, m_6 > 0` (`mb 0`, `mb 1`), let
`m_l > 0` (`μ l`, `l ∈ Fin N`), `c ≠ 0`, `ẑ_5 = c m_6`, `ẑ_6 = −c m_5` (`zh 0`, `zh 1`), and let `p̂_jl` (`P j l`)
satisfy `p̂_jl² ẑ_j X_l = −1`. If `m_k |X_k|^{−1/2} > Σ_{l≠k} m_l |X_l|^{−1/2}` for some `k`, then
`Σ_{j,l} m_j m_l p̂_jl ≠ 0`, whatever the signs of the `p̂_jl`. The `l`-th group `m_l (m_5 p̂_5l + m_6 p̂_6l)` has modulus
`K' m_l |X_l|^{−1/2}` with `K' > 0` independent of `l`, and the dominant group cannot be cancelled. For `N = 4` this is
the test for the leading data of Lemma 6.16 (a) (`Six.d88_Ttest`). -/
theorem Ttest_a {N : ℕ} {mb : Fin 2 → ℝ} (hmb : ∀ j, 0 < mb j) {μ : Fin N → ℝ} (hμ : ∀ l, 0 < μ l) {c : ℂ}
    (hc : c ≠ 0) {zh : Fin 2 → ℂ} (hz0 : zh 0 = c * mb 1) (hz1 : zh 1 = -c * mb 0) {X : Fin N → ℂ}
    {P : Fin 2 → Fin N → ℂ} (hP : ∀ j l, P j l ^ 2 * zh j * X l = -1)
    (hT : ∃ k, μ k * ‖X k‖ ^ (-(1 / 2 : ℝ)) > ∑ l ∈ univ.erase k, μ l * ‖X l‖ ^ (-(1 / 2 : ℝ))) :
    ∑ j, ∑ l, (mb j : ℂ) * (μ l : ℂ) * P j l ≠ 0 := by
  obtain ⟨r, hr⟩ : ∃ r : Fin N → ℂ, ∀ l, r l ^ 2 = X l :=
    ⟨fun l => X l ^ ((2 : ℕ) : ℂ)⁻¹, fun l => Complex.cpow_nat_inv_pow _ two_ne_zero⟩
  obtain ⟨q, hq0, ε, s, hε, hs, hgl⟩ := Ttest.decomp hmb μ hc hz0 hz1 hP hr
  generalize (mb 1 / mb 0) ^ ((3 : ℝ) / 2) = ρ at hgl
  have hεn : ∀ l, ‖ε l‖ = 1 := fun l => by
    rcases hε l with h | h <;> simp [h]
  have hsn : ∀ l, ‖1 + Complex.I * s l * (ρ : ℂ)‖ = Real.sqrt (1 ^ 2 + ρ ^ 2) := by
    intro l
    rcases hs l with h | h
    · have e : (1 : ℂ) + Complex.I * s l * (ρ : ℂ) = ((1 : ℝ) : ℂ) + (ρ : ℂ) * Complex.I := by
        rw [h]
        push_cast
        ring
      rw [e, Complex.norm_add_mul_I]
    · have e : (1 : ℂ) + Complex.I * s l * (ρ : ℂ) = ((1 : ℝ) : ℂ) + ((-ρ : ℝ) : ℂ) * Complex.I := by
        rw [h]
        push_cast
        ring
      rw [e, Complex.norm_add_mul_I, neg_sq]
  have hrn : ∀ l, ‖r l‖ = ‖X l‖ ^ (1 / 2 : ℝ) := fun l => by
    rw [← Real.sqrt_eq_rpow, ← hr l, norm_pow, Real.sqrt_sq (norm_nonneg _)]
  have hK : 0 < mb 0 * ‖q‖ * Real.sqrt (1 ^ 2 + ρ ^ 2) :=
    mul_pos (mul_pos (hmb 0) (norm_pos_iff.mpr hq0)) (Real.sqrt_pos.mpr (by positivity))
  have hnorm : ∀ l, ‖(mb 0 : ℂ) * (μ l : ℂ) * P 0 l + (mb 1 : ℂ) * (μ l : ℂ) * P 1 l‖ =
      (mb 0 * ‖q‖ * Real.sqrt (1 ^ 2 + ρ ^ 2)) * (μ l * ‖X l‖ ^ (-(1 / 2 : ℝ))) := by
    intro l
    rw [hgl l, norm_mul, norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_of_nonneg (hmb 0).le,
      Complex.norm_of_nonneg (hμ l).le, hεn l, hsn l, hrn l, Real.rpow_neg (norm_nonneg _)]
    ring
  obtain ⟨k, hk⟩ := hT
  have hne := Ttest.sum_ne_zero_of_dominant
    (fun l => (mb 0 : ℂ) * (μ l : ℂ) * P 0 l + (mb 1 : ℂ) * (μ l : ℂ) * P 1 l)
    (fun l => μ l * ‖X l‖ ^ (-(1 / 2 : ℝ))) hK hnorm hk
  rwa [Fin.sum_univ_two, ← Finset.sum_add_distrib]

/-- **Lemma 6.17 (b)** (`lem:Ttest`), as a statement about complex numbers. Let `m_5, m_6 > 0` (`mb 0`, `mb 1`),
`c ≠ 0`, `ẑ_5 = c m_6`, `ẑ_6 = −c m_5` (`zh 0`, `zh 1`), and let `p̂_jl` (`P j l`, `l ∈ Fin N`) satisfy
`p̂_jl² ẑ_j X_l = −1`. Let `β_l = m_l / √X_l` for fixed branches of `√X_l` (any `r_l` with `r_l² = X_l`) and
`ρ = (m_6/m_5)^{3/2}`. If `Σ_{j,l} m_j m_l p̂_jl = 0`, then `Σ_l ε_l β_l (1 + i s_l ρ) = 0` for some signs
`ε, s ∈ {±1}^N`: the sum is `m_5 q Σ_l ε_l β_l (1 + i s_l ρ)` with `q = (−c m_6)^{−1/2}`. For `N = 3` this is the
reduction for the leading data of Lemma 6.16 (b) (`Six.d94_Ttest`). -/
theorem Ttest_b {N : ℕ} {mb : Fin 2 → ℝ} (hmb : ∀ j, 0 < mb j) (μ : Fin N → ℝ) {c : ℂ} (hc : c ≠ 0)
    {zh : Fin 2 → ℂ} (hz0 : zh 0 = c * mb 1) (hz1 : zh 1 = -c * mb 0) {X : Fin N → ℂ}
    {P : Fin 2 → Fin N → ℂ} (hP : ∀ j l, P j l ^ 2 * zh j * X l = -1) {r : Fin N → ℂ}
    (hr : ∀ l, r l ^ 2 = X l) (hsum : ∑ j, ∑ l, (mb j : ℂ) * (μ l : ℂ) * P j l = 0) :
    ∃ ε s : Fin N → ℂ, (∀ l, ε l = 1 ∨ ε l = -1) ∧ (∀ l, s l = 1 ∨ s l = -1) ∧
      ∑ l, ε l * ((μ l : ℂ) / r l) * (1 + Complex.I * s l * (((mb 1 / mb 0) ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) = 0 := by
  obtain ⟨q, hq0, ε, s, hε, hs, hgl⟩ := Ttest.decomp hmb μ hc hz0 hz1 hP hr
  refine ⟨ε, s, hε, hs, ?_⟩
  rw [Fin.sum_univ_two, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun l _ => hgl l,
    ← Finset.mul_sum] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left (mul_ne_zero (Complex.ofReal_ne_zero.mpr (hmb 0).ne') hq0)

/-- The normalization of the proof of **Lemma 6.17** (`lem:Ttest`): if `m_5 ẑ_5 + m_6 ẑ_6 = 0` and `ẑ_5 ≠ 0`, then
`c = ẑ_5 / m_6` satisfies `c ≠ 0`, `ẑ_5 = c m_6` and `ẑ_6 = −c m_5`. -/
theorem bin_c {m5 m6 : ℝ} (h6 : 0 < m6) {z5 z6 : ℂ} (h : (m5 : ℂ) * z5 + (m6 : ℂ) * z6 = 0) (hz : z5 ≠ 0) :
    z5 / m6 ≠ 0 ∧ z5 = z5 / m6 * m6 ∧ z6 = -(z5 / m6) * m5 := by
  have hm6 : (m6 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h6.ne'
  refine ⟨div_ne_zero hz hm6, ?_, ?_⟩
  · linear_combination -z5 * inv_mul_cancel₀ hm6
  · linear_combination (m6 : ℂ)⁻¹ * h - z6 * inv_mul_cancel₀ hm6

/-- **Lemma 6.17 (a)** (`lem:Ttest`) for the leading data of Lemma 6.16 (a) (`d88_lead`): at a singular place with
diagram `88`, with `X_l = [w_l]_{−2}` for `l ∈ K`, the inequality `m_k |X_k|^{−1/2} > Σ_{l∈K, l≠k} m_l |X_l|^{−1/2}`
holds for no `k ∈ K`, since it would make (eq:t88) fail, for every choice of the signs and all `m_5, m_6 > 0`. -/
theorem d88_Ttest (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d88) :
    ¬ ∃ k : Fin 4, m (quad k) * ‖(G.w (quad k)).coeff (-2)‖ ^ (-(1 / 2 : ℝ)) >
      ∑ l ∈ univ.erase k, m (quad l) * ‖(G.w (quad l)).coeff (-2)‖ ^ (-(1 / 2 : ℝ)) := by
  intro hT
  obtain ⟨hbin, -, -, hcross, hsum⟩ := d88_lead hm G hD
  obtain ⟨hc, hc0, hc1⟩ := bin_c (hm (bin 1)) hbin ((bin_com G (d88_facts hD).2.2.1).2 0)
  exact Ttest_a (mb := fun j => m (bin j)) (μ := fun l => m (quad l))
    (zh := fun j => (G.z (bin j)).coeff (-2)) (X := fun l => (G.w (quad l)).coeff (-2))
    (P := fun j l => (G.p (bin j) (quad l)).coeff 2) (fun j => hm _) (fun l => hm _) hc hc0 hc1 hcross hT hsum

/-- **Lemma 6.17 (b)** (`lem:Ttest`) for the leading data of Lemma 6.16 (b) (`d94_lead`): at a singular place with
diagram `94`, with `X_l = [w_l]_{−2}` for `l ≤ 3` (renumbered by `triB`), fixed branches `r_l` of `√X_l`,
`β_l = m_l / r_l` and `ρ = (m_6/m_5)^{3/2}`, there are signs `ε, s ∈ {±1}³` with `Σ_{l≤3} ε_l β_l (1 + i s_l ρ) = 0`. -/
theorem d94_Ttest (hm : ∀ i, 0 < m i) (G : Germ 6 m) (hD : G.HasDiagram Diagram.d94) {r : Fin 3 → ℂ}
    (hr : ∀ l, r l ^ 2 = (G.w (triB l)).coeff (-2)) :
    ∃ ε s : Fin 3 → ℂ, (∀ l, ε l = 1 ∨ ε l = -1) ∧ (∀ l, s l = 1 ∨ s l = -1) ∧
      ∑ l, ε l * ((m (triB l) : ℂ) / r l) *
        (1 + Complex.I * s l * (((m (bin 1) / m (bin 0)) ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) = 0 := by
  obtain ⟨hbin, -, -, hcross, hsum⟩ := d94_lead hm G hD
  obtain ⟨hc, hc0, hc1⟩ := bin_c (hm (bin 1)) hbin ((bin_com G (d94_facts hD).2.2.1).2 0)
  exact Ttest_b (mb := fun j => m (bin j)) (zh := fun j => (G.z (bin j)).coeff (-2))
    (X := fun l => (G.w (triB l)).coeff (-2)) (P := fun j l => (G.p (bin j) (triB l)).coeff 2)
    (fun j => hm _) (fun l => m (triB l)) hc hc0 hc1 hcross hr hsum

end Six

end

end CC6Full
