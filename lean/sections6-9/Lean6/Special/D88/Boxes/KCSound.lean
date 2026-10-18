import Lean6.Special.D88.Boxes.BoxSound

/-!
# What a passing box of KC12 means (Lemma 6.19(d) and Sec. 6.7, last paragraph)

* `kcSum v w ε s = Σ_l ε_l β_l (1 + i s_l ρ)` with `β_l = μ_l / w_l` (`μ = (1, 2, 3)`), `w_l² = X_l(v)`, `ρ = 2√2`.
* **`kc_box_sound`**: a box with `kcBoxOK` has exactly one zero of KC12 in its polydisc, with an invertible Jacobian;
  on the polydisc `X₃ ≠ 0`, and for every choice of the square roots and signs
  `‖kcSum‖ ≥ 1.47·10⁻⁶ (1 + ρ²)^{1/2} Σ_l ‖β_l‖`.
* **`t123_sound`**: the decision of the T-test over the bodies 1, 2, 3 holds at every point of the polydisc.
* **`small_sound`**, **`yBounds_sound`**: the decisions on the relative margin `10⁻⁴` and the bounds on `Y`.
-/

namespace Lean6.Special.D88.Boxes

open Lean6.Special.Ball Lean6.Special.Kraw Metric Complex

/-- The masses `(1, 2, 3)` of the bodies 1, 2, 3. -/
def μ3 : Fin 3 → ℂ := ![1, 2, 3]

/-- The sum `Σ_l ε_l β_l (1 + i s_l ρ)` with `β_l = μ_l / w_l`. -/
noncomputable def kcSum (w : Fin 3 → ℂ) (ε s : Fin 3 → ℤ) : ℂ :=
  ∑ l, (ε l : ℂ) * (μ3 l / w l) * (1 + I * ((s l : ℂ) * (rho : ℂ)))

/-- `Σ_l ‖β_l‖`. -/
noncomputable def betaNorm (w : Fin 3 → ℂ) : ℝ := ∑ l, ‖μ3 l / w l‖

/-- A sign. -/
def IsSign (e : ℤ) : Prop := e = 1 ∨ e = -1

theorem mem_patterns {e2 e3 s1 s2 s3 : ℤ} (h2 : IsSign e2) (h3 : IsSign e3) (k1 : IsSign s1) (k2 : IsSign s2)
    (k3 : IsSign s3) : (e2, e3, s1, s2, s3) ∈ patterns := by
  rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;> rcases k1 with rfl | rfl <;>
    rcases k2 with rfl | rfl <;> rcases k3 with rfl | rfl <;> decide

theorem kc_X_mem {b : Box} {v : Fin 12 → ℂ} (hv : v ∈ closedBall (b.center 12) b.radius) :
    kcD1.Mem (KC.X v 0) ∧ (kcD2 b).Mem (KC.X v 1) ∧ (kcD3 b).Mem (KC.X v 2) := by
  have h0 := coord_mem hv 0
  have h1 := coord_mem hv 1
  rw [show ((0 : Fin 12) : ℕ) = 0 from rfl] at h0
  rw [show ((1 : Fin 12) : ℕ) = 1 from rfl] at h1
  refine ⟨?_, h0, h1⟩
  unfold IDisc.Mem
  simp [kcD1, KC.X, IDisc.center, S_cast, Complex.ext_iff]

/-- Sign bookkeeping: the β's up to the signs `σ`, normalized to `ε₁ = 1`. -/
theorem kcSum_normalize (w : Fin 3 → ℂ) (σ : Fin 3 → ℤ) (hσ : ∀ l, IsSign (σ l)) (ε s : Fin 3 → ℤ)
    (hε : ∀ l, IsSign (ε l)) :
    ∃ e2 e3 : ℤ, IsSign e2 ∧ IsSign e3 ∧
      ‖kcSum w ε s‖ = ‖(σ 0 : ℂ) * (μ3 0 / w 0) * (1 + I * ((s 0 : ℂ) * (rho : ℂ))) +
        (e2 : ℂ) * ((σ 1 : ℂ) * (μ3 1 / w 1) * (1 + I * ((s 1 : ℂ) * (rho : ℂ)))) +
        (e3 : ℂ) * ((σ 2 : ℂ) * (μ3 2 / w 2) * (1 + I * ((s 2 : ℂ) * (rho : ℂ))))‖ := by
  have sq1 : ∀ x : ℤ, IsSign x → (x : ℂ) * x = 1 := by intro x hx; rcases hx with rfl | rfl <;> norm_num
  have mul_sign : ∀ x y : ℤ, IsSign x → IsSign y → IsSign (x * y) := by
    intro x y hx hy; rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [IsSign]
  refine ⟨ε 0 * σ 0 * ε 1 * σ 1, ε 0 * σ 0 * ε 2 * σ 2,
    mul_sign _ _ (mul_sign _ _ (mul_sign _ _ (hε 0) (hσ 0)) (hε 1)) (hσ 1),
    mul_sign _ _ (mul_sign _ _ (mul_sign _ _ (hε 0) (hσ 0)) (hε 2)) (hσ 2), ?_⟩
  have hgs : IsSign (ε 0 * σ 0) := mul_sign _ _ (hε 0) (hσ 0)
  have hg1 : ‖((ε 0 * σ 0 : ℤ) : ℂ)‖ = 1 := by rcases hgs with h | h <;> rw [h] <;> simp
  have c0 := sq1 _ (hσ 0)
  have c1 := sq1 _ (hσ 1)
  have c2 := sq1 _ (hσ 2)
  have ce := sq1 _ (hε 0)
  have e : kcSum w ε s = ((ε 0 * σ 0 : ℤ) : ℂ) * ((σ 0 : ℂ) * (μ3 0 / w 0) * (1 + I * ((s 0 : ℂ) * (rho : ℂ))) +
        ((ε 0 * σ 0 * ε 1 * σ 1 : ℤ) : ℂ) * ((σ 1 : ℂ) * (μ3 1 / w 1) * (1 + I * ((s 1 : ℂ) * (rho : ℂ)))) +
        ((ε 0 * σ 0 * ε 2 * σ 2 : ℤ) : ℂ) * ((σ 2 : ℂ) * (μ3 2 / w 2) * (1 + I * ((s 2 : ℂ) * (rho : ℂ))))) := by
    simp only [kcSum, Fin.sum_univ_three]
    push_cast
    linear_combination
      (-((ε 0 : ℂ) * (μ3 0 / w 0) * (1 + I * ((s 0 : ℂ) * (rho : ℂ)))) -
        (ε 1 : ℂ) * (μ3 1 / w 1) * (1 + I * ((s 1 : ℂ) * (rho : ℂ))) * ((ε 0 : ℂ) * (ε 0 : ℂ)) -
        (ε 2 : ℂ) * (μ3 2 / w 2) * (1 + I * ((s 2 : ℂ) * (rho : ℂ))) * ((ε 0 : ℂ) * (ε 0 : ℂ))) * c0 +
      (-((ε 1 : ℂ) * (μ3 1 / w 1) * (1 + I * ((s 1 : ℂ) * (rho : ℂ)))) -
        (ε 2 : ℂ) * (μ3 2 / w 2) * (1 + I * ((s 2 : ℂ) * (rho : ℂ)))) * ce +
      (-((ε 1 : ℂ) * (μ3 1 / w 1) * (1 + I * ((s 1 : ℂ) * (rho : ℂ)))) *
        ((ε 0 : ℂ) * (ε 0 : ℂ) * ((σ 0 : ℂ) * (σ 0 : ℂ)))) * c1 +
      (-((ε 2 : ℂ) * (μ3 2 / w 2) * (1 + I * ((s 2 : ℂ) * (rho : ℂ)))) *
        ((ε 0 : ℂ) * (ε 0 : ℂ) * ((σ 0 : ℂ) * (σ 0 : ℂ)))) * c2
  rw [e, norm_mul, hg1, one_mul]

/-- Integer signs from the complex signs of `betaDisc_sound`. -/
theorem int_sign {σ : ℂ} (h : σ = 1 ∨ σ = -1) : ∃ k : ℤ, IsSign k ∧ σ = (k : ℂ) := by
  rcases h with rfl | rfl
  · exact ⟨1, Or.inl rfl, by simp⟩
  · exact ⟨-1, Or.inr rfl, by simp⟩

/-- The β-discs at a point: signs `σ_l` with `σ_l β_l` in the discs. -/
theorem kc_betas {b : Box} {B1 B2 B3 : QDisc} (e1 : betaDisc 1 kcD1 = some B1) (e2 : betaDisc 2 (kcD2 b) = some B2)
    (e3 : betaDisc 3 (kcD3 b) = some B3) {v : Fin 12 → ℂ} (hv : v ∈ closedBall (b.center 12) b.radius)
    {w : Fin 3 → ℂ} (hw : ∀ l, w l ^ 2 = KC.X v l.castSucc) :
    ∃ σ : Fin 3 → ℤ, (∀ l, IsSign (σ l)) ∧ B1.Mem ((σ 0 : ℂ) * (μ3 0 / w 0)) ∧
      B2.Mem ((σ 1 : ℂ) * (μ3 1 / w 1)) ∧ B3.Mem ((σ 2 : ℂ) * (μ3 2 / w 2)) := by
  obtain ⟨m1, m2, m3⟩ := kc_X_mem hv
  obtain ⟨σ1, hσ1, b1⟩ := betaDisc_sound e1 m1 (hw 0)
  obtain ⟨σ2, hσ2, b2⟩ := betaDisc_sound e2 m2 (hw 1)
  obtain ⟨σ3, hσ3, b3⟩ := betaDisc_sound e3 m3 (hw 2)
  obtain ⟨k1, hk1, rfl⟩ := int_sign hσ1
  obtain ⟨k2, hk2, rfl⟩ := int_sign hσ2
  obtain ⟨k3, hk3, rfl⟩ := int_sign hσ3
  refine ⟨![k1, k2, k3], fun l => by fin_cases l <;> simpa, ?_, ?_, ?_⟩
  · simpa [μ3] using b1
  · simpa [μ3] using b2
  · simpa [μ3] using b3

theorem norm_signed {k : ℤ} (hk : IsSign k) (z : ℂ) : ‖(k : ℂ) * z‖ = ‖z‖ := by
  rcases hk with rfl | rfl <;> simp

/-- **The sums of Lemma 6.19(d) on a box.** -/
theorem kc_sums_sound {b : Box} (h : kcExtra b = true) {v : Fin 12 → ℂ}
    (hv : v ∈ closedBall (b.center 12) b.radius) {w : Fin 3 → ℂ} (hw : ∀ l, w l ^ 2 = KC.X v l.castSucc)
    (ε s : Fin 3 → ℤ) (hε : ∀ l, IsSign (ε l)) (hs : ∀ l, IsSign (s l)) :
    (147 / 100000000 : ℝ) * Real.sqrt (1 + rho ^ 2) * betaNorm w ≤ ‖kcSum w ε s‖ := by
  unfold kcExtra at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hlen, hrho⟩, hnz⟩, hm⟩ := h
  split at hm
  · rename_i B1 B2 B3 e1 e2 e3
    split at hm
    · rename_i u1 u2 u3 f1 f2 f3
      obtain ⟨σ, hσ, b1, b2, b3⟩ := kc_betas e1 e2 e3 hv hw
      obtain ⟨d2, d3, hd2, hd3, hnorm⟩ := kcSum_normalize w σ hσ ε s hε
      rw [hnorm]
      have hpat := (List.all_eq_true.mp hm) _ (mem_patterns hd2 hd3 (hs 0) (hs 1) (hs 2))
      unfold sumTestAt at hpat
      dsimp only at hpat
      split at hpat
      · rename_i lo hlo
        have hmem := sumDisc3_mem hrho b1 b2 b3 (e2 := d2) (e3 := d3) (hs 0) (hs 1) (hs 2)
        have hge := norm_ge_of_normLo hlo hmem
        have hb : betaNorm w ≤ (u1 : ℝ) + u2 + u3 := by
          unfold betaNorm
          rw [Fin.sum_univ_three]
          have g1 := discUp_sound f1 b1
          have g2 := discUp_sound f2 b2
          have g3 := discUp_sound f3 b3
          rw [norm_signed (hσ 0)] at g1
          rw [norm_signed (hσ 1)] at g2
          rw [norm_signed (hσ 2)] at g3
          linarith
        have hpat' : (147 / 100000000 : ℝ) * 3 * ((u1 : ℝ) + u2 + u3) ≤ lo - (sumDisc3 B1 B2 B3 d2 d3 (s 0) (s 1) (s 2)).r := by
          have hq := hpat
          simp only [decide_eq_true_eq] at hq
          have hr := (Rat.cast_le (K := ℝ)).mpr hq
          push_cast at hr
          exact hr
        rw [sqrt_one_add_rho_sq]
        have hc : (147 / 100000000 : ℝ) * 3 * betaNorm w ≤ (147 / 100000000 : ℝ) * 3 * ((u1 : ℝ) + u2 + u3) := by
          gcongr
        have := hge
        push_cast at this ⊢
        linarith
      · exact absurd hpat (by simp)
    · exact absurd hm (by simp)
  · exact absurd hm (by simp)

theorem kc12T_termOK : ∀ Fi ∈ kc12T, ∀ t ∈ Fi, termOK 12 t = true := by
  have : kc12T.all (fun Fi => Fi.all (termOK 12)) = true := by decide
  simp only [List.all_eq_true] at this
  exact this

/-- `KC12` is the row-scaled generated map. -/
theorem KC12_eq (z : Fin 12 → ℂ) (i : Fin 12) :
    KC.KC12 z i = (KC.scale i)⁻¹ * (kc12T.getD i []).eval κ1 (extF z) := by
  have : kc12T.getD i [] = kc12T.get (i.cast KC.kc12T_length.symm) := by
    rw [List.getD_eq_getElem _ _ (by rw [KC.kc12T_length]; exact i.2)]; rfl
  rw [this, KC.eval_kc12T, ← mul_assoc, inv_mul_cancel₀ (KC.scale_ne_zero i), one_mul]

/-- `X₂ ≠ 0` on the polydisc: the β-disc of `X₂` exists. -/
theorem kc_X1_ne_zero {b : Box} (h : kcExtra b = true) {v : Fin 12 → ℂ}
    (hv : v ∈ closedBall (b.center 12) b.radius) : KC.X v 1 ≠ 0 := by
  unfold kcExtra at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, -⟩, -⟩, hm⟩ := h
  split at hm
  · rename_i B1 B2 B3 e1 e2 e3
    exact betaDisc_X_ne_zero e2 (kc_X_mem hv).2.1
  · exact absurd hm (by simp)

/-- **A box of Lemma 6.19(d), as a `Box` value** (the test after parsing). -/
theorem kc_box_soundB {b : Box} (h : (kcRadiusOK b && krawBox kc12T b && kcExtra b) = true) :
    0 < b.radius ∧ b.radius < 5 / 10 ^ 54 ∧
      (∃ z ∈ closedBall (b.center 12) b.radius, KC.KC12 z = 0 ∧
        (∀ w ∈ closedBall (b.center 12) b.radius, KC.KC12 w = 0 → w = z) ∧
        ∃ J : Matrix (Fin 12) (Fin 12) ℂ, IsUnit J.det ∧ HasFDerivAt KC.KC12 (Matrix.toLin' J).toContinuousLinearMap z) ∧
      ∀ v ∈ closedBall (b.center 12) b.radius, KC.X v 2 ≠ 0 ∧
        (∀ w : Fin 3 → ℂ, (∀ l, w l ^ 2 = KC.X v l.castSucc) → ∀ ε s : Fin 3 → ℤ, (∀ l, IsSign (ε l)) →
          (∀ l, IsSign (s l)) → (147 / 100000000 : ℝ) * Real.sqrt (1 + rho ^ 2) * betaNorm w ≤ ‖kcSum w ε s‖) ∧
        ∀ l : Fin 3, KC.X v l.castSucc ≠ 0 := by
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hrad, hkraw⟩, hext⟩ := h
  unfold kcRadiusOK at hrad
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrad
  unfold krawBox at hkraw
  simp only [Bool.and_eq_true] at hkraw
  obtain ⟨hsmall, hk⟩ := hkraw
  have hext' := hext
  unfold kcExtra at hext'
  simp only [Bool.and_eq_true, beq_iff_eq] at hext'
  obtain ⟨⟨⟨hlen, -⟩, hnz⟩, -⟩ := hext'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Box.radius
    have : (0 : ℝ) < b.rho := by exact_mod_cast hrad.1
    positivity
  · unfold Box.radius
    have h5 : (b.rho : ℝ) * 10 ^ 54 < 5 * 2 ^ P := by
      have := hrad.2
      rw [← S_cast]
      exact_mod_cast this
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith
  · exact zero_jac_of_kraw KC.kc12T_length (by norm_num) kc12T_termOK KC.scale_ne_zero KC12_eq hsmall hlen hk
  · intro v hv
    refine ⟨discNonzero_sound hnz (by simp [kcD3, S]) (kc_X_mem hv).2.2, ?_, ?_⟩
    · intro w hw ε s hε hs
      exact kc_sums_sound hext hv hw ε s hε hs
    · intro l
      fin_cases l
      · simp [KC.X]
      · exact kc_X1_ne_zero hext hv
      · exact discNonzero_sound hnz (by simp [kcD3, S]) (kc_X_mem hv).2.2

/-- The test of a box of Lemma 6.19(d) fixes the number of centres: `12`. -/
theorem kc_len_of_test {b : Box} (h : (kcRadiusOK b && krawBox kc12T b && kcExtra b) = true) : b.cs.length = 12 := by
  simp only [Bool.and_eq_true] at h
  have := h.2
  unfold kcExtra at this
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1.1

/-- **A box of Lemma 6.19(d)**, as a string of the certificate file: `kc_box_soundB` after parsing. -/
theorem kc_box_sound {s : String} (h : kcBoxOK s = true) :
    ∃ b, parseBox s = some b ∧ 0 < b.radius ∧ b.radius < 5 / 10 ^ 54 ∧
      (∃ z ∈ closedBall (b.center 12) b.radius, KC.KC12 z = 0 ∧
        (∀ w ∈ closedBall (b.center 12) b.radius, KC.KC12 w = 0 → w = z) ∧
        ∃ J : Matrix (Fin 12) (Fin 12) ℂ, IsUnit J.det ∧ HasFDerivAt KC.KC12 (Matrix.toLin' J).toContinuousLinearMap z) ∧
      ∀ v ∈ closedBall (b.center 12) b.radius, KC.X v 2 ≠ 0 ∧
        (∀ w : Fin 3 → ℂ, (∀ l, w l ^ 2 = KC.X v l.castSucc) → ∀ ε s : Fin 3 → ℤ, (∀ l, IsSign (ε l)) →
          (∀ l, IsSign (s l)) → (147 / 100000000 : ℝ) * Real.sqrt (1 + rho ^ 2) * betaNorm w ≤ ‖kcSum w ε s‖) ∧
        ∀ l : Fin 3, KC.X v l.castSucc ≠ 0 := by
  unfold kcBoxOK at h
  split at h
  · rename_i b hb
    exact ⟨b, hb, kc_box_soundB h⟩
  · exact absurd h (by simp)

/-! ## Sec. 6.7, last paragraph -/

/-- The T-test over the bodies 1, 2, 3 passes at `t` (`t_l = ‖X_l‖^{-1/2}`). -/
def T123Pass (t : Fin 3 → ℝ) : Prop :=
  ∃ k : Fin 3, (∑ l, if l = k then 0 else (μ3 l).re * t l) < (μ3 k).re * t k

/-- It fails at `t`: every body is dominated by the others. -/
def T123Fail (t : Fin 3 → ℝ) : Prop :=
  ∀ k : Fin 3, (μ3 k).re * t k < ∑ l, if l = k then 0 else (μ3 l).re * t l

/-- **The decision of the T-test over the bodies 1, 2, 3.** -/
theorem t123_sound {b : Box} {d : Bool} (h : t123Decide b = some d) {v : Fin 12 → ℂ}
    (hv : v ∈ closedBall (b.center 12) b.radius) :
    (d = true → T123Pass fun l => 1 / Real.sqrt ‖KC.X v l.castSucc‖) ∧
      (d = false → T123Fail fun l => 1 / Real.sqrt ‖KC.X v l.castSucc‖) := by
  unfold t123Decide at h
  obtain ⟨m1, m2, m3⟩ := kc_X_mem hv
  set t0 := 1 / Real.sqrt ‖KC.X v 0‖ with ht0
  set t1 := 1 / Real.sqrt ‖KC.X v 1‖ with ht1
  set t2 := 1 / Real.sqrt ‖KC.X v 2‖ with ht2
  have ht : (fun l : Fin 3 => 1 / Real.sqrt ‖KC.X v l.castSucc‖) = ![t0, t1, t2] := by
    funext l
    fin_cases l <;> rfl
  rw [ht]
  split at h
  · rename_i l1 u1 l2 u2 l3 u3 e1 e2 e3
    obtain ⟨a1, c1⟩ := discInvSqrt_sound e1 (by simp [kcD1, S]) m1
    obtain ⟨a2, c2⟩ := discInvSqrt_sound e2 (by simp [kcD2, S]) m2
    obtain ⟨a3, c3⟩ := discInvSqrt_sound e3 (by simp [kcD3, S]) m3
    rw [← ht0] at a1 c1
    rw [← ht1] at a2 c2
    rw [← ht2] at a3 c3
    have hq : (0 : ℝ) < 2 ^ Q := by positivity
    rw [div_le_iff₀ hq] at a1 a2 a3
    rw [le_div_iff₀ hq] at c1 c2 c3
    have key : ∀ x y : ℝ, x * 2 ^ Q < y * 2 ^ Q → x < y := fun x y hxy => lt_of_mul_lt_mul_right hxy hq.le
    split_ifs at h with hp hf
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
      unfold t123Pass at hp
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hp
      unfold T123Pass
      rcases hp with (hp | hp) | hp
      · refine ⟨0, ?_⟩
        have hp' : (2 * u2 + 3 * u3 : ℝ) < l1 := by exact_mod_cast hp
        simp [Fin.sum_univ_three, μ3]
        exact key _ _ (by nlinarith)
      · refine ⟨1, ?_⟩
        have hp' : (u1 + 3 * u3 : ℝ) < 2 * l2 := by exact_mod_cast hp
        simp [Fin.sum_univ_three, μ3]
        exact key _ _ (by nlinarith)
      · refine ⟨2, ?_⟩
        have hp' : (u1 + 2 * u2 : ℝ) < 3 * l3 := by exact_mod_cast hp
        simp [Fin.sum_univ_three, μ3]
        exact key _ _ (by nlinarith)
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
      unfold t123Fail at hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
      obtain ⟨⟨f1, f2⟩, f3⟩ := hf
      have f1' : (u1 : ℝ) < 2 * l2 + 3 * l3 := by exact_mod_cast f1
      have f2' : (2 * u2 : ℝ) < l1 + 3 * l3 := by exact_mod_cast f2
      have f3' : (3 * u3 : ℝ) < l1 + 2 * l2 := by exact_mod_cast f3
      unfold T123Fail
      intro k
      fin_cases k
      · simp [Fin.sum_univ_three, μ3]
        exact key _ _ (by nlinarith)
      · simp [Fin.sum_univ_three, μ3]
        exact key _ _ (by nlinarith)
      · simp [Fin.sum_univ_three, μ3]
        exact key _ _ (by nlinarith)
  · exact absurd h (by simp)

/-- **The decision of the relative margin `10⁻⁴`.** -/
theorem small_sound {b : Box} {d : Bool} (h : smallDecide b = some d) (hrho : rho0OK = true) {v : Fin 12 → ℂ}
    (hv : v ∈ closedBall (b.center 12) b.radius) {w : Fin 3 → ℂ} (hw : ∀ l, w l ^ 2 = KC.X v l.castSucc) :
    (d = true → ∃ ε s : Fin 3 → ℤ, (∀ l, IsSign (ε l)) ∧ (∀ l, IsSign (s l)) ∧
        ‖kcSum w ε s‖ < (1 / 10000 : ℝ) * Real.sqrt (1 + rho ^ 2) * betaNorm w) ∧
      (d = false → ∀ ε s : Fin 3 → ℤ, (∀ l, IsSign (ε l)) → (∀ l, IsSign (s l)) →
        (1 / 10000 : ℝ) * Real.sqrt (1 + rho ^ 2) * betaNorm w ≤ ‖kcSum w ε s‖) := by
  unfold smallDecide at h
  split at h
  · rename_i B1 B2 B3 e1 e2 e3
    split at h
    · rename_i l1 l2 l3 u1 u2 u3 g1 g2 g3 f1 f2 f3
      obtain ⟨σ, hσ, b1, b2, b3⟩ := kc_betas e1 e2 e3 hv hw
      have hsign : ∀ k : ℤ, IsSign k → ∀ z : ℂ, ‖(k : ℂ) * z‖ = ‖z‖ := fun k hk z => norm_signed hk z
      have hbu : betaNorm w ≤ (u1 : ℝ) + u2 + u3 := by
        unfold betaNorm
        rw [Fin.sum_univ_three]
        have q1 := discUp_sound f1 b1
        have q2 := discUp_sound f2 b2
        have q3 := discUp_sound f3 b3
        rw [hsign _ (hσ 0)] at q1
        rw [hsign _ (hσ 1)] at q2
        rw [hsign _ (hσ 2)] at q3
        linarith
      have hbl : (l1 : ℝ) + l2 + l3 ≤ betaNorm w := by
        unfold betaNorm
        rw [Fin.sum_univ_three]
        have q1 := discLo_sound g1 b1
        have q2 := discLo_sound g2 b2
        have q3 := discLo_sound g3 b3
        rw [hsign _ (hσ 0)] at q1
        rw [hsign _ (hσ 1)] at q2
        rw [hsign _ (hσ 2)] at q3
        linarith
      rw [sqrt_one_add_rho_sq]
      split_ifs at h with hsm hbig
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
        obtain ⟨pt, hpt, hsmall⟩ := List.any_eq_true.mp hsm
        obtain ⟨d2, d3, t1, t2, t3⟩ := pt
        simp only [patterns, List.mem_flatMap, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hpt
        obtain ⟨d2', hd2, d3', hd3, t1', ht1, t2', ht2, t3', ht3, he⟩ := hpt
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
        refine ⟨![σ 0, d2' * σ 1, d3' * σ 2], ![t1', t2', t3'], ?_, ?_, ?_⟩
        · intro l
          have mul_sign : ∀ x y : ℤ, IsSign x → IsSign y → IsSign (x * y) := by
            intro x y hx hy; rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [IsSign]
          fin_cases l
          · exact hσ 0
          · exact mul_sign _ _ (by rcases hd2 with rfl | rfl <;> simp [IsSign]) (hσ 1)
          · exact mul_sign _ _ (by rcases hd3 with rfl | rfl <;> simp [IsSign]) (hσ 2)
        · intro l
          fin_cases l
          · rcases ht1 with rfl | rfl <;> simp [IsSign]
          · rcases ht2 with rfl | rfl <;> simp [IsSign]
          · rcases ht3 with rfl | rfl <;> simp [IsSign]
        · unfold smallAt at hsmall
          dsimp only at hsmall
          split at hsmall
          · rename_i hi hhi
            have hs1 : IsSign t1' := by rcases ht1 with rfl | rfl <;> simp [IsSign]
            have hs2 : IsSign t2' := by rcases ht2 with rfl | rfl <;> simp [IsSign]
            have hs3 : IsSign t3' := by rcases ht3 with rfl | rfl <;> simp [IsSign]
            have hmem := sumDisc3_mem hrho b1 b2 b3 (e2 := d2') (e3 := d3') hs1 hs2 hs3
            have hle := norm_le_of_normHi hhi hmem
            have hsm' : (hi : ℝ) + (sumDisc3 B1 B2 B3 d2' d3' t1' t2' t3').r < (1 / 10000 : ℝ) * 3 * ((l1 : ℝ) + l2 + l3) := by
              have hq := hsmall
              simp only [decide_eq_true_eq] at hq
              have hr := (Rat.cast_lt (K := ℝ)).mpr hq
              push_cast at hr
              exact hr
            have heq : kcSum w ![σ 0, d2' * σ 1, d3' * σ 2] ![t1', t2', t3'] =
                (σ 0 : ℂ) * (μ3 0 / w 0) * (1 + I * ((t1' : ℂ) * (rho : ℂ))) +
                (d2' : ℂ) * ((σ 1 : ℂ) * (μ3 1 / w 1) * (1 + I * ((t2' : ℂ) * (rho : ℂ)))) +
                (d3' : ℂ) * ((σ 2 : ℂ) * (μ3 2 / w 2) * (1 + I * ((t3' : ℂ) * (rho : ℂ)))) := by
              simp only [kcSum, Fin.sum_univ_three]
              simp
              ring
            rw [heq]
            nlinarith
          · exact absurd hsmall (by simp)
      · simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun h => absurd h (by simp), fun _ ε s hε hs => ?_⟩
        obtain ⟨d2, d3, hd2, hd3, hnorm⟩ := kcSum_normalize w σ hσ ε s hε
        rw [hnorm]
        have hpat := (List.all_eq_true.mp hbig) _ (mem_patterns hd2 hd3 (hs 0) (hs 1) (hs 2))
        unfold bigAt at hpat
        dsimp only at hpat
        split at hpat
        · rename_i lo hlo
          have hmem := sumDisc3_mem hrho b1 b2 b3 (e2 := d2) (e3 := d3) (hs 0) (hs 1) (hs 2)
          have hge := norm_ge_of_normLo hlo hmem
          have hpat' : (1 / 10000 : ℝ) * 3 * ((u1 : ℝ) + u2 + u3) ≤ lo - (sumDisc3 B1 B2 B3 d2 d3 (s 0) (s 1) (s 2)).r := by
            have hq := hpat
            simp only [decide_eq_true_eq] at hq
            have hr := (Rat.cast_le (K := ℝ)).mpr hq
            push_cast at hr
            exact hr
          nlinarith
        · exact absurd hpat (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **The bounds on `Y`.** -/
theorem yBounds_sound {b : Box} (h : yBounds b = true) {v : Fin 12 → ℂ} (hv : v ∈ closedBall (b.center 12) b.radius) :
    5000 < ‖KC.Y v 3‖ ∧ ∀ l : Fin 3, ‖KC.Y v l.castSucc‖ < 3 / 100000 * ‖KC.Y v 3‖ := by
  unfold yBounds at h
  split at h
  · rename_i L4 u4 l1 U1 l2 U2 l3 U3 e4 e1 e2 e3
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h4, h1⟩, h2⟩, h3⟩ := h
    have hS : (0 : ℝ) < (S : ℝ) := by rw [S_cast]; positivity
    have c4 := coord_mem hv 5
    have c1 := coord_mem hv 2
    have c2 := coord_mem hv 3
    have c3 := coord_mem hv 4
    rw [show ((5 : Fin 12) : ℕ) = 5 from rfl] at c4
    rw [show ((2 : Fin 12) : ℕ) = 2 from rfl] at c1
    rw [show ((3 : Fin 12) : ℕ) = 3 from rfl] at c2
    rw [show ((4 : Fin 12) : ℕ) = 4 from rfl] at c3
    have g4 := (modBounds_sound e4 (by simp [coordDisc, S]) c4).1
    have g1 := (modBounds_sound e1 (by simp [coordDisc, S]) c1).2
    have g2 := (modBounds_sound e2 (by simp [coordDisc, S]) c2).2
    have g3 := (modBounds_sound e3 (by simp [coordDisc, S]) c3).2
    simp only [coordDisc] at g4 g1 g2 g3
    have h4' : (5000 : ℝ) * S < L4 := by exact_mod_cast h4
    have h1' : (U1 : ℝ) * 100000 < 3 * L4 := by exact_mod_cast h1
    have h2' : (U2 : ℝ) * 100000 < 3 * L4 := by exact_mod_cast h2
    have h3' : (U3 : ℝ) * 100000 < 3 * L4 := by exact_mod_cast h3
    have hY4 : KC.Y v 3 = v 5 := rfl
    have ratio : ∀ (y : ℂ) (U : ℕ), (S : ℝ) * ‖y‖ ≤ U → (U : ℝ) * 100000 < 3 * L4 → ‖y‖ < 3 / 100000 * ‖v 5‖ := by
      intro y U hy hU
      have : (S : ℝ) * (‖y‖ * 100000) < (S : ℝ) * (3 * ‖v 5‖) := by nlinarith
      have := lt_of_mul_lt_mul_left this hS.le
      linarith
    refine ⟨?_, fun l => ?_⟩
    · rw [hY4]
      have : (S : ℝ) * 5000 < (S : ℝ) * ‖v 5‖ := by linarith
      exact lt_of_mul_lt_mul_left this hS.le
    · fin_cases l
      · exact ratio (v 2) U1 g1 h1'
      · exact ratio (v 3) U2 g2 h2'
      · exact ratio (v 4) U3 g3 h3'
  · exact absurd h (by simp)

end Lean6.Special.D88.Boxes
