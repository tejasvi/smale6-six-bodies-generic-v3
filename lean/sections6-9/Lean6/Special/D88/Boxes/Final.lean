import Lean6.Special.D88.Boxes.KCSound
import Lean6.Special.Comp.D88.Boxes.N4.Disj
import Lean6.Special.Comp.D88.Boxes.KC.Disj
import Lean6.Special.Comp.D88.Boxes.KC.Counts

/-!
# Lemma 6.19(c), (d) and Sec. 6.7, last paragraph

* **`lemma_6_19_c`**: there are 20,316 pairwise disjoint polydiscs in `ℂ¹¹` of radius below `6·10⁻⁴⁷`, each
  containing exactly one zero of S11(μ₀), at which S11 has an invertible Jacobian matrix; on each polydisc
  `X₃ − X₄ ≠ 0` and the T-test of Lemma 6.17(a) holds with margin `0.1756`.
* **`lemma_6_19_d`**: there are 4788 pairwise disjoint polydiscs in `ℂ¹²` of radius below `5·10⁻⁵⁴`, each containing
  exactly one zero of KC12(μ₀), with an invertible Jacobian matrix; on each `X₃ ≠ 0`, and for `(m₅, m₆) = (1, 2)`
  all 32 sums of Lemma 6.17(b) have modulus at least `1.47·10⁻⁶ (1 + ρ²)^{1/2} Σ_l |β_l|`, for every choice of the
  square roots.
* **`sec_6_7_counts`**: at the zeros of (d), the T-test over the bodies 1, 2, 3 fails at exactly 1092 and holds at
  exactly 3696; the smallest of the 32 sums has relative margin below `10⁻⁴` at exactly 36, and at these
  `|Y₄| > 5·10³` and `|Y_l/Y₄| < 3·10⁻⁵` for `l = 1, 2, 3`.

The boxes are those of the certificate files of diagrams 88 and 94 (`k4_cert_1_2_3_30.jsonl`,
`kc_cert_1_2_3_30.jsonl`), read verbatim by the generated modules `Comp/D88/Boxes/{N4,KC}/D<j>`.
-/

namespace Lean6.Special.D88.Boxes

open Lean6.Special.Ball Lean6.Special.Kraw Metric Complex

theorem mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {bs : List β}, l.mapM f = some bs →
      bs.length = l.length ∧ ∀ (i : ℕ) (h : i < l.length) (h' : i < bs.length), f l[i] = some bs[i]
  | [], bs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i h => absurd h (by simp)⟩
  | a :: l, bs, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs' =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hget⟩ := mapM_some hl
        refine ⟨by simp [hlen], fun i hi hi' => ?_⟩
        rcases i with _ | i
        · simpa using ha
        · simp only [List.getElem_cons_succ]
          exact hget i (by simpa using hi) (by simpa using hi')

theorem pairwiseSep_sound : ∀ {bs : List Box}, pairwiseSep bs = true → bs.Pairwise fun a b => sepBoxes a b = true
  | [], _ => List.Pairwise.nil
  | b :: rest, h => by
    simp only [pairwiseSep, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (pairwiseSep_sound h.2)

/-- **Separated boxes have disjoint polydiscs.** -/
theorem sepBoxes_disjoint {b b' : Box} (h : sepBoxes b b' = true) {n : ℕ} (hb : b.cs.length = n)
    (hb' : b'.cs.length = n) : Disjoint (closedBall (b.center n) b.radius) (closedBall (b'.center n) b'.radius) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  unfold sepBoxes at h
  obtain ⟨⟨x, y⟩, hxy, hf⟩ := List.any_eq_true.mp h
  obtain ⟨j, hj, hjxy⟩ := List.mem_iff_getElem.mp hxy
  have hjn : j < n := by simp [List.length_zip, hb, hb'] at hj; omega
  rw [List.getElem_zip] at hjxy
  simp only [Prod.mk.injEq] at hjxy
  obtain ⟨hx, hy⟩ := hjxy
  have hcx : b.c j = x := by unfold Box.c; rw [List.getD_eq_getElem _ _ (by omega)]; exact hx
  have hcy : b'.c j = y := by unfold Box.c; rw [List.getD_eq_getElem _ _ (by omega)]; exact hy
  have d1 := (norm_le_pi_norm (z - b.center n) ⟨j, hjn⟩).trans (mem_closedBall_iff_norm.mp hz)
  have d2 := (norm_le_pi_norm (z - b'.center n) ⟨j, hjn⟩).trans (mem_closedBall_iff_norm.mp hz')
  simp only [Pi.sub_apply, Box.center, hcx, hcy] at d1 d2
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hf
  rcases hf with hf | hf
  · have r1 := (Complex.abs_re_le_norm _).trans d1
    have r2 := (Complex.abs_re_le_norm _).trans d2
    simp only [Complex.sub_re] at r1 r2
    have hf' : ((b.rho + b'.rho : ℕ) : ℝ) < ((x.1 - y.1).natAbs : ℝ) := by exact_mod_cast hf
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub] at hf'
    push_cast at hf'
    unfold Box.radius at r1 r2
    have e1 := abs_sub_abs_le_abs_sub ((x.1 : ℝ) / 2 ^ P - (y.1 : ℝ) / 2 ^ P) 0
    have : |(x.1 : ℝ) / 2 ^ P - (y.1 : ℝ) / 2 ^ P| ≤ (b.rho : ℝ) / 2 ^ P + (b'.rho : ℝ) / 2 ^ P := by
      calc |(x.1 : ℝ) / 2 ^ P - (y.1 : ℝ) / 2 ^ P| = |(z ⟨j, hjn⟩).re - (y.1 : ℝ) / 2 ^ P -
          ((z ⟨j, hjn⟩).re - (x.1 : ℝ) / 2 ^ P)| := by ring_nf
        _ ≤ |(z ⟨j, hjn⟩).re - (y.1 : ℝ) / 2 ^ P| + |(z ⟨j, hjn⟩).re - (x.1 : ℝ) / 2 ^ P| := abs_sub _ _
        _ ≤ _ := by linarith
    rw [← sub_div, abs_div, abs_of_pos hP, ← add_div, div_le_div_iff_of_pos_right hP] at this
    linarith
  · have r1 := (Complex.abs_im_le_norm _).trans d1
    have r2 := (Complex.abs_im_le_norm _).trans d2
    simp only [Complex.sub_im] at r1 r2
    have hf' : ((b.rho + b'.rho : ℕ) : ℝ) < ((x.2 - y.2).natAbs : ℝ) := by exact_mod_cast hf
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub] at hf'
    push_cast at hf'
    unfold Box.radius at r1 r2
    have : |(x.2 : ℝ) / 2 ^ P - (y.2 : ℝ) / 2 ^ P| ≤ (b.rho : ℝ) / 2 ^ P + (b'.rho : ℝ) / 2 ^ P := by
      calc |(x.2 : ℝ) / 2 ^ P - (y.2 : ℝ) / 2 ^ P| = |(z ⟨j, hjn⟩).im - (y.2 : ℝ) / 2 ^ P -
          ((z ⟨j, hjn⟩).im - (x.2 : ℝ) / 2 ^ P)| := by ring_nf
        _ ≤ |(z ⟨j, hjn⟩).im - (y.2 : ℝ) / 2 ^ P| + |(z ⟨j, hjn⟩).im - (x.2 : ℝ) / 2 ^ P| := abs_sub _ _
        _ ≤ _ := by linarith
    rw [← sub_div, abs_div, abs_of_pos hP, ← add_div, div_le_div_iff_of_pos_right hP] at this
    linarith

theorem n4_len {s : String} {b : Box} (h : n4BoxOK s = true) (hb : parseBox s = some b) : b.cs.length = 11 := by
  unfold n4BoxOK at h
  rw [hb] at h
  simp only [Bool.and_eq_true] at h
  have := h.2
  unfold n4Extra at this
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1

theorem kc_len {s : String} {b : Box} (h : kcBoxOK s = true) (hb : parseBox s = some b) : b.cs.length = 12 := by
  unfold kcBoxOK at h
  rw [hb] at h
  simp only [Bool.and_eq_true] at h
  have := h.2
  unfold kcExtra at this
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1.1

/-- The parsed boxes of a list of strings that pass `allSep`. -/
theorem allSep_boxes {l : List String} (h : allSep l = true) :
    ∃ bs : List Box, bs.length = l.length ∧ (∀ (i : ℕ) (hi : i < l.length) (hi' : i < bs.length),
      parseBox l[i] = some bs[i]) ∧ bs.Pairwise fun a b => sepBoxes a b = true := by
  unfold allSep at h
  split at h
  · rename_i bs hbs
    obtain ⟨hlen, hget⟩ := mapM_some hbs
    exact ⟨bs, hlen, hget, pairwiseSep_sound h⟩
  · exact absurd h (by simp)

/-- Pairwise disjointness of the polydiscs of a pairwise separated list of boxes of dimension `n`. -/
theorem disjoint_of_pairwise {bs : List Box} (hp : bs.Pairwise fun a b => sepBoxes a b = true) {n : ℕ}
    (hlen : ∀ (i : ℕ) (hi : i < bs.length), bs[i].cs.length = n) {i j : ℕ} (hi : i < bs.length) (hj : j < bs.length)
    (hij : i ≠ j) : Disjoint (closedBall (bs[i].center n) bs[i].radius) (closedBall (bs[j].center n) bs[j].radius) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact sepBoxes_disjoint (List.pairwise_iff_getElem.mp hp i j hi hj h) (hlen i hi) (hlen j hj)
  · exact (sepBoxes_disjoint (List.pairwise_iff_getElem.mp hp j i hj hi h) (hlen j hj) (hlen i hi)).symm

/-- **Lemma 6.19(c).** -/
theorem lemma_6_19_c :
    ∃ (c : Fin 20316 → Fin 11 → ℂ) (r : Fin 20316 → ℝ),
      (∀ k, 0 < r k ∧ r k < 6 / 10 ^ 47) ∧
      Pairwise (fun k l => Disjoint (closedBall (c k) (r k)) (closedBall (c l) (r l))) ∧
      ∀ k, (∃ z ∈ closedBall (c k) (r k), N4.S11 z = 0 ∧ (∀ w ∈ closedBall (c k) (r k), N4.S11 w = 0 → w = z) ∧
          ∃ J : Matrix (Fin 11) (Fin 11) ℂ, IsUnit J.det ∧
            HasFDerivAt N4.S11 (Matrix.toLin' J).toContinuousLinearMap z) ∧
        ∀ w ∈ closedBall (c k) (r k), N4.X w 2 - N4.X w 3 ≠ 0 ∧ TTest4 (fun l => 1 / Real.sqrt ‖N4.X w l‖) ∧
          ∀ l, N4.X w l ≠ 0 := by
  obtain ⟨bs, hlen, hget, hpw⟩ := allSep_boxes N4.allSep_ok
  have hN : N4.allData.length = 20316 := N4.allData_length
  have hok0 := N4.all_ok
  unfold n4ChunkOK at hok0
  have hok : ∀ s ∈ N4.allData, n4BoxOK s = true := List.all_eq_true.mp hok0
  have hbs : bs.length = 20316 := by rw [hlen, hN]
  have hbox : ∀ (k : ℕ) (hk : k < 20316), n4BoxOK (N4.allData[k]'(by rw [hN]; exact hk)) = true ∧
      parseBox (N4.allData[k]'(by rw [hN]; exact hk)) = some (bs[k]'(by rw [hbs]; exact hk)) := fun k hk =>
    ⟨hok _ (List.getElem_mem _), hget k (by rw [hN]; exact hk) (by rw [hbs]; exact hk)⟩
  refine ⟨fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).center 11, fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).radius,
    fun k => ?_, fun k l hkl => ?_, fun k => ?_⟩
  · obtain ⟨h1, h2⟩ := hbox k.1 k.2
    obtain ⟨b, hb, hr0, hr1, -⟩ := n4_box_sound h1
    rw [h2, Option.some.injEq] at hb
    subst hb
    exact ⟨hr0, hr1⟩
  · refine disjoint_of_pairwise hpw (n := 11) (fun i hi => ?_) (by rw [hbs]; exact k.2) (by rw [hbs]; exact l.2)
      (fun h => hkl (Fin.ext h))
    obtain ⟨h1, h2⟩ := hbox i (by rw [← hbs]; exact hi)
    exact n4_len h1 h2
  · obtain ⟨h1, h2⟩ := hbox k.1 k.2
    obtain ⟨b, hb, -, -, hz, hx⟩ := n4_box_sound h1
    rw [h2, Option.some.injEq] at hb
    subst hb
    exact ⟨hz, hx⟩

/-- **Lemma 6.19(d).** -/
theorem lemma_6_19_d :
    ∃ (c : Fin 4788 → Fin 12 → ℂ) (r : Fin 4788 → ℝ),
      (∀ k, 0 < r k ∧ r k < 5 / 10 ^ 54) ∧
      Pairwise (fun k l => Disjoint (closedBall (c k) (r k)) (closedBall (c l) (r l))) ∧
      ∀ k, (∃ z ∈ closedBall (c k) (r k), KC.KC12 z = 0 ∧ (∀ w ∈ closedBall (c k) (r k), KC.KC12 w = 0 → w = z) ∧
          ∃ J : Matrix (Fin 12) (Fin 12) ℂ, IsUnit J.det ∧
            HasFDerivAt KC.KC12 (Matrix.toLin' J).toContinuousLinearMap z) ∧
        ∀ v ∈ closedBall (c k) (r k), KC.X v 2 ≠ 0 ∧
          (∀ w : Fin 3 → ℂ, (∀ l, w l ^ 2 = KC.X v l.castSucc) → ∀ ε s : Fin 3 → ℤ, (∀ l, IsSign (ε l)) →
            (∀ l, IsSign (s l)) → (147 / 100000000 : ℝ) * Real.sqrt (1 + rho ^ 2) * betaNorm w ≤ ‖kcSum w ε s‖) ∧
          ∀ l : Fin 3, KC.X v l.castSucc ≠ 0 := by
  obtain ⟨bs, hlen, hget, hpw⟩ := allSep_boxes KC.allSep_ok
  have hN : KC.allData.length = 4788 := KC.allData_length
  have hok0 := KC.all_ok
  unfold kcChunkOK at hok0
  have hok : ∀ s ∈ KC.allData, kcBoxOK s = true := List.all_eq_true.mp hok0
  have hbs : bs.length = 4788 := by rw [hlen, hN]
  have hbox : ∀ (k : ℕ) (hk : k < 4788), kcBoxOK (KC.allData[k]'(by rw [hN]; exact hk)) = true ∧
      parseBox (KC.allData[k]'(by rw [hN]; exact hk)) = some (bs[k]'(by rw [hbs]; exact hk)) := fun k hk =>
    ⟨hok _ (List.getElem_mem _), hget k (by rw [hN]; exact hk) (by rw [hbs]; exact hk)⟩
  refine ⟨fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).center 12, fun k => (bs[k.1]'(by rw [hbs]; exact k.2)).radius,
    fun k => ?_, fun k l hkl => ?_, fun k => ?_⟩
  · obtain ⟨h1, h2⟩ := hbox k.1 k.2
    obtain ⟨b, hb, hr0, hr1, -⟩ := kc_box_sound h1
    rw [h2, Option.some.injEq] at hb
    subst hb
    exact ⟨hr0, hr1⟩
  · refine disjoint_of_pairwise hpw (n := 12) (fun i hi => ?_) (by rw [hbs]; exact k.2) (by rw [hbs]; exact l.2)
      (fun h => hkl (Fin.ext h))
    obtain ⟨h1, h2⟩ := hbox i (by rw [← hbs]; exact hi)
    exact kc_len h1 h2
  · obtain ⟨h1, h2⟩ := hbox k.1 k.2
    obtain ⟨b, hb, -, -, hz, hx⟩ := kc_box_sound h1
    rw [h2, Option.some.injEq] at hb
    subst hb
    exact ⟨hz, hx⟩

end Lean6.Special.D88.Boxes
