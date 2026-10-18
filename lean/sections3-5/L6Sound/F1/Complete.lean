import L6Sound.F1.Basic

/-!
# Completeness of the search

* `mem_edgesUpTo`: an edge code satisfying (E2), (E3), (E6) passes every check of the edge stage, so its residues
  modulo `4 ^ j` are listed at every position `j`; `mem_edgeLeaves`: it is a leaf.
* `mem_candsUpTo`: a circle mask satisfying (C1) is among the candidates.
* `mem_search`: **every labelled diagram on `n` bodies satisfying `okRules` is listed by `search n`.**

The checks of the search are instances of the rules themselves (`e2At`, `e3At`, `e6At` at single triangles and
4-cycles, and `ruleE1`, …, `ruleC4`), so no table or auxiliary encoding of the rules is involved.
-/

namespace L6F1

/-! ## The edge stage -/

theorem e2At_of {n e a b c : ℕ} (h2 : ruleE2 n e = true) (ha : a < n) (hb : b < n) (hc : c < n) (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) : e2At e a b c = true := by
  simp only [ruleE2, decide_eq_true_eq] at h2
  unfold e2At
  cases hx : isZW e a b
  · simp
  · cases hy : isZW e b c
    · simp
    · simp [h2 a ha b hb hab hx c hc (Ne.symm hac) (Ne.symm hbc) hy]

theorem e3At_of {n e a b c : ℕ} (h3 : ruleE3 n e = true) (ha : a < n) (hb : b < n) (hc : c < n) (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) : e3At e a b c = true := by
  simp only [ruleE3, decide_eq_true_eq] at h3
  unfold e3At
  cases hx : isEdge e a b <;> cases hy : isEdge e b c <;> cases hz : isEdge e a c <;> simp
  obtain ⟨h1, h2⟩ := h3 a ha b hb hab hx c hc (Ne.symm hac) (Ne.symm hbc) hy hz
  exact ⟨h1, h2⟩

theorem e6At_of {n e a b c d : ℕ} (h6 : ruleE6 n e = true) (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    e6At e a b c d = true := by
  simp only [ruleE6, decide_eq_true_eq] at h6
  unfold e6At
  cases hx : isEdge e a b <;> cases hy : isEdge e b c <;> cases hz : isEdge e c d <;> cases hw : isEdge e d a <;>
    simp
  obtain ⟨h1, h2⟩ := h6 a ha b hb hab hx c hc (Ne.symm hac) (Ne.symm hbc) hy d hd (Ne.symm had) (Ne.symm hbd)
    (Ne.symm hcd) hz hw
  exact ⟨h1, h2⟩

theorem mem_trianglesAt {n j a b c : ℕ} (h : (a, b, c) ∈ trianglesAt n j) :
    a < b ∧ b < c ∧ c < n ∧ ppos a b ≤ j ∧ ppos a c ≤ j ∧ ppos b c ≤ j := by
  unfold trianglesAt at h
  simp only [List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range, beq_iff_eq, Prod.mk.injEq] at h
  obtain ⟨⟨c', hc', b', hb', a', ha', h1, h2, h3⟩, hm⟩ := h
  subst h1 h2 h3
  omega

theorem mem_cyclesAt {n j a b c d : ℕ} (h : (a, b, c, d) ∈ cyclesAt n j) :
    a < n ∧ b < n ∧ c < n ∧ d < n ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ppos a b ≤ j ∧ ppos b c ≤ j ∧ ppos c d ≤ j ∧ ppos d a ≤ j := by
  unfold cyclesAt at h
  simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false,
    beq_iff_eq, Prod.mk.injEq] at h
  obtain ⟨⟨d', hd', c', hc', b', hb', a', ha', h⟩, hm⟩ := h
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> subst h1 h2 h3 h4 <;> omega

/-- An edge code satisfying (E2), (E3), (E6) passes the checks of the position `j` on its residue modulo
`4 ^ (j + 1)`. -/
theorem stageOK_of {n e j : ℕ} (h2 : ruleE2 n e = true) (h3 : ruleE3 n e = true) (h6 : ruleE6 n e = true) :
    stageOK (trianglesAt n j) (cyclesAt n j) (e % 4 ^ (j + 1)) = true := by
  unfold stageOK
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun t ht => ?_, fun q hq => ?_⟩
  · obtain ⟨a, b, c⟩ := t
    obtain ⟨hab, hbc, hc, h1, h2', h3'⟩ := mem_trianglesAt ht
    have k1 := kind_mod (e := e) (show ppos a b < j + 1 by omega)
    have k2 := kind_mod (e := e) (show ppos b a < j + 1 by rw [ppos_comm]; omega)
    have k3 := kind_mod (e := e) (show ppos b c < j + 1 by omega)
    have k4 := kind_mod (e := e) (show ppos a c < j + 1 by omega)
    have k5 := kind_mod (e := e) (show ppos c b < j + 1 by rw [ppos_comm]; omega)
    have k6 := kind_mod (e := e) (show ppos c a < j + 1 by rw [ppos_comm]; omega)
    have ha : a < n := by omega
    have hb : b < n := by omega
    have t1 := e2At_of h2 ha hb hc (by omega) (by omega) (by omega)
    have t2 := e2At_of h2 hb ha hc (by omega) (by omega) (by omega)
    have t3 := e2At_of h2 ha hc hb (by omega) (by omega) (by omega)
    have t4 := e3At_of h3 ha hb hc (by omega) (by omega) (by omega)
    simp only [triOK, e2At, e3At, isZW, isEdge] at t1 t2 t3 t4 ⊢
    rw [k1, k2, k3, k4, k5]
    simp only [t1, t2, t3, t4, Bool.and_self]
  · obtain ⟨a, b, c, d⟩ := q
    obtain ⟨ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd, h1, h2', h3', h4⟩ := mem_cyclesAt hq
    have k1 := kind_mod (e := e) (show ppos a b < j + 1 by omega)
    have k2 := kind_mod (e := e) (show ppos b c < j + 1 by omega)
    have k3 := kind_mod (e := e) (show ppos c d < j + 1 by omega)
    have k4 := kind_mod (e := e) (show ppos d a < j + 1 by omega)
    have t := e6At_of h6 ha hb hc hd hab hac had hbc hbd hcd
    simp only [e6At, isEdge] at t ⊢
    rw [k1, k2, k3, k4]
    exact t

theorem mem_four {v : ℕ} (h : v < 4) : v ∈ [0, 1, 2, 3] := by
  interval_cases v <;> simp

/-- **The edge stage lists every edge code satisfying (E2), (E3), (E6)**, by its residues modulo `4 ^ j`. -/
theorem mem_edgesUpTo {n e : ℕ} (h2 : ruleE2 n e = true) (h3 : ruleE3 n e = true) (h6 : ruleE6 n e = true) :
    ∀ j, e % 4 ^ j ∈ edgesUpTo n j := by
  intro j
  induction j with
  | zero => simp [edgesUpTo, Nat.mod_one]
  | succ j ih =>
    show e % 4 ^ (j + 1) ∈ extendAt n j (edgesUpTo n j)
    unfold extendAt
    simp only [List.mem_flatMap, List.mem_filter, List.mem_map]
    exact ⟨e % 4 ^ j, ih, ⟨digit e j, mem_four (digit_lt e j), (mod_four_pow_succ e j).symm⟩,
      stageOK_of h2 h3 h6⟩

theorem mem_edgeLeaves {n e : ℕ} (he : e < 4 ^ numPairs n) (h2 : ruleE2 n e = true) (h3 : ruleE3 n e = true)
    (h6 : ruleE6 n e = true) : e ∈ edgeLeaves n := by
  have := mem_edgesUpTo h2 h3 h6 (numPairs n)
  rwa [Nat.mod_eq_of_lt he] at this

/-! ## The circles -/

theorem bit_val (c k : ℕ) : c / 2 ^ k % 2 = if circled c k = true then 1 else 0 := by
  simp only [circled, bit, beq_iff_eq]
  have := Nat.mod_lt (c / 2 ^ k) (show 2 > 0 by norm_num)
  split_ifs with h
  · exact h
  · omega

theorem mod_two_pow_succ (c k : ℕ) : c % 2 ^ (k + 1) = c % 2 ^ k + (c / 2 ^ k % 2) * 2 ^ k := by
  rw [Nat.mod_pow_succ]
  ring

/-- **The candidates of the circles contain every mask satisfying (C1).** -/
theorem mem_candsUpTo {n e c : ℕ}
    (h1 : ∀ k < n, (zDeg n e k = 0 → circled c k = false) ∧ (zDeg n e k = 1 → circled c k = true)) :
    ∀ k ≤ n, c % 2 ^ k ∈ candsUpTo n e k := by
  intro k hk
  induction k with
  | zero => simp [candsUpTo, Nat.mod_one]
  | succ k ih =>
    show c % 2 ^ (k + 1) ∈ (candsUpTo n e k).flatMap fun c' => (choices n e k).map fun v => c' + v * 2 ^ k
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨c % 2 ^ k, ih (by omega), c / 2 ^ k % 2, ?_, (mod_two_pow_succ c k).symm⟩
    obtain ⟨hz, ho⟩ := h1 k (by omega)
    rw [bit_val]
    unfold choices
    split_ifs with g1 g2 g3 g4 <;> simp_all

theorem mem_circles {n e c : ℕ} (hc : c < 2 ^ n) (h1 : ruleC1 n e c = true) (h2 : ruleC2 n e c = true)
    (h3 : ruleC3 n e c = true) (h4 : ruleC4 n e c = true) : c ∈ circles n e := by
  unfold circles
  rw [List.mem_filter]
  refine ⟨?_, by simp [circleOK, h1, h2, h3, h4]⟩
  have H1 := h1
  simp only [ruleC1, decide_eq_true_eq] at H1
  have := mem_candsUpTo H1 n le_rfl
  rwa [Nat.mod_eq_of_lt hc] at this

/-! ## The search -/

/-- The ten rules of one colour. -/
theorem rulesZ_iff {n e c : ℕ} : rulesZ n e c = true ↔
    ruleE1 n e = true ∧ ruleE2 n e = true ∧ ruleE3 n e = true ∧ ruleE4 n e = true ∧ ruleE5 n e = true ∧
      ruleE6 n e = true ∧ ruleC1 n e c = true ∧ ruleC2 n e c = true ∧ ruleC3 n e c = true ∧
      ruleC4 n e c = true := by
  simp only [rulesZ, Bool.and_eq_true]
  tauto

/-- **Every labelled diagram on `n` bodies satisfying the rules in both colours is listed by the search.** -/
theorem mem_search {n : ℕ} {d : Diagram} (hr : inRange n d = true) (h : okRules n d = true) : d ∈ search n := by
  obtain ⟨e, zc, wc⟩ := d
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨he, hz⟩, hw⟩ := hr
  simp only [okRules, Bool.and_eq_true] at h
  obtain ⟨hZ, hW⟩ := h
  obtain ⟨z1, z2, z3, z4, z5, z6, zc1, zc2, zc3, zc4⟩ := rulesZ_iff.mp hZ
  obtain ⟨w1, -, -, w4, w5, -, wc1, wc2, wc3, wc4⟩ := rulesZ_iff.mp hW
  unfold search searchFrom
  rw [List.mem_flatMap]
  refine ⟨e, mem_edgeLeaves he z2 z3 z6, ?_⟩
  unfold diagramsAt
  simp only
  rw [ite_eq_left (by simp [edgeColourOK, z1, z4, z5]), ite_eq_left (by simp [edgeColourOK, w1, w4, w5]), List.mem_flatMap]
  refine ⟨zc, mem_circles hz zc1 zc2 zc3 zc4, ?_⟩
  rw [List.mem_map]
  exact ⟨wc, mem_circles hw wc1 wc2 wc3 wc4, rfl⟩

end L6F1
