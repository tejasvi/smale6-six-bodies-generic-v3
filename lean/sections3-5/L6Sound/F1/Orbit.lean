import L6Sound.F1.Basic

/-!
# Relabelling, the exchange of the colours, orbits and the canonical key

For `n ≤ 6` bodies:

* `kind_relabel`, `circled_relabel_zc`, `circled_relabel_wc`, `kind_swapE`: the kinds and circles of the relabelled
  and of the colour-exchanged diagram;
* `diagram_ext`: a labelled diagram is determined by its kinds and circles;
* `actP n σ s`: the symmetry given by a permutation `σ` of the bodies and the exchange of the colours if `s`;
  `actP_actP`: these maps compose like the group `S_n × ℤ/2`;
* `orbit n d`: the set of the images of `d` under the `2 · n!` symmetries; `orbit_actP`, `orbit_eq_of_mem`: the orbit
  of an element of the orbit of `d` is the orbit of `d`.
-/

namespace L6F1

/-! ## Digit values -/

theorem digitsVal_succ (base : ℕ) (g : ℕ → ℕ) (m : ℕ) :
    digitsVal base g (m + 1) = digitsVal base g m + g m * base ^ m := rfl

theorem digitsVal_lt {base m : ℕ} {g : ℕ → ℕ} (hg : ∀ i < m, g i < base) : digitsVal base g m < base ^ m := by
  induction m with
  | zero => simp [digitsVal]
  | succ m ih =>
    rw [digitsVal_succ, pow_succ]
    have h1 := ih (fun i hi => hg i (by omega))
    have h2 := hg m (by omega)
    have h3 : (g m + 1) * base ^ m ≤ base * base ^ m := Nat.mul_le_mul_right _ h2
    nlinarith

theorem digitsVal_digit {base m : ℕ} (hb : 0 < base) {g : ℕ → ℕ} (hg : ∀ i < m, g i < base) :
    ∀ j < m, digitsVal base g m / base ^ j % base = g j := by
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    intro j hj
    have hD := digitsVal_lt (base := base) (m := m) (g := g) (fun i hi => hg i (by omega))
    rw [digitsVal_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hj
      have e : g m * base ^ m = (g m * base ^ (k + 1)) * base ^ j := by rw [hk, mul_assoc, ← pow_add]; ring_nf
      rw [e, Nat.add_mul_div_right _ _ (pow_pos hb j)]
      have e2 : g m * base ^ (k + 1) = base * (g m * base ^ k) := by ring
      rw [e2, Nat.add_mul_mod_self_left]
      exact ih (fun i hi => hg i (by omega)) j hj
    · subst hj
      rw [Nat.add_mul_div_right _ _ (pow_pos hb j), Nat.div_eq_of_lt hD, zero_add,
        Nat.mod_eq_of_lt (hg j (by omega))]

theorem digitsVal_congr {base m : ℕ} {f g : ℕ → ℕ} (h : ∀ i < m, f i = g i) :
    digitsVal base f m = digitsVal base g m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [digitsVal_succ, digitsVal_succ, ih (fun i hi => h i (by omega)), h m (by omega)]

/-- Two numbers below `base ^ m` with the same digits below `m` are equal. -/
theorem eq_of_digits {base m e e' : ℕ} (he : e < base ^ m) (he' : e' < base ^ m)
    (h : ∀ i < m, e / base ^ i % base = e' / base ^ i % base) : e = e' := by
  have key : ∀ j ≤ m, e % base ^ j = e' % base ^ j := by
    intro j hj
    induction j with
    | zero => simp [Nat.mod_one]
    | succ j ih => rw [Nat.mod_pow_succ, Nat.mod_pow_succ, ih (by omega), h j (by omega)]
  have := key m le_rfl
  rwa [Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt he'] at this

/-! ## Positions for at most six bodies -/

theorem pairAt_pos : ∀ a < 6, ∀ b < 6, a < b → pairAt (pos a b) = (a, b) := by decide

theorem pos_lt_numPairs : ∀ n ≤ 6, ∀ a < 6, ∀ b < 6, a < b → b < n → pos a b < numPairs n := by decide

theorem pairAt_spec : ∀ n ≤ 6, ∀ i < numPairs n,
    (pairAt i).1 < (pairAt i).2 ∧ (pairAt i).2 < n ∧ pos (pairAt i).1 (pairAt i).2 = i := by decide

/-! ## Kinds and circles of codes -/

theorem kind_codeOf {n : ℕ} (hn : n ≤ 6) {f : ℕ → ℕ → ℕ} (hf : ∀ x y, f x y < 4) (hs : ∀ x y, f x y = f y x)
    (h0 : ∀ x, f x x = 0) {x y : ℕ} (hx : x < n) (hy : y < n) : kind (codeOf n f) x y = f x y := by
  have main : ∀ a b, a < b → b < n → kind (codeOf n f) a b = f a b := by
    intro a b hab hb
    have hp := pos_lt_numPairs n hn a (by omega) b (by omega) hab hb
    unfold kind
    rw [ite_eq_right (Nat.ne_of_lt hab), ppos, ite_eq_left hab]
    unfold codeOf digit
    rw [digitsVal_digit (by norm_num) (fun i _ => hf _ _) _ hp, pairAt_pos a (by omega) b (by omega) hab]
  rcases lt_trichotomy x y with h | rfl | h
  · exact main x y h hy
  · rw [kind_self, h0]
  · rw [kind_comm, hs]
    exact main y x h hx

theorem codeOf_lt {n : ℕ} {f : ℕ → ℕ → ℕ} (hf : ∀ x y, f x y < 4) : codeOf n f < 4 ^ numPairs n :=
  digitsVal_lt fun _ _ => hf _ _

theorem maskOf_lt {n : ℕ} (f : ℕ → Bool) : maskOf n f < 2 ^ n :=
  digitsVal_lt fun _ _ => by split_ifs <;> norm_num

theorem circled_maskOf {n k : ℕ} (f : ℕ → Bool) (hk : k < n) : circled (maskOf n f) k = f k := by
  unfold circled bit maskOf
  rw [digitsVal_digit (by norm_num) (fun _ _ => by split_ifs <;> norm_num) k hk]
  cases f k <;> simp

/-- The digit `i` of an edge code is the kind of the pair at the position `i`. -/
theorem digit_eq_kind {n : ℕ} (hn : n ≤ 6) {i : ℕ} (hi : i < numPairs n) (e : ℕ) :
    digit e i = kind e (pairAt i).1 (pairAt i).2 := by
  obtain ⟨h1, -, h3⟩ := pairAt_spec n hn i hi
  unfold kind
  rw [ite_eq_right (Nat.ne_of_lt h1), ppos, ite_eq_left h1, h3]

theorem circled_eq_iff (c c' k : ℕ) :
    circled c k = circled c' k ↔ c / 2 ^ k % 2 = c' / 2 ^ k % 2 := by
  have h1 := Nat.mod_lt (c / 2 ^ k) (show 2 > 0 by norm_num)
  have h2 := Nat.mod_lt (c' / 2 ^ k) (show 2 > 0 by norm_num)
  unfold circled bit
  constructor
  · intro h
    by_cases a : c / 2 ^ k % 2 = 1 <;> by_cases b : c' / 2 ^ k % 2 = 1
    · omega
    · simp [a, b] at h
    · simp [a, b] at h
    · omega
  · intro h
    rw [h]

/-- **A labelled diagram on `n ≤ 6` bodies is determined by its kinds and its circles.** -/
theorem diagram_ext {n : ℕ} (hn : n ≤ 6) {d d' : Diagram} (hd : inRange n d = true) (hd' : inRange n d' = true)
    (hk : ∀ a b, a < b → b < n → kind d.e a b = kind d'.e a b)
    (hz : ∀ k < n, circled d.zc k = circled d'.zc k) (hw : ∀ k < n, circled d.wc k = circled d'.wc k) :
    d = d' := by
  obtain ⟨e, zc, wc⟩ := d
  obtain ⟨e', zc', wc'⟩ := d'
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hd hd'
  simp only at hk hz hw
  have h1 : e = e' := by
    apply eq_of_digits hd.1.1 hd'.1.1
    intro i hi
    have := pairAt_spec n hn i hi
    have h := hk _ _ this.1 this.2.1
    rw [← digit_eq_kind hn hi, ← digit_eq_kind hn hi] at h
    exact h
  have h2 : zc = zc' := eq_of_digits hd.1.2 hd'.1.2 fun k hk' => (circled_eq_iff _ _ _).mp (hz k hk')
  have h3 : wc = wc' := eq_of_digits hd.2 hd'.2 fun k hk' => (circled_eq_iff _ _ _).mp (hw k hk')
  rw [h1, h2, h3]

/-! ## Relabelling and the exchange of the colours -/

theorem swapKind_lt {v : ℕ} (h : v < 4) : swapKind v < 4 := by unfold swapKind; split_ifs <;> omega

theorem swapKind_swapKind {v : ℕ} : swapKind (swapKind v) = v := by unfold swapKind; split_ifs <;> omega

theorem inRange_relabel (n : ℕ) (τ : ℕ → ℕ) (d : Diagram) : inRange n (d.relabel n τ) = true := by
  simp only [inRange, Diagram.relabel, Bool.and_eq_true]
  exact ⟨⟨decide_eq_true (codeOf_lt fun _ _ => kind_lt _ _ _), decide_eq_true (maskOf_lt _)⟩,
    decide_eq_true (maskOf_lt _)⟩

theorem inRange_swap {n : ℕ} {d : Diagram} (hd : inRange n d = true) : inRange n (d.swap n) = true := by
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hd
  simp only [inRange, Diagram.swap, swapE, Bool.and_eq_true]
  exact ⟨⟨decide_eq_true (codeOf_lt fun _ _ => swapKind_lt (kind_lt _ _ _)), decide_eq_true hd.2⟩,
    decide_eq_true hd.1.2⟩

theorem kind_relabel {n : ℕ} (hn : n ≤ 6) (τ : ℕ → ℕ) (d : Diagram) {x y : ℕ} (hx : x < n) (hy : y < n) :
    kind (d.relabel n τ).e x y = kind d.e (τ x) (τ y) :=
  kind_codeOf (f := fun a b => kind d.e (τ a) (τ b)) hn (fun _ _ => kind_lt _ _ _) (fun _ _ => kind_comm _ _ _)
    (fun _ => kind_self _ _) hx hy

theorem circled_relabel_zc {n : ℕ} (τ : ℕ → ℕ) (d : Diagram) {k : ℕ} (hk : k < n) :
    circled (d.relabel n τ).zc k = circled d.zc (τ k) := circled_maskOf _ hk

theorem circled_relabel_wc {n : ℕ} (τ : ℕ → ℕ) (d : Diagram) {k : ℕ} (hk : k < n) :
    circled (d.relabel n τ).wc k = circled d.wc (τ k) := circled_maskOf _ hk

theorem kind_swapE {n : ℕ} (hn : n ≤ 6) (e : ℕ) {x y : ℕ} (hx : x < n) (hy : y < n) :
    kind (swapE n e) x y = swapKind (kind e x y) :=
  kind_codeOf (f := fun a b => swapKind (kind e a b)) hn (fun _ _ => swapKind_lt (kind_lt _ _ _))
    (fun _ _ => by simp only [kind_comm e]) (fun _ => by simp [kind_self, swapKind]) hx hy

theorem relabel_congr {n : ℕ} {τ τ' : ℕ → ℕ} (h : ∀ k < n, τ k = τ' k) (hn : n ≤ 6) (d : Diagram) :
    d.relabel n τ = d.relabel n τ' := by
  unfold Diagram.relabel codeOf maskOf
  congr 1
  · apply digitsVal_congr
    intro i hi
    obtain ⟨h1, h2, -⟩ := pairAt_spec n hn i hi
    beta_reduce
    rw [h _ (by omega), h _ h2]
  · exact digitsVal_congr fun k hk => by beta_reduce; rw [h k hk]
  · exact digitsVal_congr fun k hk => by beta_reduce; rw [h k hk]

theorem relabel_relabel {n : ℕ} (hn : n ≤ 6) {τ₁ : ℕ → ℕ} (hτ : ∀ k < n, τ₁ k < n) (τ₂ : ℕ → ℕ) (d : Diagram) :
    (d.relabel n τ₂).relabel n τ₁ = d.relabel n (fun k => τ₂ (τ₁ k)) := by
  apply diagram_ext hn (inRange_relabel _ _ _) (inRange_relabel _ _ _)
  · intro a b hab hb
    rw [kind_relabel hn _ _ (by omega) hb, kind_relabel hn _ _ (hτ a (by omega)) (hτ b hb),
      kind_relabel hn _ _ (by omega) hb]
  · intro k hk
    rw [circled_relabel_zc _ _ hk, circled_relabel_zc _ _ (hτ k hk), circled_relabel_zc _ _ hk]
  · intro k hk
    rw [circled_relabel_wc _ _ hk, circled_relabel_wc _ _ (hτ k hk), circled_relabel_wc _ _ hk]

theorem swap_relabel {n : ℕ} (hn : n ≤ 6) {τ : ℕ → ℕ} (hτ : ∀ k < n, τ k < n) (d : Diagram) :
    (d.relabel n τ).swap n = (d.swap n).relabel n τ := by
  apply diagram_ext hn (inRange_swap (inRange_relabel _ _ _)) (inRange_relabel _ _ _)
  · intro a b hab hb
    simp only [Diagram.swap]
    rw [kind_swapE hn _ (by omega) hb, kind_relabel hn _ _ (by omega) hb, kind_relabel hn _ _ (by omega) hb,
      kind_swapE hn _ (hτ a (by omega)) (hτ b hb)]
  · intro k hk
    simp only [Diagram.swap]
    rw [circled_relabel_wc _ _ hk, circled_relabel_zc _ _ hk]
  · intro k hk
    simp only [Diagram.swap]
    rw [circled_relabel_zc _ _ hk, circled_relabel_wc _ _ hk]

theorem swap_swap {n : ℕ} (hn : n ≤ 6) {d : Diagram} (hd : inRange n d = true) : (d.swap n).swap n = d := by
  apply diagram_ext hn (inRange_swap (inRange_swap hd)) hd
  · intro a b hab hb
    simp only [Diagram.swap]
    rw [kind_swapE hn _ (by omega) hb, kind_swapE hn _ (by omega) hb, swapKind_swapKind]
  · intro k _; rfl
  · intro k _; rfl

/-! ## Symmetries and orbits -/

/-- The inverse of the permutation `σ` of the bodies `0, …, n - 1`, extended by the identity. -/
def invMap {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : ℕ := if h : k < n then (σ.symm ⟨k, h⟩ : ℕ) else k

theorem invMap_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k < n) : invMap σ k < n := by
  simp [invMap, hk]

theorem invMap_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k < n) :
    invMap (σ * τ) k = invMap τ (invMap σ k) := by
  simp [invMap, hk, Equiv.Perm.mul_def]

/-- **The symmetry `(σ, s)`**: the relabelling of the bodies by `σ` (the body `k` becomes `σ k`), followed by the
exchange of the colours if `s`. -/
def actP (n : ℕ) (σ : Equiv.Perm (Fin n)) (s : Bool) (d : Diagram) : Diagram :=
  let d' := d.relabel n (invMap σ)
  if s then d'.swap n else d'

/-- **The orbit of `d`** under the relabellings and the exchange of the colours. -/
def orbit (n : ℕ) (d : Diagram) : Set Diagram := {d' | ∃ σ : Equiv.Perm (Fin n), ∃ s : Bool, d' = actP n σ s d}

theorem inRange_actP {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Bool) (d : Diagram) : inRange n (actP n σ s d) = true := by
  unfold actP
  cases s
  · exact inRange_relabel _ _ _
  · exact inRange_swap (inRange_relabel _ _ _)

theorem invMap_one {n : ℕ} (k : ℕ) : invMap (1 : Equiv.Perm (Fin n)) k = k := by
  unfold invMap
  split_ifs <;> rfl

theorem actP_one {n : ℕ} (hn : n ≤ 6) {d : Diagram} (hd : inRange n d = true) : actP n 1 false d = d := by
  simp only [actP, Bool.false_eq_true, ite_false]
  apply diagram_ext hn (inRange_relabel _ _ _) hd
  · intro a b hab hb
    rw [kind_relabel hn _ _ (by omega) hb, invMap_one, invMap_one]
  · intro k hk
    rw [circled_relabel_zc _ _ hk, invMap_one]
  · intro k hk
    rw [circled_relabel_wc _ _ hk, invMap_one]

/-- **The symmetries compose like `S_n × ℤ/2`.** -/
theorem actP_actP {n : ℕ} (hn : n ≤ 6) (d : Diagram) (σ τ : Equiv.Perm (Fin n))
    (s t : Bool) : actP n σ s (actP n τ t d) = actP n (σ * τ) (xor s t) d := by
  have hσ : ∀ k < n, invMap σ k < n := fun k hk => invMap_lt σ hk
  have hcomp : d.relabel n (fun k => invMap τ (invMap σ k)) = d.relabel n (invMap (σ * τ)) :=
    relabel_congr (fun k hk => (invMap_mul σ τ hk).symm) hn d
  have hr : (d.relabel n (invMap τ)).relabel n (invMap σ) = d.relabel n (invMap (σ * τ)) := by
    rw [relabel_relabel hn hσ, hcomp]
  have hR := inRange_relabel n (invMap (σ * τ)) d
  simp only [actP]
  cases s <;> cases t <;> simp only [Bool.false_eq_true, ite_false, ite_true, eq_self, Bool.xor_false,
    Bool.xor_true, Bool.not_false, Bool.not_true]
  · exact hr
  · rw [← swap_relabel hn hσ, hr]
  · rw [hr]
  · rw [← swap_relabel hn hσ, hr, swap_swap hn hR]

theorem self_mem_orbit {n : ℕ} (hn : n ≤ 6) {d : Diagram} (hd : inRange n d = true) : d ∈ orbit n d :=
  ⟨1, false, (actP_one hn hd).symm⟩

theorem inRange_of_mem_orbit {n : ℕ} {d d' : Diagram} (h : d' ∈ orbit n d) : inRange n d' = true := by
  obtain ⟨σ, s, rfl⟩ := h
  exact inRange_actP σ s d

/-- **The orbit of an image of `d` is the orbit of `d`.** -/
theorem orbit_actP {n : ℕ} (hn : n ≤ 6) (d : Diagram) (σ : Equiv.Perm (Fin n)) (s : Bool) :
    orbit n (actP n σ s d) = orbit n d := by
  ext x
  constructor
  · rintro ⟨τ, t, rfl⟩
    exact ⟨τ * σ, xor t s, actP_actP hn d τ σ t s⟩
  · rintro ⟨τ, t, rfl⟩
    refine ⟨τ * σ⁻¹, xor t s, ?_⟩
    rw [actP_actP hn, mul_assoc, inv_mul_cancel, mul_one, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

theorem orbit_eq_of_mem {n : ℕ} (hn : n ≤ 6) {d d' : Diagram} (h : d' ∈ orbit n d) : orbit n d' = orbit n d := by
  obtain ⟨σ, s, rfl⟩ := h
  exact orbit_actP hn d σ s

end L6F1
