import CC6Full.Germ.Basic

/-!
# The orders at a singular place (Lemma 2.8, `lem:orders`)

For a germ (any masses) and a pair `k ≠ l` of bodies, with `ζ = ζ_kl`, `ω = ω_kl` and `x = x_kl`:

* `Germ.orderTop_termZ_z`, `Germ.orderTop_termZ_w`: `e(Z_kl) = −(ζ + 3ω)/2` and `e(W_kl) = −(3ζ + ω)/2`;
* `Germ.min_le_zeta`, `Germ.zeta_eq_min` (and `Germ.min_le_omega`, `Germ.omega_eq_min`): `ζ_kl ≥ min(a_k, a_l)`,
  with equality if `a_k ≠ a_l` (as elements of `WithTop ℚ`; `a_k = e(z_k)` is `⊤` if `z_k = 0`);
* `Germ.O1`, `Germ.O1_le`, `Germ.O2`, `Germ.O3_z`, `Germ.O3_w`, `Germ.O4`, `Germ.O5_z`, `Germ.O5_w`, `Germ.O6_z`,
  `Germ.O6_z'`, `Germ.O6_w`, `Germ.O6_w'`: (O1)–(O6) of Lemma 2.8, for `z` and for `w`.

The arguments are written once for a *colour pair* `Colour.Pair m p h h'`: the hypotheses of a germ seen from the
colour `h`, the other colour being `h'`. A germ `G` gives the colour pairs `G.colZ` (`h = z`, `h' = w`) and
`G.colW` (`h = w`, `h' = z`), and a statement about the colour `w` is the statement about `z` for `G.colW`. For a
colour `h`, `Colour.ord h k l = e(h_k − h_l)`, `Colour.Stroke p h k l` and `Colour.Circle h k` are `ζ_kl`, the
`z`-strokes and the `z`-circles for `h = z`, and `ω_kl`, the `w`-strokes and the `w`-circles for `h = w`
(definitionally).
-/

namespace CC6Full

open Finset

noncomputable section

namespace Colour

variable {n : ℕ}

/-- The exponent `e(h_k − h_l)` of a difference in the colour `h` (junk `0` on the diagonal): `ζ_kl` for `h = z`,
`ω_kl` for `h = w`. -/
def ord (h : Fin n → Ser) (k l : Fin n) : ℚ := (h k - h l).order

/-- `kl` is a stroke of the colour `h`: `e(p_kl³ (h_k − h_l)) = −2`. -/
def Stroke (p : Fin n → Fin n → Ser) (h : Fin n → Ser) (k l : Fin n) : Prop :=
  k ≠ l ∧ (termZ p h k l).orderTop = ((-2 : ℚ) : WithTop ℚ)

/-- Body `k` is circled in the colour `h`: `e(h_k) = −2`. -/
def Circle (h : Fin n → Ser) (k : Fin n) : Prop := (h k).orderTop = ((-2 : ℚ) : WithTop ℚ)

/-- A *colour pair*: the hypotheses of a germ for the masses `m` seen from the colour `h`, the other colour being
`h'` (the equations of the bodies, the distance equations and Lemma 2.5 for both colours). It is symmetric under
the exchange of `h` and `h'` (`Pair.symm`). -/
structure Pair (m : Fin n → ℝ) (p : Fin n → Fin n → Ser) (h h' : Fin n → Ser) : Prop where
  p_symm : ∀ k l, p k l = p l k
  body : ∀ k, h k = ∑ l ∈ univ.erase k, cS (m l) * termZ p h k l
  body' : ∀ k, h' k = ∑ l ∈ univ.erase k, cS (m l) * termZ p h' k l
  dist : ∀ k l, k ≠ l → p k l ^ 2 * (h k - h l) * (h' k - h' l) = 1
  low : LowAt p h
  low' : LowAt p h'

theorem ord_comm (h : Fin n → Ser) (k l : Fin n) : ord h k l = ord h l k := by
  unfold ord
  rw [← neg_sub, HahnSeries.order_neg]

/-! ## Three or four rational numbers -/

/-- If each of three numbers is at least the minimum of the other two, the minimum is attained twice. -/
theorem min_twice {a b c : ℚ} (ha : min b c ≤ a) (hb : min c a ≤ b) (hc : min a b ≤ c) :
    (a = b ∧ a ≤ c) ∨ (b = c ∧ b ≤ a) ∨ (c = a ∧ c ≤ b) := by
  rcases min_le_iff.mp ha with h1 | h1 <;> rcases min_le_iff.mp hb with h2 | h2 <;>
    rcases min_le_iff.mp hc with h3 | h3 <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

namespace Pair

variable {m : Fin n → ℝ} {p : Fin n → Fin n → Ser} {h h' : Fin n → Ser}

/-- The exchange of the two colours. -/
theorem symm (H : Pair m p h h') : Pair m p h' h where
  p_symm := H.p_symm
  body := H.body'
  body' := H.body
  dist k l hkl := by rw [mul_right_comm]; exact H.dist k l hkl
  low := H.low'
  low' := H.low

theorem diff_ne_zero (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) : h k - h l ≠ 0 := by
  intro h0
  have := H.dist k l hkl
  rw [h0, mul_zero, zero_mul] at this
  exact zero_ne_one this

theorem p_ne_zero (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) : p k l ≠ 0 := by
  intro h0
  have := H.dist k l hkl
  rw [h0] at this
  simp at this

theorem orderTop_diff (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) :
    (h k - h l).orderTop = (ord h k l : WithTop ℚ) :=
  (HahnSeries.order_eq_orderTop_of_ne_zero (H.diff_ne_zero hkl)).symm

theorem orderTop_p (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) :
    (p k l).orderTop = ((p k l).order : WithTop ℚ) :=
  (HahnSeries.order_eq_orderTop_of_ne_zero (H.p_ne_zero hkl)).symm

/-- `2 e(p_kl) + e(h_kl) + e(h'_kl) = 0`, from the distance equation. -/
theorem order_p (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) :
    2 * (p k l).order + ord h k l + ord h' k l = 0 := by
  have hd := congrArg HahnSeries.orderTop (H.dist k l hkl)
  rw [HahnSeries.orderTop_one, HahnSeries.orderTop_mul, HahnSeries.orderTop_mul, pow_two,
    HahnSeries.orderTop_mul, H.orderTop_diff hkl, H.symm.orderTop_diff hkl, H.orderTop_p hkl] at hd
  have h2 : (p k l).order + (p k l).order + ord h k l + ord h' k l = 0 := by exact_mod_cast hd
  linarith

/-- `e(p_kl³ h_kl) = −(e(h_kl) + 3 e(h'_kl))/2`. -/
theorem orderTop_termZ (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) :
    (termZ p h k l).orderTop = ((-(ord h k l + 3 * ord h' k l) / 2 : ℚ) : WithTop ℚ) := by
  have e := H.order_p hkl
  have e2 : (p k l).order + (p k l).order + (p k l).order + ord h k l =
      -(ord h k l + 3 * ord h' k l) / 2 := by linarith
  rw [termZ, HahnSeries.orderTop_mul, pow_three', HahnSeries.orderTop_mul, HahnSeries.orderTop_mul,
    H.orderTop_p hkl, H.orderTop_diff hkl, ← e2]
  norm_cast

theorem termZ_swap (H : Pair m p h h') (k l : Fin n) : termZ p h l k = -termZ p h k l := by
  unfold termZ
  rw [H.p_symm l k]
  ring

theorem stroke_comm (H : Pair m p h h') {k l : Fin n} : Stroke p h k l ↔ Stroke p h l k := by
  unfold Stroke
  rw [H.termZ_swap k l, HahnSeries.orderTop_neg, ne_comm]

theorem low_ord (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) : -2 ≤ ord h k l := by
  have h1 : ((-2 : ℚ) : WithTop ℚ) ≤ (h k - h l).orderTop :=
    le_trans (le_min (H.low.1 k) (H.low.1 l)) HahnSeries.min_orderTop_le_orderTop_sub
  rw [H.orderTop_diff hkl] at h1
  exact_mod_cast h1

/-- (O1) for a colour pair. -/
theorem bounds (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) :
    -2 ≤ ord h k l ∧ -2 ≤ ord h' k l ∧ ord h k l + 3 * ord h' k l ≤ 4 ∧
      3 * ord h k l + ord h' k l ≤ 4 := by
  have hz := H.low.2.1 k l hkl
  have hw := H.low'.2.1 k l hkl
  rw [H.orderTop_termZ hkl] at hz
  rw [H.symm.orderTop_termZ hkl] at hw
  have hz' : (-2 : ℚ) ≤ -(ord h k l + 3 * ord h' k l) / 2 := by exact_mod_cast hz
  have hw' : (-2 : ℚ) ≤ -(ord h' k l + 3 * ord h k l) / 2 := by exact_mod_cast hw
  exact ⟨H.low_ord hkl, H.symm.low_ord hkl, by linarith, by linarith⟩

/-- (O2) for a colour pair, colour `h`. -/
theorem stroke_iff (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) :
    Stroke p h k l ↔ ord h k l + 3 * ord h' k l = 4 := by
  unfold Stroke
  rw [H.orderTop_termZ hkl, WithTop.coe_inj]
  constructor
  · rintro ⟨-, e⟩
    linarith
  · intro e
    exact ⟨hkl, by linarith⟩

/-- (O2) for a colour pair, colour `h'`. -/
theorem stroke_iff' (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) :
    Stroke p h' k l ↔ 3 * ord h k l + ord h' k l = 4 := by
  rw [H.symm.stroke_iff hkl]
  constructor <;> intro e <;> linarith

theorem min_le_ord (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l) :
    min (h k).orderTop (h l).orderTop ≤ (ord h k l : WithTop ℚ) := by
  rw [← H.orderTop_diff hkl]
  exact HahnSeries.min_orderTop_le_orderTop_sub

theorem ord_eq_min (H : Pair m p h h') {k l : Fin n} (hkl : k ≠ l)
    (hne : (h k).orderTop ≠ (h l).orderTop) :
    (ord h k l : WithTop ℚ) = min (h k).orderTop (h l).orderTop := by
  rw [← H.orderTop_diff hkl]
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rw [HahnSeries.orderTop_sub hlt, min_eq_left hlt.le]
  · rw [← neg_sub, HahnSeries.orderTop_neg, HahnSeries.orderTop_sub hlt, min_eq_right hlt.le]

/-- The ultrametric inequality on a triangle (O5). -/
theorem ultra (H : Pair m p h h') {k l j : Fin n} (hkl : k ≠ l) (hlj : l ≠ j) (hkj : k ≠ j) :
    min (ord h k l) (ord h l j) ≤ ord h k j := by
  have h1 := HahnSeries.min_orderTop_le_orderTop_add (x := h k - h l) (y := h l - h j)
  rw [sub_add_sub_cancel, H.orderTop_diff hkl, H.orderTop_diff hlj, H.orderTop_diff hkj,
    ← WithTop.coe_min] at h1
  exact_mod_cast h1

theorem ultra' (H : Pair m p h h') {k l j : Fin n} (hkl : k ≠ l) (hlj : l ≠ j) (hkj : k ≠ j) :
    min (ord h k l) (ord h l j) ≤ ord h j k := by
  rw [ord_comm h j k]
  exact H.ultra hkl hlj hkj

/-- The ultrametric inequality on a 4-cycle. -/
theorem ultra4 (H : Pair m p h h') {k l j i : Fin n} (hkl : k ≠ l) (hlj : l ≠ j) (hji : j ≠ i)
    (hki : k ≠ i) : min (ord h k l) (min (ord h l j) (ord h j i)) ≤ ord h k i := by
  have h1 := HahnSeries.min_orderTop_le_orderTop_add (x := h k - h l) (y := h l - h i)
  have h2 := HahnSeries.min_orderTop_le_orderTop_add (x := h l - h j) (y := h j - h i)
  rw [sub_add_sub_cancel, H.orderTop_diff hkl, H.orderTop_diff hki] at h1
  rw [sub_add_sub_cancel, H.orderTop_diff hlj, H.orderTop_diff hji] at h2
  have h3 := le_trans (min_le_min_left _ h2) h1
  rw [← WithTop.coe_min, ← WithTop.coe_min] at h3
  exact_mod_cast h3

theorem ultra4' (H : Pair m p h h') {k l j i : Fin n} (hkl : k ≠ l) (hlj : l ≠ j) (hji : j ≠ i)
    (hki : k ≠ i) : min (ord h k l) (min (ord h l j) (ord h j i)) ≤ ord h i k := by
  rw [ord_comm h i k]
  exact H.ultra4 hkl hlj hji hki

/-- (O6), first part, for a colour pair. -/
theorem ord_of_circle (H : Pair m p h h') {k l : Fin n} (hk : Circle h k) (hl : ¬ Circle h l) :
    ord h k l = -2 := by
  have hkl : k ≠ l := by
    rintro rfl
    exact hl hk
  have hlt : (h k).orderTop < (h l).orderTop := by
    rw [hk]
    exact lt_of_le_of_ne (H.low.1 l) (Ne.symm hl)
  have h1 := HahnSeries.orderTop_sub hlt
  rw [H.orderTop_diff hkl, hk] at h1
  exact_mod_cast h1

/-- (O6), second part, for a colour pair. -/
theorem ord_eq_two (H : Pair m p h h') {k l : Fin n} (h2 : ord h k l = 2) :
    ord h' k l = -2 ∧ Stroke p h' k l := by
  have hkl : k ≠ l := by
    rintro rfl
    rw [ord, sub_self, HahnSeries.order_zero] at h2
    norm_num at h2
  obtain ⟨-, hw, -, b4⟩ := H.bounds hkl
  have hw2 : ord h' k l = -2 := by linarith
  exact ⟨hw2, (H.stroke_iff' hkl).mpr (by linarith)⟩

end Pair

end Colour

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ} (G : Germ n m)

/-- The colour pair `(z, w)` of a germ. -/
theorem colZ : Colour.Pair m G.p G.z G.w :=
  ⟨G.p_symm, G.body_z, G.body_w, G.dist, G.low_z, G.low_w⟩

/-- The colour pair `(w, z)` of a germ: the colours exchanged. -/
theorem colW : Colour.Pair m G.p G.w G.z := G.colZ.symm

theorem zeta_comm (k l : Fin n) : G.zeta k l = G.zeta l k := Colour.ord_comm G.z k l

theorem omega_comm (k l : Fin n) : G.omega k l = G.omega l k := Colour.ord_comm G.w k l

theorem x_comm (k l : Fin n) : G.x k l = G.x l k := by
  unfold x
  rw [G.p_symm]

theorem zStroke_comm {k l : Fin n} : G.zStroke k l ↔ G.zStroke l k := G.colZ.stroke_comm

theorem wStroke_comm {k l : Fin n} : G.wStroke k l ↔ G.wStroke l k := G.colW.stroke_comm

/-- `e(Z_kl) = −(ζ_kl + 3ω_kl)/2` (§2.2). -/
theorem orderTop_termZ_z {k l : Fin n} (hkl : k ≠ l) :
    (termZ G.p G.z k l).orderTop = ((-(G.zeta k l + 3 * G.omega k l) / 2 : ℚ) : WithTop ℚ) :=
  G.colZ.orderTop_termZ hkl

/-- `e(W_kl) = −(3ζ_kl + ω_kl)/2` (§2.2). -/
theorem orderTop_termZ_w {k l : Fin n} (hkl : k ≠ l) :
    (termZ G.p G.w k l).orderTop = ((-(3 * G.zeta k l + G.omega k l) / 2 : ℚ) : WithTop ℚ) := by
  rw [G.colW.orderTop_termZ hkl]
  change ((-(G.omega k l + 3 * G.zeta k l) / 2 : ℚ) : WithTop ℚ) = _
  congr 1
  ring

/-- `ζ_kl ≥ min(a_k, a_l)` (§2.2). -/
theorem min_le_zeta {k l : Fin n} (hkl : k ≠ l) :
    min (G.z k).orderTop (G.z l).orderTop ≤ (G.zeta k l : WithTop ℚ) :=
  G.colZ.min_le_ord hkl

/-- `ζ_kl = min(a_k, a_l)` if `a_k ≠ a_l` (§2.2). -/
theorem zeta_eq_min {k l : Fin n} (hkl : k ≠ l) (hne : (G.z k).orderTop ≠ (G.z l).orderTop) :
    (G.zeta k l : WithTop ℚ) = min (G.z k).orderTop (G.z l).orderTop :=
  G.colZ.ord_eq_min hkl hne

/-- `ω_kl ≥ min(b_k, b_l)` (§2.2). -/
theorem min_le_omega {k l : Fin n} (hkl : k ≠ l) :
    min (G.w k).orderTop (G.w l).orderTop ≤ (G.omega k l : WithTop ℚ) :=
  G.colW.min_le_ord hkl

/-- `ω_kl = min(b_k, b_l)` if `b_k ≠ b_l` (§2.2). -/
theorem omega_eq_min {k l : Fin n} (hkl : k ≠ l) (hne : (G.w k).orderTop ≠ (G.w l).orderTop) :
    (G.omega k l : WithTop ℚ) = min (G.w k).orderTop (G.w l).orderTop :=
  G.colW.ord_eq_min hkl hne

/-- **(O1)** of Lemma 2.8 (`lem:orders`): `ζ_kl, ω_kl ≥ −2`, `ζ_kl + 3ω_kl ≤ 4` and `3ζ_kl + ω_kl ≤ 4`. -/
theorem O1 {k l : Fin n} (hkl : k ≠ l) :
    -2 ≤ G.zeta k l ∧ -2 ≤ G.omega k l ∧ G.zeta k l + 3 * G.omega k l ≤ 4 ∧
      3 * G.zeta k l + G.omega k l ≤ 4 :=
  G.colZ.bounds hkl

/-- **(O1)** of Lemma 2.8 (`lem:orders`), the consequences: `ζ_kl, ω_kl ≤ 2` and `−2 ≤ x_kl ≤ 1`. -/
theorem O1_le {k l : Fin n} (hkl : k ≠ l) :
    G.zeta k l ≤ 2 ∧ G.omega k l ≤ 2 ∧ -2 ≤ G.x k l ∧ G.x k l ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := G.O1 hkl
  rw [G.x_eq hkl]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **(O2)** of Lemma 2.8 (`lem:orders`): `kl` is a `z`-stroke iff `ζ_kl + 3ω_kl = 4`, and a `w`-stroke iff
`3ζ_kl + ω_kl = 4`. -/
theorem O2 {k l : Fin n} (hkl : k ≠ l) :
    (G.zStroke k l ↔ G.zeta k l + 3 * G.omega k l = 4) ∧
      (G.wStroke k l ↔ 3 * G.zeta k l + G.omega k l = 4) :=
  ⟨G.colZ.stroke_iff hkl, G.colZ.stroke_iff' hkl⟩

/-- **(O3)** of Lemma 2.8 (`lem:orders`), `z`-strokes: `ζ_kl = 3x_kl − 2`, `ω_kl = 2 − x_kl` and
`0 ≤ x_kl ≤ 1`. -/
theorem O3_z {k l : Fin n} (hs : G.zStroke k l) :
    G.zeta k l = 3 * G.x k l - 2 ∧ G.omega k l = 2 - G.x k l ∧ 0 ≤ G.x k l ∧ G.x k l ≤ 1 := by
  have hkl := hs.1
  have e := (G.O2 hkl).1.mp hs
  obtain ⟨h1, h2, h3, h4⟩ := G.O1 hkl
  rw [G.x_eq hkl]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **(O3)** of Lemma 2.8 (`lem:orders`), `w`-strokes: `ω_kl = 3x_kl − 2`, `ζ_kl = 2 − x_kl` and
`0 ≤ x_kl ≤ 1`. -/
theorem O3_w {k l : Fin n} (hs : G.wStroke k l) :
    G.omega k l = 3 * G.x k l - 2 ∧ G.zeta k l = 2 - G.x k l ∧ 0 ≤ G.x k l ∧ G.x k l ≤ 1 := by
  have hkl := hs.1
  have e := (G.O2 hkl).2.mp hs
  obtain ⟨h1, h2, h3, h4⟩ := G.O1 hkl
  rw [G.x_eq hkl]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **(O4)** of Lemma 2.8 (`lem:orders`): `x_kl = 1` iff `kl` is both a `z`-stroke and a `w`-stroke. -/
theorem O4 {k l : Fin n} (hkl : k ≠ l) : G.x k l = 1 ↔ G.zStroke k l ∧ G.wStroke k l := by
  obtain ⟨h1, h2, h3, h4⟩ := G.O1 hkl
  rw [G.x_eq hkl, (G.O2 hkl).1, (G.O2 hkl).2]
  constructor
  · intro e
    constructor <;> linarith
  · rintro ⟨e1, e2⟩
    linarith

/-- The ultrametric inequality `ζ_kj ≥ min(ζ_kl, ζ_lj)` (O5). -/
theorem zeta_ultra {k l j : Fin n} (hkl : k ≠ l) (hlj : l ≠ j) (hkj : k ≠ j) :
    min (G.zeta k l) (G.zeta l j) ≤ G.zeta k j :=
  G.colZ.ultra hkl hlj hkj

/-- The ultrametric inequality `ω_kj ≥ min(ω_kl, ω_lj)` (O5). -/
theorem omega_ultra {k l j : Fin n} (hkl : k ≠ l) (hlj : l ≠ j) (hkj : k ≠ j) :
    min (G.omega k l) (G.omega l j) ≤ G.omega k j :=
  G.colW.ultra hkl hlj hkj

/-- **(O5)** of Lemma 2.8 (`lem:orders`) for `ζ`: in every triangle `klj` the minimum of `ζ_kl, ζ_lj, ζ_jk` is
attained at least twice. -/
theorem O5_z {k l j : Fin n} (hkl : k ≠ l) (hlj : l ≠ j) (hkj : k ≠ j) :
    (G.zeta k l = G.zeta l j ∧ G.zeta k l ≤ G.zeta j k) ∨
      (G.zeta l j = G.zeta j k ∧ G.zeta l j ≤ G.zeta k l) ∨
      (G.zeta j k = G.zeta k l ∧ G.zeta j k ≤ G.zeta l j) :=
  Colour.min_twice (G.colZ.ultra' hlj hkj.symm hkl.symm) (G.colZ.ultra' hkj.symm hkl hlj.symm)
    (G.colZ.ultra' hkl hlj hkj)

/-- **(O5)** of Lemma 2.8 (`lem:orders`) for `ω`: in every triangle `klj` the minimum of `ω_kl, ω_lj, ω_jk` is
attained at least twice. -/
theorem O5_w {k l j : Fin n} (hkl : k ≠ l) (hlj : l ≠ j) (hkj : k ≠ j) :
    (G.omega k l = G.omega l j ∧ G.omega k l ≤ G.omega j k) ∨
      (G.omega l j = G.omega j k ∧ G.omega l j ≤ G.omega k l) ∨
      (G.omega j k = G.omega k l ∧ G.omega j k ≤ G.omega l j) :=
  Colour.min_twice (G.colW.ultra' hlj hkj.symm hkl.symm) (G.colW.ultra' hkj.symm hkl hlj.symm)
    (G.colW.ultra' hkl hlj hkj)

/-- **(O6)** of Lemma 2.8 (`lem:orders`), first part, colour `z`: if `k` is `z`-circled and `l` is not, then
`ζ_kl = −2`. -/
theorem O6_z {k l : Fin n} (hk : G.zCircle k) (hl : ¬ G.zCircle l) : G.zeta k l = -2 :=
  G.colZ.ord_of_circle hk hl

/-- **(O6)** of Lemma 2.8 (`lem:orders`), second part, colour `z`: if `ζ_kl = 2`, then `ω_kl = −2` and `kl` is a
`w`-stroke. -/
theorem O6_z' {k l : Fin n} (h2 : G.zeta k l = 2) : G.omega k l = -2 ∧ G.wStroke k l :=
  G.colZ.ord_eq_two h2

/-- **(O6)** of Lemma 2.8 (`lem:orders`), first part, colour `w`: if `k` is `w`-circled and `l` is not, then
`ω_kl = −2`. -/
theorem O6_w {k l : Fin n} (hk : G.wCircle k) (hl : ¬ G.wCircle l) : G.omega k l = -2 :=
  G.colW.ord_of_circle hk hl

/-- **(O6)** of Lemma 2.8 (`lem:orders`), second part, colour `w`: if `ω_kl = 2`, then `ζ_kl = −2` and `kl` is a
`z`-stroke. -/
theorem O6_w' {k l : Fin n} (h2 : G.omega k l = 2) : G.zeta k l = -2 ∧ G.zStroke k l :=
  G.colW.ord_eq_two h2

end Germ

end

end CC6Full
