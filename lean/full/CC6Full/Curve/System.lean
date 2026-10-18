import CC6Full.Statement
import CC6Full.Curve.ACurve
import Mathlib.Data.Fintype.Sum
import Mathlib.RingTheory.Ideal.Span

/-!
# Normalized central configurations as an affine variety

Paper §2.1 (`ss:system`), in coordinates adapted to the bodies. For `n + 2` bodies (body `k` of the paper is
`k - 1`) the coordinates of `ℂ^{Coord}` are the positions `z_k`, `w_k` of all bodies (`z = x + iy`, `w = x - iy`
for a real configuration) and `p_kl` for the pairs `k < l`. The *rows* are

* the equations of the bodies (2.2): `z_k − Σ_{l ≠ k} m_l p_kl³ (z_k − z_l)` and the same in `w`;
* the distance equations `p_kl² (z_k − z_l)(w_k − w_l) − 1`.

`X_m` is their zero set and the *slice* `Y_m = X_m ∩ {z₁ − z₂ = 1}` (bodies `1, 2` of the paper).

Relation with the paper. The paper uses the positions `u_k = z_k − z_6`, `v_k = w_k − w_6` relative to the last
body and the rows `F_k(u) − F_6(u)` with `F_k(h) = h_k − Σ_l m_l p_kl³ (h_k − h_l)`, and the slice `u₁ = 1`. The maps
`u_k = z_k − z_6` and `z_k = u_k − F_6(u)` are inverse isomorphisms between the two zero sets (the equations of the
bodies say `F_k(u) = −z_6` for all `k`), and they commute with the rotations `(z, w) ↦ (s z, s⁻¹ w)`. Any slice of
the free action of the rotations serves; we fix the rotation by `z₁ − z₂ = 1`. In these coordinates relabelling
the bodies permutes the coordinates, and `U = Σ_k m_k z_k w_k` holds on `X_m` for all masses.

* `U = Σ_{k<l} m_k m_l p_kl` and `r²_kl = (z_k − z_l)(w_k − w_l)` (§2.1).
* `Curve n m`: an irreducible curve in `Y_m` (`ACurve` with the ideal of `Y_m` in its ideal); *nontrivial*
  (Corollary 2.4, `cor:curve`): `U` does not vanish identically on it and some `r²_kl` is not constant.
-/

namespace CC6Full

open Finset MvPolynomial

noncomputable section

/-- The pairs `k < l` of bodies. -/
abbrev Pair (N : ℕ) := {e : Fin N × Fin N // e.1 < e.2}

/-- The coordinates: `z_k` (`inl k`), `w_k` (`inr (inl k)`), `p_e` (`inr (inr e)`) for the pairs `e`. -/
abbrev Coord (N : ℕ) := Fin N ⊕ Fin N ⊕ Pair N

/-- The polynomial ring of `ℂ^{Coord}`. -/
abbrev Poly (N : ℕ) := MvPolynomial (Coord N) ℂ

variable {N : ℕ}

/-- The coordinate `z_k`. -/
def zc (k : Fin N) : Coord N := Sum.inl k

/-- The coordinate `w_k`. -/
def wc (k : Fin N) : Coord N := Sum.inr (Sum.inl k)

/-- The coordinate `p_e` of a pair. -/
def pc (e : Pair N) : Coord N := Sum.inr (Sum.inr e)

/-- `z_k` as a polynomial. -/
def zP (k : Fin N) : Poly N := X (zc k)

/-- `w_k` as a polynomial. -/
def wP (k : Fin N) : Poly N := X (wc k)

/-- `p_kl` as a polynomial, symmetric in `k, l`; the diagonal value `0` is junk. -/
def pP (k l : Fin N) : Poly N :=
  if h : k < l then X (pc ⟨(k, l), h⟩) else if h' : l < k then X (pc ⟨(l, k), h'⟩) else 0

theorem pP_comm (k l : Fin N) : pP k l = pP l k := by
  unfold pP
  rcases lt_trichotomy k l with h | rfl | h
  · simp [h, not_lt.mpr h.le]
  · simp
  · simp [h, not_lt.mpr h.le]

/-- The row of the equation of body `k` in the colour `z`: `z_k − Σ_{l ≠ k} m_l p_kl³ (z_k − z_l)`. -/
def rowZ (m : Fin N → ℝ) (k : Fin N) : Poly N :=
  zP k - ∑ l ∈ univ.erase k, C (m l : ℂ) * pP k l ^ 3 * (zP k - zP l)

/-- The row of the equation of body `k` in the colour `w`. -/
def rowW (m : Fin N → ℝ) (k : Fin N) : Poly N :=
  wP k - ∑ l ∈ univ.erase k, C (m l : ℂ) * pP k l ^ 3 * (wP k - wP l)

/-- The distance row `p_kl² (z_k − z_l)(w_k − w_l) − 1` of a pair `e = kl`. -/
def rowD (e : Pair N) : Poly N :=
  X (pc e) ^ 2 * (zP e.1.1 - zP e.1.2) * (wP e.1.1 - wP e.1.2) - 1

/-- The rows. -/
def rows (m : Fin N → ℝ) : Set (Poly N) := Set.range (rowZ m) ∪ Set.range (rowW m) ∪ Set.range rowD

/-- The ideal of `X_m`. -/
def idealX (m : Fin N → ℝ) : Ideal (Poly N) := Ideal.span (rows m)

/-- `X_m`, the zero set of the rows. -/
def Xm (m : Fin N → ℝ) : Set (Coord N → ℂ) := {y | ∀ f ∈ rows m, eval y f = 0}

variable {n : ℕ}

/-- The slice polynomial `z₁ − z₂ − 1`. -/
def sliceP : Poly (n + 2) := zP 0 - zP 1 - 1

/-- The ideal of the slice `Y_m = X_m ∩ {z₁ − z₂ = 1}`. -/
def idealY (m : Fin (n + 2) → ℝ) : Ideal (Poly (n + 2)) := Ideal.span (rows m ∪ {sliceP})

/-- The slice `Y_m`. -/
def Ym (m : Fin (n + 2) → ℝ) : Set (Coord (n + 2) → ℂ) := {y | y ∈ Xm m ∧ eval y sliceP = 0}

/-- `U = Σ_{k<l} m_k m_l p_kl`. -/
def Upoly (m : Fin N → ℝ) : Poly N := ∑ e : Pair N, C ((m e.1.1 * m e.1.2 : ℝ) : ℂ) * X (pc e)

/-- `r²_kl = (z_k − z_l)(w_k − w_l)`. -/
def r2P (k l : Fin N) : Poly N := (zP k - zP l) * (wP k - wP l)

/-- The configuration `(z_k)_k` of a point. -/
def zConf (y : Coord N → ℂ) : Conf N := fun k => y (zc k)

/-- An irreducible curve `C ⊆ Y_m`. -/
structure Curve (n : ℕ) (m : Fin (n + 2) → ℝ) extends ACurve (Coord (n + 2)) where
  le_ideal : idealY m ≤ toACurve.ideal

/-- A *nontrivial* curve (Corollary 2.4, `cor:curve`): `U` does not vanish identically on `C` and some `r²_kl` is not
constant on `C`. -/
def Curve.Nontrivial {m : Fin (n + 2) → ℝ} (C : Curve n m) : Prop :=
  Upoly m ∉ C.ideal ∧ ∃ k l : Fin (n + 2), ¬ C.IsConst (r2P k l)

end

end CC6Full

/-! ### Values of the coordinates and of the rows; the zero sets of the ideals -/

namespace CC6Full

open Finset MvPolynomial

section evaluation

variable {N : ℕ}

@[simp] theorem eval_zP (y : Coord N → ℂ) (k : Fin N) : eval y (zP k) = y (zc k) := eval_X _

@[simp] theorem eval_wP (y : Coord N → ℂ) (k : Fin N) : eval y (wP k) = y (wc k) := eval_X _

theorem eval_pP (y : Coord N → ℂ) (k l : Fin N) :
    eval y (pP k l) =
      if h : k < l then y (pc ⟨(k, l), h⟩) else if h' : l < k then y (pc ⟨(l, k), h'⟩) else 0 := by
  unfold pP
  split_ifs <;> simp

/-- The value of `p_kl` (`k ≠ l`) at a point whose coordinates `p_e` are given by a symmetric function `f`. -/
theorem eval_pP_eq {y : Coord N → ℂ} {f : Fin N → Fin N → ℂ} (hf : ∀ e : Pair N, y (pc e) = f e.1.1 e.1.2)
    (hsymm : ∀ k l, f k l = f l k) {k l : Fin N} (hkl : k ≠ l) : eval y (pP k l) = f k l := by
  rw [eval_pP]
  split_ifs with h h'
  · exact hf _
  · exact (hf ⟨(l, k), h'⟩).trans (hsymm l k)
  · exact ((Ne.lt_or_gt hkl).elim h h').elim

theorem eval_r2P (y : Coord N → ℂ) (k l : Fin N) :
    eval y (r2P k l) = (y (zc k) - y (zc l)) * (y (wc k) - y (wc l)) := by
  simp only [r2P, map_sub, map_mul, eval_zP, eval_wP]

theorem eval_rowZ (y : Coord N → ℂ) (m : Fin N → ℝ) (k : Fin N) :
    eval y (rowZ m k) =
      y (zc k) - ∑ l ∈ univ.erase k, (m l : ℂ) * eval y (pP k l) ^ 3 * (y (zc k) - y (zc l)) := by
  simp only [rowZ, map_sub, map_sum, map_mul, map_pow, eval_C, eval_zP]

theorem eval_rowW (y : Coord N → ℂ) (m : Fin N → ℝ) (k : Fin N) :
    eval y (rowW m k) =
      y (wc k) - ∑ l ∈ univ.erase k, (m l : ℂ) * eval y (pP k l) ^ 3 * (y (wc k) - y (wc l)) := by
  simp only [rowW, map_sub, map_sum, map_mul, map_pow, eval_C, eval_wP]

theorem eval_rowD (y : Coord N → ℂ) (e : Pair N) :
    eval y (rowD e) = y (pc e) ^ 2 * (y (zc e.1.1) - y (zc e.1.2)) * (y (wc e.1.1) - y (wc e.1.2)) - 1 := by
  simp only [rowD, map_sub, map_mul, map_pow, map_one, eval_X, eval_zP, eval_wP]

theorem rowZ_mem_rows (m : Fin N → ℝ) (k : Fin N) : rowZ m k ∈ rows m := Or.inl (Or.inl ⟨k, rfl⟩)

theorem rowW_mem_rows (m : Fin N → ℝ) (k : Fin N) : rowW m k ∈ rows m := Or.inl (Or.inr ⟨k, rfl⟩)

theorem rowD_mem_rows (m : Fin N → ℝ) (e : Pair N) : rowD e ∈ rows m := Or.inr ⟨e, rfl⟩

/-- A polynomial of the ideal of `X_m` vanishes on `X_m`. -/
theorem eval_eq_zero_of_mem_idealX {m : Fin N → ℝ} {f : Poly N} (hf : f ∈ idealX m) {y : Coord N → ℂ}
    (hy : y ∈ Xm m) : eval y f = 0 := by
  have : idealX m ≤ RingHom.ker (eval y) := Ideal.span_le.mpr fun g hg => hy g hg
  exact this hf

end evaluation

section slice

variable {n : ℕ}

theorem eval_sliceP (y : Coord (n + 2) → ℂ) : eval y sliceP = y (zc 0) - y (zc 1) - 1 := by
  simp only [sliceP, map_sub, map_one, eval_zP]

/-- A polynomial of the ideal of `Y_m` vanishes on `Y_m`. -/
theorem eval_eq_zero_of_mem_idealY {m : Fin (n + 2) → ℝ} {f : Poly (n + 2)} (hf : f ∈ idealY m)
    {y : Coord (n + 2) → ℂ} (hy : y ∈ Ym m) : eval y f = 0 := by
  have : idealY m ≤ RingHom.ker (eval y) := by
    refine Ideal.span_le.mpr fun g hg => ?_
    rcases hg with hg | hg
    · exact hy.1 g hg
    · rw [Set.mem_singleton_iff.mp hg]
      exact hy.2
  exact this hf

/-- `Y_m` is the zero set of the ideal `idealY m`. -/
theorem mem_Ym_iff_zeroLocus {m : Fin (n + 2) → ℝ} {y : Coord (n + 2) → ℂ} :
    y ∈ Ym m ↔ ∀ f ∈ idealY m, eval y f = 0 :=
  ⟨fun hy _ hf => eval_eq_zero_of_mem_idealY hf hy, fun h =>
    ⟨fun f hf => h f (Ideal.subset_span (Or.inl hf)), h _ (Ideal.subset_span (Or.inr rfl))⟩⟩

end slice

end CC6Full
