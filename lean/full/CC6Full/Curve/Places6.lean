import CC6Full.Curve.System
import CC6Full.Curve.FunctionField.Divisor

/-!
# Places of a curve `C ⊆ Y_m`: orders, singular places, `d`, `γ` and the type

Paper §2.2 (`ss:places`), in the coordinates `z_k, w_k, p_kl` of `CC6Full.Curve.System`. For a place `P` of a curve
`C` in `ℂ^{Coord}` (a normalized discrete valuation of `ℂ(C)` trivial on `ℂ`, `Place C`), `P.v f` is the order of
the function of the polynomial `f`, an element of `WithTop ℤ` (`⊤` exactly on the ideal of `C`).

* `Place.vZ`, `Place.vW`: `ν(𝒵)` and `ν(𝒲)`, the minima of the orders of the components `z_k`, `Z_kl = p_kl³ z_kl`
  of `𝒵`, resp. `w_k`, `W_kl = p_kl³ w_kl` of `𝒲`. The pairs are `k < l`; `Z_lk = −Z_kl` has the same order
  (`Place.vZ_le_termZ`).
* `Place.Singular`: `ν(𝒵) + ν(𝒲) < 0`. `Place.dd = d = −½(ν(𝒵) + ν(𝒲))`, `Place.gamma = γ = ½(ν(𝒲) − ν(𝒵))` and
  the type `Place.type e = x_e = −(2/d) ν(p_e)`; by Lemma 2.5 (`lem:place`) the exponent of the neutral function
  `p_e` is `e(p_e) = (2/d) ν(p_e) = −x_e`.
* On a curve `C ⊆ Y_m` (`Curve n m`) the functions `z_k − z_l`, `w_k − w_l` and `p_kl` (`k ≠ l`) are units (the
  distance rows), so their orders are integers, with `2 ν(p_kl) + ν(z_kl) + ν(w_kl) = 0` (`Curve.ordZ_dist`).
* `Curve.v_pP_eq_zero_of_not_singular`: at a place that is not singular every `p_kl` has order `0`, since
  `4 ν(p_kl) = ν(Z_kl) + ν(W_kl) ≥ ν(𝒵) + ν(𝒲) ≥ 0` and `−2 ν(p_kl) = ν(z_kl) + ν(w_kl) ≥ ν(𝒵) + ν(𝒲) ≥ 0`.
* `Place.exists_neg_of_singular`: a singular place is a pole of some coordinate (a place at infinity), since at
  a place where all coordinates have order `≥ 0` so have all polynomials.
-/

namespace CC6Full

open Finset MvPolynomial

noncomputable section

/-! ## Functions of polynomials -/

section fn

variable {σ : Type*} (C : ACurve σ)

/-- `C.fn` as a ring hom `ℂ[σ] → ℂ(C)`. -/
def ACurve.fnHom : MvPolynomial σ ℂ →+* C.FunctionField :=
  (algebraMap C.Ring C.FunctionField).comp (Ideal.Quotient.mk C.ideal)

variable {C}

theorem ACurve.fnHom_apply (f : MvPolynomial σ ℂ) : C.fnHom f = C.fn f := rfl

theorem ACurve.fn_eq_zero_iff {f : MvPolynomial σ ℂ} : C.fn f = 0 ↔ f ∈ C.ideal := by
  rw [ACurve.fn, ← map_zero (algebraMap C.Ring C.FunctionField),
    (IsFractionRing.injective C.Ring C.FunctionField).eq_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem ACurve.fn_eq_fn_iff {f g : MvPolynomial σ ℂ} : C.fn f = C.fn g ↔ f - g ∈ C.ideal := by
  rw [← sub_eq_zero, ← ACurve.fnHom_apply, ← ACurve.fnHom_apply, ← map_sub, ACurve.fnHom_apply,
    ACurve.fn_eq_zero_iff]

end fn

/-! ## Orders of polynomials at a place -/

section place

variable {σ : Type*} {C : ACurve σ} (P : Place C)

theorem Place.v_def (f : MvPolynomial σ ℂ) : P.v f = P.ord (C.fnHom f) := rfl

theorem Place.v_mul (f g : MvPolynomial σ ℂ) : P.v (f * g) = P.v f + P.v g := by
  simp only [Place.v_def, map_mul, P.ord.map_mul]

theorem Place.v_pow (f : MvPolynomial σ ℂ) (k : ℕ) : P.v (f ^ k) = k • P.v f := by
  simp only [Place.v_def, map_pow, P.ord.map_pow]

theorem Place.v_add (f g : MvPolynomial σ ℂ) : min (P.v f) (P.v g) ≤ P.v (f + g) := by
  simp only [Place.v_def, map_add]
  exact P.ord.map_add _ _

theorem Place.v_neg (f : MvPolynomial σ ℂ) : P.v (-f) = P.v f := by
  simp only [Place.v_def, map_neg, P.ord.map_neg]

theorem Place.v_sub (f g : MvPolynomial σ ℂ) : min (P.v f) (P.v g) ≤ P.v (f - g) := by
  rw [sub_eq_add_neg, ← P.v_neg g]
  exact P.v_add f (-g)

theorem Place.v_C {c : ℂ} (hc : c ≠ 0) : P.v (MvPolynomial.C c) = 0 := P.ord_const c hc

theorem Place.v_one : P.v 1 = 0 := by
  simp only [Place.v_def, map_one, P.ord.map_one]

theorem Place.v_eq_top_iff (f : MvPolynomial σ ℂ) : P.v f = ⊤ ↔ f ∈ C.ideal := by
  rw [Place.v, AddValuation.top_iff, ACurve.fn_eq_zero_iff]

/-- The order of a function that does not vanish is its integer order. -/
theorem Place.v_eq_ordZ {f : MvPolynomial σ ℂ} (hf : C.fn f ≠ 0) :
    P.v f = (ordZ P.ord (C.fn f) : WithTop ℤ) :=
  ordZ_spec P.ord hf

/-- Nonnegative order of every polynomial when the coordinates have nonnegative order. -/
theorem Place.v_nonneg_of_coords (h : ∀ c, 0 ≤ P.v (X c)) (f : MvPolynomial σ ℂ) : 0 ≤ P.v f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    by_cases ha : a = 0
    · subst ha
      rw [map_zero, (P.v_eq_top_iff 0).mpr (Ideal.zero_mem _)]
      exact le_top
    · rw [P.v_C ha]
  | add f g hf hg => exact le_trans (le_min hf hg) (P.v_add f g)
  | mul_X f c hf =>
    rw [P.v_mul]
    exact add_nonneg hf (h c)

end place

/-! ## The coordinates `p_kl` -/

namespace Curve

variable {N : ℕ}

theorem pP_of_lt {k l : Fin N} (h : k < l) : pP k l = X (pc ⟨(k, l), h⟩) := by
  unfold pP
  rw [dite_eq_left h]

theorem pP_of_gt {k l : Fin N} (h : l < k) : pP k l = X (pc ⟨(l, k), h⟩) := by
  unfold pP
  rw [dite_eq_right (not_lt.mpr h.le), dite_eq_left h]

theorem pP_pair (e : Pair N) : pP e.1.1 e.1.2 = X (pc e) := pP_of_lt e.2

theorem pP_self (k : Fin N) : pP k k = 0 := by
  unfold pP
  simp

end Curve

open Curve

/-! ## `ν(𝒵)`, `ν(𝒲)`, singular places, `d`, `γ` and the type (§2.2) -/

section defs

variable {N : ℕ} {C : ACurve (Coord N)} (P : Place C)

/-- `ν(𝒵)`: the minimum of the orders of the components `z_k` and `Z_kl = p_kl³ (z_k − z_l)` (`k < l`) of `𝒵`. -/
def Place.vZ : WithTop ℤ :=
  (univ.inf fun k => P.v (zP k)) ⊓ univ.inf fun e : Pair N => P.v (X (pc e) ^ 3 * (zP e.1.1 - zP e.1.2))

/-- `ν(𝒲)`: the minimum of the orders of the components `w_k` and `W_kl = p_kl³ (w_k − w_l)` (`k < l`) of `𝒲`. -/
def Place.vW : WithTop ℤ :=
  (univ.inf fun k => P.v (wP k)) ⊓ univ.inf fun e : Pair N => P.v (X (pc e) ^ 3 * (wP e.1.1 - wP e.1.2))

/-- `P` is *singular* (§2.2): `ν(𝒵) + ν(𝒲) < 0`. -/
def Place.Singular : Prop := P.vZ + P.vW < 0

/-- `d = −½ (ν(𝒵) + ν(𝒲))` (§2.2); positive at a singular place (`Place.dd_pos`). -/
def Place.dd : ℚ := -((WithTop.untopD 0 (P.vZ + P.vW) : ℤ) : ℚ) / 2

/-- `γ = ½ (ν(𝒲) − ν(𝒵))` (§2.2). -/
def Place.gamma : ℚ := ((WithTop.untopD 0 P.vW - WithTop.untopD 0 P.vZ : ℤ) : ℚ) / 2

/-- The *type* `x(P) = (x_e)_e`, `x_e = −(2/d) ν(p_e)` (§2.2: `x_kl = −e(p_kl)`). -/
def Place.type (e : Pair N) : ℚ := -(2 / P.dd) * (ordZ P.ord (C.fn (X (pc e))) : ℚ)

theorem Place.vZ_le_z (k : Fin N) : P.vZ ≤ P.v (zP k) :=
  inf_le_left.trans (Finset.inf_le (Finset.mem_univ k))

theorem Place.vW_le_w (k : Fin N) : P.vW ≤ P.v (wP k) :=
  inf_le_left.trans (Finset.inf_le (Finset.mem_univ k))

theorem Place.vZ_le_Z (e : Pair N) : P.vZ ≤ P.v (X (pc e) ^ 3 * (zP e.1.1 - zP e.1.2)) :=
  inf_le_right.trans (Finset.inf_le (Finset.mem_univ e))

theorem Place.vW_le_W (e : Pair N) : P.vW ≤ P.v (X (pc e) ^ 3 * (wP e.1.1 - wP e.1.2)) :=
  inf_le_right.trans (Finset.inf_le (Finset.mem_univ e))

/-- `ν(𝒵) ≤ ν(z_k − z_l)`. -/
theorem Place.vZ_le_zsub (k l : Fin N) : P.vZ ≤ P.v (zP k - zP l) :=
  le_trans (le_min (P.vZ_le_z k) (P.vZ_le_z l)) (P.v_sub _ _)

/-- `ν(𝒲) ≤ ν(w_k − w_l)`. -/
theorem Place.vW_le_wsub (k l : Fin N) : P.vW ≤ P.v (wP k - wP l) :=
  le_trans (le_min (P.vW_le_w k) (P.vW_le_w l)) (P.v_sub _ _)

/-- `ν(𝒵) ≤ ν(Z_kl)` for every ordered pair `k ≠ l`. -/
theorem Place.vZ_le_termZ {k l : Fin N} (h : k ≠ l) : P.vZ ≤ P.v (pP k l ^ 3 * (zP k - zP l)) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [pP_of_lt h']
    exact P.vZ_le_Z ⟨(k, l), h'⟩
  · rw [pP_of_gt h', show X (pc ⟨(l, k), h'⟩) ^ 3 * (zP k - zP l) =
      -(X (pc ⟨(l, k), h'⟩) ^ 3 * (zP l - zP k)) by ring, P.v_neg]
    exact P.vZ_le_Z ⟨(l, k), h'⟩

/-- `ν(𝒲) ≤ ν(W_kl)` for every ordered pair `k ≠ l`. -/
theorem Place.vW_le_termW {k l : Fin N} (h : k ≠ l) : P.vW ≤ P.v (pP k l ^ 3 * (wP k - wP l)) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [pP_of_lt h']
    exact P.vW_le_W ⟨(k, l), h'⟩
  · rw [pP_of_gt h', show X (pc ⟨(l, k), h'⟩) ^ 3 * (wP k - wP l) =
      -(X (pc ⟨(l, k), h'⟩) ^ 3 * (wP l - wP k)) by ring, P.v_neg]
    exact P.vW_le_W ⟨(l, k), h'⟩

/-- At a singular place `ν(𝒵)` and `ν(𝒲)` are finite. -/
theorem Place.vZ_vW_ne_top (h : P.Singular) : P.vZ ≠ ⊤ ∧ P.vW ≠ ⊤ :=
  WithTop.add_ne_top.mp (ne_top_of_lt h)

/-- At a singular place, `ν(𝒵) = zv`, `ν(𝒲) = wv` with integers `zv + wv < 0`, `d = −(zv + wv)/2` and
`γ = (wv − zv)/2`. -/
theorem Place.exists_of_singular (h : P.Singular) :
    ∃ zv wv : ℤ, P.vZ = zv ∧ P.vW = wv ∧ zv + wv < 0 ∧ P.dd = -((zv + wv : ℤ) : ℚ) / 2 ∧
      P.gamma = ((wv - zv : ℤ) : ℚ) / 2 := by
  obtain ⟨hZ, hW⟩ := P.vZ_vW_ne_top h
  obtain ⟨zv, hzv⟩ := WithTop.ne_top_iff_exists.mp hZ
  obtain ⟨wv, hwv⟩ := WithTop.ne_top_iff_exists.mp hW
  have hs : P.vZ + P.vW = ((zv + wv : ℤ) : WithTop ℤ) := by rw [← hzv, ← hwv, WithTop.coe_add]
  refine ⟨zv, wv, hzv.symm, hwv.symm, ?_, ?_, ?_⟩
  · have h' := h
    rw [Place.Singular, hs] at h'
    exact_mod_cast h'
  · rw [Place.dd, hs, WithTop.untopD_coe]
  · rw [Place.gamma, ← hzv, ← hwv, WithTop.untopD_coe, WithTop.untopD_coe]

/-- `d > 0` at a singular place. -/
theorem Place.dd_pos (h : P.Singular) : 0 < P.dd := by
  obtain ⟨zv, wv, -, -, hlt, hd, -⟩ := P.exists_of_singular h
  rw [hd]
  have : ((zv + wv : ℤ) : ℚ) < 0 := by exact_mod_cast hlt
  linarith

/-- **A singular place is a place at infinity**: some coordinate has a pole there. -/
theorem Place.exists_neg_of_singular (h : P.Singular) : ∃ c, P.v (X c) < 0 := by
  by_contra hinf
  have hc : ∀ c, 0 ≤ P.v (X c) := fun c => by
    by_contra hneg
    exact hinf ⟨c, lt_of_not_ge hneg⟩
  have hZ : 0 ≤ P.vZ := le_inf (Finset.le_inf fun k _ => P.v_nonneg_of_coords hc _)
    (Finset.le_inf fun e _ => P.v_nonneg_of_coords hc _)
  have hW : 0 ≤ P.vW := le_inf (Finset.le_inf fun k _ => P.v_nonneg_of_coords hc _)
    (Finset.le_inf fun e _ => P.v_nonneg_of_coords hc _)
  exact absurd h (not_lt.mpr (add_nonneg hZ hW))

end defs

/-! ## Curves in `Y_m`: the units and the orders of the `p_kl` -/

section curve

variable {n : ℕ} {m : Fin (n + 2) → ℝ} (C : Curve n m)

/-- The rows vanish on `C`. -/
theorem Curve.rows_mem {f : Poly (n + 2)} (hf : f ∈ rows m) : f ∈ C.ideal :=
  C.le_ideal (Ideal.subset_span (Or.inl hf))

/-- The slice polynomial vanishes on `C`. -/
theorem Curve.sliceP_mem : sliceP ∈ C.ideal :=
  C.le_ideal (Ideal.subset_span (Or.inr rfl))

/-- The distance row of an ordered pair `k ≠ l`: `p_kl² (z_k − z_l)(w_k − w_l) − 1` vanishes on `C`. -/
theorem Curve.dist_mem {k l : Fin (n + 2)} (h : k ≠ l) :
    pP k l ^ 2 * (zP k - zP l) * (wP k - wP l) - 1 ∈ C.ideal := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [pP_of_lt h']
    exact C.rows_mem (rowD_mem_rows m ⟨(k, l), h'⟩)
  · rw [pP_of_gt h']
    have := C.rows_mem (rowD_mem_rows m ⟨(l, k), h'⟩)
    convert this using 1
    simp only [rowD]
    ring

/-- `p_kl² z_kl w_kl = 1` in `ℂ(C)`. -/
theorem Curve.fn_dist {k l : Fin (n + 2)} (h : k ≠ l) :
    C.fn (pP k l) ^ 2 * C.fn (zP k - zP l) * C.fn (wP k - wP l) = 1 := by
  have h1 := (ACurve.fn_eq_fn_iff (C := C.toACurve) (g := 1)).mpr (C.dist_mem h)
  simp only [← ACurve.fnHom_apply, map_mul, map_pow, map_one] at h1 ⊢
  exact h1

theorem Curve.fn_pP_ne_zero {k l : Fin (n + 2)} (h : k ≠ l) : C.fn (pP k l) ≠ 0 := by
  intro h0
  have := C.fn_dist h
  rw [h0] at this
  simp at this

theorem Curve.fn_zsub_ne_zero {k l : Fin (n + 2)} (h : k ≠ l) : C.fn (zP k - zP l) ≠ 0 := by
  intro h0
  have := C.fn_dist h
  rw [h0, mul_zero, zero_mul] at this
  exact zero_ne_one this

theorem Curve.fn_wsub_ne_zero {k l : Fin (n + 2)} (h : k ≠ l) : C.fn (wP k - wP l) ≠ 0 := by
  intro h0
  have := C.fn_dist h
  rw [h0, mul_zero] at this
  exact zero_ne_one this

theorem Curve.fn_X_pc_ne_zero (e : Pair (n + 2)) : C.fn (X (pc e)) ≠ 0 := by
  rw [← pP_pair]
  exact C.fn_pP_ne_zero (ne_of_lt e.2)

/-- `2 ν(p_kl) + ν(z_kl) + ν(w_kl) = 0`. -/
theorem Curve.ordZ_dist (P : Place C.toACurve) {k l : Fin (n + 2)} (h : k ≠ l) :
    2 * ordZ P.ord (C.fn (pP k l)) + ordZ P.ord (C.fn (zP k - zP l)) + ordZ P.ord (C.fn (wP k - wP l)) = 0 := by
  have hp := C.fn_pP_ne_zero h
  have hz := C.fn_zsub_ne_zero h
  have hw := C.fn_wsub_ne_zero h
  have h1 := congrArg (ordZ P.ord) (C.fn_dist h)
  rw [ordZ_mul _ (mul_ne_zero (pow_ne_zero 2 hp) hz) hw, ordZ_mul _ (pow_ne_zero 2 hp) hz, ordZ_pow _ hp,
    ordZ_one] at h1
  linear_combination h1

/-- **`ν(p_kl) = 0` at a place that is not singular** (used in the proof of Lemma 2.6, `lem:balance`). -/
theorem Curve.v_pP_eq_zero_of_not_singular {P : Place C.toACurve} (hns : ¬ P.Singular) {k l : Fin (n + 2)}
    (h : k ≠ l) : P.v (pP k l) = 0 := by
  have hp := C.fn_pP_ne_zero h
  have hz := C.fn_zsub_ne_zero h
  have hw := C.fn_wsub_ne_zero h
  have hD := C.ordZ_dist P h
  set a := ordZ P.ord (C.fn (pP k l))
  set b := ordZ P.ord (C.fn (zP k - zP l))
  set c := ordZ P.ord (C.fn (wP k - wP l))
  have hZ := P.vZ_le_termZ h
  have hW := P.vW_le_termW h
  have hu := P.vZ_le_zsub k l
  have hv := P.vW_le_wsub k l
  rw [P.v_mul, P.v_pow, P.v_eq_ordZ hp, P.v_eq_ordZ hz] at hZ
  rw [P.v_mul, P.v_pow, P.v_eq_ordZ hp, P.v_eq_ordZ hw] at hW
  rw [P.v_eq_ordZ hz] at hu
  rw [P.v_eq_ordZ hw] at hv
  obtain ⟨nZ, hnZ⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hu)
  obtain ⟨nW, hnW⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hv)
  rw [← hnZ] at hZ hu
  rw [← hnW] at hW hv
  have hZ' : nZ ≤ 3 * a + b := by
    have : ((3 * a + b : ℤ) : WithTop ℤ) = 3 • (a : WithTop ℤ) + (b : WithTop ℤ) := by
      push_cast
      rfl
    rw [← this] at hZ
    exact_mod_cast hZ
  have hW' : nW ≤ 3 * a + c := by
    have : ((3 * a + c : ℤ) : WithTop ℤ) = 3 • (a : WithTop ℤ) + (c : WithTop ℤ) := by
      push_cast
      rfl
    rw [← this] at hW
    exact_mod_cast hW
  have hu' : nZ ≤ b := by exact_mod_cast hu
  have hv' : nW ≤ c := by exact_mod_cast hv
  have hns' : 0 ≤ nZ + nW := by
    unfold Place.Singular at hns
    rw [not_lt, ← hnZ, ← hnW] at hns
    exact_mod_cast hns
  have ha : a = 0 := by omega
  rw [P.v_eq_ordZ hp, show ordZ P.ord (C.fn (pP k l)) = 0 from ha]
  rfl

/-- `ν(p_e) = 0` at a place that is not singular, for the pairs `e`. -/
theorem Curve.ordZ_pc_eq_zero_of_not_singular {P : Place C.toACurve} (hns : ¬ P.Singular) (e : Pair (n + 2)) :
    ordZ P.ord (C.fn (X (pc e))) = 0 := by
  have h := C.v_pP_eq_zero_of_not_singular hns (ne_of_lt e.2)
  rw [pP_pair] at h
  rw [ordZ, show P.ord (C.fn (X (pc e))) = P.v (X (pc e)) from rfl, h]
  rfl

end curve

end

end CC6Full
