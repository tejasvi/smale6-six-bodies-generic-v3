import Lean6.Special.K4.E4.Final
import Lean6.Special.Comp.K4.E4.ExportRun
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# The Macaulay determinants of §7.2, exported

The runs `allF_*`, `allG_*` certify, for every pattern, that a selected square block of the Macaulay matrix of
`F_ε` (degree 7) or of `G_σ` (degree 8) is invertible modulo `p`; `macCheck_sound` turns this into "no common zero".
This module exports the determinants themselves, with the Macaulay matrices written for every mass vector
`μ ∈ ℂ⁴`.

**Conventions.** Rows of the matrix of `F_ε`: `r = 35 i + j` (`r < 245`) is `x^{α_j} F_{ε,i}`, where `F_{ε,i}` is
the `i`-th form of `Fcomp` (the forms `q_j² A_k − q_k² A_j` for the pairs `01, 02, 03, 12, 13, 23`, then
`Σ_k μ_k q_k³`) and `α_j = rowAlphaF r` is the `j`-th exponent vector of degree `4` in the order of
`Comp.E4.monos 4 4`; columns: `l < 120` is the monomial `q^{colMonoF l}`, the `l`-th exponent vector of degree `7` in
the order of `Comp.E4.monos 4 7`. For `G_σ`: rows `r = 15 k + j` (`r < 60`) are `ξ^{α_j} G_{σ,k}` (`Gcomp`, bodies
`k = 0, …, 3`, `ξ_1 = 0`, variables `ξ_2, ξ_3, ξ_4`), columns `l < 45` the monomials of degree `8` of
`Comp.E4.monos 3 8`.

* `macF ω μ e`, `macG μ σ`: the matrices, linear in `μ` (`Σ_k μ_k` times the unit-mass matrices of the checker).
* `macF_row`, `macG_row`: each row is the coefficient vector of its form, as an identity of functions of `q`.
* `macFpoly ω e`, `macGpoly σ` (entries in `MvPolynomial (Fin 4) ℂ`, the masses as variables; `ω` a parameter):
  `macFpoly_map_eval`, `macGpoly_map_eval`.
* `rowsF μl e`, `rowsG μl σ`: the rows selected by the checker; `macF_det_ne_zero_3_5_7_11`, `macF_det_ne_zero_1111`,
  `macG_det_ne_zero_3_5_7_11`, `macG_det_ne_zero_1111` (the determinants), and `macFpoly_det_ne_zero`,
  `macGpoly_det_ne_zero` (the determinant is a nonzero polynomial in the masses).
* `F_eq_zero_of_macF_det`, `G_eq_zero_of_macG_det`: at any `μ` where a selected determinant is nonzero, the forms have
  no common zero other than `0`.
-/

namespace Lean6.Special.K4.E4

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.E4 Matrix

/-! ## Values, entries, the checks -/

/-- The value of `a + b j ∈ ℤ[j]` at `j = ω`. -/
def zjVal (ω : ℂ) (x : ZJ) : ℂ := (x.1 : ℂ) + (x.2 : ℂ) * ω

theorem zjVal_eq_f {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (x : ZJ) : zjVal ω x = (zjHom ℂ ω hω).f x := rfl

theorem zjVal_zero (ω : ℂ) : zjVal ω (0, 0) = 0 := by simp [zjVal]

theorem zjVal_lin4 (ω : ℂ) (μ : List ℤ) (a0 a1 a2 a3 : ZJ) :
    zjVal ω (lin4 μ a0 a1 a2 a3) = (μ.getD 0 0 : ℂ) * zjVal ω a0 + (μ.getD 1 0 : ℂ) * zjVal ω a1 +
      (μ.getD 2 0 : ℂ) * zjVal ω a2 + (μ.getD 3 0 : ℂ) * zjVal ω a3 := by
  simp only [lin4, zjC, zjVal]
  push_cast
  ring

theorem lin4_fst (μ : List ℤ) (a0 a1 a2 a3 : ZJ) (h0 : a0.2 = 0) (h1 : a1.2 = 0) (h2 : a2.2 = 0) (h3 : a3.2 = 0) :
    (lin4 μ a0 a1 a2 a3).2 = 0 := by
  simp only [lin4, zjC, h0, h1, h2, h3]
  ring

theorem entA_toArr (A : List (List ZJ)) (r l : ℕ) : entA (toArr A) r l = ent A r l := by
  show ((A.map List.toArray).toArray.getD r #[]).getD l (0, 0) = (A.getD r []).getD l (0, 0)
  rw [toArray_getD (A.map List.toArray) r #[], getD_map_list List.toArray A [] #[] rfl r,
    toArray_getD (A.getD r []) l (0, 0)]

theorem linOK_sound {R C : ℕ} {μ : List ℤ} {A A0 A1 A2 A3 : List (List ZJ)}
    (h : linOK R C μ (toArr A) (toArr A0) (toArr A1) (toArr A2) (toArr A3) = true) {r l : ℕ} (hr : r < R)
    (hl : l < C) : ent A r l = lin4 μ (ent A0 r l) (ent A1 r l) (ent A2 r l) (ent A3 r l) := by
  simp only [linOK, List.all_eq_true, List.mem_range, beq_iff_eq, entA_toArr] at h
  exact h r hr l hl

theorem realOK_sound {R C : ℕ} {A : List (List ZJ)} (h : realOK R C (toArr A) = true) {r l : ℕ} (hr : r < R)
    (hl : l < C) : (ent A r l).2 = 0 := by
  simp only [realOK, List.all_eq_true, List.mem_range, beq_iff_eq, entA_toArr] at h
  exact h r hr l hl

theorem ent_of_length_le {A : List (List ZJ)} {r : ℕ} (hr : A.length ≤ r) (l : ℕ) : ent A r l = (0, 0) := by
  unfold ent
  rw [List.getD_eq_default _ _ hr]
  simp

/-- The rows of a passing `rowsOK` are the sums of their listed terms (at every point of `ℂ^ℕ`). -/
theorem rowsOK_sound {n D R : ℕ} {fs : List (Poly ZJ × ℕ)} (h : rowsOK n D R fs = true) :
    (macRows n D fs).length = R ∧ ∀ (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (x : ℕ → ℂ) (r : ℕ),
      Poly.eval (zjHom ℂ ω hω) x ((macRows n D fs).getD r []) =
        ∑ l ∈ Finset.range (monos n D).length, zjVal ω (ent (coeffMat n D fs) r l) *
          Mono.eval x ((monos n D).getD l []) 0 := by
  simp only [rowsOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  refine ⟨hlen, fun ω hω x r => ?_⟩
  set rows := macRows n D fs
  set A := rows.map (coeffVec (monos n D)) with hA
  have hAc : coeffMat n D fs = A := rfl
  rw [hAc]
  by_cases hr : r < rows.length
  · have hrA : r < A.length := by rw [hA, List.length_map]; exact hr
    have hmem : (rows[r], A[r]) ∈ rows.zip A := by
      rw [List.mem_iff_getElem]
      exact ⟨r, by simp [hr, hrA], by simp [List.getElem_zip]⟩
    have h1 := Poly.eqv_sound (zjHom ℂ ω hω) x (hall _ hmem)
    rw [List.getD_eq_getElem _ _ hr, h1, eval_expand]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [ent, List.getD_eq_getElem _ _ hrA]
    rfl
  · have hA0 : ∀ l, ent A r l = (0, 0) := ent_of_length_le (by rw [hA, List.length_map]; omega)
    rw [List.getD_eq_default _ _ (by omega)]
    simp [hA0, zjVal_zero]

/-! ## The rows of the Macaulay matrices -/

theorem getD_flatMap_block {α β : Type*} (g : α → List β) (L : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (g a).length = L) → ∀ (i j : ℕ), i < l.length → j < L → ∀ (a0 : α) (d : β),
      (l.flatMap g).getD (L * i + j) d = (g (l.getD i a0)).getD j d
  | [], _, i, j, hi, _, _, _ => by simp at hi
  | a :: l, hL, i, j, hi, hj, a0, d => by
    rw [List.flatMap_cons]
    have ha : (g a).length = L := hL a List.mem_cons_self
    cases i with
    | zero =>
      simp only [mul_zero, zero_add, List.getD_cons_zero]
      exact List.getD_append _ _ _ _ (by omega)
    | succ i =>
      rw [List.getD_append_right _ _ _ _ (by rw [ha]; nlinarith)]
      have e : L * (i + 1) + j - (g a).length = L * i + j := by rw [ha, Nat.mul_succ]; omega
      rw [e, List.getD_cons_succ]
      exact getD_flatMap_block g L l (fun b hb => hL b (List.mem_cons_of_mem _ hb)) i j
        (by simpa using hi) hj a0 d

/-- The row `B i + j` of the Macaulay rows of forms of one degree `d` is `x^{α_j} f_i`. -/
theorem macRows_getD (n D d : ℕ) (fs : List (Poly ZJ × ℕ)) (hd : ∀ f ∈ fs, f.2 = d) (i j : ℕ)
    (hi : i < fs.length) (hj : j < (monos n (D - d)).length) :
    (macRows n D fs).getD ((monos n (D - d)).length * i + j) [] =
      Poly.normalize zjC (Poly.mulTerm zjC zjC.one ((monos n (D - d)).getD j []) (fs.getD i ([], 0)).1) := by
  unfold macRows
  rw [getD_flatMap_block _ (monos n (D - d)).length fs (fun f hf => by simp [hd f hf]) i j hi hj ([], 0) []]
  have hf : (fs.getD i ([], 0)).2 = d := hd _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  rw [hf, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]

theorem eval_row (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (x : ℕ → ℂ) (α : Mono) (f : Poly ZJ) :
    Poly.eval (zjHom ℂ ω hω) x (Poly.normalize zjC (Poly.mulTerm zjC zjC.one α f)) =
      Mono.eval x α 0 * Poly.eval (zjHom ℂ ω hω) x f := by
  rw [Poly.eval_normalize, Poly.eval_mulTerm, (zjHom ℂ ω hω).map_one, one_mul]

/-- `q^m = ∏_i q_i^{m_i}`. -/
def qpow {n : ℕ} (q : Fin n → ℂ) (m : Fin n → ℕ) : ℂ := ∏ i, q i ^ m i

theorem mono_eval_xq4 (q : Fin 4 → ℂ) (m : Mono) (hm : m.length = 4) :
    Mono.eval (xq q) m 0 = qpow q fun i => m.getD i 0 := by
  match m, hm with
  | [a, b, c, d], _ => simp [Mono.eval, xq, qpow, Fin.prod_univ_four]; ring

theorem mono_eval_xq3 (q : Fin 3 → ℂ) (m : Mono) (hm : m.length = 3) :
    Mono.eval (xq q) m 0 = qpow q fun i => m.getD i 0 := by
  match m, hm with
  | [a, b, c], _ => simp [Mono.eval, xq, qpow, Fin.prod_univ_three]; ring

/-! ## The monomial facts -/

theorem monosOK_facts :
    (monos 4 7).length = 120 ∧ (monos 4 4).length = 35 ∧ (monos 3 8).length = 45 ∧ (monos 3 4).length = 15 ∧
      (∀ m ∈ monos 4 7, m.length = 4) ∧ (∀ m ∈ monos 4 4, m.length = 4) ∧ (∀ m ∈ monos 3 8, m.length = 3) ∧
      (∀ m ∈ monos 3 4, m.length = 3) ∧ (∀ k < 4, purePow 4 k 7 ∈ monos 4 7) ∧
      (∀ k < 3, purePow 3 k 8 ∈ monos 3 8) := by
  have h := monosOK_ok
  simp only [monosOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem len_getD_monos {n D L : ℕ} (hL : ∀ m ∈ monos n D, m.length = L) (l : ℕ) (hl : l < (monos n D).length) :
    ((monos n D).getD l []).length = L := by
  rw [List.getD_eq_getElem _ _ hl]
  exact hL _ (List.getElem_mem hl)

theorem getD_purePow (n k D i : ℕ) (hi : i < n) : (purePow n k D).getD i 0 = if i = k then D else 0 := by
  simp [purePow, List.getD_eq_getElem?_getD, hi]

/-! ## The determinant certified by `macCheck` -/

/-- **The determinant of the selected block** is nonzero over `ℂ` (with `j ↦ ω`) when `macCheck` passes. -/
theorem macCheck_det {n D p s : ℕ} {fs : List (Poly ZJ × ℕ)} (hp : 1 < p) (hs : (s * s + 3) % p = 0)
    (hc : macCheck n D p s fs = true) (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (Matrix.of fun i l : Fin (monos n D).length => zjVal ω (ent (coeffMat n D fs)
      ((selectRows p (monos n D).length (modMat p s (coeffMat n D fs))).getD i 0) l)).det ≠ 0 := by
  have : Fact (1 < p) := ⟨hp⟩
  have hp0 : 0 < p := by omega
  simp only [macCheck] at hc
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨-, hsize⟩, hver⟩, -⟩ := hc
  simp only [verifyInv, List.all_eq_true, beq_iff_eq] at hver
  have hAdef : coeffMat n D fs = (macRows n D fs).map (coeffVec (monos n D)) := rfl
  rw [hAdef]
  generalize hA : (macRows n D fs).map (coeffVec (monos n D)) = A at hver hsize ⊢
  generalize hAp : modMat p s A = Ap at hver hsize ⊢
  generalize hsel : selectRows p (monos n D).length Ap = sel at hver hsize ⊢
  generalize hAsub : sel.map (fun r => Ap.getD r #[]) = Asub at hver
  generalize hB : inverseMod p (monos n D).length Asub = B at hver
  set m := (monos n D).length with hm
  let aZ : Matrix (Fin m) (Fin m) (ℤ√(-3)) := fun i l => twoZ ((A.getD (sel.getD i 0) []).getD l (0, 0))
  let Mp : Matrix (Fin m) (Fin m) (ZMod p) := fun i l => (((Asub.getD i #[]).getD l 0 : ℕ) : ZMod p)
  let Bp : Matrix (Fin m) (Fin m) (ZMod p) := fun l j => (((B.getD l #[]).getD j 0 : ℕ) : ZMod p)
  have hAsub_entry : ∀ (i : Fin m) (l : ℕ),
      (Asub.getD i #[]).getD l 0 = toModS p s ((A.getD (sel.getD i 0) []).getD l (0, 0)) := by
    intro i l
    have hi : (i : ℕ) < sel.size := by rw [hsize]; exact i.2
    have e1 : Asub.getD i #[] = Ap.getD (sel.getD i 0) #[] := by
      rw [← hAsub]
      simp [Array.getD_eq_getD_getElem?, hi]
    rw [e1, ← hAp, modMat, getD_toArray_map _ A [] #[] (by simp)]
    exact getD_toArray_map _ _ (0, 0) 0 (toModS_zero p s) l
  have hMp : (phiP p s hs).mapMatrix aZ = Mp := by
    ext i l
    simp only [RingHom.mapMatrix_apply, aZ, Mp]
    rw [hAsub_entry]
    exact phiP_twoZ hp0 hs _
  have hMB : Mp * Bp = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hv := hver i (List.mem_range.mpr i.2) j (List.mem_range.mpr j.2)
    have hcast : ((dotIJ m Asub B i j : ℕ) : ZMod p) = if (i : ℕ) = j then 1 else 0 := by
      rw [← ZMod.natCast_mod, hv]
      split <;> simp
    rw [dotIJ, natCast_sum_range] at hcast
    simp only [Nat.cast_mul] at hcast
    simp only [Mp, Bp]
    rw [hcast]
    simp [Fin.ext_iff]
  have hdetP : Mp.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hMB
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetZ : aZ.det ≠ 0 := by
    intro h0
    apply hdetP
    rw [← hMp, ← RingHom.map_det, h0, map_zero]
  have hdetC : ((psiC ω hω).mapMatrix aZ).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    exact hdetZ (psiC_injective hω (h0.trans (map_zero _).symm))
  have hmat : (psiC ω hω).mapMatrix aZ =
      (2 : ℂ) • Matrix.of fun i l : Fin m => zjVal ω (ent A (sel.getD i 0) l) := by
    ext i l
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    show psiC ω hω (twoZ ((A.getD (sel.getD i 0) []).getD l (0, 0))) = _
    rw [psiC_twoZ hω]
    rfl
  rw [hmat, Matrix.det_smul] at hdetC
  intro h0
  apply hdetC
  rw [h0, mul_zero]

/-! ## The forms `F_ε` -/

/-- The seven forms `F_ε` at `q`, in the order of the checker: `q_j² A_k − q_k² A_j` for the pairs
`01, 02, 03, 12, 13, 23`, then `Σ_k μ_k q_k³`. -/
noncomputable def Fcomp (ω : ℂ) (μ : Fin 4 → ℂ) (e : Fin 4 → Fin 4 → ℕ) (q : Fin 4 → ℂ) : Fin 7 → ℂ :=
  ![q 0 ^ 2 * Aeps ω μ e q 1 - q 1 ^ 2 * Aeps ω μ e q 0, q 0 ^ 2 * Aeps ω μ e q 2 - q 2 ^ 2 * Aeps ω μ e q 0,
    q 0 ^ 2 * Aeps ω μ e q 3 - q 3 ^ 2 * Aeps ω μ e q 0, q 1 ^ 2 * Aeps ω μ e q 2 - q 2 ^ 2 * Aeps ω μ e q 1,
    q 1 ^ 2 * Aeps ω μ e q 3 - q 3 ^ 2 * Aeps ω μ e q 1, q 2 ^ 2 * Aeps ω μ e q 3 - q 3 ^ 2 * Aeps ω μ e q 2,
    ∑ k, μ k * q k ^ 3]

theorem Fcomp_of_FZero {ω : ℂ} {μ : Fin 4 → ℂ} {e : Fin 4 → Fin 4 → ℕ} {q : Fin 4 → ℂ} (hq : FZero ω μ e q)
    (i : Fin 7) : Fcomp ω μ e q i = 0 := by
  obtain ⟨hp, hc⟩ := hq
  fin_cases i
  · exact hp 0 1 (by decide)
  · exact hp 0 2 (by decide)
  · exact hp 0 3 (by decide)
  · exact hp 1 2 (by decide)
  · exact hp 1 3 (by decide)
  · exact hp 2 3 (by decide)
  · exact hc

/-- The unit mass vectors in `ℂ⁴`. -/
def unitC (k : Fin 4) : Fin 4 → ℂ := fun l => if l = k then 1 else 0

theorem muOf_unitL (k : Fin 4) : muOf (unitL k) = unitC k := by
  funext l
  fin_cases k <;> fin_cases l <;> simp [muOf, unitL, unitC]

theorem Fcomp_lin (ω : ℂ) (μ : Fin 4 → ℂ) (e : Fin 4 → Fin 4 → ℕ) (q : Fin 4 → ℂ) (i : Fin 7) :
    Fcomp ω μ e q i = ∑ k : Fin 4, μ k * Fcomp ω (unitC k) e q i := by
  fin_cases i <;> simp [Fcomp, Aeps, Fin.sum_univ_four, unitC] <;> ring

theorem eval_formsF_get {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (μl : List ℤ) (e : Fin 4 → Fin 4 → ℕ)
    (he : ∀ k l, e k l = e l k) (q : Fin 4 → ℂ) (i : Fin 7) :
    Poly.eval (zjHom ℂ ω hω) (xq q) ((formsF μl (vOf e)).getD i ([], 0)).1 = Fcomp ω (muOf μl) e q i := by
  have hA := eval_Apoly hω μl e he q
  have hP : ∀ j k : Fin 4,
      Poly.eval (zjHom ℂ ω hω) (xq q) (Poly.sub zjC (Poly.mulTerm zjC zjC.one (powMono j 2) (Apoly μl (vOf e) k))
        (Poly.mulTerm zjC zjC.one (powMono k 2) (Apoly μl (vOf e) j))) =
        q j ^ 2 * Aeps ω (muOf μl) e q k - q k ^ 2 * Aeps ω (muOf μl) e q j := by
    intro j k
    rw [Poly.eval_sub, Poly.eval_mulTerm, Poly.eval_mulTerm, (zjHom ℂ ω hω).map_one, eval_powMono,
      eval_powMono, hA, hA]
    simp only [xq, j.2, k.2, dite_true, one_mul]
  fin_cases i
  · exact hP 0 1
  · exact hP 0 2
  · exact hP 0 3
  · exact hP 1 2
  · exact hP 1 3
  · exact hP 2 3
  · show Poly.eval (zjHom ℂ ω hω) (xq q) ((List.range 4).map fun k => ((μl.getD k 0, 0), powMono k 3)) = _
    rw [range4]
    simp only [List.map_cons, List.map_nil, Poly.eval_cons, Poly.eval_nil, eval_mu, eval_powMono]
    simp [Fcomp, Fin.sum_univ_four, muOf, xq]
    ring

theorem formsF_deg (μl : List ℤ) (v : List ℕ) : ∀ f ∈ formsF μl v, f.2 = 3 := by
  intro f hf
  simp only [formsF, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem formsF_length (μl : List ℤ) (v : List ℕ) : (formsF μl v).length = 7 := by
  simp [formsF]

/-! ## The Macaulay matrix of `F_ε` -/

/-- The unit-mass coefficient matrices of `F_ε` (the checker's matrices at the masses `unitL k`). -/
def AF (k : Fin 4) (e : Fin 4 → Fin 4 → ℕ) : List (List ZJ) := coeffMat 4 7 (formsF (unitL k) (vOf e))

/-- **The Macaulay matrix of `F_ε` in degree 7** at masses `μ ∈ ℂ⁴`, `ε_{kl} = ω^{e_{kl}}`: rows `x^{α} F_{ε,i}`,
columns the monomials of degree 7 (conventions in the module docstring). -/
noncomputable def macF (ω : ℂ) (μ : Fin 4 → ℂ) (e : Fin 4 → Fin 4 → ℕ) : Matrix (Fin 245) (Fin 120) ℂ :=
  Matrix.of fun r l => ∑ k : Fin 4, μ k * zjVal ω (ent (AF k e) r l)

/-- The same with the masses as variables of `MvPolynomial (Fin 4) ℂ` (entries linear in the masses). -/
noncomputable def macFpoly (ω : ℂ) (e : Fin 4 → Fin 4 → ℕ) : Matrix (Fin 245) (Fin 120) (MvPolynomial (Fin 4) ℂ) :=
  Matrix.of fun r l => ∑ k : Fin 4, MvPolynomial.X k * MvPolynomial.C (zjVal ω (ent (AF k e) r l))

theorem macFpoly_map_eval (ω : ℂ) (μ : Fin 4 → ℂ) (e : Fin 4 → Fin 4 → ℕ) :
    (macFpoly ω e).map (MvPolynomial.eval μ) = macF ω μ e := by
  ext r l
  simp [macFpoly, macF, Matrix.map_apply, map_sum]

/-- The exponent vector of the monomial `l` of degree 7 (as a natural number index). -/
def colMonoN (l : ℕ) : Fin 4 → ℕ := fun i => ((monos 4 7).getD l []).getD i 0

/-- The exponent vector of the column `l` (degree 7). -/
def colMonoF (l : Fin 120) : Fin 4 → ℕ := colMonoN l

/-- The form of the row `r`. -/
def rowFormF (r : Fin 245) : Fin 7 := ⟨r / 35, by omega⟩

/-- The exponent vector of the multiplier of the row `r` (degree 4). -/
def rowAlphaF (r : Fin 245) : Fin 4 → ℕ := fun i => ((monos 4 4).getD (r % 35) []).getD i 0

theorem exportF_at (e : Fin 4 → Fin 4 → ℕ) : exportF [[3, 5, 7, 11], [1, 1, 1, 1]] (vOf e) = true :=
  List.all_eq_true.mp exportF_ok _ (vOf_mem e)

theorem rowsOK_F (e : Fin 4 → Fin 4 → ℕ) (k : Fin 4) : rowsOK 4 7 245 (formsF (unitL k) (vOf e)) = true := by
  have h := exportF_at e
  simp only [exportF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩ := h
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- **The rows of `macF`**: the row `r` is the coefficient vector of `x^{α_r} F_{ε, i_r}`. -/
theorem macF_row (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (μ : Fin 4 → ℂ) (e : Fin 4 → Fin 4 → ℕ)
    (he : ∀ k l, e k l = e l k) (q : Fin 4 → ℂ) (r : Fin 245) :
    ∑ l : Fin 120, macF ω μ e r l * qpow q (colMonoF l) = qpow q (rowAlphaF r) * Fcomp ω μ e q (rowFormF r) := by
  obtain ⟨h120, h35, -, -, hl7, hl4, -, -, -, -⟩ := monosOK_facts
  have hunit : ∀ k : Fin 4, ∑ l : Fin 120, zjVal ω (ent (AF k e) r l) * qpow q (colMonoF l) =
      qpow q (rowAlphaF r) * Fcomp ω (unitC k) e q (rowFormF r) := by
    intro k
    obtain ⟨-, hrows⟩ := rowsOK_sound (rowsOK_F e k)
    have hsum := hrows ω hω (xq q) r
    rw [h120] at hsum
    have hr : (r : ℕ) = (monos 4 (7 - 3)).length * (r / 35) + r % 35 := by
      rw [show 7 - 3 = 4 by rfl, h35]; omega
    rw [hr, macRows_getD 4 7 3 _ (formsF_deg _ _) _ _ (by rw [formsF_length]; omega)
      (by rw [show 7 - 3 = 4 by rfl, h35]; omega), eval_row] at hsum
    have hf := eval_formsF_get hω (unitL k) e he q ⟨r / 35, by omega⟩
    rw [muOf_unitL] at hf
    simp only at hf
    rw [hf] at hsum
    rw [← hr] at hsum
    rw [show (∑ l : Fin 120, zjVal ω (ent (AF k e) r l) * qpow q (colMonoF l)) =
        ∑ l : Fin 120, zjVal ω (ent (AF k e) r (l : ℕ)) * qpow q (colMonoN l) from rfl,
      Fin.sum_univ_eq_sum_range (fun l => zjVal ω (ent (AF k e) r l) * qpow q (colMonoN l)) 120]
    have hcol : ∀ l ∈ Finset.range 120, zjVal ω (ent (AF k e) r l) * qpow q (colMonoN l) =
        zjVal ω (ent (coeffMat 4 7 (formsF (unitL k) (vOf e))) r l) * Mono.eval (xq q) ((monos 4 7).getD l []) 0 := by
      intro l hl
      rw [Finset.mem_range] at hl
      have hlen := len_getD_monos hl7 l (by rw [h120]; exact hl)
      rw [mono_eval_xq4 q _ hlen]
      rfl
    rw [Finset.sum_congr rfl hcol, ← hsum, mono_eval_xq4 q _ (len_getD_monos hl4 _ (by rw [h35]; omega))]
    rfl
  calc ∑ l : Fin 120, macF ω μ e r l * qpow q (colMonoF l)
      = ∑ k : Fin 4, μ k * ∑ l : Fin 120, zjVal ω (ent (AF k e) r l) * qpow q (colMonoF l) := by
        simp only [macF, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = qpow q (rowAlphaF r) * Fcomp ω μ e q (rowFormF r) := by
        simp only [hunit]
        rw [Fcomp_lin ω μ e q (rowFormF r), Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

/-- **The transfer**: at any `μ` where the block of `macF` on some rows has a nonzero determinant, the forms `F_ε` have
no common zero in `ℂ⁴` other than `0`. -/
theorem F_eq_zero_of_macF_det (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (μ : Fin 4 → ℂ) (e : Fin 4 → Fin 4 → ℕ)
    (he : ∀ k l, e k l = e l k) (rows : Fin 120 → Fin 245) (hdet : ((macF ω μ e).submatrix rows id).det ≠ 0)
    (q : Fin 4 → ℂ) (hq : FZero ω μ e q) : q = 0 := by
  obtain ⟨h120, -, -, -, hl7, -, -, -, hpure, -⟩ := monosOK_facts
  let v : Fin 120 → ℂ := fun l => qpow q (colMonoF l)
  have hMv : (macF ω μ e).submatrix rows id *ᵥ v = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Pi.zero_apply, v]
    rw [macF_row ω hω μ e he q (rows i), Fcomp_of_FZero hq, mul_zero]
  have hv0 : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hMv
  funext k
  obtain ⟨l, hl, hle⟩ := List.mem_iff_getElem.mp (hpure k k.2)
  have hvl := congrFun hv0 ⟨l, by rw [← h120]; exact hl⟩
  simp only [v, Pi.zero_apply, colMonoF, colMonoN, qpow] at hvl
  rw [List.getD_eq_getElem _ _ hl, hle] at hvl
  have hprod : ∏ i : Fin 4, q i ^ (purePow 4 k 7).getD i 0 = q k ^ 7 := by
    rw [Finset.prod_eq_single k]
    · rw [getD_purePow 4 k 7 k k.2, if_pos rfl]
    · intro b _ hb
      rw [getD_purePow 4 k 7 b b.2, if_neg (fun h => hb (Fin.ext h)), pow_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [hprod] at hvl
  simpa using pow_eq_zero_iff (n := 7) (by norm_num) |>.mp hvl

/-! ## The determinants of `F_ε` at `μ₀` and at `(1, 1, 1, 1)` -/

/-- The rows selected by the checker for the masses `μl`. -/
def selF (μl : List ℤ) (e : Fin 4 → Fin 4 → ℕ) : Array ℕ :=
  selectRows pE (monos 4 7).length (modMat pE sE (coeffMat 4 7 (formsF μl (vOf e))))

/-- The selected rows, as indices of `macF` (`% 245` only keeps the type; the proofs show the indices are `< 245`). -/
def rowsF (μl : List ℤ) (e : Fin 4 → Fin 4 → ℕ) : Fin 120 → Fin 245 :=
  fun i => ⟨(selF μl e).getD i 0 % 245, Nat.mod_lt _ (by norm_num)⟩

theorem det_macF_of {μl : List ℤ} (hc : allF μl pE sE = true) (hmem : μl ∈ [[3, 5, 7, 11], [1, 1, 1, 1]])
    (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (e : Fin 4 → Fin 4 → ℕ) :
    ((macF ω (muOf μl) e).submatrix (rowsF μl e) id).det ≠ 0 := by
  obtain ⟨h120, -, -, -, -, -, -, -, -, -⟩ := monosOK_facts
  have hcheck : macCheck 4 7 pE sE (formsF μl (vOf e)) = true := List.all_eq_true.mp hc _ (vOf_mem e)
  have hdet := macCheck_det (by norm_num) sE_sq hcheck ω hω
  -- the export facts at `μl`
  have hex := exportF_at e
  simp only [exportF, Bool.and_eq_true, List.all_eq_true] at hex
  obtain ⟨-, hμ⟩ := hex
  have hμl := hμ μl hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hμl
  obtain ⟨hlen, hlin⟩ := hμl
  set A := coeffMat 4 7 (formsF μl (vOf e)) with hA
  set sel := selF μl e with hsel
  -- transport to `Fin 120`
  let M : Matrix (Fin (monos 4 7).length) (Fin (monos 4 7).length) ℂ :=
    Matrix.of fun i l => zjVal ω (ent A (sel.getD i 0) l)
  have hM : M.det ≠ 0 := hdet
  let M' : Matrix (Fin 120) (Fin 120) ℂ := Matrix.reindex (finCongr h120) (finCongr h120) M
  have hM' : M'.det ≠ 0 := by rw [Matrix.det_reindex_self]; exact hM
  -- every selected row is a row of `A`
  have hin : ∀ i : Fin 120, sel.getD i 0 < 245 := by
    intro i
    by_contra hge
    apply hM'
    refine Matrix.det_eq_zero_of_row_eq_zero i fun l => ?_
    simp only [M', M, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, finCongr_symm,
      finCongr_apply, Fin.val_cast]
    rw [ent_of_length_le (by rw [hlen]; omega), zjVal_zero]
  -- the entries
  have hent : (macF ω (muOf μl) e).submatrix (rowsF μl e) id = M' := by
    ext i l
    simp only [M', M, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, finCongr_symm,
      finCongr_apply, Fin.val_cast, id, rowsF, macF]
    have hi := hin i
    rw [← hsel, Nat.mod_eq_of_lt hi, linOK_sound hlin hi l.2, zjVal_lin4, Fin.sum_univ_four]
    simp only [muOf, AF]
    rfl
  rw [hent]
  exact hM'

theorem muOf_3_5_7_11 : muOf [3, 5, 7, 11] = ![3, 5, 7, 11] := by
  funext k; fin_cases k <;> simp [muOf]

theorem muOf_1111 : muOf [1, 1, 1, 1] = fun _ => 1 := by
  funext k; fin_cases k <;> simp [muOf]

/-- **The determinant at `μ₀ = (3, 5, 7, 11)`**: for every pattern, the block of `macF` on the rows selected by the
checker has a nonzero determinant. -/
theorem macF_det_ne_zero_3_5_7_11 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (e : Fin 4 → Fin 4 → ℕ) :
    ((macF ω ![3, 5, 7, 11] e).submatrix (rowsF [3, 5, 7, 11] e) id).det ≠ 0 := by
  rw [← muOf_3_5_7_11]
  exact det_macF_of allF_3_5_7_11 (by simp) ω hω e

/-- **The determinant at `(1, 1, 1, 1)`.** -/
theorem macF_det_ne_zero_1111 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (e : Fin 4 → Fin 4 → ℕ) :
    ((macF ω (fun _ => 1) e).submatrix (rowsF [1, 1, 1, 1] e) id).det ≠ 0 := by
  rw [← muOf_1111]
  exact det_macF_of allF_1111 (by simp) ω hω e

theorem exists_macF_det_ne_zero_3_5_7_11 (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (e : Fin 4 → Fin 4 → ℕ) :
    ∃ rows : Fin 120 → Fin 245, ((macF ω ![3, 5, 7, 11] e).submatrix rows id).det ≠ 0 :=
  ⟨_, macF_det_ne_zero_3_5_7_11 ω hω e⟩

/-- **The determinant is a nonzero polynomial in the masses**: its value at `μ₀` is the determinant of
`macF_det_ne_zero_3_5_7_11`. -/
theorem macFpoly_det_ne_zero (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (e : Fin 4 → Fin 4 → ℕ) :
    ((macFpoly ω e).submatrix (rowsF [3, 5, 7, 11] e) id).det ≠ 0 := by
  intro h0
  apply macF_det_ne_zero_3_5_7_11 ω hω e
  have := congrArg (MvPolynomial.eval (![3, 5, 7, 11] : Fin 4 → ℂ)) h0
  rw [map_zero, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, macFpoly_map_eval] at this
  exact this

/-! ## The forms `G_σ` -/

/-- A primitive cube root of unity in `ℂ` (the forms `G_σ` have integer coefficients; the checker's arithmetic is in
`ℤ[j]`, so one value of `j` is fixed to read the matrices of `G_σ` over `ℂ`). -/
noncomputable def omega0 : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

theorem omega0_root : omega0 ^ 2 + omega0 + 1 = 0 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp [omega0, sq]
    linear_combination (-1 / 4 : ℝ) * h3
  · simp [omega0, sq]
    ring

/-- The four forms `G_σ` at `ξ = (ξ_2, ξ_3, ξ_4)` (with `ξ_1 = 0`), in the order of the bodies. -/
noncomputable def Gcomp (μ : Fin 4 → ℂ) (σ : Fin 4 → Fin 4 → ℤ) (ξ : Fin 3 → ℂ) (k : Fin 4) : ℂ :=
  Gsig μ σ ![0, ξ 0, ξ 1, ξ 2] k

theorem Gcomp_lin (μ : Fin 4 → ℂ) (σ : Fin 4 → Fin 4 → ℤ) (ξ : Fin 3 → ℂ) (k : Fin 4) :
    Gcomp μ σ ξ k = ∑ k' : Fin 4, μ k' * Gcomp (unitC k') σ ξ k := by
  fin_cases k <;> simp [Gcomp, Gsig, Fin.sum_univ_four, unitC] <;> ring

theorem formsG_getD (μl : List ℤ) (w : List ℤ) (k : ℕ) (hk : k < 4) :
    (formsG μl w).getD k ([], 0) = (Gform μl w k, 4) := by
  rw [List.getD_eq_getElem _ _ (by simpa [formsG] using hk)]
  simp [formsG]

theorem eval_formsG_get {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (μl : List ℤ) (σ : Fin 4 → Fin 4 → ℤ)
    (hσ : ∀ k l, σ l k = -σ k l) (ξ : Fin 3 → ℂ) (k : Fin 4) :
    Poly.eval (zjHom ℂ ω hω) (xq ξ) ((formsG μl (wOf σ)).getD k ([], 0)).1 = Gcomp (muOf μl) σ ξ k := by
  rw [formsG_getD _ _ k k.2]
  exact eval_Gform hω μl σ hσ ξ k

theorem formsG_deg (μl : List ℤ) (w : List ℤ) : ∀ f ∈ formsG μl w, f.2 = 4 := by
  intro f hf
  simp only [formsG, List.mem_map] at hf
  obtain ⟨k, -, rfl⟩ := hf
  rfl

theorem formsG_length (μl : List ℤ) (w : List ℤ) : (formsG μl w).length = 4 := by
  simp [formsG]

/-! ## The Macaulay matrix of `G_σ` -/

/-- The unit-mass coefficient matrices of `G_σ`. -/
def AG (k : Fin 4) (σ : Fin 4 → Fin 4 → ℤ) : List (List ZJ) := coeffMat 3 8 (formsG (unitL k) (wOf σ))

/-- **The Macaulay matrix of `G_σ` in degree 8** at masses `μ ∈ ℂ⁴` (integer entries for integer masses). -/
noncomputable def macG (μ : Fin 4 → ℂ) (σ : Fin 4 → Fin 4 → ℤ) : Matrix (Fin 60) (Fin 45) ℂ :=
  Matrix.of fun r l => ∑ k : Fin 4, μ k * ((ent (AG k σ) r l).1 : ℂ)

/-- The same with the masses as variables of `MvPolynomial (Fin 4) ℂ`. -/
noncomputable def macGpoly (σ : Fin 4 → Fin 4 → ℤ) : Matrix (Fin 60) (Fin 45) (MvPolynomial (Fin 4) ℂ) :=
  Matrix.of fun r l => ∑ k : Fin 4, MvPolynomial.X k * MvPolynomial.C (((ent (AG k σ) r l).1 : ℤ) : ℂ)

theorem macGpoly_map_eval (μ : Fin 4 → ℂ) (σ : Fin 4 → Fin 4 → ℤ) :
    (macGpoly σ).map (MvPolynomial.eval μ) = macG μ σ := by
  ext r l
  simp [macGpoly, macG, Matrix.map_apply, map_sum]

/-- The exponent vector of the monomial `l` of degree 8 in three variables (natural number index). -/
def colMonoGN (l : ℕ) : Fin 3 → ℕ := fun i => ((monos 3 8).getD l []).getD i 0

/-- The exponent vector of the column `l` of `macG`. -/
def colMonoG (l : Fin 45) : Fin 3 → ℕ := colMonoGN l

/-- The body (form) of the row `r` of `macG`. -/
def rowFormG (r : Fin 60) : Fin 4 := ⟨r / 15, by omega⟩

/-- The exponent vector of the multiplier of the row `r` of `macG` (degree 4). -/
def rowAlphaG (r : Fin 60) : Fin 3 → ℕ := fun i => ((monos 3 4).getD (r % 15) []).getD i 0

theorem exportG_at (σ : Fin 4 → Fin 4 → ℤ) (hσs : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) :
    exportG [[3, 5, 7, 11], [1, 1, 1, 1]] (wOf σ) = true :=
  List.all_eq_true.mp exportG_ok _ (wOf_mem σ hσs)

theorem rowsOK_G (σ : Fin 4 → Fin 4 → ℤ) (hσs : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) (k : Fin 4) :
    rowsOK 3 8 60 (formsG (unitL k) (wOf σ)) = true ∧
      realOK 60 45 (toArr (coeffMat 3 8 (formsG (unitL k) (wOf σ)))) = true := by
  have h := exportG_at σ hσs
  simp only [exportG, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, r0⟩, r1⟩, r2⟩, r3⟩, -⟩ := h
  fin_cases k
  · exact ⟨h0, r0⟩
  · exact ⟨h1, r1⟩
  · exact ⟨h2, r2⟩
  · exact ⟨h3, r3⟩

/-- **The rows of `macG`**: the row `r` is the coefficient vector of `ξ^{α_r} G_{σ, k_r}`. -/
theorem macG_row (μ : Fin 4 → ℂ) (σ : Fin 4 → Fin 4 → ℤ) (hσa : ∀ k l, σ l k = -σ k l)
    (hσs : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) (ξ : Fin 3 → ℂ) (r : Fin 60) :
    ∑ l : Fin 45, macG μ σ r l * qpow ξ (colMonoG l) = qpow ξ (rowAlphaG r) * Gcomp μ σ ξ (rowFormG r) := by
  obtain ⟨-, -, h45, h15, -, -, hl8, hl4, -, -⟩ := monosOK_facts
  have hunit : ∀ k : Fin 4, ∑ l : Fin 45, ((ent (AG k σ) r l).1 : ℂ) * qpow ξ (colMonoG l) =
      qpow ξ (rowAlphaG r) * Gcomp (unitC k) σ ξ (rowFormG r) := by
    intro k
    obtain ⟨hrk, hreal⟩ := rowsOK_G σ hσs k
    obtain ⟨-, hrows⟩ := rowsOK_sound hrk
    have hsum := hrows omega0 omega0_root (xq ξ) r
    rw [h45] at hsum
    have hr : (r : ℕ) = (monos 3 (8 - 4)).length * (r / 15) + r % 15 := by
      rw [show 8 - 4 = 4 by rfl, h15]; omega
    rw [hr, macRows_getD 3 8 4 _ (formsG_deg _ _) _ _ (by rw [formsG_length]; omega)
      (by rw [show 8 - 4 = 4 by rfl, h15]; omega), eval_row] at hsum
    have hf := eval_formsG_get omega0_root (unitL k) σ hσa ξ ⟨r / 15, by omega⟩
    rw [muOf_unitL] at hf
    simp only at hf
    rw [hf, ← hr] at hsum
    rw [show (∑ l : Fin 45, ((ent (AG k σ) r l).1 : ℂ) * qpow ξ (colMonoG l)) =
        ∑ l : Fin 45, ((ent (AG k σ) r (l : ℕ)).1 : ℂ) * qpow ξ (colMonoGN l) from rfl,
      Fin.sum_univ_eq_sum_range (fun l => ((ent (AG k σ) r l).1 : ℂ) * qpow ξ (colMonoGN l)) 45]
    have hcol : ∀ l ∈ Finset.range 45, ((ent (AG k σ) r l).1 : ℂ) * qpow ξ (colMonoGN l) =
        zjVal omega0 (ent (coeffMat 3 8 (formsG (unitL k) (wOf σ))) r l) *
          Mono.eval (xq ξ) ((monos 3 8).getD l []) 0 := by
      intro l hl
      rw [Finset.mem_range] at hl
      have hlen := len_getD_monos hl8 l (by rw [h45]; exact hl)
      rw [mono_eval_xq3 ξ _ hlen]
      have h2 : (ent (coeffMat 3 8 (formsG (unitL k) (wOf σ))) r l).2 = 0 := realOK_sound hreal r.2 hl
      show ((ent (coeffMat 3 8 (formsG (unitL k) (wOf σ))) r l).1 : ℂ) * qpow ξ (colMonoGN l) =
        (((ent (coeffMat 3 8 (formsG (unitL k) (wOf σ))) r l).1 : ℂ) +
          ((ent (coeffMat 3 8 (formsG (unitL k) (wOf σ))) r l).2 : ℂ) * omega0) *
          qpow ξ (fun i => ((monos 3 8).getD l []).getD i 0)
      rw [h2, Int.cast_zero, zero_mul, add_zero]
      rfl
    rw [Finset.sum_congr rfl hcol, ← hsum, mono_eval_xq3 ξ _ (len_getD_monos hl4 _ (by rw [h15]; omega))]
    rfl
  calc ∑ l : Fin 45, macG μ σ r l * qpow ξ (colMonoG l)
      = ∑ k : Fin 4, μ k * ∑ l : Fin 45, ((ent (AG k σ) r l).1 : ℂ) * qpow ξ (colMonoG l) := by
        simp only [macG, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = qpow ξ (rowAlphaG r) * Gcomp μ σ ξ (rowFormG r) := by
        simp only [hunit]
        rw [Gcomp_lin μ σ ξ (rowFormG r), Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

/-- **The transfer for `G_σ`**: at any `μ` where the block of `macG` on some rows has a nonzero determinant, the forms
`G_σ` have no common zero in `ℂ³` other than `0`. -/
theorem G_eq_zero_of_macG_det (μ : Fin 4 → ℂ) (σ : Fin 4 → Fin 4 → ℤ) (hσa : ∀ k l, σ l k = -σ k l)
    (hσs : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) (rows : Fin 45 → Fin 60)
    (hdet : ((macG μ σ).submatrix rows id).det ≠ 0) (ξ : Fin 3 → ℂ) (hξ : GZero μ σ ξ) : ξ = 0 := by
  obtain ⟨-, -, h45, -, -, -, hl8, -, -, hpure⟩ := monosOK_facts
  let v : Fin 45 → ℂ := fun l => qpow ξ (colMonoG l)
  have hMv : (macG μ σ).submatrix rows id *ᵥ v = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Pi.zero_apply, v]
    rw [macG_row μ σ hσa hσs ξ (rows i)]
    simp only [Gcomp]
    rw [hξ, mul_zero]
  have hv0 : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hMv
  funext k
  obtain ⟨l, hl, hle⟩ := List.mem_iff_getElem.mp (hpure k k.2)
  have hvl := congrFun hv0 ⟨l, by rw [← h45]; exact hl⟩
  simp only [v, Pi.zero_apply, colMonoG, colMonoGN, qpow] at hvl
  rw [List.getD_eq_getElem _ _ hl, hle] at hvl
  have hprod : ∏ i : Fin 3, ξ i ^ (purePow 3 k 8).getD i 0 = ξ k ^ 8 := by
    rw [Finset.prod_eq_single k]
    · rw [getD_purePow 3 k 8 k k.2, if_pos rfl]
    · intro b _ hb
      rw [getD_purePow 3 k 8 b b.2, if_neg (fun h => hb (Fin.ext h)), pow_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [hprod] at hvl
  simpa using pow_eq_zero_iff (n := 8) (by norm_num) |>.mp hvl

/-! ## The determinants of `G_σ` at `μ₀` and at `(1, 1, 1, 1)` -/

/-- The rows selected by the checker for `G_σ` at the masses `μl`. -/
def selG (μl : List ℤ) (σ : Fin 4 → Fin 4 → ℤ) : Array ℕ :=
  selectRows pE (monos 3 8).length (modMat pE sE (coeffMat 3 8 (formsG μl (wOf σ))))

/-- The selected rows, as indices of `macG` (`% 60` only keeps the type; the proofs show the indices are `< 60`). -/
def rowsG (μl : List ℤ) (σ : Fin 4 → Fin 4 → ℤ) : Fin 45 → Fin 60 :=
  fun i => ⟨(selG μl σ).getD i 0 % 60, Nat.mod_lt _ (by norm_num)⟩

theorem det_macG_of {μl : List ℤ} (hc : allG μl pE sE = true) (hmem : μl ∈ [[3, 5, 7, 11], [1, 1, 1, 1]])
    (σ : Fin 4 → Fin 4 → ℤ) (hσs : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) :
    ((macG (muOf μl) σ).submatrix (rowsG μl σ) id).det ≠ 0 := by
  obtain ⟨-, -, h45, -, -, -, -, -, -, -⟩ := monosOK_facts
  have hcheck : macCheck 3 8 pE sE (formsG μl (wOf σ)) = true := List.all_eq_true.mp hc _ (wOf_mem σ hσs)
  have hdet := macCheck_det (by norm_num) sE_sq hcheck omega0 omega0_root
  have hex := exportG_at σ hσs
  simp only [exportG, Bool.and_eq_true, List.all_eq_true] at hex
  obtain ⟨⟨⟨⟨⟨-, r0⟩, r1⟩, r2⟩, r3⟩, hμ⟩ := hex
  have hμl := hμ μl hmem
  simp only [Bool.and_eq_true, beq_iff_eq] at hμl
  obtain ⟨hlen, hlin⟩ := hμl
  set A := coeffMat 3 8 (formsG μl (wOf σ)) with hA
  set sel := selG μl σ with hsel
  let M : Matrix (Fin (monos 3 8).length) (Fin (monos 3 8).length) ℂ :=
    Matrix.of fun i l => zjVal omega0 (ent A (sel.getD i 0) l)
  have hM : M.det ≠ 0 := hdet
  let M' : Matrix (Fin 45) (Fin 45) ℂ := Matrix.reindex (finCongr h45) (finCongr h45) M
  have hM' : M'.det ≠ 0 := by rw [Matrix.det_reindex_self]; exact hM
  have hin : ∀ i : Fin 45, sel.getD i 0 < 60 := by
    intro i
    by_contra hge
    apply hM'
    refine Matrix.det_eq_zero_of_row_eq_zero i fun l => ?_
    simp only [M', M, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, finCongr_symm,
      finCongr_apply, Fin.val_cast]
    rw [ent_of_length_le (by rw [hlen]; omega), zjVal_zero]
  have hent : (macG (muOf μl) σ).submatrix (rowsG μl σ) id = M' := by
    ext i l
    simp only [M', M, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, finCongr_symm,
      finCongr_apply, Fin.val_cast, id, rowsG, macG]
    have hi := hin i
    have hre : ∀ B : List (List ZJ), realOK 60 45 (toArr B) = true →
        zjVal omega0 (ent B (sel.getD i 0) l) = ((ent B (sel.getD i 0) l).1 : ℂ) := by
      intro B hB
      have h2 := realOK_sound hB hi l.2
      simp only [zjVal, h2, Int.cast_zero, zero_mul, add_zero]
    rw [← hsel, Nat.mod_eq_of_lt hi, linOK_sound hlin hi l.2, zjVal_lin4, hre _ r0, hre _ r1, hre _ r2, hre _ r3,
      Fin.sum_univ_four]
    simp only [muOf, AG]
    rfl
  rw [hent]
  exact hM'

/-- **The determinant of `G_σ` at `μ₀ = (3, 5, 7, 11)`.** -/
theorem macG_det_ne_zero_3_5_7_11 (σ : Fin 4 → Fin 4 → ℤ) (hσs : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) :
    ((macG ![3, 5, 7, 11] σ).submatrix (rowsG [3, 5, 7, 11] σ) id).det ≠ 0 := by
  rw [← muOf_3_5_7_11]
  exact det_macG_of allG_3_5_7_11 (by simp) σ hσs

/-- **The determinant of `G_σ` at `(1, 1, 1, 1)`.** -/
theorem macG_det_ne_zero_1111 (σ : Fin 4 → Fin 4 → ℤ) (hσs : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) :
    ((macG (fun _ => 1) σ).submatrix (rowsG [1, 1, 1, 1] σ) id).det ≠ 0 := by
  rw [← muOf_1111]
  exact det_macG_of allG_1111 (by simp) σ hσs

theorem exists_macG_det_ne_zero_3_5_7_11 (σ : Fin 4 → Fin 4 → ℤ)
    (hσs : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) :
    ∃ rows : Fin 45 → Fin 60, ((macG ![3, 5, 7, 11] σ).submatrix rows id).det ≠ 0 :=
  ⟨_, macG_det_ne_zero_3_5_7_11 σ hσs⟩

/-- **The determinant of `G_σ` is a nonzero polynomial in the masses.** -/
theorem macGpoly_det_ne_zero (σ : Fin 4 → Fin 4 → ℤ) (hσs : ∀ k l : Fin 4, k ≠ l → σ k l = 1 ∨ σ k l = -1) :
    ((macGpoly σ).submatrix (rowsG [3, 5, 7, 11] σ) id).det ≠ 0 := by
  intro h0
  apply macG_det_ne_zero_3_5_7_11 σ hσs
  have := congrArg (MvPolynomial.eval (![3, 5, 7, 11] : Fin 4 → ℂ)) h0
  rw [map_zero, RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, macGpoly_map_eval] at this
  exact this

end Lean6.Special.K4.E4
