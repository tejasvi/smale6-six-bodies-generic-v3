import Lean6.Special.Comp.K4.E4.Mac
import Lean6.Special.Poly.Sem
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.List.GetD

/-!
# Soundness of the Macaulay check

**`macCheck_sound`**: if `macCheck n D p s fs = true` with `p > 1` and `s² ≡ −3 (mod p)`, then for every `ω ∈ ℂ` with
`ω² + ω + 1 = 0` (that is, `j ↦ ω`), every common zero `x` over `ℂ` of the forms `fs` has `x_k = 0` for `k < n`.

The proof follows the paper's argument after Proposition 7.8. Write each coefficient `a + b j` of the selected square
block as `2(a + b j) = (2a − b) + b √−3 ∈ ℤ√−3`. Its images under `√−3 ↦ s` in `ZMod p` and under `√−3 ↦ 2ω + 1` in
`ℂ` are the matrices of the check and of the rows over `ℂ`. The block has an inverse modulo `p`, so its determinant
in `ℤ√−3` is nonzero; `ℤ√−3 → ℂ` is injective, so the block is invertible over `ℂ`. Each selected row is
`x^α f_i`, so at a common zero the block kills the vector of the monomials of degree `D`; hence that vector is `0`,
and so is each `x_k`, since `x_k^D` is one of these monomials.
-/

namespace Lean6.Special.K4.E4

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.E4 Matrix

/-! ## Lists -/

theorem natCast_sum_range {R : Type*} [CommSemiring R] (g : ℕ → ℕ) :
    ∀ m : ℕ, ((((List.range m).map g).sum : ℕ) : R) = ∑ l : Fin m, (g l : R)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, Nat.cast_add, natCast_sum_range g m,
      Fin.sum_univ_castSucc]
    simp

theorem toArray_getD {α : Type*} (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_map_list {α β : Type*} (f : α → β) (l : List α) (d : α) (e : β) (hd : f d = e) (i : ℕ) :
    (l.map f).getD i e = f (l.getD i d) := by
  rw [← hd, List.getD_map]

theorem getD_toArray_map {α β : Type*} (f : α → β) (l : List α) (d : α) (e : β) (hd : f d = e) (i : ℕ) :
    (l.map f).toArray.getD i e = f (l.getD i d) := by
  rw [toArray_getD, getD_map_list f l d e hd]

/-! ## The rings -/

/-- `√−3 ↦ 2ω + 1` in `ℂ`. -/
noncomputable def psiC (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : ℤ√(-3) →+* ℂ :=
  Zsqrtd.lift ⟨2 * ω + 1, by push_cast; linear_combination 4 * hω⟩

/-- `√−3 ↦ s` in `ZMod p`. -/
def phiP (p s : ℕ) (hs : (s * s + 3) % p = 0) : ℤ√(-3) →+* ZMod p :=
  Zsqrtd.lift ⟨(s : ZMod p), by
    have h : ((s * s + 3 : ℕ) : ZMod p) = 0 := by rw [← ZMod.natCast_mod, hs, Nat.cast_zero]
    push_cast at h ⊢
    linear_combination h⟩

/-- `2(a + b j) = (2a − b) + b √−3`. -/
def twoZ (x : ZJ) : ℤ√(-3) := ⟨2 * x.1 - x.2, x.2⟩

theorem psiC_twoZ {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (x : ZJ) :
    psiC ω hω (twoZ x) = 2 * (zjHom ℂ ω hω).f x := by
  simp only [psiC, Zsqrtd.lift_apply_apply, twoZ, zjHom]
  push_cast
  ring

theorem psiC_injective {ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) : Function.Injective (psiC ω hω) :=
  Zsqrtd.lift_injective _ fun n h => by nlinarith [sq_nonneg n]

theorem toModS_cast {p : ℕ} (hp : 0 < p) (s : ℕ) (x : ZJ) :
    ((toModS p s x : ℕ) : ZMod p) = ((2 * x.1 - x.2 + x.2 * (s : ℤ) : ℤ) : ZMod p) := by
  unfold toModS
  have hnn : 0 ≤ (2 * x.1 - x.2 + x.2 * (s : ℤ)) % (p : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have h1 : (((2 * x.1 - x.2 + x.2 * (s : ℤ)) % (p : ℤ)).toNat : ℤ) =
      (2 * x.1 - x.2 + x.2 * (s : ℤ)) % (p : ℤ) := Int.toNat_of_nonneg hnn
  rw [← Int.cast_natCast, h1, ZMod.intCast_mod]

theorem phiP_twoZ {p s : ℕ} (hp : 0 < p) (hs : (s * s + 3) % p = 0) (x : ZJ) :
    phiP p s hs (twoZ x) = (toModS p s x : ZMod p) := by
  rw [toModS_cast hp]
  simp only [phiP, Zsqrtd.lift_apply_apply, twoZ]
  push_cast
  ring

theorem toModS_zero (p s : ℕ) : toModS p s (0, 0) = 0 := by simp [toModS]

/-! ## Polynomials -/

theorem eval_expand {R : Type*} [CommRing R] (h : zjC.Hom R) (x : ℕ → R) :
    ∀ (ms : List Mono) (a : List ZJ), Poly.eval h x (expand ms a) =
      ∑ l ∈ Finset.range ms.length, h.f (a.getD l (0, 0)) * Mono.eval x (ms.getD l []) 0
  | [], a => by cases a <;> simp [expand]
  | μ :: ms, [] => by
    have h0 : h.f (0, 0) = 0 := h.map_zero
    simp [expand, h0]
  | μ :: ms, c :: a => by
    have ih := eval_expand h x ms a
    simp only [expand, List.zip_cons_cons, Poly.eval_cons] at ih ⊢
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

theorem eval_map_range' {R : Type*} [CommRing R] (x : ℕ → R) (g : ℕ → ℕ) :
    ∀ (n i0 : ℕ), Mono.eval x ((List.range' i0 n).map g) i0 = ∏ i ∈ Finset.range n, x (i0 + i) ^ g (i0 + i)
  | 0, i0 => by simp [Mono.eval]
  | n + 1, i0 => by
    rw [List.range'_succ, List.map_cons, Mono.eval, eval_map_range' x g n (i0 + 1), Finset.prod_range_succ']
    simp only [add_zero]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show i0 + 1 + i = i0 + (i + 1) by omega]

theorem eval_purePow {R : Type*} [CommRing R] (x : ℕ → R) (n k D : ℕ) (hk : k < n) :
    Mono.eval x (purePow n k D) 0 = x k ^ D := by
  unfold purePow
  rw [List.range_eq_range', eval_map_range' x _ n 0]
  simp only [zero_add, beq_iff_eq]
  rw [Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hk'
    exact absurd (Finset.mem_range.mpr hk) hk'

/-! ## The check -/

theorem eval_macRows_mem {R : Type*} [CommRing R] (h : zjC.Hom R) (x : ℕ → R) {n D : ℕ}
    {fs : List (Poly ZJ × ℕ)} (hx : ∀ f ∈ fs, Poly.eval h x f.1 = 0) :
    ∀ row ∈ macRows n D fs, Poly.eval h x row = 0 := by
  intro row hrow
  simp only [macRows, List.mem_flatMap, List.mem_map] at hrow
  obtain ⟨f, hf, α, -, rfl⟩ := hrow
  rw [Poly.eval_normalize, Poly.eval_mulTerm, hx f hf, mul_zero]

/-- **Soundness of the Macaulay check.** -/
theorem macCheck_sound {n D p s : ℕ} {fs : List (Poly ZJ × ℕ)} (hp : 1 < p) (hs : (s * s + 3) % p = 0)
    (hc : macCheck n D p s fs = true) (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (x : ℕ → ℂ)
    (hx : ∀ f ∈ fs, Poly.eval (zjHom ℂ ω hω) x f.1 = 0) : ∀ k < n, x k = 0 := by
  have : Fact (1 < p) := ⟨hp⟩
  have hp0 : 0 < p := by omega
  simp only [macCheck] at hc
  generalize hms : monos n D = ms at hc
  generalize hrows : macRows n D fs = rows at hc
  generalize hA : rows.map (coeffVec ms) = A at hc
  generalize hAp : modMat p s A = Ap at hc
  generalize hsel : selectRows p ms.length Ap = sel at hc
  generalize hAsub : sel.map (fun r => Ap.getD r #[]) = Asub at hc
  generalize hB : inverseMod p ms.length Asub = B at hc
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hrowsOK, hsize⟩, hver⟩, hpow⟩ := hc
  simp only [verifyInv, List.all_eq_true, beq_iff_eq] at hver
  set m := ms.length with hm
  set hz := zjHom ℂ ω hω
  have hlenA : A.length = rows.length := by rw [← hA, List.length_map]
  -- every row vanishes, and equals the sum of its listed terms
  have hrow0 : ∀ r : ℕ, Poly.eval hz x (rows.getD r []) = 0 := by
    intro r
    by_cases hr : r < rows.length
    · rw [List.getD_eq_getElem _ _ hr]
      have hmem : rows[r] ∈ macRows n D fs := by rw [hrows]; exact List.getElem_mem hr
      exact eval_macRows_mem hz x hx _ hmem
    · rw [List.getD_eq_default _ _ (by omega)]
      rfl
  have hexp : ∀ r : ℕ, Poly.eval hz x (expand ms (A.getD r [])) = Poly.eval hz x (rows.getD r []) := by
    intro r
    by_cases hr : r < rows.length
    · have hrA : r < A.length := by omega
      rw [List.getD_eq_getElem _ _ hrA, List.getD_eq_getElem _ _ hr]
      have hmem : (rows[r], A[r]) ∈ rows.zip A := by
        rw [List.mem_iff_getElem]
        exact ⟨r, by simp [hr, hrA], by simp [List.getElem_zip]⟩
      exact (Poly.eqv_sound hz x (hrowsOK _ hmem)).symm
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      simp [expand]
  -- the matrices
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
  -- the vector of the monomials is killed
  let v : Fin m → ℂ := fun l => Mono.eval x (ms.getD l []) 0
  have hMv : (psiC ω hω).mapMatrix aZ *ᵥ v = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Pi.zero_apply]
    have e1 : ∀ l : Fin m, psiC ω hω (aZ i l) * v l =
        2 * (hz.f ((A.getD (sel.getD i 0) []).getD l (0, 0)) * Mono.eval x (ms.getD l []) 0) := by
      intro l
      simp only [aZ, v]
      rw [psiC_twoZ hω]
      ring
    rw [Finset.sum_congr rfl fun l _ => e1 l, ← Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun l => hz.f ((A.getD (sel.getD i 0) []).getD l (0, 0)) *
      Mono.eval x (ms.getD l []) 0) m]
    rw [← eval_expand, hexp, hrow0, mul_zero]
  have hv0 : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdetC hMv
  -- the pure powers
  intro k hk
  have hmem : purePow n k D ∈ ms := by
    have := hpow k (List.mem_range.mpr hk)
    simpa [List.contains_iff_mem] using this
  obtain ⟨l, hl, hle⟩ := List.mem_iff_getElem.mp hmem
  have hvl := congrFun hv0 ⟨l, hl⟩
  simp only [v, Pi.zero_apply] at hvl
  rw [List.getD_eq_getElem _ _ hl, hle, eval_purePow x n k D hk] at hvl
  by_contra hne
  exact pow_ne_zero D hne hvl

end Lean6.Special.K4.E4
