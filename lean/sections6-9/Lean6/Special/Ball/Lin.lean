import Lean6.Special.Ball.Sem
import Lean6.Special.Ball.Kraw
import Mathlib.Data.List.GetD

/-!
# Linear algebra in balls: products, the contraction bound, invertibility, enclosures of solutions

Vectors and matrices of balls are lists (`VecMem`, `MatMem`: entrywise containment of `v : Fin n → ℂ`,
`A : Matrix (Fin n) (Fin n) ℂ`, rows of the matrix as lists).

* `vecMem_matVec`: `matVec` encloses `A v`; `matMem_transpose`; `matMem_fixMat` (the preconditioner `fixMat`, its exact
  centers);
* **`rowSum_sound`**: if the histories of the entries of `resMat M Aᵀ` are small, its `rowSumBound` `q` bounds
  `Σⱼ ‖(1 − M A)ᵢⱼ‖ · 2^P` for every row;
* **`mulVec_injective_of_contr`**: `q < 2^P` makes `A` injective (`w = (1 − M A) w` forces `w = 0`), hence bijective;
* **`vecMem_solve`**: the solution of `A v = −b` lies in the balls of `solve`: with `x̃ = −M b` (centers),
  `v − x̃ = (1 − M A)(v − x̃) − M (b + A x̃)`, so `‖v − x̃‖ ≤ ‖M (b + A x̃)‖ / (1 − q/2^P)`.
-/

namespace Lean6.Special.Ball

open Matrix

variable {P : ℕ}

/-! ## Vectors and matrices of balls -/

/-- The ball vector `vb` encloses `v`. -/
def VecMem (P : ℕ) {n : ℕ} (v : Fin n → ℂ) (vb : List CB) : Prop :=
  List.Forall₂ (fun z x => CB.Mem P z x) (List.ofFn v) vb

/-- The ball matrix `Ab` (rows) encloses `A`. -/
def MatMem (P : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (Ab : List (List CB)) : Prop :=
  List.Forall₂ (fun r rb => List.Forall₂ (fun z x => CB.Mem P z x) r rb) (List.ofFn fun i => List.ofFn (A i)) Ab

theorem forall₂_ofFn_iff {α β : Type*} {R : α → β → Prop} {n : ℕ} {f : Fin n → α} {l : List β} :
    List.Forall₂ R (List.ofFn f) l ↔ ∃ h : l.length = n, ∀ i : Fin n, R (f i) (l.get ⟨i, by omega⟩) := by
  rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨hl, h⟩
    refine ⟨by simpa using hl.symm, fun i => ?_⟩
    have := h i (by simp) (by simp at hl; omega)
    simpa using this
  · rintro ⟨hl, h⟩
    refine ⟨by simpa using hl.symm, fun i h1 h2 => ?_⟩
    have := h ⟨i, by simpa using h1⟩
    simpa using this

theorem VecMem.length {n : ℕ} {v : Fin n → ℂ} {vb : List CB} (h : VecMem P v vb) : vb.length = n :=
  (forall₂_ofFn_iff.mp h).1

theorem VecMem.get {n : ℕ} {v : Fin n → ℂ} {vb : List CB} (h : VecMem P v vb) (i : Fin n) :
    (vb.get ⟨i, by rw [h.length]; exact i.2⟩).Mem P (v i) :=
  (forall₂_ofFn_iff.mp h).2 i

theorem vecMem_of_get {n : ℕ} {v : Fin n → ℂ} {vb : List CB} (hl : vb.length = n)
    (h : ∀ i : Fin n, (vb.get ⟨i, by omega⟩).Mem P (v i)) : VecMem P v vb :=
  forall₂_ofFn_iff.mpr ⟨hl, h⟩

theorem zipWith_mul_ofFn {n : ℕ} (f g : Fin n → ℂ) :
    (List.zipWith (· * ·) (List.ofFn f) (List.ofFn g)).sum = ∑ i, f i * g i := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_get <;> simp

/-- **Matrix times vector.** -/
theorem vecMem_matVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {Ab : List (List CB)} {x : Fin n → ℂ} {xb : List CB}
    (hA : MatMem P A Ab) (hx : VecMem P x xb) : VecMem P (A *ᵥ x) (matVec P Ab xb) := by
  obtain ⟨hl, hrow⟩ := forall₂_ofFn_iff.mp hA
  refine vecMem_of_get (by simp [matVec, hl]) fun i => ?_
  simp only [matVec, List.get_eq_getElem, List.getElem_map]
  have h := mem_dot (hrow i) hx
  rwa [zipWith_mul_ofFn] at h

/-- **Transpose.** -/
theorem matMem_transpose {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {Ab : List (List CB)} (hA : MatMem P A Ab) :
    MatMem P Aᵀ (transpose P n Ab) := by
  obtain ⟨hl, hrow⟩ := forall₂_ofFn_iff.mp hA
  refine forall₂_ofFn_iff.mpr ⟨by simp [transpose], fun j => forall₂_ofFn_iff.mpr ⟨by simp [transpose, hl], fun i => ?_⟩⟩
  obtain ⟨hli, hi⟩ := forall₂_ofFn_iff.mp (hrow i)
  simp only [transpose, List.get_eq_getElem, List.getElem_map, List.getElem_range]
  have := hi j
  simp only [List.get_eq_getElem] at this
  rw [List.getD_eq_getElem _ _ (by simp only [List.get_eq_getElem] at hli; rw [hli]; exact j.2)]
  exact this

/-! ## The preconditioner -/

theorem center_center (x : CB) : center P (center P x) = center P x := rfl

theorem center_zero : center P (zero P) = zero P := by
  simp [center, zero, absB]

/-- The exact matrix of the centers of `fixMat`. -/
noncomputable def centerMat (P n : ℕ) (Mb : List (List CB)) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => centerC P ((Mb.getD i []).getD j (zero P))

theorem length_fixMat (n : ℕ) (rows : List (List CB)) : (fixMat P n rows).length = n := by
  simp [fixMat]

theorem fixMat_row {n : ℕ} {rows : List (List CB)} {row : List CB} (h : row ∈ fixMat P n rows) :
    row.length = n ∧ ∀ x ∈ row, center P x = x := by
  unfold fixMat at h
  rcases List.mem_append.mp (List.mem_of_mem_take h) with h1 | h1
  · obtain ⟨r, -, rfl⟩ := List.mem_map.mp h1
    refine ⟨by simp, fun x hx => ?_⟩
    rcases List.mem_append.mp (List.mem_of_mem_take hx) with h2 | h2
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp h2; rfl
    · rw [List.eq_of_mem_replicate h2]; exact center_zero
  · rw [List.eq_of_mem_replicate h1]
    exact ⟨by simp, fun x hx => by rw [List.eq_of_mem_replicate hx]; exact center_zero⟩

theorem matMem_fixMat (n : ℕ) (rows : List (List CB)) :
    MatMem P (centerMat P n (fixMat P n rows)) (fixMat P n rows) := by
  refine forall₂_ofFn_iff.mpr ⟨length_fixMat n rows, fun i => ?_⟩
  set row := (fixMat P n rows).get ⟨i, by rw [length_fixMat]; exact i.2⟩
  have hrow : row ∈ fixMat P n rows := List.get_mem _ _
  obtain ⟨hl, hc⟩ := fixMat_row hrow
  refine forall₂_ofFn_iff.mpr ⟨hl, fun j => ?_⟩
  have hx : row.get ⟨j, by omega⟩ ∈ row := List.get_mem _ _
  have e1 : (fixMat P n rows).getD i [] = row := by
    rw [List.getD_eq_getElem _ _ (by rw [length_fixMat]; exact i.2)]; rfl
  have e : centerMat P n (fixMat P n rows) i j = centerC P (row.get ⟨j, by omega⟩) := by
    simp only [centerMat]
    rw [e1, List.getD_eq_getElem _ _ (by rw [hl]; exact j.2)]
    rfl
  rw [e, ← hc _ hx]
  exact mem_center _

/-! ## The residual matrix `1 − M A` and its row sums -/

/-- The residual `1 − M A` up to the sign of the off-diagonal entries (as `resMat` computes it). -/
def resTrue {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j then 1 - (M * A) i j else (M * A) i j

theorem norm_resTrue {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖resTrue M A i j‖ = ‖(1 - M * A) i j‖ := by
  unfold resTrue
  split_ifs with h
  · subst h; simp [Matrix.sub_apply]
  · simp [Matrix.sub_apply, Matrix.one_apply, h]

theorem matMem_resMat {n : ℕ} {M A : Matrix (Fin n) (Fin n) ℂ} {Mb Ab : List (List CB)} (hM : MatMem P M Mb)
    (hA : MatMem P A Ab) : MatMem P (resTrue M A) (resMat P Mb (transpose P n Ab)) := by
  have hT := matMem_transpose hA
  obtain ⟨hlM, hrowM⟩ := forall₂_ofFn_iff.mp hM
  obtain ⟨hlT, hrowT⟩ := forall₂_ofFn_iff.mp hT
  refine forall₂_ofFn_iff.mpr ⟨by simp [resMat, hlM], fun i => forall₂_ofFn_iff.mpr ⟨by simp [resMat, hlT], fun j => ?_⟩⟩
  simp only [resMat, List.get_eq_getElem, List.getElem_map, List.getElem_zipIdx, zero_add]
  have hd := mem_dot (hrowM i) (hrowT j)
  rw [zipWith_mul_ofFn] at hd
  have e : ∑ k, M i k * Aᵀ j k = (M * A) i j := by simp [Matrix.mul_apply]
  rw [e] at hd
  simp only [List.get_eq_getElem] at hd
  unfold resTrue
  by_cases h : i = j
  · subst h
    simp only [beq_self_eq_true, ↓reduceIte]
    exact mem_sub mem_one hd
  · have hb : ((i : ℕ) == (j : ℕ)) = false := by simp [Fin.val_ne_of_ne h]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, h]
    exact hd

theorem foldl_add_eq {α : Type*} (f : α → ℕ) : ∀ (l : List α) (t : ℕ),
    l.foldl (fun t x => Nat.add t (f x)) t = t + (l.map f).sum
  | [], t => by simp
  | x :: l, t => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add_eq f l]; simp only [Nat.add_eq]; ring

/-- The fold of `rowSumBound`: the first component bounds every row sum of `magB`, the second every history. -/
theorem rowSumBound_aux : ∀ (E : List (List CB)) (acc : ℕ × ℕ),
    acc.1 ≤ (E.foldl (fun (acc : ℕ × ℕ) row =>
      (if Nat.blt acc.1 (row.foldl (fun t x => Nat.add t (magB P x)) 0) then
        row.foldl (fun t x => Nat.add t (magB P x)) 0 else acc.1, row.foldl (fun t x => Nat.add t x.s) acc.2)) acc).1 ∧
    acc.2 ≤ (E.foldl (fun (acc : ℕ × ℕ) row =>
      (if Nat.blt acc.1 (row.foldl (fun t x => Nat.add t (magB P x)) 0) then
        row.foldl (fun t x => Nat.add t (magB P x)) 0 else acc.1, row.foldl (fun t x => Nat.add t x.s) acc.2)) acc).2 ∧
    ∀ row ∈ E, (row.map (magB P)).sum ≤ (E.foldl (fun (acc : ℕ × ℕ) row =>
      (if Nat.blt acc.1 (row.foldl (fun t x => Nat.add t (magB P x)) 0) then
        row.foldl (fun t x => Nat.add t (magB P x)) 0 else acc.1, row.foldl (fun t x => Nat.add t x.s) acc.2)) acc).1 ∧
      ∀ x ∈ row, x.s ≤ (E.foldl (fun (acc : ℕ × ℕ) row =>
      (if Nat.blt acc.1 (row.foldl (fun t x => Nat.add t (magB P x)) 0) then
        row.foldl (fun t x => Nat.add t (magB P x)) 0 else acc.1, row.foldl (fun t x => Nat.add t x.s) acc.2)) acc).2
  | [], acc => by simp
  | row :: E, acc => by
    obtain ⟨h1, h2, h3⟩ := rowSumBound_aux E (if Nat.blt acc.1 (row.foldl (fun t x => Nat.add t (magB P x)) 0) then
        row.foldl (fun t x => Nat.add t (magB P x)) 0 else acc.1, row.foldl (fun t x => Nat.add t x.s) acc.2)
    simp only [List.foldl_cons]
    rw [foldl_add_eq, foldl_add_eq] at h1 h2 h3 ⊢
    have hq : acc.1 ≤ (if Nat.blt acc.1 (0 + (row.map (magB P)).sum) then 0 + (row.map (magB P)).sum else acc.1) ∧
        (0 + (row.map (magB P)).sum) ≤ (if Nat.blt acc.1 (0 + (row.map (magB P)).sum) then
          0 + (row.map (magB P)).sum else acc.1) := by
      split_ifs with h
      · simp only [Nat.blt_eq] at h; omega
      · simp only [Nat.blt_eq, not_lt] at h; omega
    refine ⟨hq.1.trans h1, le_trans (by omega) h2, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨by have := hq.2; omega, fun x hx => ?_⟩
      have : x.s ≤ (r.map CB.s).sum := List.le_sum_of_mem (List.mem_map_of_mem hx)
      omega
    · exact h3 r hr

theorem sum_magB_eq {n : ℕ} (row : List CB) (hl : row.length = n) :
    (row.map (magB P)).sum = ∑ j : Fin n, magB P (row.get ⟨j, by omega⟩) := by
  subst hl
  conv_lhs => rw [← List.ofFn_get row]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-- **The row sums**: with small histories, `q` bounds `Σⱼ ‖(1 − M A)ᵢⱼ‖ · 2^P`. -/
theorem rowSum_sound {n : ℕ} {E : Matrix (Fin n) (Fin n) ℂ} {Eb : List (List CB)} (hE : MatMem P E Eb)
    (hs : (rowSumBound P Eb).2 ≤ smax P) (i : Fin n) :
    (∑ j, ‖E i j‖) * 2 ^ P ≤ (rowSumBound P Eb).1 := by
  obtain ⟨hl, hrow⟩ := forall₂_ofFn_iff.mp hE
  obtain ⟨hli, hi⟩ := forall₂_ofFn_iff.mp (hrow i)
  obtain ⟨-, -, h3⟩ := rowSumBound_aux (P := P) Eb (0, 0)
  obtain ⟨hq, hsx⟩ := h3 _ (List.get_mem Eb ⟨i, by omega⟩)
  have hb : ∀ j : Fin n, ‖E i j‖ * 2 ^ P ≤ magB P ((Eb.get ⟨i, by omega⟩).get ⟨j, by rw [hli]; exact j.2⟩) :=
    fun j => norm_le_magB (hi j) ((hsx _ (List.get_mem _ _)).trans hs)
  rw [sum_magB_eq _ hli] at hq
  calc (∑ j, ‖E i j‖) * 2 ^ P = ∑ j, ‖E i j‖ * 2 ^ P := Finset.sum_mul _ _ _
    _ ≤ ∑ j : Fin n, (magB P ((Eb.get ⟨i, by omega⟩).get ⟨j, by rw [hli]; exact j.2⟩) : ℝ) :=
        Finset.sum_le_sum fun j _ => hb j
    _ ≤ (rowSumBound P Eb).1 := by exact_mod_cast hq

/-! ## Invertibility and the enclosure of solutions -/

/-- `‖(1 − M A) w‖ ≤ (q / 2^P) ‖w‖`. -/
theorem norm_res_le {n : ℕ} {E : Matrix (Fin n) (Fin n) ℂ} {q : ℕ} (h : ∀ i, (∑ j, ‖E i j‖) * 2 ^ P ≤ q)
    (w : Fin n → ℂ) : ‖E *ᵥ w‖ ≤ (q / 2 ^ P) * ‖w‖ := by
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  refine (norm_mulVec_apply_le E w i).trans ?_
  have := h i
  have h2 : ∑ j, ‖E i j‖ ≤ q / 2 ^ P := by rw [le_div_iff₀ hp]; exact this
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- **Injectivity** from the contraction bound. -/
theorem mulVec_injective_of_contr {n : ℕ} {M A : Matrix (Fin n) (Fin n) ℂ} {q : ℕ} (hq : q < 2 ^ P)
    (h : ∀ i, (∑ j, ‖(1 - M * A) i j‖) * 2 ^ P ≤ q) : Function.Injective (A *ᵥ ·) := by
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have hq' : (q : ℝ) / 2 ^ P < 1 := by rw [div_lt_one hp]; exact_mod_cast hq
  intro u v huv
  simp only at huv
  have h0 : A *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
  have e : (1 - M * A) *ᵥ (u - v) = u - v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, sub_zero]
  have hn := norm_res_le h (u - v)
  rw [e] at hn
  have : ‖u - v‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem mulVec_bijective_of_contr {n : ℕ} {M A : Matrix (Fin n) (Fin n) ℂ} {q : ℕ} (hq : q < 2 ^ P)
    (h : ∀ i, (∑ j, ‖(1 - M * A) i j‖) * 2 ^ P ≤ q) : Function.Bijective (A *ᵥ ·) := by
  have hi := mulVec_injective_of_contr hq h
  have hi' : Function.Injective (Matrix.mulVecLin A) := hi
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi'⟩

/-- The maximum fold of `solve`. -/
theorem foldl_max_ge (f : CB → ℕ) : ∀ (l : List CB) (t : ℕ),
    t ≤ l.foldl (fun t x => if Nat.blt t (f x) then f x else t) t ∧
      ∀ x ∈ l, f x ≤ l.foldl (fun t x => if Nat.blt t (f x) then f x else t) t
  | [], t => by simp
  | x :: l, t => by
    obtain ⟨h1, h2⟩ := foldl_max_ge f l (if Nat.blt t (f x) then f x else t)
    have hm : t ≤ (if Nat.blt t (f x) then f x else t) ∧ f x ≤ (if Nat.blt t (f x) then f x else t) := by
      split_ifs with h
      · simp only [Nat.blt_eq] at h; omega
      · simp only [Nat.blt_eq, not_lt] at h; omega
    simp only [List.foldl_cons]
    refine ⟨hm.1.trans h1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hm.2.trans h1
    · exact h2 y hy

theorem cv_center (x : CB) : cv P (center P x).re = cv P x.re ∧ cv P (center P x).im = cv P x.im := ⟨rfl, rfl⟩

/-- The analytic part of the enclosure: `u = (1 − M A) u − w` with `‖w‖ · 2^P ≤ e` gives
`‖u‖ · 2^P ≤ e · 2^P / (2^P − q)`. -/
theorem solve_bound {n : ℕ} {M A : Matrix (Fin n) (Fin n) ℂ} {q : ℕ} (hq : q < 2 ^ P)
    (hres : ∀ i, (∑ j, ‖(1 - M * A) i j‖) * 2 ^ P ≤ q) {u w : Fin n → ℂ} (hu : u = (1 - M * A) *ᵥ u - w)
    {e : ℝ} (hw : ‖w‖ * 2 ^ P ≤ e) : ‖u‖ * 2 ^ P ≤ e * 2 ^ P / (2 ^ P - q) := by
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have hqp : (0 : ℝ) < 2 ^ P - q := by
    have : (q : ℝ) < 2 ^ P := by exact_mod_cast hq
    linarith
  have h1 := norm_res_le hres u
  have h2 : ‖u‖ ≤ ‖(1 - M * A) *ᵥ u‖ + ‖w‖ := by
    conv_lhs => rw [hu]
    exact norm_sub_le _ _
  have h3 : ‖u‖ * 2 ^ P ≤ q * ‖u‖ + e := by
    have h4 := mul_le_mul_of_nonneg_right (h2.trans (add_le_add h1 le_rfl)) hp.le
    have h5 : ((q : ℝ) / 2 ^ P * ‖u‖ + ‖w‖) * 2 ^ P = q * ‖u‖ + ‖w‖ * 2 ^ P := by field_simp
    linarith
  rw [le_div_iff₀ hqp]
  nlinarith [norm_nonneg u]

/-- The radius of `solve` exceeds `e · 2^P / (2^P − q)`. -/
theorem solve_radius (e q : ℕ) (hq : q < 2 ^ P) :
    (e : ℝ) * 2 ^ P / (2 ^ P - q) < ((Nat.add (Nat.div (Nat.shiftLeft e P) (Nat.sub (Nat.pow 2 P) q)) 1 : ℕ) : ℝ) := by
  have hqp : (0 : ℝ) < 2 ^ P - q := by
    have : (q : ℝ) < 2 ^ P := by exact_mod_cast hq
    linarith
  have hd : 0 < 2 ^ P - q := by omega
  have h := Nat.lt_div_mul_add (a := e * 2 ^ P) hd
  have hc : ((2 ^ P - q : ℕ) : ℝ) = 2 ^ P - q := by rw [Nat.cast_sub hq.le]; push_cast; ring
  have h' : ((e * 2 ^ P : ℕ) : ℝ) < ((e * 2 ^ P / (2 ^ P - q) : ℕ) : ℝ) * ((2 ^ P - q : ℕ) : ℝ) +
      ((2 ^ P - q : ℕ) : ℝ) := by exact_mod_cast h
  rw [hc] at h'
  simp only [Nat.add_eq, shiftLeft_eq', Nat.sub_eq, Nat.pow_eq]
  rw [div_lt_iff₀ hqp]
  have e1 : (Nat.div (e * 2 ^ P) (2 ^ P - q) : ℕ) = e * 2 ^ P / (2 ^ P - q) := rfl
  rw [e1]
  push_cast at h' ⊢
  nlinarith

/-- **The enclosure of the solution** of `A v = −b`. -/
theorem vecMem_solve {n : ℕ} {M A : Matrix (Fin n) (Fin n) ℂ} {Mb Ab : List (List CB)} {q : ℕ}
    (hM : MatMem P M Mb) (hA : MatMem P A Ab) (hq : q < 2 ^ P)
    (hres : ∀ i, (∑ j, ‖(1 - M * A) i j‖) * 2 ^ P ≤ q)
    {b : Fin n → ℂ} {bb : List CB} (hb : VecMem P b bb) {v : Fin n → ℂ} (hv : A *ᵥ v = -b) :
    VecMem P v (solve P Mb Ab q bb) := by
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have hneg : VecMem P (-b) (bb.map (neg P)) := by
    refine vecMem_of_get (by simp [hb.length]) fun i => ?_
    simp only [List.get_eq_getElem, List.getElem_map, Pi.neg_apply]
    exact mem_neg (by simpa using hb.get i)
  have hy := vecMem_matVec hM hneg
  -- the centers `x̃`
  generalize hyb : matVec P Mb (bb.map (neg P)) = yb at hy
  have hyl : yb.length = n := hy.length
  have hxl : (yb.map (center P)).length = n := by simp [hyl]
  let xt : Fin n → ℂ := fun i => centerC P (yb.get ⟨i, by omega⟩)
  have hxt : VecMem P xt (yb.map (center P)) := vecMem_of_get hxl fun i => by
    simp only [List.get_eq_getElem, List.getElem_map]
    exact mem_center _
  have hAx := vecMem_matVec hA hxt
  have hr : VecMem P (b + A *ᵥ xt) (List.zipWith (fun bi ri => add P bi ri) bb (matVec P Ab (yb.map (center P)))) := by
    refine vecMem_of_get (by simp [hb.length, hAx.length]) fun i => ?_
    simp only [List.get_eq_getElem, List.getElem_zipWith, Pi.add_apply]
    exact mem_add (by simpa using hb.get i) (by simpa using hAx.get i)
  have hw := vecMem_matVec hM hr
  generalize hwb : matVec P Mb (List.zipWith (fun bi ri => add P bi ri) bb (matVec P Ab (yb.map (center P)))) = wb at hw
  have hwl : wb.length = n := hw.length
  have hsol : solve P Mb Ab q bb = (yb.map (center P)).map fun x =>
      ⟨x.re, x.im, Nat.add (Nat.div (Nat.shiftLeft (wb.foldl (fun t x => if Nat.blt t (magB P x) then magB P x else t) 0) P)
        (Nat.sub (Nat.pow 2 P) q)) 1, x.a, Nat.add x.s (wb.foldl (fun t x => Nat.add t x.s) 0)⟩ := by
    rw [← hwb, ← hyb]; rfl
  rw [hsol]
  generalize he : wb.foldl (fun t x => if Nat.blt t (magB P x) then magB P x else t) 0 = e
  generalize hsw : wb.foldl (fun t x => Nat.add t x.s) 0 = sw
  have hR := solve_radius (P := P) e q hq
  generalize hRR : Nat.add (Nat.div (Nat.shiftLeft e P) (Nat.sub (Nat.pow 2 P) q)) 1 = R at hR
  refine vecMem_of_get (by simp [hyl]) fun i => ?_
  intro hs
  simp only [List.get_eq_getElem, List.getElem_map] at hs ⊢
  have hsw' : sw ≤ smax P := by simp only [center, Nat.add_eq] at hs; omega
  -- `‖w‖ · 2^P ≤ e`
  have hwn : ‖M *ᵥ (b + A *ᵥ xt)‖ * 2 ^ P ≤ e := by
    have hwj : ∀ j : Fin n, ‖(M *ᵥ (b + A *ᵥ xt)) j‖ * 2 ^ P ≤ e := by
      intro j
      have hmem := hw.get j
      have hj := List.get_mem wb ⟨j, by omega⟩
      have hxs : (wb.get ⟨j, by omega⟩).s ≤ sw := by
        rw [← hsw, foldl_add_eq CB.s wb 0]
        have := List.le_sum_of_mem (List.mem_map_of_mem (f := CB.s) hj)
        omega
      have h1 := norm_le_magB hmem (hxs.trans hsw')
      have h2 := (foldl_max_ge (magB P) wb 0).2 _ hj
      rw [he] at h2
      exact h1.trans (by exact_mod_cast h2)
    have : ‖M *ᵥ (b + A *ᵥ xt)‖ ≤ e / 2 ^ P :=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => by rw [le_div_iff₀ hp]; exact hwj j
    rwa [le_div_iff₀ hp] at this
  -- `u = v − x̃` satisfies `u = (1 − M A) u − w`
  have hu : v - xt = (1 - M * A) *ᵥ (v - xt) - M *ᵥ (b + A *ᵥ xt) := by
    have hAu : A *ᵥ (v - xt) = -(b + A *ᵥ xt) := by
      rw [Matrix.mulVec_sub, hv]; abel
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hAu, Matrix.mulVec_neg]; abel
  have hub := solve_bound hq hres hu hwn
  have hui : ‖(v - xt) i‖ ≤ ‖v - xt‖ := norm_le_pi_norm (v - xt) i
  have hxti : xt i = centerC P (yb[(i : ℕ)]'(by omega)) := rfl
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [center, Nat.add_eq]; push_cast; rw [absB_eq, absB_eq]
  · simp only [center, Nat.add_eq]; omega
  · have e1 : (cv P (center P (yb[(i : ℕ)]'(by omega))).re : ℝ) = (xt i).re * 2 ^ P := by
      rw [hxti]; simp [centerC, center, div_mul_cancel₀ _ hp.ne']
    rw [e1, ← sub_mul, abs_mul, abs_of_pos hp]
    have h1 : |(v i).re - (xt i).re| ≤ ‖(v - xt) i‖ := by
      have := Complex.abs_re_le_norm ((v - xt) i); simpa using this
    have h2 : |(v i).re - (xt i).re| * 2 ^ P ≤ ‖v - xt‖ * 2 ^ P :=
      mul_le_mul_of_nonneg_right (h1.trans hui) hp.le
    linarith
  · have e1 : (cv P (center P (yb[(i : ℕ)]'(by omega))).im : ℝ) = (xt i).im * 2 ^ P := by
      rw [hxti]; simp [centerC, center, div_mul_cancel₀ _ hp.ne']
    rw [e1, ← sub_mul, abs_mul, abs_of_pos hp]
    have h1 : |(v i).im - (xt i).im| ≤ ‖(v - xt) i‖ := by
      have := Complex.abs_im_le_norm ((v - xt) i); simpa using this
    have h2 : |(v i).im - (xt i).im| * 2 ^ P ≤ ‖v - xt‖ * 2 ^ P :=
      mul_le_mul_of_nonneg_right (h1.trans hui) hp.le
    linarith

end Lean6.Special.Ball
