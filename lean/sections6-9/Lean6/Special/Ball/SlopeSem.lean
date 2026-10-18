import Lean6.Special.Comp.Ball.Slope
import Lean6.Special.Ball.TPolySem
import Lean6.Special.Ball.Lin

/-!
# Uniqueness in a box by divided-difference slopes: soundness

* `hyb u v j`: the hybrid point `(u₀, …, u_{j-1}, v_j, v_{j+1}, …)`; `hsum a b d = Σ_{i ≤ d} a^i b^{d-i}`, so that
  `a^e - b^e = (a - b) h_{e-1}(a, b)` (`pow_sub_pow_hsum`, Mathlib's `geom_sum₂_mul`).
* `prod_sub_prod`: two points that agree off the variable `j` give products of powers (distinct variables, positive
  exponents) whose difference is `(f_j - g_j)` times the product with the factor of `j` replaced by `h`.
* `TTerm.dd`, `TPoly.dd`: the divided differences; **`TPoly.eval_sub_eq`**: `F(u) - F(v) = Σ_{j<n} (u_j - v_j) D_j(u, v)`
  (telescoping over the hybrid points) for admissible terms.
* `mem_ddPoly`: the balls of `ddPoly` enclose `D_j(u, v)` for all `u, v` in the box; `matMem_slopeMat`.
* **`slope_unique`**: if `slopeOK`, two points of the box at which every `F_i` takes the same value are equal: the
  slope matrix `S(u, v)` lies in the balls of `slopeMat`, the contraction bound makes it injective
  (`mulVec_injective_of_contr`), and `S(u, v) (u - v) = F(u) - F(v) = 0`.
-/

namespace Lean6.Special.Kraw

open Lean6.Special.Ball Matrix

variable {P : ℕ}

/-! ## Divided differences of products of powers -/

/-- The hybrid point `(u₀, …, u_{j-1}, v_j, v_{j+1}, …)`. -/
def hyb (u v : ℕ → ℂ) (j : ℕ) : ℕ → ℂ := fun i => if i < j then u i else v i

/-- `h_d(a, b) = Σ_{i ≤ d} a^i b^{d-i}`. -/
def hsum (a b : ℂ) (d : ℕ) : ℂ := ∑ i ∈ Finset.range (d + 1), a ^ i * b ^ (d - i)

theorem pow_sub_pow_hsum (a b : ℂ) {e : ℕ} (he : 0 < e) : a ^ e - b ^ e = (a - b) * hsum a b (e - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  have h := geom_sum₂_mul a b (d + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [← h, hsum, Nat.add_sub_cancel, mul_comm]

theorem hyb_zero (u v : ℕ → ℂ) : hyb u v 0 = v := by
  funext i; simp [hyb]

theorem hyb_succ_self (u v : ℕ → ℂ) (j : ℕ) : hyb u v (j + 1) j = u j := by simp [hyb]

theorem hyb_self (u v : ℕ → ℂ) (j : ℕ) : hyb u v j j = v j := by simp [hyb]

theorem hyb_succ_ne (u v : ℕ → ℂ) {i j : ℕ} (h : i ≠ j) : hyb u v (j + 1) i = hyb u v j i := by
  simp only [hyb]
  by_cases h1 : i < j
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

/-- **The difference of two products of powers** at points that agree off `j`. -/
theorem prod_sub_prod (f g : ℕ → ℂ) (j : ℕ) (hfg : ∀ i, i ≠ j → f i = g i) :
    ∀ (mono : List (ℕ × ℕ)), (∀ ve ∈ mono, 0 < ve.2) → (mono.map Prod.fst).Nodup →
      (mono.map fun ve => f ve.1 ^ ve.2).prod - (mono.map fun ve => g ve.1 ^ ve.2).prod =
        if j ∈ mono.map Prod.fst then
          (f j - g j) * (mono.map fun ve => if ve.1 = j then hsum (f j) (g j) (ve.2 - 1) else g ve.1 ^ ve.2).prod
        else 0
  | [], _, _ => by simp
  | ve :: rest, hpos, hnd => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hnot, hnd'⟩ := hnd
    have hrest : ∀ x ∈ rest, 0 < x.2 := fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    have ih := prod_sub_prod f g j hfg rest hrest (by simpa using hnd')
    simp only [List.map_cons, List.prod_cons, List.mem_cons]
    by_cases hv : ve.1 = j
    · -- the head is the variable `j`; it does not occur in the tail
      have hnr : j ∉ rest.map Prod.fst := by
        intro hm
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
        exact hnot ⟨x, hx, by rw [hxe, hv]⟩
      have hrest_eq : (rest.map fun ve => f ve.1 ^ ve.2).prod = (rest.map fun ve => g ve.1 ^ ve.2).prod := by
        congr 1
        refine List.map_congr_left fun x hx => ?_
        have : x.1 ≠ j := fun h => hnr (List.mem_map.mpr ⟨x, hx, h⟩)
        rw [hfg _ this]
      have hrest_if : (rest.map fun ve => if ve.1 = j then hsum (f j) (g j) (ve.2 - 1) else g ve.1 ^ ve.2).prod =
          (rest.map fun ve => g ve.1 ^ ve.2).prod := by
        congr 1
        refine List.map_congr_left fun x hx => ?_
        have : x.1 ≠ j := fun h => hnr (List.mem_map.mpr ⟨x, hx, h⟩)
        rw [if_neg this]
      rw [if_pos (Or.inl hv.symm), if_pos hv, hrest_eq, hrest_if, hv, ← sub_mul,
        pow_sub_pow_hsum _ _ (hpos ve (List.mem_cons_self ..))]
      ring
    · -- another variable: the two points agree on it
      have hfe : f ve.1 = g ve.1 := hfg _ hv
      rw [if_neg hv, hfe, ← mul_sub, ih]
      have hiff : (j = ve.1 ∨ j ∈ rest.map Prod.fst) ↔ j ∈ rest.map Prod.fst := by
        constructor
        · rintro (h | h)
          · exact absurd h.symm hv
          · exact h
        · exact Or.inr
      by_cases hj : j ∈ rest.map Prod.fst
      · rw [if_pos hj, if_pos (hiff.mpr hj)]; ring
      · rw [if_neg hj, if_neg (fun h => hj (hiff.mp h))]; ring

/-! ## Divided differences of terms and polynomials -/

/-- The product of a monomial with the factor of `j` replaced by `h_{e-1}(u_j, v_j)` and the others taken at the
hybrid point `hyb u v j`. -/
def ddProd (u v : ℕ → ℂ) (j : ℕ) (mono : List (ℕ × ℕ)) : ℂ :=
  (mono.map fun ve => if ve.1 = j then hsum (u j) (v j) (ve.2 - 1) else hyb u v j ve.1 ^ ve.2).prod

/-- The divided difference of a term in the variable `j`. -/
def TTerm.dd (κ u v : ℕ → ℂ) (j : ℕ) (t : TTerm) : ℂ :=
  if j ∈ t.mono.map Prod.fst then (t.c : ℂ) * κ t.k * ddProd u v j t.mono else 0

/-- The divided difference of a polynomial in the variable `j`. -/
def TPoly.dd (κ u v : ℕ → ℂ) (j : ℕ) (p : TPoly) : ℂ := (p.map (TTerm.dd κ u v j)).sum

/-- One step of the telescope for a term. -/
theorem TTerm.eval_hyb_sub (κ u v : ℕ → ℂ) (j : ℕ) (t : TTerm) (hpos : ∀ ve ∈ t.mono, 0 < ve.2)
    (hnd : (t.mono.map Prod.fst).Nodup) :
    t.eval κ (hyb u v (j + 1)) - t.eval κ (hyb u v j) = (u j - v j) * t.dd κ u v j := by
  have h := prod_sub_prod (hyb u v (j + 1)) (hyb u v j) j (fun i hi => hyb_succ_ne u v hi) t.mono hpos hnd
  rw [hyb_succ_self, hyb_self] at h
  simp only [TTerm.eval, TTerm.dd, ddProd]
  rw [← mul_sub, h]
  split_ifs <;> ring

/-- One step of the telescope for a polynomial. -/
theorem TPoly.eval_hyb_sub (κ u v : ℕ → ℂ) (j : ℕ) :
    ∀ p : TPoly, (∀ t ∈ p, (∀ ve ∈ t.mono, 0 < ve.2) ∧ (t.mono.map Prod.fst).Nodup) →
      p.eval κ (hyb u v (j + 1)) - p.eval κ (hyb u v j) = (u j - v j) * p.dd κ u v j
  | [], _ => by simp [TPoly.dd]
  | t :: rest, h => by
    have h1 := TTerm.eval_hyb_sub κ u v j t (h t (List.mem_cons_self ..)).1 (h t (List.mem_cons_self ..)).2
    have h2 := TPoly.eval_hyb_sub κ u v j rest fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    simp only [TPoly.eval_cons, TPoly.dd, List.map_cons, List.sum_cons] at h2 ⊢
    rw [mul_add, ← h1, ← h2]
    ring

/-- The value of a term depends only on its variables. -/
theorem TTerm.eval_congr (κ : ℕ → ℂ) {f g : ℕ → ℂ} (t : TTerm) (h : ∀ ve ∈ t.mono, f ve.1 = g ve.1) :
    t.eval κ f = t.eval κ g := by
  simp only [TTerm.eval]
  congr 2
  exact List.map_congr_left fun ve hve => by rw [h ve hve]

theorem TPoly.eval_congr (κ : ℕ → ℂ) {f g : ℕ → ℂ} :
    ∀ p : TPoly, (∀ t ∈ p, ∀ ve ∈ t.mono, f ve.1 = g ve.1) → p.eval κ f = p.eval κ g
  | [], _ => rfl
  | t :: rest, h => by
    simp only [TPoly.eval_cons]
    rw [TTerm.eval_congr κ t (h t (List.mem_cons_self ..)),
      TPoly.eval_congr κ rest fun t' ht' => h t' (List.mem_cons_of_mem _ ht')]

/-- **The telescope**: `F(u) - F(v) = Σ_{j<n} (u_j - v_j) D_j(u, v)` for admissible terms with variables below `n`. -/
theorem TPoly.eval_sub_eq (κ u v : ℕ → ℂ) (n : ℕ) (p : TPoly)
    (h : ∀ t ∈ p, (∀ ve ∈ t.mono, ve.1 < n ∧ 0 < ve.2) ∧ (t.mono.map Prod.fst).Nodup) :
    p.eval κ u - p.eval κ v = ∑ j ∈ Finset.range n, (u j - v j) * p.dd κ u v j := by
  have hn : p.eval κ u = p.eval κ (hyb u v n) := by
    refine TPoly.eval_congr κ p fun t ht ve hve => ?_
    have := ((h t ht).1 ve hve).1
    simp [hyb, this]
  have h' : ∀ t ∈ p, (∀ ve ∈ t.mono, 0 < ve.2) ∧ (t.mono.map Prod.fst).Nodup :=
    fun t ht => ⟨fun ve hve => ((h t ht).1 ve hve).2, (h t ht).2⟩
  rw [hn]
  conv_lhs => rw [show p.eval κ v = p.eval κ (hyb u v 0) by rw [hyb_zero]]
  rw [← Finset.sum_range_sub (fun j => p.eval κ (hyb u v j)) n]
  exact Finset.sum_congr rfl fun j _ => TPoly.eval_hyb_sub κ u v j p h'

/-! ## Admissibility -/

theorem nodupS_iff : ∀ l : List ℕ, nodupS l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nodupS, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodupS_iff l h.2⟩
    have : l.contains a = true := List.contains_iff_mem.mpr hm
    rw [this] at h
    exact Bool.false_ne_true h.1.symm

theorem termOK_spec {n : ℕ} {t : TTerm} (h : termOK n t = true) :
    (∀ ve ∈ t.mono, ve.1 < n ∧ 0 < ve.2) ∧ (t.mono.map Prod.fst).Nodup := by
  simp only [termOK, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  exact ⟨fun ve hve => h.1 ve hve, nodupS_iff _ h.2⟩

/-! ## The balls -/

theorem mem_foldl_add' {L : List ℕ} {f : ℕ → CB} {g : ℕ → ℂ} (hfg : ∀ i ∈ L, (f i).Mem P (g i)) :
    ∀ {acc : CB} {z : ℂ}, acc.Mem P z → (L.foldl (fun acc i => add P acc (f i)) acc).Mem P (z + (L.map g).sum) := by
  induction L with
  | nil => intro acc z h; simpa using h
  | cons i L ih =>
    intro acc z hacc
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have := ih (fun j hj => hfg j (List.mem_cons_of_mem _ hj)) (mem_add hacc (hfg i (List.mem_cons_self ..)))
    rwa [add_assoc] at this

theorem list_sum_range (g : ℕ → ℂ) : ∀ n, ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range g n, Finset.sum_range_succ]; simp

theorem mem_hBall {B : CB} {a b : ℂ} (ha : B.Mem P a) (hb : B.Mem P b) (d : ℕ) : (hBall P B d).Mem P (hsum a b d) := by
  have h := mem_foldl_add' (P := P) (L := List.range (d + 1))
    (f := fun i => mul P (tPow P B i) (tPow P B (Nat.sub d i))) (g := fun i => a ^ i * b ^ (d - i))
    (fun i _ => mem_mul (mem_tPow ha i) (mem_tPow hb (d - i))) (mem_zero (P := P))
  rw [zero_add, list_sum_range] at h
  exact h

theorem mem_ddMono {bx : List CB} {u v : ℕ → ℂ} {n j : ℕ} (hj : j < n)
    (hb : ∀ i < n, (bx.getD i (zero P)).Mem P (u i) ∧ (bx.getD i (zero P)).Mem P (v i)) :
    ∀ mono : List (ℕ × ℕ), (∀ ve ∈ mono, ve.1 < n) → (ddMono P bx j mono).Mem P (ddProd u v j mono)
  | [], _ => by simpa [ddMono, ddProd] using mem_one
  | ve :: rest, h => by
    have ih := mem_ddMono hj hb rest fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [ddMono, ddProd, List.map_cons, List.prod_cons] at ih ⊢
    refine mem_mul ?_ ih
    by_cases hv : ve.1 = j
    · have hbj : (ve.1 == j) = true := by simpa using hv
      rw [if_pos hbj, if_pos hv]
      exact mem_hBall (hb j hj).1 (hb j hj).2 _
    · have hbj : (ve.1 == j) = false := by simpa using hv
      simp only [hbj, Bool.false_eq_true, ↓reduceIte, hv]
      have hlt := h ve (List.mem_cons_self ..)
      refine mem_tPow ?_ ve.2
      simp only [hyb]
      split_ifs
      · exact (hb _ hlt).1
      · exact (hb _ hlt).2

theorem mem_ddTerm {tab bx : List CB} {κ u v : ℕ → ℂ} {n j : ℕ} (hκ : ListMemF P κ tab) (hj : j < n)
    (hb : ∀ i < n, (bx.getD i (zero P)).Mem P (u i) ∧ (bx.getD i (zero P)).Mem P (v i)) {t : TTerm}
    (ht : ∀ ve ∈ t.mono, ve.1 < n) : (ddTerm P tab bx j t).Mem P (t.dd κ u v j) := by
  unfold ddTerm TTerm.dd
  by_cases hm : j ∈ t.mono.map Prod.fst
  · rw [if_pos (List.contains_iff_mem.mpr hm), if_pos hm]
    exact mem_mul (mem_mul (mem_ofInt t.c) (hκ t.k)) (mem_ddMono hj hb t.mono ht)
  · have hc : (t.mono.map Prod.fst).contains j = false := by
      rcases hcb : (t.mono.map Prod.fst).contains j with _ | _
      · rfl
      · exact absurd (List.contains_iff_mem.mp hcb) hm
    rw [hc, if_neg hm]
    exact mem_zero

theorem mem_ddPoly {tab bx : List CB} {κ u v : ℕ → ℂ} {n j : ℕ} (hκ : ListMemF P κ tab) (hj : j < n)
    (hb : ∀ i < n, (bx.getD i (zero P)).Mem P (u i) ∧ (bx.getD i (zero P)).Mem P (v i)) :
    ∀ p : TPoly, (∀ t ∈ p, ∀ ve ∈ t.mono, ve.1 < n) → (ddPoly P tab bx j p).Mem P (p.dd κ u v j)
  | [], _ => by simpa [ddPoly, TPoly.dd] using mem_zero
  | t :: rest, h => by
    simp only [ddPoly, TPoly.dd, List.map_cons, List.sum_cons]
    refine mem_add (mem_ddTerm hκ hj hb (h t (List.mem_cons_self ..))) ?_
    exact mem_ddPoly hκ hj hb rest fun t' ht' => h t' (List.mem_cons_of_mem _ ht')

/-- The slope matrix `S(u, v)`. -/
def slopeMatrix (κ u v : ℕ → ℂ) (F : List TPoly) : Matrix (Fin F.length) (Fin F.length) ℂ :=
  fun i j => (F.get i).dd κ u v j

theorem matMem_slopeMat {tab bx : List CB} {κ u v : ℕ → ℂ} {F : List TPoly} (hκ : ListMemF P κ tab)
    (hb : ∀ i < F.length, (bx.getD i (zero P)).Mem P (u i) ∧ (bx.getD i (zero P)).Mem P (v i))
    (hF : ∀ Fi ∈ F, ∀ t ∈ Fi, ∀ ve ∈ t.mono, ve.1 < F.length) :
    MatMem P (slopeMatrix κ u v F) (slopeMat P tab F bx) := by
  refine forall₂_ofFn_iff.mpr ⟨by simp [slopeMat], fun i => forall₂_ofFn_iff.mpr ⟨by simp [slopeMat], fun j => ?_⟩⟩
  simp only [slopeMat, List.get_eq_getElem, List.getElem_map, List.getElem_range, slopeMatrix]
  exact mem_ddPoly hκ j.2 hb _ (hF _ (List.getElem_mem _))

/-! ## Uniqueness -/

/-- **Uniqueness in the box**: if `slopeOK`, two points of the box at which every equation takes the same value are
equal. -/
theorem slope_unique {tab : List CB} {F : List TPoly} {bx : List CB} (h : slopeOK P tab F bx = true)
    {κ u v : ℕ → ℂ} (hκ : ListMemF P κ tab) (hu : ∀ j < F.length, (bx.getD j (zero P)).Mem P (u j))
    (hv : ∀ j < F.length, (bx.getD j (zero P)).Mem P (v j))
    (hF : ∀ i < F.length, (F.getD i []).eval κ u = (F.getD i []).eval κ v) : ∀ j < F.length, u j = v j := by
  unfold slopeOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.pow_eq, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨-, hwf⟩, hq⟩, hqs⟩ := h
  have hok : ∀ Fi ∈ F, ∀ t ∈ Fi, (∀ ve ∈ t.mono, ve.1 < F.length ∧ 0 < ve.2) ∧ (t.mono.map Prod.fst).Nodup :=
    fun Fi hFi t ht => termOK_spec (hwf Fi hFi t ht)
  have hb : ∀ i < F.length, (bx.getD i (zero P)).Mem P (u i) ∧ (bx.getD i (zero P)).Mem P (v i) :=
    fun i hi => ⟨hu i hi, hv i hi⟩
  generalize hSb : slopeMat P tab F bx = Sb at hq hqs
  generalize hMb : fixMat P F.length (approxInv P Sb) = Mb at hq hqs
  generalize hq0 : (rowSumBound P (resMat P Mb (transpose P F.length Sb))).1 = q at hq
  set A := slopeMatrix κ u v F with hAdef
  have hA : MatMem P A Sb :=
    hSb ▸ matMem_slopeMat hκ hb fun Fi hFi t ht ve hve => ((hok Fi hFi t ht).1 ve hve).1
  have hM : MatMem P (centerMat P F.length Mb) Mb := hMb ▸ matMem_fixMat _ _
  have hE := matMem_resMat hM hA
  have hres : ∀ i, (∑ j, ‖(1 - centerMat P F.length Mb * A) i j‖) * 2 ^ P ≤ q := by
    intro i
    have := rowSum_sound hE hqs i
    rw [hq0] at this
    simpa only [norm_resTrue] using this
  have hinj := mulVec_injective_of_contr hq hres
  -- `A (u - v) = 0`
  set d : Fin F.length → ℂ := fun j => u j - v j with hd
  have hAd : A *ᵥ d = A *ᵥ 0 := by
    rw [Matrix.mulVec_zero]
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, hAdef, slopeMatrix, hd]
    have hFi : F.get i ∈ F := List.get_mem _ _
    have htel := TPoly.eval_sub_eq κ u v F.length (F.get i) (hok _ hFi)
    have hzero : (F.get i).eval κ u - (F.get i).eval κ v = 0 := by
      have := hF i i.2
      rw [List.getD_eq_getElem _ _ i.2] at this
      simp only [List.get_eq_getElem]
      rw [this, sub_self]
    rw [hzero, ← Fin.sum_univ_eq_sum_range (fun j => (u j - v j) * (F.get i).dd κ u v j)] at htel
    rw [htel]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h0 := hinj hAd
  intro j hj
  have := congrFun h0 ⟨j, hj⟩
  simp only [hd, Pi.zero_apply] at this
  exact sub_eq_zero.mp this

end Lean6.Special.Kraw
