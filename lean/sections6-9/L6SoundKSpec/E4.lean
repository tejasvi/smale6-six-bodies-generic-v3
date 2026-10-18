import L6KSpec.E4
import Lean6.Special.K4.E4.Sound

/-!
# Soundness of the kernel Macaulay check

**`macCheckK_sound`**: the conclusion of lean6_special's `macCheck_sound` from `macCheckK n D p s fs sel B = true`.
The proof is that of `macCheck_sound` (`Lean6.Special.K4.E4.Sound`, whose lemmas it uses), with two new steps:

* `eval_expand_coeffVecK`: a row equals the polynomial with its coefficient vector on the monomials of degree `D`,
  when the trimmed monomials are distinct and cover the terms of the row (each term is counted at the one position
  of its monomial);
* `verifyPacked_sound`: the packed test gives `A B ≡ 1 (mod p)` (the slots of 72 bits do not overflow).
-/

namespace L6KSpec.E4

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.E4 Lean6.Special.K4.E4 Matrix

/-! ## Coefficient vectors -/

section Coeff

variable {R : Type*} [CommRing R] (h : zjC.Hom R) (x : ℕ → R)

theorem nodupB_spec : ∀ {L : List Mono}, nodupB L = true → L.Nodup
  | [], _ => List.nodup_nil
  | a :: l, hL => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at hL
    refine List.nodup_cons.mpr ⟨fun ha => ?_, nodupB_spec hL.2⟩
    rw [List.contains_iff_mem.mpr ha] at hL
    exact absurd hL.1 (by decide)

theorem coefSum_hom (k : Mono) :
    ∀ p : Poly ZJ, h.f (coefSum k p) = ((p.filter fun t => t.2 == k).map fun t => h.f t.1).sum
  | [] => h.map_zero
  | t :: rest => by
    simp only [coefSum, List.filter_cons]
    split
    · rw [h.map_add, coefSum_hom k rest, List.map_cons, List.sum_cons]
    · exact coefSum_hom k rest

/-- In a list without repetitions, `∑_l [L_l = k] g` is `g` for `k ∈ L`. -/
theorem sum_ite_getD {L : List Mono} (hL : L.Nodup) {k : Mono} (hk : k ∈ L) (g : R) :
    ∑ l ∈ Finset.range L.length, (if k = L.getD l [] then g else 0) = g := by
  obtain ⟨l0, hl0, rfl⟩ := List.getElem_of_mem hk
  rw [Finset.sum_eq_single l0]
  · rw [List.getD_eq_getElem _ _ hl0]
    simp
  · intro b hb hne
    have hb' : b < L.length := Finset.mem_range.mp hb
    rw [List.getD_eq_getElem _ _ hb']
    exact ite_eq_right_iff.mpr fun heq => absurd ((List.Nodup.getElem_inj_iff hL).mp heq.symm) hne
  · intro h0
    exact absurd (Finset.mem_range.mpr hl0) h0

/-- The positions of the trimmed monomials `msT`, weighted by the coefficient sums of the trimmed terms of `p`, give
the value of `p`, if every term of `p` has one of these monomials. -/
theorem sum_coefSum (msT : List Mono) (hnd : msT.Nodup) :
    ∀ p : Poly ZJ, (∀ t ∈ p, Mono.trim t.2 ∈ msT) →
      ∑ l ∈ Finset.range msT.length,
        h.f (coefSum (msT.getD l []) (p.map fun t => (t.1, Mono.trim t.2))) * Mono.eval x (msT.getD l []) 0 =
      Poly.eval h x p
  | [], _ => by
    have h0 : h.f (0, 0) = 0 := h.map_zero
    simp [coefSum, h0, Poly.eval]
  | t :: q, hcov => by
    have ih := sum_coefSum msT hnd q fun u hu => hcov u (List.mem_cons_of_mem _ hu)
    have hsplit : ∀ l, h.f (coefSum (msT.getD l []) ((t :: q).map fun t => (t.1, Mono.trim t.2))) *
        Mono.eval x (msT.getD l []) 0 =
        (if Mono.trim t.2 = msT.getD l [] then h.f t.1 * Mono.eval x t.2 0 else 0) +
          h.f (coefSum (msT.getD l []) (q.map fun t => (t.1, Mono.trim t.2))) * Mono.eval x (msT.getD l []) 0 := by
      intro l
      simp only [List.map_cons, coefSum, beq_iff_eq]
      split
      · rename_i heq
        rw [h.map_add, add_mul, ← heq, Mono.eval_trim]
      · rw [zero_add]
    rw [Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib, ih,
      sum_ite_getD hnd (hcov t List.mem_cons_self), Poly.eval_cons]

theorem eval_expand_coeffVecK (ms : List Mono) (hnd : (ms.map Mono.trim).Nodup) (p : Poly ZJ)
    (hcov : covered (ms.map Mono.trim) p = true) :
    Poly.eval h x (expand ms (coeffVecK (ms.map Mono.trim) p)) = Poly.eval h x p := by
  have hcov' : ∀ t ∈ p, Mono.trim t.2 ∈ ms.map Mono.trim := by
    intro t ht
    have := List.all_eq_true.mp hcov t ht
    simpa [List.contains_iff_mem] using this
  rw [eval_expand, ← sum_coefSum h x (ms.map Mono.trim) hnd p hcov', List.length_map]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l < ms.length := Finset.mem_range.mp hl
  have e1 : (coeffVecK (ms.map Mono.trim) p).getD l (0, 0) =
      coefSum ((ms.map Mono.trim).getD l []) (p.map fun t => (t.1, Mono.trim t.2)) := by
    simp only [coeffVecK]
    rw [List.getD_eq_getElem _ _ (by simpa using hl'), List.getD_eq_getElem _ _ (by simpa using hl')]
    simp
  have e2 : (ms.map Mono.trim).getD l [] = Mono.trim (ms.getD l []) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hl'), List.getD_eq_getElem _ _ hl']
    simp
  rw [e1, e2, Mono.eval_trim]

end Coeff

/-! ## The packed product test -/

/-- `Σ_{j<m} d_j 2^(72 j)`. -/
def packF (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => d 0 + packF (fun j => d (j + 1)) m * 2 ^ 72

theorem packF_add (d e : ℕ → ℕ) : ∀ m, packF d m + packF e m = packF (fun j => d j + e j) m
  | 0 => rfl
  | m + 1 => by
    simp only [packF]
    rw [← packF_add (fun j => d (j + 1)) (fun j => e (j + 1)) m]
    ring

theorem packF_smul (a : ℕ) (d : ℕ → ℕ) : ∀ m, a * packF d m = packF (fun j => a * d j) m
  | 0 => by simp [packF]
  | m + 1 => by
    simp only [packF]
    rw [← packF_smul a (fun j => d (j + 1)) m]
    ring

theorem packF_zero : ∀ m, packF (fun _ => 0) m = 0
  | 0 => rfl
  | m + 1 => by simp only [packF, packF_zero m]; ring

theorem packF_congr {d e : ℕ → ℕ} : ∀ {m}, (∀ j < m, d j = e j) → packF d m = packF e m
  | 0, _ => rfl
  | m + 1, hde => by
    simp only [packF]
    rw [hde 0 (Nat.succ_pos _), packF_congr fun j hj => hde (j + 1) (by omega)]

theorem packF_succ (d : ℕ → ℕ) (m : ℕ) : packF d (m + 1) = d 0 + packF (fun j => d (j + 1)) m * 2 ^ 72 := rfl

theorem packRow_cons (p c : ℕ) (bs : List ℕ) : packRow p (c :: bs) = c % p + (packRow p bs <<< 72) := rfl

theorem packRow_eq (p : ℕ) : ∀ b : List ℕ, packRow p b = packF (fun j => b.getD j 0 % p) b.length
  | [] => rfl
  | c :: bs => by
    rw [packRow_cons, packRow_eq p bs, Nat.shiftLeft_eq, List.length_cons, packF_succ]
    simp only [List.getD_cons_zero, List.getD_cons_succ]

/-- The integer entries of `a B`: `Σ_l a_l (B_{l j} mod p)`. -/
def dotSlots (p : ℕ) : List ℕ → List (List ℕ) → ℕ → ℕ
  | a :: as, b :: bs, j => a * (b.getD j 0 % p) + dotSlots p as bs j
  | _, _, _ => 0

theorem dotPacked_eq (p m : ℕ) : ∀ (a : List ℕ) (B : List (List ℕ)), (∀ b ∈ B, b.length = m) →
    dotPacked a (B.map (packRow p)) = packF (dotSlots p a B) m
  | [], B, _ => by cases B <;> simp [dotPacked, dotSlots, packF_zero]
  | c :: as, [], _ => by simp [dotPacked, dotSlots, packF_zero]
  | c :: as, b :: bs, hB => by
    simp only [List.map_cons, dotPacked]
    rw [dotPacked_eq p m as bs fun b' hb' => hB b' (List.mem_cons_of_mem _ hb'), packRow_eq, hB b List.mem_cons_self,
      packF_smul, packF_add]
    rfl

theorem dotSlots_le (p j : ℕ) : ∀ (a : List ℕ) (B : List (List ℕ)), (∀ c ∈ a, c < p) →
    dotSlots p a B j ≤ a.length * (p * p)
  | [], _, _ => by simp [dotSlots]
  | c :: as, [], _ => by simp [dotSlots]
  | c :: as, b :: bs, ha => by
    simp only [dotSlots, List.length_cons]
    have h1 : c * (b.getD j 0 % p) ≤ p * p := by
      have hc := ha c List.mem_cons_self
      have hp : 0 < p := by omega
      exact Nat.mul_le_mul hc.le (Nat.mod_lt _ hp).le
    have h2 := dotSlots_le p j as bs fun c' hc' => ha c' (List.mem_cons_of_mem _ hc')
    rw [Nat.add_mul, one_mul]
    omega

theorem slotsUnit_packF (p i : ℕ) : ∀ (m j : ℕ) (d : ℕ → ℕ), (∀ l < m, d l < 2 ^ 72) →
    slotsUnit p i m j (packF d m) = true → ∀ l < m, d l % p = if j + l = i then 1 else 0
  | 0, _, _, _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | m + 1, j, d, hd, h => by
    have hd0 := hd 0 (Nat.succ_pos _)
    simp only [slotsUnit, packF, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h0, h1⟩ := h
    have hmod : (d 0 + packF (fun j => d (j + 1)) m * 2 ^ 72) % 2 ^ 72 = d 0 := by
      rw [Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hd0
    have hshr : (d 0 + packF (fun j => d (j + 1)) m * 2 ^ 72) >>> 72 = packF (fun j => d (j + 1)) m := by
      rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hd0, zero_add]
    rw [hmod] at h0
    rw [hshr] at h1
    intro l hl
    cases l with
    | zero =>
      rw [h0]
      simp only [Nat.add_zero]
    | succ l =>
      have := slotsUnit_packF p i m (j + 1) (fun l => d (l + 1)) (fun l hl => hd (l + 1) (by omega)) h1 l (by omega)
      rw [this, show j + 1 + l = j + (l + 1) by omega]

/-- **The packed test**: `A B ≡ 1 (mod p)`, entry by entry. -/
theorem verifyPacked_sound {p m : ℕ} {A B : List (List ℕ)} (h : verifyPacked p m A B = true) :
    A.length = m ∧ B.length = m ∧ (∀ b ∈ B, b.length = m) ∧
      ∀ i < m, ∀ j < m, dotSlots p (A.getD i []) B j % p = if i = j then 1 else 0 := by
  simp only [verifyPacked, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hm, hp⟩, hA⟩, hB⟩, hBl⟩, hAl⟩, hrows⟩ := h
  refine ⟨hA, hB, hBl, fun i hi j hj => ?_⟩
  have hiA : i < A.length := by omega
  have hmem : (A[i], i) ∈ A.zipIdx := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simpa using hiA, by simp [List.getElem_zipIdx]⟩
  have hs := hrows _ hmem
  have ha := hAl _ (List.getElem_mem hiA)
  rw [dotPacked_eq p m _ _ hBl] at hs
  have hbound : ∀ l < m, dotSlots p A[i] B l < 2 ^ 72 := by
    intro l _
    have := dotSlots_le p l A[i] B ha.2
    rw [ha.1] at this
    have hpp : p * p < 2 ^ 62 := by
      calc p * p < 2 ^ 31 * 2 ^ 31 := Nat.mul_lt_mul'' hp hp
        _ = 2 ^ 62 := by norm_num
    calc dotSlots p A[i] B l ≤ m * (p * p) := this
      _ ≤ 128 * (p * p) := Nat.mul_le_mul_right _ hm
      _ < 128 * 2 ^ 62 := by omega
      _ ≤ 2 ^ 72 := by norm_num
  have := slotsUnit_packF p i m 0 _ hbound hs j hj
  rw [List.getD_eq_getElem _ _ hiA, this, zero_add]
  simp only [eq_comm]

/-! ## The check -/

theorem cast_dotSlots (p : ℕ) : ∀ (a : List ℕ) (B : List (List ℕ)) (j : ℕ) (m : ℕ), a.length = m → B.length = m →
    ((dotSlots p a B j : ℕ) : ZMod p) =
      ∑ l : Fin m, ((a.getD l 0 : ℕ) : ZMod p) * (((B.getD l []).getD j 0 : ℕ) : ZMod p)
  | [], [], _, m, ha, _ => by subst ha; simp [dotSlots]
  | [], _ :: _, _, m, ha, hB => by simp at ha hB; omega
  | _ :: _, [], _, m, ha, hB => by simp at ha hB; omega
  | c :: as, b :: bs, j, m, ha, hB => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨as.length, by simpa using ha.symm⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at ha hB
    rw [Fin.sum_univ_succ, dotSlots, Nat.cast_add, Nat.cast_mul, cast_dotSlots p as bs j m' ha hB]
    simp [ZMod.natCast_mod]

/-- **Soundness of the kernel Macaulay check** (the conclusion of `macCheck_sound`). -/
theorem macCheckK_sound {n D p s : ℕ} {fs : List (Poly ZJ × ℕ)} {sel : List ℕ} {B : List (List ℕ)} (hp : 1 < p)
    (hs : (s * s + 3) % p = 0) (hc : macCheckK n D p s fs sel B = true) (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
    (x : ℕ → ℂ) (hx : ∀ f ∈ fs, Poly.eval (zjHom ℂ ω hω) x f.1 = 0) : ∀ k < n, x k = 0 := by
  have : Fact (1 < p) := ⟨hp⟩
  have hp0 : 0 < p := by omega
  simp only [macCheckK] at hc
  generalize hms : monos n D = ms at hc
  generalize hrows : rowsRaw n D fs = rows at hc
  generalize hsrows : sel.map (fun r => rows.getD r []) = srows at hc
  generalize hAsub : srows.map (fun row => (coeffVecK (ms.map Mono.trim) row).map (toModS p s)) = Asub at hc
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hnd, hcov⟩, hsize⟩, hver⟩, hpow⟩ := hc
  have hnd' := nodupB_spec hnd
  obtain ⟨hAlen, hBlen, hBl, hdot⟩ := verifyPacked_sound hver
  set m := ms.length with hm
  set hz := zjHom ℂ ω hω
  have hslen : srows.length = m := by rw [← hsrows, List.length_map, hsize]
  -- every selected row vanishes, and equals the polynomial of its coefficient vector
  have hrow0 : ∀ i : ℕ, Poly.eval hz x (srows.getD i []) = 0 := by
    intro i
    by_cases hi : i < sel.length
    · rw [← hsrows, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
      generalize sel[i] = r
      by_cases hr' : r < rows.length
      · rw [List.getD_eq_getElem _ _ hr']
        have hmr : rows[r] ∈ rowsRaw n D fs := by rw [hrows]; exact List.getElem_mem hr'
        simp only [rowsRaw, List.mem_flatMap, List.mem_map] at hmr
        obtain ⟨f, hf, α, -, hfa⟩ := hmr
        rw [← hfa, Poly.eval_mulTerm, hx f hf, mul_zero]
      · rw [List.getD_eq_default _ _ (by omega)]
        rfl
    · rw [List.getD_eq_default _ _ (by rw [← hsrows, List.length_map]; omega)]
      rfl
  have hexp : ∀ i : ℕ, Poly.eval hz x (expand ms (coeffVecK (ms.map Mono.trim) (srows.getD i []))) =
      Poly.eval hz x (srows.getD i []) := by
    intro i
    by_cases hi : i < srows.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact eval_expand_coeffVecK hz x ms hnd' _ (hcov _ (List.getElem_mem hi))
    · rw [List.getD_eq_default _ _ (by omega), eval_expand]
      have h0 : hz.f (0, 0) = 0 := hz.map_zero
      have e : coeffVecK (ms.map Mono.trim) [] = (ms.map Mono.trim).map fun _ => ((0 : ℤ), (0 : ℤ)) := rfl
      rw [e]
      simp only [getD_map_list (fun _ => ((0 : ℤ), (0 : ℤ))) (ms.map Mono.trim) [] (0, 0) rfl, h0, zero_mul,
        Finset.sum_const_zero]
      rfl
  -- the matrices
  let aZ : Matrix (Fin m) (Fin m) (ℤ√(-3)) := fun i l =>
    twoZ ((coeffVecK (ms.map Mono.trim) (srows.getD i [])).getD l (0, 0))
  let Mp : Matrix (Fin m) (Fin m) (ZMod p) := fun i l => (((Asub.getD i []).getD l 0 : ℕ) : ZMod p)
  let Bp : Matrix (Fin m) (Fin m) (ZMod p) := fun l j => (((B.getD l []).getD j 0 : ℕ) : ZMod p)
  have hAsub_entry : ∀ (i : Fin m) (l : ℕ),
      (Asub.getD i []).getD l 0 = toModS p s ((coeffVecK (ms.map Mono.trim) (srows.getD i [])).getD l (0, 0)) := by
    intro i l
    have hi : (i : ℕ) < srows.length := by rw [hslen]; exact i.2
    have e1 : Asub.getD i [] = (coeffVecK (ms.map Mono.trim) (srows.getD i [])).map (toModS p s) := by
      rw [← hAsub, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]
    rw [e1, getD_map_list _ _ (0, 0) 0 (toModS_zero p s)]
  have hMp : (phiP p s hs).mapMatrix aZ = Mp := by
    ext i l
    simp only [aZ, Mp]
    rw [hAsub_entry]
    exact phiP_twoZ hp0 hs _
  have hMB : Mp * Bp = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hi : (i : ℕ) < Asub.length := by rw [hAlen]; exact i.2
    have hall : ∀ a ∈ Asub, a.length = m := by
      rw [← hAsub]
      intro a ha
      obtain ⟨row, -, rfl⟩ := List.mem_map.mp ha
      simp [coeffVecK, hm]
    have hlen : (Asub.getD i []).length = m := by
      rw [List.getD_eq_getElem _ _ hi]
      exact hall _ (List.getElem_mem hi)
    have hc := cast_dotSlots p (Asub.getD i []) B j m hlen hBlen
    rw [← hc, ← ZMod.natCast_mod, hdot i i.2 j j.2]
    simp only [Fin.ext_iff]
    split <;> simp
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
        2 * (hz.f ((coeffVecK (ms.map Mono.trim) (srows.getD i [])).getD l (0, 0)) * Mono.eval x (ms.getD l []) 0) := by
      intro l
      simp only [aZ, v]
      rw [psiC_twoZ hω]
      ring
    rw [Finset.sum_congr rfl fun l _ => e1 l, ← Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun l => hz.f ((coeffVecK (ms.map Mono.trim) (srows.getD i [])).getD l (0, 0)) *
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

end L6KSpec.E4
