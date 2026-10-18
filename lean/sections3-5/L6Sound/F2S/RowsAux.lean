import L6Sound.F2S.Mask

/-!
# Auxiliary facts for the rows of the specification search

* Values of forms: `formVal` of `form`, of `fsub`, of a zero form.
* The variables of nodes: `heightVec` at the variable of a node is the height of the node read off the complete tree.
* Facts about a complete tree with heights: the lowest common ancestor is a node (or absent), all heights and all
  exponents are at least the root height, `lca` is symmetric.
* Facts about a partial tree with `LevelFacts`: all its nodes have height at least `−2`.

The lemmas are in the namespace `L6.F2S.RS`.
-/

namespace L6.F2S.RS

open Finset
open L6.F2 (Diag pairs6)

/-! ## Arrays -/

theorem getElem!_set!_eq (a : Array Int) (i : Nat) (x : Int) (hi : i < a.size) : (a.set! i x)[i]! = x := by
  rw [Array.set!_eq_setIfInBounds]
  exact L6.Farkas.getElem!_setIfInBounds_self a i x hi

theorem getElem!_set!_ne (a : Array Int) (i j : Nat) (x : Int) (hij : i ≠ j) : (a.set! i x)[j]! = a[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  exact L6.Farkas.getElem!_setIfInBounds_ne a i j x hij

theorem size_set! (a : Array Int) (i : Nat) (x : Int) : (a.set! i x).size = a.size := by
  rw [Array.set!_eq_setIfInBounds]
  simp

/-! ## Values of forms -/

theorem formVal_set (a : Array Int) (nv i : Nat) (c : Int) (h : ℕ → ℚ) (ha : a.size = nv) (hi : i < nv) :
    formVal nv (a.set! i (a[i]! + c)) h = formVal nv a h + (c : ℚ) * h i := by
  unfold formVal
  have key : ∀ j ∈ range nv, ((a.set! i (a[i]! + c))[j]! : ℚ) * h j =
      (a[j]! : ℚ) * h j + (if j = i then (c : ℚ) * h i else 0) := by
    intro j _
    by_cases hji : j = i
    · subst hji
      rw [getElem!_set!_eq a j _ (by omega)]
      simp only [ite_true]
      push_cast
      ring
    · rw [getElem!_set!_ne a i j _ (Ne.symm hji)]
      simp [hji]
  rw [sum_congr rfl key, sum_add_distrib, sum_ite_eq' (range nv) i (fun _ => (c : ℚ) * h i)]
  simp [mem_range.mpr hi]

theorem form_foldl_size (cs : List (Nat × Int)) :
    ∀ a : Array Int, (cs.foldl (fun a ic => a.set! ic.1 (a[ic.1]! + ic.2)) a).size = a.size := by
  induction cs with
  | nil => intro a; rfl
  | cons ic cs ih =>
    intro a
    simp only [List.foldl_cons]
    rw [ih, size_set!]

theorem form_size (nv : Nat) (cs : List (Nat × Int)) : (form nv cs).size = nv := by
  unfold form
  rw [form_foldl_size]
  simp

theorem formVal_foldl (nv : Nat) (h : ℕ → ℚ) (cs : List (Nat × Int)) (hcs : ∀ ic ∈ cs, ic.1 < nv) :
    ∀ a : Array Int, a.size = nv →
      formVal nv (cs.foldl (fun a ic => a.set! ic.1 (a[ic.1]! + ic.2)) a) h =
        formVal nv a h + (cs.map fun ic => (ic.2 : ℚ) * h ic.1).sum := by
  induction cs with
  | nil => intro a _; simp
  | cons ic cs ih =>
    intro a ha
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx)) _ (by rw [size_set!]; exact ha),
      formVal_set a nv ic.1 ic.2 h ha (hcs ic List.mem_cons_self)]
    ring

theorem formVal_replicate (nv : Nat) (h : ℕ → ℚ) : formVal nv (Array.replicate nv 0) h = 0 := by
  unfold formVal
  refine sum_eq_zero fun j hj => ?_
  have hj' : j < (Array.replicate nv (0 : Int)).size := by simpa using mem_range.mp hj
  rw [getElem!_pos _ j hj']
  simp

/-- The value of a form with the given coefficients. -/
theorem formVal_form (nv : Nat) (cs : List (Nat × Int)) (h : ℕ → ℚ) (hcs : ∀ ic ∈ cs, ic.1 < nv) :
    formVal nv (form nv cs) h = (cs.map fun ic => (ic.2 : ℚ) * h ic.1).sum := by
  unfold form
  rw [formVal_foldl nv h cs hcs _ (by simp), formVal_replicate]
  ring

theorem formVal_sub {nv : Nat} {a b : Array Int} (ha : a.size = nv) (hb : b.size = nv) (h : ℕ → ℚ) :
    formVal nv (fsub a b) h = formVal nv a h - formVal nv b h := by
  unfold formVal fsub
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < nv := mem_range.mp hj
  have hza : j < (Array.zipWith (· - ·) a b).size := by simp [Array.size_zipWith, ha, hb, hj']
  rw [getElem!_pos (Array.zipWith (· - ·) a b) j hza, getElem!_pos a j (by omega),
    getElem!_pos b j (by omega), Array.getElem_zipWith]
  push_cast
  ring

/-! ## Strict forms of the rows -/

theorem strict_gt {nv : Nat} {d : Array Int} {h : ℕ → ℚ} :
    (rowGt d).StrictHolds nv h ↔ 0 < formVal nv d h := by
  unfold Row.StrictHolds rowGt
  simp [Row.lin, formVal]

theorem strict_eq {nv : Nat} {d : Array Int} {h : ℕ → ℚ} :
    (rowEq d).StrictHolds nv h ↔ formVal nv d h = 0 := by
  unfold Row.StrictHolds rowEq
  simp only [ite_true, Option.some.injEq, forall_eq', Int.cast_zero, Row.lin]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h2 h1
  · intro h0
    exact ⟨h0.symm.le, h0.le⟩

/-- A row `a ∈ [lo, hi]` with `c = 0`: its strict form is the two non-strict bounds. -/
theorem strict_c0 {nv : Nat} {a : Array Int} {lo hi : Option Int} {h : ℕ → ℚ} :
    (({ a := a, c := 0, lo := lo, hi := hi } : Row)).StrictHolds nv h ↔
      (∀ x, lo = some x → (x : ℚ) ≤ formVal nv a h) ∧ (∀ x, hi = some x → formVal nv a h ≤ (x : ℚ)) := by
  unfold Row.StrictHolds
  simp [Row.lin, formVal]

/-- A row `a + c s ≤ hi` with `c > 0` and no lower bound: its strict form is `a < hi`. -/
theorem strict_cpos {nv : Nat} {a : Array Int} {c : Int} (hc : 0 < c) {x : Int} {h : ℕ → ℚ} :
    (({ a := a, c := c, lo := none, hi := some x } : Row)).StrictHolds nv h ↔ formVal nv a h < (x : ℚ) := by
  unfold Row.StrictHolds
  have h1 : c ≠ 0 := by omega
  have h2 : ¬ c < 0 := by omega
  simp [h1, h2, Row.lin, formVal]

/-- A row `lo ≤ a + c s` with `c < 0` and no upper bound: its strict form is `lo < a`. -/
theorem strict_cneg {nv : Nat} {a : Array Int} {c : Int} (hc : c < 0) {x : Int} {h : ℕ → ℚ} :
    (({ a := a, c := c, lo := some x, hi := none } : Row)).StrictHolds nv h ↔ (x : ℚ) < formVal nv a h := by
  unfold Row.StrictHolds
  have h1 : c ≠ 0 := by omega
  simp [h1, hc, Row.lin, formVal]

/-! ## Variables of nodes -/

theorem idx_lt {T : TS} {C : Nat} (hC : C ∈ T.nodes) : T.idx C < T.nodes.length :=
  List.idxOf_lt_length_of_mem hC

theorem getD_idx {T : TS} {C : Nat} (hC : C ∈ T.nodes) : T.nodes.getD (T.idx C) 0 = C := by
  unfold TS.idx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hC)]
  simp [List.getElem_idxOf]

theorem heightVec_vz {Xz Xw : ExpTree} {P : Pair} {C : Nat} (hC : C ∈ P.tz.nodes) :
    heightVec Xz Xw P (P.tz.idx C) = Xz.hc C := by
  have h1 : P.tz.idx C < P.nz := by unfold Pair.nz; exact idx_lt hC
  unfold heightVec
  simp only [h1, ite_true, getD_idx hC]

theorem heightVec_vw {Xz Xw : ExpTree} {P : Pair} {C : Nat} (hC : C ∈ P.tw.nodes) :
    heightVec Xz Xw P (P.nz + P.tw.idx C) = Xw.hc C := by
  have h1 : ¬ P.nz + P.tw.idx C < P.nz := by omega
  unfold heightVec
  simp only [h1, ite_false, show P.nz + P.tw.idx C - P.nz = P.tw.idx C by omega, getD_idx hC]

theorem vz_lt {P : Pair} {C : Nat} (hC : C ∈ P.tz.nodes) : P.tz.idx C < P.nv := by
  have := idx_lt hC
  unfold Pair.nv
  omega

theorem vw_lt {P : Pair} {C : Nat} (hC : C ∈ P.tw.nodes) : P.nz + P.tw.idx C < P.nv := by
  have := idx_lt hC
  unfold Pair.nv Pair.nz
  omega

/-! ## The lowest common ancestor in a tree -/

/-- A fold whose step keeps the accumulator or replaces it by the current element ends with the initial value or
with some element of the list. -/
theorem foldl_mem_or (f : Option Nat → Nat → Option Nat) (hf : ∀ acc C, f acc C = acc ∨ f acc C = some C) :
    ∀ (L : List Nat) (acc : Option Nat), L.foldl f acc = acc ∨ ∃ C ∈ L, L.foldl f acc = some C
  | [], acc => Or.inl rfl
  | x :: L, acc => by
    simp only [List.foldl_cons]
    rcases foldl_mem_or f hf L (f acc x) with h | ⟨C, hC, h⟩
    · rcases hf acc x with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨x, List.mem_cons_self, h.trans h'⟩
    · exact Or.inr ⟨C, List.mem_cons_of_mem _ hC, h⟩

theorem foldl_some_mem {f : Option Nat → Nat → Option Nat} (hf : ∀ acc C, f acc C = acc ∨ f acc C = some C)
    {L : List Nat} {C : Nat} (h : L.foldl f none = some C) : C ∈ L := by
  rcases foldl_mem_or f hf L none with h' | ⟨C', hC', h'⟩
  · rw [h] at h'
    exact absurd h' (by simp)
  · rw [h] at h'
    cases h'
    exact hC'

theorem lca_mem {T : TS} {p q C : Nat} (h : T.lca p q = some C) : C ∈ T.nodes := by
  unfold TS.lca at h
  refine foldl_some_mem ?_ h
  intro acc C
  split_ifs
  · cases acc with
    | none => exact Or.inr rfl
    | some D =>
      dsimp only
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · exact Or.inl rfl

theorem lca_comm (T : TS) (p q : Nat) : T.lca p q = T.lca q p := by
  unfold TS.lca
  congr 1
  funext acc C
  rw [Bool.and_comm (mem q C)]

theorem toList_all : toList all = [0, 1, 2, 3, 4, 5, 6] := by decide

theorem twoLeaves_all (T : TS) : twoLeaves T all = true := by
  have h01 : T.lrep 0 ≠ T.lrep 1 := by
    unfold TS.lrep
    cases T.leafO with
    | none => simp
    | some k =>
      dsimp only
      by_cases hk0 : k = 0
      · subst hk0
        decide
      · by_cases hk1 : k = 1
        · subst hk1
          decide
        · simp [beq_false_of_ne (Ne.symm hk0), beq_false_of_ne (Ne.symm hk1)]
  unfold twoLeaves
  rw [toList_all, List.any_eq_true]
  refine ⟨0, by simp, ?_⟩
  rw [List.any_eq_true]
  exact ⟨1, by simp, by simpa using h01⟩

/-! ## Complete trees with heights -/

theorem h_ge {X : ExpTree} (hX : X.Good) (hr : -2 ≤ X.h all) : ∀ C ∈ X.T.nodes, -2 ≤ X.h C := by
  intro C hC
  have hall : all ∈ X.T.nodes := hX.1.root (twoLeaves_all X.T)
  by_cases hCa : C = all
  · subst hCa
    exact hr
  · have hss : ssubset C all = true := by
      unfold ssubset
      simp [hX.1.sub C hC, hCa]
    have := hX.2 C hC all hall hss
    linarith

theorem e_ge {X : ExpTree} (hX : X.Good) (hr : -2 ≤ X.h all) (p q : Nat) : -2 ≤ X.e p q := by
  unfold ExpTree.e
  cases h : X.T.lca p q with
  | none => norm_num
  | some C => exact h_ge hX hr C (lca_mem h)

theorem e_comm (X : ExpTree) (p q : Nat) : X.e p q = X.e q p := by
  unfold ExpTree.e
  rw [lca_comm]

theorem zstroke_comm (D : Diag) (k l : Nat) : D.zstroke k l = D.zstroke l k := by
  unfold Diag.zstroke
  rw [min_comm, max_comm]

theorem wstroke_comm (D : Diag) (k l : Nat) : D.wstroke k l = D.wstroke l k := by
  unfold Diag.wstroke
  rw [min_comm, max_comm]

section cond

variable {D : Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw)
include hX

theorem zeta_ge (k l : Nat) : -2 ≤ Xz.e k l := e_ge hX.gz hX.root_z k l

theorem omega_ge (k l : Nat) : -2 ≤ Xw.e k l := e_ge hX.gw hX.root_w k l

theorem O1z' {k l : Nat} (hkl : k ≠ l) (hk : k < 6) (hl : l < 6) : Xz.e k l + 3 * Xw.e k l ≤ 4 := by
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · exact hX.O1z k l h hl
  · rw [e_comm Xz, e_comm Xw]
    exact hX.O1z l k h hk

theorem O1w' {k l : Nat} (hkl : k ≠ l) (hk : k < 6) (hl : l < 6) : 3 * Xz.e k l + Xw.e k l ≤ 4 := by
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · exact hX.O1w k l h hl
  · rw [e_comm Xz, e_comm Xw]
    exact hX.O1w l k h hk

theorem O2z' {k l : Nat} (hkl : k ≠ l) (hk : k < 6) (hl : l < 6) :
    (Xz.e k l + 3 * Xw.e k l = 4 ↔ D.zstroke k l = true) := by
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · exact hX.O2z k l h hl
  · rw [e_comm Xz, e_comm Xw, zstroke_comm]
    exact hX.O2z l k h hk

theorem O2w' {k l : Nat} (hkl : k ≠ l) (hk : k < 6) (hl : l < 6) :
    (3 * Xz.e k l + Xw.e k l = 4 ↔ D.wstroke k l = true) := by
  rcases Nat.lt_or_gt_of_ne hkl with h | h
  · exact hX.O2w k l h hl
  · rw [e_comm Xz, e_comm Xw, wstroke_comm]
    exact hX.O2w l k h hk

theorem x_le_one {k l : Nat} (hkl : k ≠ l) (hk : k < 6) (hl : l < 6) : xkl Xz Xw k l ≤ 1 := by
  have h1 := O1z' hX hkl hk hl
  have h2 := O1w' hX hkl hk hl
  unfold xkl
  linarith

theorem x_eq_one_iff {k l : Nat} (hkl : k ≠ l) (hk : k < 6) (hl : l < 6) :
    xkl Xz Xw k l = 1 ↔ (D.zstroke k l && D.wstroke k l) = true := by
  have h1 := O1z' hX hkl hk hl
  have h2 := O1w' hX hkl hk hl
  rw [Bool.and_eq_true, ← O2z' hX hkl hk hl, ← O2w' hX hkl hk hl]
  unfold xkl
  constructor
  · intro h
    constructor <;> linarith
  · rintro ⟨ha, hb⟩
    linarith

theorem lowerX_le {k l : Nat} (hkl : k ≠ l) (hk : k < 6) (hl : l < 6) :
    ((lowerX D k l : Int) : ℚ) ≤ xkl Xz Xw k l := by
  have hz := zeta_ge hX k l
  have hw := omega_ge hX k l
  have h1 := O1z' hX hkl hk hl
  have h2 := O1w' hX hkl hk hl
  have e1 := O2z' hX hkl hk hl
  have e2 := O2w' hX hkl hk hl
  unfold lowerX xkl
  cases hzs : D.zstroke k l <;> cases hws : D.wstroke k l
  · simp only [Bool.and_self, Bool.or_self, Bool.false_eq_true, ite_false]
    push_cast
    linarith
  · simp only [Bool.false_and, Bool.false_or, Bool.false_eq_true, ite_false, ite_true]
    have := e2.mpr hws
    push_cast
    linarith
  · simp only [Bool.and_false, Bool.true_or, Bool.false_eq_true, ite_false, ite_true]
    have := e1.mpr hzs
    push_cast
    linarith
  · simp only [Bool.and_self, ite_true]
    have := e1.mpr hzs
    have := e2.mpr hws
    push_cast
    linarith

end cond

/-! ## Partial trees -/

theorem hc_ge_of_levelFacts {X : ExpTree} {T : TS} {S : Nat} (hf : LevelFacts X T S) :
    ∀ C ∈ T.nodes, -2 ≤ X.hc C := by
  intro C hC
  obtain ⟨C0, hC0, hmin⟩ := T.nodes.toFinset.exists_min_image X.hc ⟨C, List.mem_toFinset.mpr hC⟩
  have h0 : -2 ≤ X.hc C0 := by
    rcases hf.par C0 (List.mem_toFinset.mp hC0) with ⟨_, h⟩ | ⟨P, hP, _, hlt⟩
    · exact h
    · have := hmin P (List.mem_toFinset.mpr hP)
      linarith
  have := hmin C (List.mem_toFinset.mpr hC)
  linarith

end L6.F2S.RS
