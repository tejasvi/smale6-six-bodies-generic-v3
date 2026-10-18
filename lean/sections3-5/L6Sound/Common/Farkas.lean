import Mathlib
import L6Common.Rows

/-!
# Lemma 4.6: soundness of the certificate check

`L6.Farkas.check n rows cert` (module `L6Common.Rows`) tests the hypotheses of Lemma 4.6 of the paper for integer
multipliers. We prove, over any ordered field:

* `L6.Farkas.check_sound`: if the check passes, there are no heights `h` and slack `s > 0` satisfying the rows used
  by the certificate (`lo ≤ a · h + c · s ≤ hi`);
* `L6.Farkas.check_sound_strict`: if the check passes and the rows used are *strict-form* rows (a row with `c ≠ 0`
  has its only bound on the side that `s` relaxes), there are no heights satisfying their strict forms
  (`Row.strictHolds`: `lo ≤ a · h ≤ hi` when `c = 0`, `lo < a · h` when `c < 0`, `a · h < hi` when `c > 0`).

The strict form is the polyhedron of the paper: equalities and non-strict inequalities, and strict inequalities
encoded with the common slack `s`.
-/

namespace L6

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

set_option linter.unusedSectionVars false

namespace Row

/-- `a · h` over the first `n` heights. -/
def lin (n : ℕ) (r : Row) (h : ℕ → K) : K := ∑ j ∈ range n, (r.a[j]! : K) * h j

/-- The row holds at heights `h` and slack `s`. -/
def Holds (n : ℕ) (r : Row) (h : ℕ → K) (s : K) : Prop :=
  (∀ lo, r.lo = some lo → (lo : K) ≤ r.lin n h + r.c * s) ∧ (∀ hi, r.hi = some hi → r.lin n h + r.c * s ≤ hi)

/-- The strict form of the row at heights `h`. -/
def StrictHolds (n : ℕ) (r : Row) (h : ℕ → K) : Prop :=
  if r.c = 0 then (∀ lo, r.lo = some lo → (lo : K) ≤ r.lin n h) ∧ (∀ hi, r.hi = some hi → r.lin n h ≤ hi)
  else if r.c < 0 then (∀ lo, r.lo = some lo → (lo : K) < r.lin n h) ∧ r.hi = none
  else (∀ hi, r.hi = some hi → r.lin n h < hi) ∧ r.lo = none

end Row

namespace Farkas

/-! ## The linear combination -/

/-- `Σ_{j<n} v[j]! h_j`. -/
def dot (n : ℕ) (v : Array Int) (h : ℕ → K) : K := ∑ j ∈ range n, (v[j]! : K) * h j

theorem getElem!_setIfInBounds_self (v : Array Int) (j : ℕ) (x : Int) (hj : j < v.size) :
    (v.setIfInBounds j x)[j]! = x := by
  rw [getElem!_pos (v.setIfInBounds j x) j (by simpa using hj)]
  exact Array.getElem_setIfInBounds_self _

theorem getElem!_setIfInBounds_ne (v : Array Int) (j k : ℕ) (x : Int) (hjk : j ≠ k) :
    (v.setIfInBounds j x)[k]! = v[k]! := by
  by_cases hk : k < v.size
  · rw [getElem!_pos (v.setIfInBounds j x) k (by simpa using hk), getElem!_pos v k hk]
    exact Array.getElem_setIfInBounds_ne hk hjk
  · rw [getElem!_neg (v.setIfInBounds j x) k (by simpa using hk), getElem!_neg v k hk]

/-- The fold of `axpy` over a list of distinct indices. -/
theorem foldl_axpy (y : Int) (a : Array Int) :
    ∀ (L : List ℕ) (v : Array Int), L.Nodup → (∀ j ∈ L, j < v.size) →
      (L.foldl (fun v j => v.set! j (v[j]! + y * a[j]!)) v).size = v.size ∧
      ∀ k, (L.foldl (fun v j => v.set! j (v[j]! + y * a[j]!)) v)[k]! = v[k]! + if k ∈ L then y * a[k]! else 0
  | [], v, _, _ => by simp
  | j :: L, v, hnd, hlt => by
    have hj : j < v.size := hlt j (by simp)
    have hnd' := List.nodup_cons.mp hnd
    set v' := v.set! j (v[j]! + y * a[j]!) with hv'
    have hsz : v'.size = v.size := by simp [hv']
    have ih := foldl_axpy y a L v' hnd'.2 (fun k hk => by rw [hsz]; exact hlt k (by simp [hk]))
    simp only [List.foldl_cons]
    refine ⟨by rw [ih.1, hsz], fun k => ?_⟩
    rw [ih.2 k]
    by_cases hk : k = j
    · subst hk
      have : k ∉ L := hnd'.1
      simp only [hv', Array.set!_eq_setIfInBounds, getElem!_setIfInBounds_self v k _ hj]
      simp [this]
    · simp only [hv', Array.set!_eq_setIfInBounds, getElem!_setIfInBounds_ne v j k _ (Ne.symm hk)]
      simp [hk]

theorem axpy_size (n : ℕ) (v : Array Int) (y : Int) (a : Array Int) (hv : v.size = n) :
    (axpy n v y a).size = n := by
  have := (foldl_axpy y a (List.range n) v (List.nodup_range) (fun j hj => by
    rw [hv]; exact List.mem_range.mp hj)).1
  unfold axpy; rw [this, hv]

theorem axpy_get (n : ℕ) (v : Array Int) (y : Int) (a : Array Int) (hv : v.size = n) {k : ℕ} (hk : k < n) :
    (axpy n v y a)[k]! = v[k]! + y * a[k]! := by
  have := (foldl_axpy y a (List.range n) v (List.nodup_range) (fun j hj => by
    rw [hv]; exact List.mem_range.mp hj)).2 k
  unfold axpy; rw [this]; simp [hk]

theorem dot_axpy (n : ℕ) (v : Array Int) (y : Int) (a : Array Int) (hv : v.size = n) (h : ℕ → K) :
    dot n (axpy n v y a) h = dot n v h + (y : K) * ∑ j ∈ range n, (a[j]! : K) * h j := by
  unfold dot
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j hj => ?_
  rw [axpy_get n v y a hv (mem_range.mp hj)]
  push_cast; ring

/-- One row with its multiplier: `y (a · h + c s) ≤ y · bound`. -/
theorem row_comb {n : ℕ} {r : Row} {h : ℕ → K} {s : K} (hr : r.Holds n h s) {y bd : Int}
    (hb : r.bound? y = some bd) : (y : K) * (r.lin n h + r.c * s) ≤ (y : K) * bd := by
  unfold Row.bound? at hb
  split_ifs at hb with hy hy'
  · exact mul_le_mul_of_nonneg_left (hr.2 bd hb) (by exact_mod_cast hy.le)
  · exact mul_le_mul_of_nonpos_left (hr.1 bd hb) (by exact_mod_cast hy'.le)
  · have : y = 0 := by omega
    subst this; simp

/-- A monotone row that holds at `s` holds at any smaller positive `s'`. -/
theorem holds_mono {n : ℕ} {r : Row} {h : ℕ → K} {s s' : K} (hm : r.monotone = true) (hr : r.Holds n h s)
    (hs : s' ≤ s) : r.Holds n h s' := by
  unfold Row.monotone at hm
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hm
  obtain ⟨h1, h2⟩ := hm
  refine ⟨fun lo hlo => ?_, fun hi hhi => ?_⟩
  · rcases h1 with hc | hc
    · have : (r.c : K) * s ≤ r.c * s' := mul_le_mul_of_nonpos_left hs (by exact_mod_cast hc)
      linarith [hr.1 lo hlo]
    · rw [hc] at hlo; exact absurd hlo (by simp)
  · rcases h2 with hc | hc
    · have : (r.c : K) * s' ≤ r.c * s := mul_le_mul_of_nonneg_left hs (by exact_mod_cast hc)
      linarith [hr.2 hi hhi]
    · rw [hc] at hhi; exact absurd hhi (by simp)

/-- Folding preserves an invariant (used with the step function of `combine`). -/
theorem foldl_inv {α β : Type*} (f : β → α → β) (P : β → Prop) (Q : α → Prop)
    (hstep : ∀ b a, Q a → P b → P (f b a)) : ∀ (L : List α) (b : β), (∀ a ∈ L, Q a) → P b → P (L.foldl f b)
  | [], _, _, hb => hb
  | a :: L, b, hQ, hb => foldl_inv f P Q hstep L (f b a) (fun x hx => hQ x (by simp [hx]))
      (hstep b a (hQ a (by simp)) hb)

/-- The invariant of `combine`: at heights and slack where all monotone rows of the certificate hold, the
accumulated combination satisfies `Σ v h + g s ≤ b`. -/
theorem combine_inv {n : ℕ} {rows : Array Row} {cert : List (ℕ × Int)} {h : ℕ → K} {s : K}
    (hrows : ∀ p ∈ cert, ∀ r, rows[p.1]? = some r → r.monotone = true → r.Holds n h s)
    {v : Array Int} {g b : Int} (hcomb : combine n rows cert = some (v, g, b)) :
    v.size = n ∧ dot n v h + (g : K) * s ≤ b := by
  unfold combine at hcomb
  let P : Option (Array Int × Int × Int) → Prop := fun acc =>
    ∀ v g b, acc = some (v, g, b) → v.size = n ∧ dot n v h + (g : K) * s ≤ b
  let Q : ℕ × Int → Prop := fun p => ∀ r, rows[p.1]? = some r → r.monotone = true → r.Holds n h s
  refine foldl_inv _ P Q ?_ cert (some (Array.replicate n 0, 0, 0)) hrows ?_ v g b hcomb
  · rintro acc ⟨i, y⟩ hQ hP v' g' b' hstep
    cases acc with
    | none => simp at hstep
    | some t =>
      obtain ⟨v0, g0, b0⟩ := t
      obtain ⟨hsz0, hineq0⟩ := hP v0 g0 b0 rfl
      cases hri : rows[i]? with
      | none => simp [hri] at hstep
      | some r =>
        simp only [hri] at hstep
        by_cases hy : y = 0
        · simp only [hy, ite_true, Option.some.injEq, Prod.mk.injEq] at hstep
          obtain ⟨rfl, rfl, rfl⟩ := hstep
          exact ⟨hsz0, hineq0⟩
        · simp only [hy, ite_false] at hstep
          by_cases hm : r.monotone = true
          · simp only [hm, Bool.not_true, Bool.false_eq_true, ite_false] at hstep
            cases hb : r.bound? y with
            | none => simp [hb] at hstep
            | some bd =>
              simp only [hb, Option.some.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl, rfl⟩ := hstep
              refine ⟨axpy_size n v0 y r.a hsz0, ?_⟩
              have hr := hQ r hri hm
              have hc := row_comb hr hb
              rw [dot_axpy n v0 y r.a hsz0 h]
              unfold Row.lin at hc
              push_cast
              nlinarith [hc, hineq0]
          · simp only [Bool.not_eq_true] at hm
            simp [hm] at hstep
  · intro v g b h0
    simp only [Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl, rfl⟩ := h0
    refine ⟨by simp, ?_⟩
    have : dot n (Array.replicate n (0 : Int)) h = 0 := by
      unfold dot
      refine sum_eq_zero fun j hj => ?_
      have hj' : j < (Array.replicate n (0 : Int)).size := by simpa using mem_range.mp hj
      rw [getElem!_pos _ j hj']
      simp
    rw [this]; simp

/-- All entries of an array of size `n` are zero, so its dot product is zero. -/
theorem dot_eq_zero {n : ℕ} {v : Array Int} (hsz : v.size = n) (hv : v.all (· == 0) = true) (h : ℕ → K) :
    dot n v h = 0 := by
  unfold dot
  refine sum_eq_zero fun j hj => ?_
  have hj' : j < v.size := by rw [hsz]; exact mem_range.mp hj
  rw [Array.all_eq_true] at hv
  have := hv j hj'
  rw [getElem!_pos v j hj']
  simp only [beq_iff_eq] at this
  simp [this]

/-! ## Lemma 4.6 -/

/-- **Lemma 4.6.** If `Farkas.check n rows cert` passes, no heights `h` and slack `s > 0` satisfy the rows of the
certificate. -/
theorem check_sound {n : ℕ} {rows : Array Row} {cert : List (ℕ × Int)} (hc : check n rows cert = true)
    (h : ℕ → K) (s : K) (hs : 0 < s) (hrows : ∀ p ∈ cert, ∀ r, rows[p.1]? = some r → r.Holds n h s) : False := by
  unfold check at hc
  cases hcomb : combine n rows cert with
  | none => simp [hcomb] at hc
  | some t =>
    obtain ⟨v, g, b⟩ := t
    simp only [hcomb, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hc
    obtain ⟨⟨hv, hb⟩, hg⟩ := hc
    set s' : K := min s 1 with hs'
    have hs'pos : 0 < s' := lt_min hs one_pos
    have hs'le : s' ≤ 1 := min_le_right _ _
    have hrows' : ∀ p ∈ cert, ∀ r, rows[p.1]? = some r → r.monotone = true → r.Holds n h s' :=
      fun p hp r hr hm => holds_mono hm (hrows p hp r hr) (min_le_left _ _)
    obtain ⟨hsz, hineq⟩ := combine_inv hrows' hcomb
    rw [dot_eq_zero hsz hv h, zero_add] at hineq
    -- with gm = max 0 (-g): (g + gm) s' ≤ b + gm ≤ 0 ≤ (g + gm) s'
    set gm : Int := if g < 0 then -g else 0 with hgm
    have hgm0 : 0 ≤ gm := by rw [hgm]; split_ifs <;> omega
    have hggm : 0 ≤ g + gm := by rw [hgm]; split_ifs <;> omega
    have h1 : ((g + gm : Int) : K) * s' ≤ ((b + gm : Int) : K) := by
      push_cast
      have : (gm : K) * s' ≤ gm := by
        have := mul_le_mul_of_nonneg_left hs'le (show (0 : K) ≤ gm by exact_mod_cast hgm0)
        simpa using this
      linarith
    have h2 : ((b + gm : Int) : K) ≤ 0 := by exact_mod_cast hb
    have h3 : (0 : K) ≤ ((g + gm : Int) : K) * s' :=
      mul_nonneg (by exact_mod_cast hggm) hs'pos.le
    rcases hg with hg | hg
    · have : (0 : K) < ((g + gm : Int) : K) * s' := mul_pos (by exact_mod_cast hg) hs'pos
      linarith
    · have : ((b + gm : Int) : K) < 0 := by exact_mod_cast hg
      linarith

/-! ## The strict form -/

/-- A row in strict form (a row with `c ≠ 0` has only the bound that decreasing `s` relaxes) has, at heights where
its strict form holds, a positive slack at which it holds, and it then holds at every smaller positive slack. -/
theorem exists_slack_row {n : ℕ} {r : Row} {h : ℕ → K} (hr : r.StrictHolds n h) :
    ∃ s : K, 0 < s ∧ ∀ s', 0 < s' → s' ≤ s → r.Holds n h s' := by
  unfold Row.StrictHolds at hr
  split_ifs at hr with hc0 hcn
  · refine ⟨1, one_pos, fun s' _ _ => ⟨fun lo hlo => ?_, fun hi hhi => ?_⟩⟩
    · rw [hc0]; simpa using hr.1 lo hlo
    · rw [hc0]; simpa using hr.2 hi hhi
  · -- c < 0: lower bound only
    obtain ⟨hlo, hhi⟩ := hr
    have hc : (r.c : K) < 0 := by exact_mod_cast hcn
    cases hl : r.lo with
    | none =>
      refine ⟨1, one_pos, fun s' _ _ => ⟨fun lo h' => by simp [hl] at h', fun hi h' => by simp [hhi] at h'⟩⟩
    | some lo =>
      have hm := hlo lo hl
      refine ⟨(r.lin n h - lo) / (-(r.c : K)), div_pos (by linarith) (by linarith), fun s' hs' hle =>
        ⟨fun lo' hlo' => ?_, fun hi h' => by simp [hhi] at h'⟩⟩
      rw [hl, Option.some.injEq] at hlo'
      subst hlo'
      have : (-(r.c : K)) * s' ≤ r.lin n h - lo := by
        have := mul_le_mul_of_nonneg_left hle (show (0 : K) ≤ -(r.c : K) by linarith)
        rwa [mul_div_cancel₀ _ (show (-(r.c : K)) ≠ 0 by linarith)] at this
      linarith
  · -- c > 0: upper bound only
    obtain ⟨hhi, hlo⟩ := hr
    have hc : (0 : K) < r.c := by
      have : 0 < r.c := by omega
      exact_mod_cast this
    cases hh : r.hi with
    | none =>
      refine ⟨1, one_pos, fun s' _ _ => ⟨fun lo h' => by simp [hlo] at h', fun hi h' => by simp [hh] at h'⟩⟩
    | some hi =>
      have hm := hhi hi hh
      refine ⟨(hi - r.lin n h) / (r.c : K), div_pos (by linarith) hc, fun s' hs' hle =>
        ⟨fun lo h' => by simp [hlo] at h', fun hi' hhi' => ?_⟩⟩
      rw [hh, Option.some.injEq] at hhi'
      subst hhi'
      have : (r.c : K) * s' ≤ hi - r.lin n h := by
        have := mul_le_mul_of_nonneg_left hle hc.le
        rwa [mul_div_cancel₀ _ (show (r.c : K) ≠ 0 by linarith)] at this
      linarith

/-- Finitely many rows in strict form, all holding strictly at `h`, hold at a common positive slack. -/
theorem exists_slack {n : ℕ} {rows : Array Row} {h : ℕ → K} :
    ∀ (L : List (ℕ × Int)), (∀ p ∈ L, ∀ r, rows[p.1]? = some r → r.StrictHolds n h) →
      ∃ s : K, 0 < s ∧ ∀ p ∈ L, ∀ r, rows[p.1]? = some r → ∀ s', 0 < s' → s' ≤ s → r.Holds n h s'
  | [], _ => ⟨1, one_pos, fun p hp => by simp at hp⟩
  | p :: L, hL => by
    obtain ⟨s₁, hs₁, h₁⟩ := exists_slack L (fun q hq => hL q (by simp [hq]))
    cases hp : rows[p.1]? with
    | none =>
      exact ⟨s₁, hs₁, fun q hq r hr => by
        rcases List.mem_cons.mp hq with rfl | hq
        · rw [hp] at hr; exact absurd hr (by simp)
        · exact h₁ q hq r hr⟩
    | some r₀ =>
      obtain ⟨s₂, hs₂, h₂⟩ := exists_slack_row (hL p (by simp) r₀ hp)
      refine ⟨min s₁ s₂, lt_min hs₁ hs₂, fun q hq r hr s' hs' hle => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [hp, Option.some.injEq] at hr; subst hr
        exact h₂ s' hs' (le_trans hle (min_le_right _ _))
      · exact h₁ q hq r hr s' hs' (le_trans hle (min_le_left _ _))

/-- **Lemma 4.6, strict form.** If `Farkas.check n rows cert` passes, no heights satisfy the strict forms of the rows
of the certificate. -/
theorem check_sound_strict {n : ℕ} {rows : Array Row} {cert : List (ℕ × Int)} (hc : check n rows cert = true)
    (h : ℕ → K) (hrows : ∀ p ∈ cert, ∀ r, rows[p.1]? = some r → r.StrictHolds n h) : False := by
  obtain ⟨s, hs, hall⟩ := exists_slack cert hrows
  exact check_sound hc h s hs fun p hp r hr => hall p hp r hr s hs le_rfl

/-- The same, for the whole system: no heights satisfy the strict forms of all rows. -/
theorem check_sound_strict_all {n : ℕ} {rows : Array Row} {cert : List (ℕ × Int)} (hc : check n rows cert = true)
    (h : ℕ → K) (hrows : ∀ r ∈ rows, r.StrictHolds n h) : False :=
  check_sound_strict hc h fun _ _ r hr => hrows r (Array.mem_of_getElem? hr)

end Farkas

end L6
