import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.Weight
import Mathlib.Order.WellFoundedSet
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.List.GetD
import Lean6.Special.Comp.D88.Count.Order

/-!
# The graded reverse lexicographic order as a `MonomialOrder`

Mathlib provides `MonomialOrder.degLex`; this file builds the graded reverse lexicographic order in the same
framework: `DegRevLex (α →₀ ℕ)` ordered by the degree, then by the colexicographic order reversed (at equal degree,
at the largest index where the exponents differ, the smaller exponent gives the larger monomial). For a finite `σ`
this is a monomial order, `degRevLex σ`, with `single i 1 ≻ single j 1 ↔ i < j` (`degRevLex_single_lt_iff`).

`grevGtStd_iff`: on exponent lists of length `n`, the comparator `Comp.Count.grevGtStd` of the checkers is this
order on `Fin n →₀ ℕ` (through `vec n`).
-/

namespace Lean6.Special.D88.Count

open Finsupp
open scoped MonomialOrder

/-- A type synonym carrying the graded reverse lexicographic order. -/
def DegRevLex (α : Type*) := α

variable {α : Type*}

/-- `toDegRevLex` is the identity, into the synonym. -/
def toDegRevLex : α ≃ DegRevLex α := Equiv.refl _

/-- `ofDegRevLex` is the identity, out of the synonym. -/
def ofDegRevLex : DegRevLex α ≃ α := Equiv.refl _

@[simp] theorem ofDegRevLex_toDegRevLex (a : α) : ofDegRevLex (toDegRevLex a) = a := rfl

@[simp] theorem toDegRevLex_ofDegRevLex (a : DegRevLex α) : toDegRevLex (ofDegRevLex a) = a := rfl

theorem toDegRevLex_inj {a b : α} : toDegRevLex a = toDegRevLex b ↔ a = b := Iff.rfl

noncomputable instance [AddCommMonoid α] : AddCommMonoid (DegRevLex α) := ofDegRevLex.addCommMonoid

theorem toDegRevLex_add [AddCommMonoid α] (a b : α) : toDegRevLex (a + b) = toDegRevLex a + toDegRevLex b := rfl

theorem ofDegRevLex_add [AddCommMonoid α] (a b : DegRevLex α) :
    ofDegRevLex (a + b) = ofDegRevLex a + ofDegRevLex b := rfl

namespace DegRevLex

variable [LinearOrder α]

/-- The key of the order: the degree, then the colexicographic order reversed. -/
noncomputable def key (f : DegRevLex (α →₀ ℕ)) : Lex (ℕ × (Colex (α →₀ ℕ))ᵒᵈ) :=
  toLex ((ofDegRevLex f).degree, OrderDual.toDual (toColex (ofDegRevLex f)))

omit [LinearOrder α] in
theorem key_injective : Function.Injective (key (α := α)) := by
  intro f g h
  have h2 := congrArg (fun x => (ofLex x).2) h
  simpa [key] using h2

/-- The graded reverse lexicographic order. -/
noncomputable instance : LinearOrder (DegRevLex (α →₀ ℕ)) := LinearOrder.lift' key key_injective

theorem lt_def {a b : DegRevLex (α →₀ ℕ)} : a < b ↔ key a < key b := Iff.rfl

theorem le_def {a b : DegRevLex (α →₀ ℕ)} : a ≤ b ↔ key a ≤ key b := Iff.rfl

theorem lt_iff {a b : DegRevLex (α →₀ ℕ)} :
    a < b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      ((ofDegRevLex a).degree = (ofDegRevLex b).degree ∧ toColex (ofDegRevLex b) < toColex (ofDegRevLex a)) := by
  rw [lt_def, key, key, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual]

theorem le_iff {a b : DegRevLex (α →₀ ℕ)} :
    a ≤ b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      ((ofDegRevLex a).degree = (ofDegRevLex b).degree ∧ toColex (ofDegRevLex b) ≤ toColex (ofDegRevLex a)) := by
  rw [le_def, key, key, Prod.Lex.toLex_le_toLex, OrderDual.toDual_le_toDual]

instance : IsOrderedCancelAddMonoid (DegRevLex (α →₀ ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [le_iff] at h ⊢
    simpa only [ofDegRevLex_add, map_add, add_lt_add_iff_left, add_right_inj, toColex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa [ofDegRevLex_add, map_add, toColex_add] using h

theorem degree_le_of_le {a b : DegRevLex (α →₀ ℕ)} (h : a ≤ b) :
    (ofDegRevLex a).degree ≤ (ofDegRevLex b).degree := by
  rcases le_iff.mp h with h | h
  · exact h.le
  · exact h.1.le

/-- For a finite `α`, the exponents of bounded degree form a finite set. -/
theorem finite_degree_le [Finite α] (d : ℕ) : {f : α →₀ ℕ | f.degree ≤ d}.Finite := by
  have hle : ∀ f : α →₀ ℕ, f.degree ≤ d → ∀ i, f i < d + 1 := by
    intro f hf i
    have : f i ≤ f.degree := by
      classical
      by_cases hi : i ∈ f.support
      · rw [Finsupp.degree_apply]
        exact Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) hi
      · rw [Finsupp.notMem_support_iff.mp hi]
        exact Nat.zero_le _
    omega
  let g : {f : α →₀ ℕ | f.degree ≤ d} → (α → Fin (d + 1)) := fun f i => ⟨f.1 i, hle f.1 f.2 i⟩
  have hg : Function.Injective g := by
    intro f₁ f₂ h
    apply Subtype.ext
    ext i
    have := congrFun h i
    simpa [g] using congrArg Fin.val this
  exact Set.finite_coe_iff.mp (Finite.of_injective g hg)

/-- Accessibility from well-foundedness on a downward closed set. -/
theorem acc_of_wellFoundedOn {β : Type*} {r : β → β → Prop} {s : Set β} (hs : s.WellFoundedOn r)
    (hdown : ∀ x ∈ s, ∀ y, r y x → y ∈ s) : ∀ x ∈ s, Acc r x := by
  intro x hx
  suffices H : ∀ y : s, Acc r y.1 from H ⟨x, hx⟩
  intro y
  induction y using WellFounded.induction hs with
  | _ y ih =>
    refine ⟨_, fun z hz => ?_⟩
    exact ih ⟨z, hdown y.1 y.2 z hz⟩ hz

instance wellFoundedLT [Finite α] : WellFoundedLT (DegRevLex (α →₀ ℕ)) := by
  refine ⟨fun b => ?_⟩
  set s : Set (DegRevLex (α →₀ ℕ)) := {a | (ofDegRevLex a).degree ≤ (ofDegRevLex b).degree} with hs
  have hfin : s.Finite := by
    have h := finite_degree_le (α := α) (ofDegRevLex b).degree
    have : s = ofDegRevLex ⁻¹' {f : α →₀ ℕ | f.degree ≤ (ofDegRevLex b).degree} := rfl
    rw [this]
    exact h.preimage (ofDegRevLex.injective.injOn)
  exact acc_of_wellFoundedOn (hfin.wellFoundedOn (r := (· < ·)))
    (fun x hx y hyx => (degree_le_of_le hyx.le).trans hx) b (by simp only [hs, Set.mem_ofPred_eq, le_refl])

theorem toDegRevLex_monotone : Monotone (toDegRevLex : (α →₀ ℕ) → DegRevLex (α →₀ ℕ)) := by
  intro a b h
  rw [le_iff]
  simp only [ofDegRevLex_toDegRevLex]
  by_cases hd : a.degree < b.degree
  · exact Or.inl hd
  · right
    have hab : a.degree ≤ b.degree := Finsupp.degree_mono h
    have heq : a.degree = b.degree := le_antisymm hab (not_lt.mp hd)
    have hba : b = a + (b - a) := (add_tsub_cancel_of_le h).symm
    have h0 : (b - a).degree = 0 := by
      have := congrArg Finsupp.degree hba
      rw [map_add] at this
      omega
    rw [Finsupp.degree_eq_zero_iff] at h0
    have : b = a := by rw [hba, h0, add_zero]
    subst this
    exact ⟨rfl, le_rfl⟩

end DegRevLex

/-- **The graded reverse lexicographic monomial order** on a finite linearly ordered set of variables. -/
noncomputable def degRevLex (σ : Type*) [LinearOrder σ] [Finite σ] : MonomialOrder σ where
  syn := DegRevLex (σ →₀ ℕ)
  toSyn := { toEquiv := toDegRevLex, map_add' := toDegRevLex_add }
  toSyn_monotone := DegRevLex.toDegRevLex_monotone

variable {σ : Type*} [LinearOrder σ] [Finite σ]

theorem degRevLex_le_iff {a b : σ →₀ ℕ} : a ≼[degRevLex σ] b ↔ toDegRevLex a ≤ toDegRevLex b := Iff.rfl

theorem degRevLex_lt_iff {a b : σ →₀ ℕ} : a ≺[degRevLex σ] b ↔ toDegRevLex a < toDegRevLex b := Iff.rfl

/-- `a ≺ b` in `degRevLex`: smaller degree, or equal degree and `b` precedes `a` colexicographically. -/
theorem degRevLex_lt_iff' {a b : σ →₀ ℕ} :
    a ≺[degRevLex σ] b ↔ a.degree < b.degree ∨ (a.degree = b.degree ∧ toColex b < toColex a) := by
  rw [degRevLex_lt_iff, DegRevLex.lt_iff]
  rfl

/-- The first variable is the largest: `single a 1 ≺ single b 1 ↔ b < a`. -/
theorem degRevLex_single_lt_iff {a b : σ} :
    single a 1 ≺[degRevLex σ] single b 1 ↔ b < a := by
  rw [degRevLex_lt_iff', degree_single, degree_single]
  simp only [lt_self_iff_false, true_and, false_or]
  exact Colex.single_lt_iff

/-! ## The comparator of the checkers -/

open Lean6.Special.Comp Lean6.Special.Comp.Count

/-- The exponent vector of an exponent list (entries beyond `n` are dropped). -/
noncomputable def vec (n : ℕ) (m : Mono) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => m.getD i 0

@[simp] theorem vec_apply (n : ℕ) (m : Mono) (i : Fin n) : vec n m i = m.getD i 0 := rfl

theorem sum_getD_eq_sum : ∀ (m : Mono), ∑ i ∈ Finset.range m.length, m.getD i 0 = m.sum
  | [] => by simp
  | a :: m => by
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [sum_getD_eq_sum m]
    ring

theorem degree_vec {n : ℕ} {m : Mono} (hm : m.length = n) : (vec n m).degree = m.sum := by
  rw [Finsupp.degree_eq_sum, ← sum_getD_eq_sum m, hm]
  simp only [vec_apply]
  exact (Fin.sum_univ_eq_sum_range (fun i => m.getD i 0) n)

theorem mdegS_eq (m : Mono) : mdegS m = m.sum := rfl

/-- The last differing position. -/
def LastLt (m k : Mono) : Prop := ∃ i, (∀ j, i < j → m.getD j 0 = k.getD j 0) ∧ m.getD i 0 < k.getD i 0

theorem lastCmp_none_iff : ∀ {m k : Mono}, m.length = k.length →
    (lastCmp m k = none ↔ ∀ j, m.getD j 0 = k.getD j 0)
  | [], [], _ => by simp [lastCmp]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: m, b :: k, h => by
    have hl : m.length = k.length := by simpa using h
    have ih := lastCmp_none_iff hl
    simp only [lastCmp]
    constructor
    · intro hc j
      split at hc
      · exact absurd hc (by simp)
      · rename_i hn
        have hall := ih.mp hn
        split at hc
        · rename_i hab
          cases j with
          | zero => simpa using hab
          | succ j => simpa using hall j
        · exact absurd hc (by simp)
    · intro hall
      have hmk : ∀ j, m.getD j 0 = k.getD j 0 := fun j => by simpa using hall (j + 1)
      have hab : a = b := by simpa using hall 0
      rw [ih.mpr hmk]
      simp [hab]

theorem lastCmp_some_true_iff : ∀ {m k : Mono}, m.length = k.length → (lastCmp m k = some true ↔ LastLt m k)
  | [], [], _ => by simp [lastCmp, LastLt]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: m, b :: k, h => by
    have hl : m.length = k.length := by simpa using h
    have ih := lastCmp_some_true_iff hl
    have ihn := lastCmp_none_iff hl
    unfold LastLt at ih ⊢
    simp only [lastCmp]
    split
    · rename_i r hr
      -- the tails differ: the last differing position of the tails, shifted
      have hne : ¬ ∀ j, m.getD j 0 = k.getD j 0 := fun hall => by rw [ihn.mpr hall] at hr; simp at hr
      constructor
      · intro hc
        simp only [Option.some.injEq] at hc
        subst hc
        obtain ⟨i, hi1, hi2⟩ := ih.mp hr
        exact ⟨i + 1, fun j hj => by
          cases j with
          | zero => omega
          | succ j => simpa using hi1 j (by omega), by simpa using hi2⟩
      · rintro ⟨i, hi1, hi2⟩
        cases i with
        | zero =>
          exfalso
          exact hne fun j => by simpa using hi1 (j + 1) (by omega)
        | succ i =>
          have : lastCmp m k = some true :=
            ih.mpr ⟨i, fun j hj => by simpa using hi1 (j + 1) (by omega), by simpa using hi2⟩
          rw [hr] at this
          exact this
    · rename_i hr
      have hall := ihn.mp hr
      split
      · rename_i hab
        simp only [reduceCtorEq, false_iff]
        rintro ⟨i, hi1, hi2⟩
        cases i with
        | zero => simp at hi2; simp at hab; omega
        | succ i => simp only [List.getD_cons_succ] at hi2; rw [hall i] at hi2; omega
      · rename_i hab
        simp only [Option.some.injEq, decide_eq_true_eq]
        constructor
        · intro hlt
          exact ⟨0, fun j hj => by
            cases j with
            | zero => omega
            | succ j => simpa using hall j, by simpa using hlt⟩
        · rintro ⟨i, hi1, hi2⟩
          cases i with
          | zero => simpa using hi2
          | succ i => simp only [List.getD_cons_succ] at hi2; rw [hall i] at hi2; omega

/-- **The comparator is the graded reverse lexicographic order** on exponent lists of length `n`. -/
theorem grevGtStd_iff {n : ℕ} {m k : Mono} (hm : m.length = n) (hk : k.length = n) :
    grevGtStd m k = true ↔ vec n k ≺[degRevLex (Fin n)] vec n m := by
  rw [degRevLex_lt_iff', degree_vec hm, degree_vec hk]
  unfold grevGtStd
  by_cases hdeg : m.sum = k.sum
  · have hb : (mdegS m == mdegS k) = true := by simpa [mdegS_eq] using hdeg
    simp only [hb, ite_true, hdeg]
    simp only [lt_self_iff_false, true_and, false_or]
    rw [Colex.lt_iff]
    have hlen : m.length = k.length := by rw [hm, hk]
    rw [show (lastCmp m k == some true) = true ↔ lastCmp m k = some true by simp,
      lastCmp_some_true_iff hlen]
    unfold LastLt
    constructor
    · rintro ⟨i, hi1, hi2⟩
      have hin : i < n := by
        by_contra hni
        have h1 : m.getD i 0 = 0 := by rw [List.getD_eq_default]; omega
        rw [h1] at hi2
        have h2 : k.getD i 0 = 0 := by rw [List.getD_eq_default]; omega
        omega
      refine ⟨⟨i, hin⟩, fun j hj => ?_, by simpa using hi2⟩
      simpa using hi1 j.1 hj
    · rintro ⟨i, hi1, hi2⟩
      refine ⟨i.1, fun j hj => ?_, by simpa using hi2⟩
      by_cases hjn : j < n
      · simpa using hi1 ⟨j, hjn⟩ hj
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  · have hb : (mdegS m == mdegS k) = false := by simpa [mdegS_eq] using hdeg
    simp only [hb]
    simp only [Bool.false_eq_true, ite_false, mdegS_eq]
    constructor
    · intro h
      exact Or.inl (of_decide_eq_true h)
    · rintro (h | ⟨h, -⟩)
      · exact decide_eq_true h
      · exact absurd h.symm hdeg

end Lean6.Special.D88.Count
