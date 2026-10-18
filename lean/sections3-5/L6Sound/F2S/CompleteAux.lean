import L6Sound.F2S.Tree
import L6Sound.F2S.RowsSem
import L6Sound.F2S.Argmin

/-!
# Auxiliary facts for the completeness of the specification search

* `ins_lt`, `foldl_ins_range`: inserting the bodies keeps a set of points below `128`; inserting all six bodies
  (in any order) into `{O}` gives all seven points.
* `splitForced_eq`: when every forced argmin set has at least two terms, `splitForced` returns the forced rows, the
  entries of the forced identities and the other identities, in order.
* `argminPos_two_mul`, `minTwice_two_mul`: doubling every value changes neither the positions of the least value
  nor whether it is attained twice.
* `map_filter_zip`: filtering and mapping a list zipped with another, when the filter reads only the first list.
-/

namespace L6.F2S.CompleteAux

open L6.F2S
open L6.F2 (renderEntry Label)

/-! ## Sets of points -/

theorem ins_lt {S p : Nat} (hS : S < 128) (hp : p < 6) : ins p S < 128 := by
  unfold ins single
  have h1 : 1 <<< p < 2 ^ 7 := by
    rw [Nat.shiftLeft_eq, one_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : S < 2 ^ 7 := by norm_num; omega
  have := Nat.or_lt_two_pow h2 h1
  norm_num at this
  exact this

instance rightComm_ins : RightCommutative (fun (s p : Nat) => ins p s) :=
  ⟨fun b a₁ a₂ => by
    show (b ||| single a₁) ||| single a₂ = (b ||| single a₂) ||| single a₁
    rw [Nat.or_assoc, Nat.or_assoc, Nat.or_comm (single a₁)]⟩

theorem foldl_ins_range {l : List Nat} (h : l.Perm (List.range 6)) :
    l.foldl (fun s p => ins p s) (single O) = all := by
  rw [h.foldl_eq]
  decide

/-! ## Values doubled -/

theorem getElem!_map_two (l : List ℚ) (i : Nat) : (l.map (2 * ·))[i]! = 2 * l[i]! := by
  by_cases hi : i < l.length
  · rw [getElem!_pos (l.map (2 * ·)) i (by simpa using hi), getElem!_pos l i hi, List.getElem_map]
  · rw [getElem!_neg (l.map (2 * ·)) i (by simpa using hi), getElem!_neg l i hi]
    show (0 : ℚ) = 2 * 0
    norm_num

theorem argminPos_two_mul (l : List ℚ) : argminPos (l.map (2 * ·)) = argminPos l := by
  unfold argminPos
  rw [List.length_map]
  refine List.filter_congr fun i _ => ?_
  simp only [getElem!_map_two]
  congr 1
  apply propext
  constructor
  · intro h k hk
    have := h k hk
    linarith
  · intro h k hk
    have := h k hk
    linarith

theorem minTwice_two_mul (l : List ℚ) : MinTwice (l.map (2 * ·)) ↔ MinTwice l := by
  unfold MinTwice
  simp only [List.length_map, getElem!_map_two]
  constructor
  · rintro ⟨i, j, hi, hj, hij, he, hle⟩
    refine ⟨i, j, hi, hj, hij, by linarith, fun k hk => ?_⟩
    have := hle k hk
    linarith
  · rintro ⟨i, j, hi, hj, hij, he, hle⟩
    refine ⟨i, j, hi, hj, hij, by rw [he], fun k hk => ?_⟩
    have := hle k hk
    linarith

/-! ## `splitForced` -/

/-- The entry of a forced identity. -/
def entryF (id : SIdent) : String :=
  renderEntry id.name ((id.forced.getD []).map fun t => id.labels.getD t .E).toArray

/-- The forced rows of a list of identities, in order. -/
def extraOf (ids : List SIdent) : List Row :=
  ids.flatMap fun id =>
    match id.forced with
    | some f => forcedRows id.terms f
    | none => []

/-- A fold in `Option` that never fails on the elements of a list is a fold without `Option`. -/
theorem foldl_some {α β : Type*} (f : Option β → α → Option β) (F : β → α → β) (P : α → Prop)
    (hstep : ∀ b a, P a → f (some b) a = some (F b a)) :
    ∀ (l : List α) (b : β), (∀ a ∈ l, P a) → l.foldl f (some b) = some (l.foldl F b)
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, hstep b a (h a List.mem_cons_self)]
    exact foldl_some f F P hstep l _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- One step of `splitForced` when it does not fail. -/
def stepF (b : Array Row × List String × List SIdent) (id : SIdent) : Array Row × List String × List SIdent :=
  match id.forced with
  | some f => (b.1 ++ (forcedRows id.terms f).toArray,
      b.2.1 ++ [renderEntry id.name (f.map fun t => id.labels.getD t .E).toArray], b.2.2)
  | none => (b.1, b.2.1, b.2.2 ++ [id])

theorem foldl_stepF : ∀ (ids : List SIdent) (b : Array Row × List String × List SIdent),
    ids.foldl stepF b = (b.1 ++ (extraOf ids).toArray, b.2.1 ++ (ids.filter fun id => id.forced.isSome).map entryF,
      b.2.2 ++ ids.filter fun id => id.forced.isNone)
  | [], b => by simp [extraOf]
  | id :: ids, b => by
    rw [List.foldl_cons, foldl_stepF ids]
    cases hf : id.forced with
    | none => simp [stepF, hf, extraOf]
    | some f =>
      simp only [stepF, hf, extraOf, List.flatMap_cons, List.filter_cons, Option.isSome_some, ite_true,
        Option.isNone_some, Bool.false_eq_true, ite_false, List.map_cons, entryF, Option.getD_some]
      simp [Array.append_assoc, List.append_assoc]

theorem splitForced_eq (ids : List SIdent) (h : ∀ id ∈ ids, ∀ f, id.forced = some f → 2 ≤ f.length) :
    splitForced ids = some ((extraOf ids).toArray, (ids.filter fun id => id.forced.isSome).map entryF,
      ids.filter fun id => id.forced.isNone) := by
  unfold splitForced
  rw [foldl_some _ stepF (fun id => ∀ f, id.forced = some f → 2 ≤ f.length) ?_ ids _ h, foldl_stepF]
  · simp
  · rintro ⟨rows, fixed, branch⟩ id hid
    cases hf : id.forced with
    | none => simp [stepF, hf]
    | some f =>
      have hn : ¬ f.length < 2 := by have := hid f hf; omega
      simp [stepF, hf, hn]

/-! ## Filtering a list zipped with another -/

/-- Filtering the pairs of `(l.map g).zip m` by a predicate that depends only on the first element (through `g`),
then mapping them by a function that agrees with `G` on the first element, gives the filter of `l` mapped by `G`. -/
theorem map_filter_zip {α β γ δ : Type*} (g : α → δ) (p : δ × β → Bool) (q : α → Bool) (F : δ × β → γ)
    (G : α → γ) : ∀ (l : List α) (m : List β), l.length ≤ m.length →
      (∀ a b, (a, b) ∈ l.zip m → p (g a, b) = q a ∧ F (g a, b) = G a) →
      (((l.map g).zip m).filter p).map F = (l.filter q).map G
  | [], _, _, _ => by simp
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: m, h, hF => by
    have hab := hF a b (by rw [List.zip_cons_cons]; exact List.mem_cons_self)
    have ih := map_filter_zip g p q F G l m (by simp at h; omega)
      fun a' b' hm => hF a' b' (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hm)
    rw [List.map_cons, List.zip_cons_cons, List.filter_cons, List.filter_cons, hab.1]
    cases q a
    · simpa using ih
    · simpa [hab.2] using ih

theorem mem_extraOf {ids : List SIdent} {r : Row} (hr : r ∈ extraOf ids) :
    ∃ id ∈ ids, ∃ f, id.forced = some f ∧ r ∈ forcedRows id.terms f := by
  unfold extraOf at hr
  rw [List.mem_flatMap] at hr
  obtain ⟨id, hid, hr⟩ := hr
  cases hf : id.forced with
  | none => rw [hf] at hr; simp at hr
  | some f => rw [hf] at hr; exact ⟨id, hid, f, hf, hr⟩

end L6.F2S.CompleteAux
