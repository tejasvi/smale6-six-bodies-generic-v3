import L6K.F2S.KeepR
import L6Sound.F2S.SearchL

/-!
# The decisions of `keepR` are sound

`checkR_imp`: if `checkR n rows cert` passes, so does `lean6`'s `Farkas.check n (Array.mk rows) cert`. The pass of
`combR` applies the entries of the certificate at their row indices in increasing order; when it succeeds it has
applied every entry, in the order of the list, so its result is that of `Farkas.combine` (with the vectors as lists).
`keepR_sound`: `KeepSoundL (keepR T)`, from Lemma 4.6 (`Farkas.check_sound_strict_all`), as `keepK_sound`.
-/

namespace L6K.F2S

open L6

/-! ## Equations of the recursors -/

theorem axpyR_nil (y : Int) (a : List Int) : axpyR y [] a = [] := rfl

theorem axpyR_cons_nil (y : Int) (v : Int) (vs : List Int) : axpyR y (v :: vs) [] = v :: axpyR y vs [] := rfl

theorem axpyR_cons_cons (y : Int) (v : Int) (vs : List Int) (x : Int) (a : List Int) :
    axpyR y (v :: vs) (x :: a) = (v + y * x) :: axpyR y vs a := rfl

theorem combR_nil (i : Nat) (cs : List (Nat × Int)) (acc : Option (List Int × Int × Int)) :
    combR [] i cs acc = match cs with | [] => acc | _ :: _ => none := by
  cases cs <;> rfl

theorem combR_cons_nil (r : Row) (rows : List Row) (i : Nat) (acc : Option (List Int × Int × Int)) :
    combR (r :: rows) i [] acc = acc := rfl

theorem combR_cons_cons (r : Row) (rows : List Row) (i : Nat) (e : Nat × Int) (cs : List (Nat × Int))
    (acc : Option (List Int × Int × Int)) :
    combR (r :: rows) i (e :: cs) acc =
      if e.1 = i then combR rows (i + 1) cs (stepR r e.2 acc) else combR rows (i + 1) (e :: cs) acc := rfl

/-! ## Vectors as lists -/

theorem axpyR_length (y : Int) : ∀ (v a : List Int), (axpyR y v a).length = v.length
  | [], _ => rfl
  | _ :: vs, [] => by rw [axpyR_cons_nil, List.length_cons, List.length_cons, axpyR_length y vs []]
  | _ :: vs, _ :: a => by rw [axpyR_cons_cons, List.length_cons, List.length_cons, axpyR_length y vs a]

theorem axpyR_getElem (y : Int) : ∀ (v a : List Int) (k : Nat) (hk : k < (axpyR y v a).length),
    (axpyR y v a)[k] = v[k]'(by rw [axpyR_length] at hk; exact hk) + y * a.getD k 0
  | [], _, k, hk => by simp [axpyR_nil] at hk
  | v :: vs, [], k, hk => by
    cases k with
    | zero => simp [axpyR_cons_nil]
    | succ k =>
      have := axpyR_getElem y vs [] k (by simpa [axpyR_cons_nil] using hk)
      simp only [axpyR_cons_nil, List.getElem_cons_succ, List.getD_nil] at this ⊢
      rw [this]
  | v :: vs, x :: a, k, hk => by
    cases k with
    | zero => simp [axpyR_cons_cons]
    | succ k =>
      have := axpyR_getElem y vs a k (by simpa [axpyR_cons_cons] using hk)
      simp only [axpyR_cons_cons, List.getElem_cons_succ, List.getD_cons_succ] at this ⊢
      rw [this]

theorem axpyR_toList (n : Nat) (v : Array Int) (y : Int) (a : Array Int) (hv : v.size = n) :
    axpyR y v.toList a.toList = (Farkas.axpy n v y a).toList := by
  apply List.ext_getElem
  · rw [axpyR_length, Array.length_toList, Array.length_toList, Farkas.axpy_size n v y a hv, hv]
  · intro k h1 h2
    have hk : k < n := by rw [axpyR_length, Array.length_toList, hv] at h1; exact h1
    rw [axpyR_getElem, Array.getElem_toList, Array.getElem_toList]
    have e1 := Farkas.axpy_get n v y a hv hk
    rw [getElem!_pos (Farkas.axpy n v y a) k (by rw [Farkas.axpy_size n v y a hv]; exact hk),
      getElem!_pos v k (by rw [hv]; exact hk)] at e1
    rw [e1]
    congr 2
    by_cases ha : k < a.size
    · rw [getElem!_pos a k ha, List.getD_eq_getElem _ _ (by simpa using ha), Array.getElem_toList]
    · rw [getElem!_neg a k ha, List.getD_eq_default _ _ (by simpa using ha)]
      rfl

/-! ## The pass and the fold -/

/-- The state of `combR` (vectors as lists) against the state of `Farkas.combine` (vectors as arrays of size `n`). -/
def Rel (n : Nat) : Option (List Int × Int × Int) → Option (Array Int × Int × Int) → Prop
  | stL, none => stL = none
  | stL, some (v, g, b) => v.size = n ∧ stL = some (v.toList, g, b)

/-- The step of `Farkas.combine` with the row `r`. -/
def stepA (n : Nat) (r : Row) (y : Int) : Option (Array Int × Int × Int) → Option (Array Int × Int × Int)
  | none => none
  | some (v, g, b) =>
    if y = 0 then some (v, g, b)
    else if !r.monotone then none
    else match r.bound? y with
      | none => none
      | some bd => some (Farkas.axpy n v y r.a, g + y * r.c, b + y * bd)

theorem rel_step (n : Nat) (r : Row) (y : Int) :
    ∀ {stL stA}, Rel n stL stA → Rel n (stepR r y stL) (stepA n r y stA)
  | stL, none, h => by
    simp only [Rel] at h
    subst h
    rfl
  | stL, some (v, g, b), h => by
    obtain ⟨hv, rfl⟩ := h
    unfold stepR stepA
    by_cases hy : y = 0
    · simp only [hy, ite_true]
      exact ⟨hv, rfl⟩
    · simp only [hy, ite_false]
      by_cases hm : r.monotone = true
      · simp only [hm, Bool.not_true, Bool.false_eq_true, ite_false]
        cases hb : r.bound? y with
        | none => rfl
        | some bd =>
          refine ⟨Farkas.axpy_size n v y r.a hv, ?_⟩
          show some (axpyR y v.toList r.a.toList, g + y * r.c, b + y * bd) = _
          rw [axpyR_toList n v y r.a hv]
      · have hm' : r.monotone = false := by simpa using hm
        simp only [hm', Bool.not_false, ite_true]
        rfl

/-- The fold of `Farkas.combine` over the entries, with the rows `rows`. -/
def foldA (n : Nat) (rows : List Row) (cs : List (Nat × Int)) (st : Option (Array Int × Int × Int)) :
    Option (Array Int × Int × Int) :=
  cs.foldl (fun acc e => match acc with
    | none => none
    | some st => match rows[e.1]? with
      | none => none
      | some r => stepA n r e.2 (some st)) st

theorem foldA_none (n : Nat) (rows : List Row) : ∀ cs, foldA n rows cs none = none
  | [] => rfl
  | _ :: cs => foldA_none n rows cs

/-- A pass that meets an entry whose index is already behind it fails. -/
theorem combR_behind : ∀ (tail : List Row) (i : Nat) (cs : List (Nat × Int)) (acc : Option (List Int × Int × Int)),
    (∃ e ∈ cs, e.1 < i) → combR tail i cs acc = none
  | [], i, cs, acc, ⟨e, he, _⟩ => by
    rw [combR_nil]
    cases cs with
    | nil => exact absurd he (by simp)
    | cons _ _ => rfl
  | r :: rest, i, [], acc, ⟨e, he, _⟩ => absurd he (by simp)
  | r :: rest, i, e0 :: cs, acc, ⟨e, he, hlt⟩ => by
    rw [combR_cons_cons]
    split
    · rename_i h0
      refine combR_behind rest (i + 1) cs _ ⟨e, ?_, by omega⟩
      rcases List.mem_cons.mp he with rfl | he'
      · omega
      · exact he'
    · exact combR_behind rest (i + 1) (e0 :: cs) acc ⟨e, he, by omega⟩

theorem combR_fold (n : Nat) (rows : List Row) :
    ∀ (i : Nat) (tail : List Row), tail = rows.drop i →
      ∀ (cs : List (Nat × Int)) (stL : Option (List Int × Int × Int)) (stA : Option (Array Int × Int × Int))
        (st : List Int × Int × Int), Rel n stL stA → combR tail i cs stL = some st →
        Rel n (some st) (foldA n rows cs stA)
  | i, [], htail, cs, stL, stA, st, hR, hc => by
    rw [combR_nil] at hc
    cases cs with
    | nil => subst hc; exact hR
    | cons _ _ => exact absurd hc (by simp)
  | i, r :: rest, htail, [], stL, stA, st, hR, hc => by
    rw [combR_cons_nil] at hc
    subst hc
    exact hR
  | i, r :: rest, htail, e :: cs, stL, stA, st, hR, hc => by
    have hri : rows[i]? = some r := by
      have : (rows.drop i)[0]? = some r := by rw [← htail]; rfl
      rwa [List.getElem?_drop, Nat.add_zero] at this
    have hrest : rest = rows.drop (i + 1) := by
      have : (rows.drop i).drop 1 = rest := by rw [← htail]; rfl
      rw [← this, List.drop_drop, Nat.add_comm]
    rw [combR_cons_cons] at hc
    split at hc
    · rename_i hei
      have hR' := rel_step n r e.2 hR
      have ih := combR_fold n rows (i + 1) rest hrest cs _ _ st hR' hc
      cases stA with
      | none =>
        simp only [Rel] at hR
        subst hR
        have : stepR r e.2 none = none := rfl
        rw [this] at hc
        have hn : combR rest (i + 1) cs none ≠ some st := by
          intro h
          have := combR_fold n rows (i + 1) rest hrest cs none none st rfl h
          rw [foldA_none] at this
          exact absurd this (by simp [Rel])
        exact absurd hc hn
      | some sa =>
        have e1 : foldA n rows (e :: cs) (some sa) = foldA n rows cs (stepA n r e.2 (some sa)) := by
          simp only [foldA, List.foldl_cons, hei, hri]
        rw [e1]
        exact ih
    · rename_i hei
      have ih := combR_fold n rows (i + 1) rest hrest (e :: cs) stL stA st hR hc
      exact ih

/-- **`checkR` implies `Farkas.check`.** -/
theorem checkR_imp {n : Nat} {rows : List Row} {cert : List (Nat × Int)} (h : checkR n rows cert = true) :
    Farkas.check n (Array.mk rows) cert = true := by
  unfold checkR at h
  cases hc : combR rows 0 cert (some (List.replicate n 0, 0, 0)) with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some st =>
    rw [hc] at h
    have hR0 : Rel n (some (List.replicate n 0, 0, 0)) (some (Array.replicate n 0, 0, 0)) :=
      ⟨by simp, by simp⟩
    have hR := combR_fold n rows 0 rows (by simp) cert _ _ st hR0 hc
    have hcomb : Farkas.combine n (Array.mk rows) cert = foldA n rows cert (some (Array.replicate n 0, 0, 0)) := by
      unfold Farkas.combine foldA stepA
      congr 1
      funext acc e
      rcases acc with _ | ⟨v, g, b⟩
      · rfl
      · simp only [List.getElem?_toArray]
        rcases rows[e.1]? with _ | r
        · rfl
        · rfl
    unfold Farkas.check
    rw [hcomb]
    revert hR
    rcases foldA n rows cert (some (Array.replicate n 0, 0, 0)) with _ | ⟨v, g, b⟩
    · intro hR
      exact absurd hR (by simp [Rel])
    · intro hR
      obtain ⟨-, hst⟩ := hR
      cases hst
      simp only [Bool.and_eq_true] at h ⊢
      refine ⟨⟨?_, h.1.2⟩, h.2⟩
      rw [Array.all_eq_true_iff_forall_mem]
      intro x hx
      exact List.all_eq_true.mp h.1.1 x (by simpa using hx)

/-- **The decisions of `keepR` are sound** (`KeepSoundL`). -/
theorem keepR_sound (T : CTree) : L6.F2S.KeepSoundL (keepR T) := by
  intro rows nv hk h hrows
  unfold keepR at hk
  have hany : anyR nv rows (T.find (hashR rows)) = true := by simpa using hk
  have key : ∀ cs : List (List (Nat × Int)), anyR nv rows cs = true → ∃ c ∈ cs, checkR nv rows c = true := by
    intro cs
    induction cs with
    | nil => intro h; exact absurd h (by simp [anyR])
    | cons c cs ih =>
      intro h
      have h' : (checkR nv rows c || anyR nv rows cs) = true := h
      rcases Bool.or_eq_true_iff.mp h' with hc | hc
      · exact ⟨c, List.mem_cons_self, hc⟩
      · obtain ⟨c', hc', hcc'⟩ := ih hc
        exact ⟨c', List.mem_cons_of_mem _ hc', hcc'⟩
  obtain ⟨cert, -, hc⟩ := key _ hany
  exact Farkas.check_sound_strict_all (checkR_imp hc) h fun r hr => hrows r (by simpa using hr)

end L6K.F2S
