import L6Sound.F2S.Defs

/-!
# The argmin recursion of the specification search is complete

`argminRec_complete`: if every discarded program has no solution of its strict form, the rows `base` hold strictly at
`h`, and the least value of the terms at `h` is attained twice, then the recursion lists the set of the terms of least
value, with rows that hold strictly at `h`. `branchRec_complete`: the same for a list of identities, one after the
other.
-/

namespace L6.F2S

open L6.F2 (renderEntry Label)

/-- The values of the terms of an identity at `h`. -/
def termVals (nv : Nat) (terms : List (Array Int)) (h : ℕ → ℚ) : List ℚ := terms.map fun t => formVal nv t h

/-! ## Values of forms and the rows of the recursion -/

theorem formVal_fsub {nv : Nat} {a b : Array Int} (ha : a.size = nv) (hb : b.size = nv) (h : ℕ → ℚ) :
    formVal nv (fsub a b) h = formVal nv a h - formVal nv b h := by
  unfold formVal fsub
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < nv := Finset.mem_range.mp hj
  have hza : j < (Array.zipWith (· - ·) a b).size := by simp [Array.size_zipWith, ha, hb, hj']
  rw [getElem!_pos (Array.zipWith (· - ·) a b) j hza, getElem!_pos a j (by omega),
    getElem!_pos b j (by omega), Array.getElem_zipWith]
  push_cast
  ring

theorem strict_rowGt {nv : Nat} {d : Array Int} {h : ℕ → ℚ} :
    (rowGt d).StrictHolds nv h ↔ 0 < formVal nv d h := by
  unfold Row.StrictHolds rowGt
  simp [Row.lin, formVal]

theorem strict_rowEq {nv : Nat} {d : Array Int} {h : ℕ → ℚ} :
    (rowEq d).StrictHolds nv h ↔ formVal nv d h = 0 := by
  unfold Row.StrictHolds rowEq
  simp only [ite_true, Option.some.injEq, forall_eq', Int.cast_zero, Row.lin]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h2 h1
  · intro h0
    exact ⟨h0.symm.le, h0.le⟩

/-- A program whose rows all hold strictly is kept. -/
theorem keep_of_strict {keep : Array Row → Bool} {nv : Nat}
    (hkeep : ∀ rows, keep rows = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h)
    {R : Array Row} {h : ℕ → ℚ} (hR : ∀ r ∈ R, r.StrictHolds nv h) : keep R = true := by
  cases hk : keep R with
  | false => exact absurd hR (hkeep R hk h)
  | true => rfl

/-! ## The positions of the least value -/

theorem mem_argminPos {l : List ℚ} {i : Nat} :
    i ∈ argminPos l ↔ i < l.length ∧ ∀ k < l.length, l[i]! ≤ l[k]! := by
  unfold argminPos
  simp [List.mem_filter, List.mem_range]

theorem argminPos_pairwise (l : List ℚ) : (argminPos l).Pairwise (· < ·) := by
  unfold argminPos
  exact List.pairwise_lt_range.filter _

/-! ## The state of the recursion along the true path -/

/-- The elements of `S` below `j` (the terms taken IN so far). -/
def insAt (S : List Nat) (j : Nat) : List Nat := S.filter fun x => decide (x < j)

/-- The positions below `j` not in `S` (the terms left OUT so far). -/
def outsAt (S : List Nat) (j : Nat) : List Nat := (List.range j).filter fun x => !(S.contains x)

theorem insAt_succ {S : List Nat} (hS : S.Pairwise (· < ·)) (j : Nat) :
    insAt S (j + 1) = insAt S j ++ (if j ∈ S then [j] else []) := by
  unfold insAt
  induction S with
  | nil => simp
  | cons a S ih =>
    rw [List.pairwise_cons] at hS
    obtain ⟨ha, hS'⟩ := hS
    have ih := ih hS'
    rcases Nat.lt_trichotomy a j with haj | haj | haj
    · have h1 : a < j + 1 := by omega
      have hja : ¬ j = a := by omega
      rw [List.filter_cons, List.filter_cons, ite_eq_left (by simpa using h1), ite_eq_left (by simpa using haj), ih]
      simp [hja]
    · subst haj
      have hnil1 : S.filter (fun x => decide (x < a + 1)) = [] :=
        List.filter_eq_nil_iff.mpr fun b hb => by have := ha b hb; simp; omega
      have hnil2 : S.filter (fun x => decide (x < a)) = [] :=
        List.filter_eq_nil_iff.mpr fun b hb => by have := ha b hb; simp; omega
      rw [List.filter_cons, List.filter_cons, ite_eq_left (by simp), ite_eq_right (by simp), hnil1, hnil2]
      simp
    · have hnil1 : S.filter (fun x => decide (x < j + 1)) = [] :=
        List.filter_eq_nil_iff.mpr fun b hb => by have := ha b hb; simp; omega
      have hnil2 : S.filter (fun x => decide (x < j)) = [] :=
        List.filter_eq_nil_iff.mpr fun b hb => by have := ha b hb; simp; omega
      have hjS : j ∉ S := fun hj => by have := ha j hj; omega
      have hja : ¬ j = a := by omega
      rw [List.filter_cons, List.filter_cons, ite_eq_right (by simp; omega), ite_eq_right (by simp; omega), hnil1, hnil2]
      simp [hjS, hja]

theorem outsAt_succ (S : List Nat) (j : Nat) :
    outsAt S (j + 1) = outsAt S j ++ (if j ∈ S then [] else [j]) := by
  unfold outsAt
  rw [List.range_succ, List.filter_append]
  by_cases hj : j ∈ S
  · simp [hj]
  · simp [hj]

theorem mem_outsAt {S : List Nat} {j o : Nat} : o ∈ outsAt S j ↔ o < j ∧ o ∉ S := by
  unfold outsAt
  simp [List.mem_filter, List.mem_range]

theorem mem_insAt {S : List Nat} {j x : Nat} : x ∈ insAt S j ↔ x ∈ S ∧ x < j := by
  unfold insAt
  simp [List.mem_filter]

theorem insAt_of_lt {S : List Nat} {N : Nat} (h : ∀ x ∈ S, x < N) : insAt S N = S := by
  unfold insAt
  exact List.filter_eq_self.mpr fun a ha => by simp [h a ha]

/-- A list without repetitions of naturals in `[a, b)` has at most `b − a` elements. -/
theorem length_le_of_nodup_Ico {L : List Nat} (hL : L.Nodup) {a b : Nat} (h : ∀ x ∈ L, a ≤ x ∧ x < b) :
    L.length ≤ b - a := by
  rw [← List.toFinset_card_of_nodup hL]
  calc L.toFinset.card ≤ (Finset.Ico a b).card := Finset.card_le_card (fun x hx => by
        rw [List.mem_toFinset] at hx
        rw [Finset.mem_Ico]
        exact h x hx)
    _ = b - a := Nat.card_Ico a b

/-! ## One step of the recursion -/

section step

variable {keep : Array Row → Bool} {base : Array Row} {terms : List (Array Int)} {fuel j : Nat}
  {ins outs : List Nat} {rows : Array Row} {x : List Nat × Array Row}

theorem mem_argminRec_in_none
    (hk : keep (base ++ (rows ++ (outs.map fun o => rowGt (fsub terms[o]! terms[j]!)).toArray)) = true)
    (hx : x ∈ argminRec keep base terms fuel (j + 1) (some j) (ins ++ [j]) outs
      (rows ++ (outs.map fun o => rowGt (fsub terms[o]! terms[j]!)).toArray)) :
    x ∈ argminRec keep base terms (fuel + 1) j none ins outs rows := by
  simp only [argminRec, hk, ↓reduceIte, List.mem_append]
  exact Or.inl hx

theorem mem_argminRec_in_some {f : Nat}
    (hk : keep (base ++ rows.push (rowEq (fsub terms[j]! terms[f]!))) = true)
    (hx : x ∈ argminRec keep base terms fuel (j + 1) (some f) (ins ++ [j]) outs
      (rows.push (rowEq (fsub terms[j]! terms[f]!)))) :
    x ∈ argminRec keep base terms (fuel + 1) j (some f) ins outs rows := by
  simp only [argminRec, hk, ↓reduceIte, List.mem_append]
  exact Or.inl hx

theorem mem_argminRec_out_none (hc : 2 ≤ terms.length - j - 1)
    (hx : x ∈ argminRec keep base terms fuel (j + 1) none ins (outs ++ [j]) rows) :
    x ∈ argminRec keep base terms (fuel + 1) j none ins outs rows := by
  simp only [argminRec, hc, ↓reduceIte, List.mem_append]
  exact Or.inr hx

theorem mem_argminRec_out_some {f : Nat}
    (hc : 2 ≤ ins.length ∨ 2 - ins.length ≤ terms.length - j - 1)
    (hk : keep (base ++ rows.push (rowGt (fsub terms[j]! terms[f]!))) = true)
    (hx : x ∈ argminRec keep base terms fuel (j + 1) (some f) ins (outs ++ [j])
      (rows.push (rowGt (fsub terms[j]! terms[f]!)))) :
    x ∈ argminRec keep base terms (fuel + 1) j (some f) ins outs rows := by
  have hc' : (decide (2 ≤ ins.length) || decide (2 - ins.length ≤ terms.length - j - 1)) = true := by
    rcases hc with hc | hc <;> simp [hc]
  simp only [argminRec, hc', hk, ↓reduceIte, List.mem_append]
  exact Or.inr hx

end step

/-! ## The true path -/

/-- Along the true path (IN exactly at the positions of the least value), the recursion from step `j` lists the set of
those positions, with rows that hold strictly. -/
theorem argminRec_true (keep : Array Row → Bool) (nv : Nat)
    (hkeep : ∀ rows, keep rows = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h)
    (base : Array Row) (terms : List (Array Int)) (h : ℕ → ℚ)
    (hbase : ∀ r ∈ base, r.StrictHolds nv h) (hsize : ∀ t ∈ terms, t.size = nv)
    (h2 : 2 ≤ (argminPos (termVals nv terms h)).length) :
    ∀ fuel j, j + fuel = terms.length → ∀ rows : Array Row, (∀ r ∈ rows, r.StrictHolds nv h) →
      ∃ rows', (argminPos (termVals nv terms h), rows') ∈
        argminRec keep base terms fuel j (insAt (argminPos (termVals nv terms h)) j).head?
          (insAt (argminPos (termVals nv terms h)) j) (outsAt (argminPos (termVals nv terms h)) j) rows ∧
        ∀ r ∈ rows', r.StrictHolds nv h := by
  generalize hS : argminPos (termVals nv terms h) = S at h2 ⊢
  have hpw : S.Pairwise (· < ·) := hS ▸ argminPos_pairwise _
  have hnd : S.Nodup := hpw.imp fun hab => Nat.ne_of_lt hab
  have hlen : (termVals nv terms h).length = terms.length := by simp [termVals]
  have hmem : ∀ i, i ∈ S ↔ i < terms.length ∧
      ∀ k < terms.length, (termVals nv terms h)[i]! ≤ (termVals nv terms h)[k]! := by
    intro i
    rw [← hS, mem_argminPos, hlen]
  have hval : ∀ i < terms.length, (termVals nv terms h)[i]! = formVal nv terms[i]! h := by
    intro i hi
    rw [getElem!_pos (termVals nv terms h) i (by rw [hlen]; exact hi), getElem!_pos terms i hi]
    simp [termVals]
  have hsz : ∀ i < terms.length, (terms[i]!).size = nv := fun i hi => by
    rw [getElem!_pos terms i hi]
    exact hsize _ (List.getElem_mem hi)
  have hdiff : ∀ a b, a < terms.length → b < terms.length →
      formVal nv (fsub terms[a]! terms[b]!) h = (termVals nv terms h)[a]! - (termVals nv terms h)[b]! := by
    intro a b ha hb
    rw [formVal_fsub (hsz a ha) (hsz b hb), hval a ha, hval b hb]
  have hSlt : ∀ x ∈ S, x < terms.length := fun x hx => ((hmem x).mp hx).1
  have hlt : ∀ i k, i ∈ S → k < terms.length → k ∉ S →
      (termVals nv terms h)[i]! < (termVals nv terms h)[k]! := by
    intro i k hi hk hkS
    have hi' := (hmem i).mp hi
    have hnot : ¬ ∀ m < terms.length, (termVals nv terms h)[k]! ≤ (termVals nv terms h)[m]! :=
      fun hall => hkS ((hmem k).mpr ⟨hk, hall⟩)
    push Not at hnot
    obtain ⟨m, hm, hmk⟩ := hnot
    exact lt_of_le_of_lt (hi'.2 m hm) hmk
  have heq : ∀ i k, i ∈ S → k ∈ S → (termVals nv terms h)[i]! = (termVals nv terms h)[k]! := by
    intro i k hi hk
    have hi' := (hmem i).mp hi
    have hk' := (hmem k).mp hk
    exact le_antisymm (hi'.2 k hk'.1) (hk'.2 i hi'.1)
  intro fuel
  induction fuel with
  | zero =>
    intro j hj rows hrows
    have hjN : j = terms.length := by omega
    subst hjN
    rw [insAt_of_lt hSlt]
    refine ⟨rows, ?_, hrows⟩
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, S = a :: b :: rest := by
      match S, h2 with
      | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
    simp [argminRec]
  | succ fuel ih =>
    intro j hj rows hrows
    have hjN : j < terms.length := by omega
    have hij := ih (j + 1) (by omega)
    rw [insAt_succ hpw, outsAt_succ] at hij
    by_cases hjS : j ∈ S
    · -- the term `j` is IN
      simp only [hjS, ↓reduceIte, List.append_nil] at hij
      cases hins : insAt S j with
      | nil =>
        rw [hins] at hij
        set nrows := rows ++ ((outsAt S j).map fun o => rowGt (fsub terms[o]! terms[j]!)).toArray with hnr
        have hstrict : ∀ r ∈ nrows, r.StrictHolds nv h := by
          intro r hr
          rw [hnr, Array.mem_append] at hr
          rcases hr with hr | hr
          · exact hrows r hr
          · rw [List.mem_toArray, List.mem_map] at hr
            obtain ⟨o, ho, rfl⟩ := hr
            rw [mem_outsAt] at ho
            rw [strict_rowGt, hdiff o j (by omega) hjN, sub_pos]
            exact hlt j o hjS (by omega) ho.2
        obtain ⟨rows', hm, hr'⟩ := hij nrows hstrict
        refine ⟨rows', ?_, hr'⟩
        apply mem_argminRec_in_none
        · exact keep_of_strict hkeep fun r hr => by
            rw [Array.mem_append] at hr
            rcases hr with hr | hr
            · exact hbase r hr
            · exact hstrict r hr
        · rw [hnr] at hm
          simpa using hm
      | cons f rest =>
        rw [hins] at hij
        have hf : f ∈ S := (mem_insAt.mp (hins ▸ List.mem_cons_self : f ∈ insAt S j)).1
        set nrows := rows.push (rowEq (fsub terms[j]! terms[f]!)) with hnr
        have hstrict : ∀ r ∈ nrows, r.StrictHolds nv h := by
          intro r hr
          rw [hnr, Array.mem_push] at hr
          rcases hr with hr | rfl
          · exact hrows r hr
          · rw [strict_rowEq, hdiff j f hjN (hSlt f hf), sub_eq_zero]
            exact heq j f hjS hf
        obtain ⟨rows', hm, hr'⟩ := hij nrows hstrict
        refine ⟨rows', ?_, hr'⟩
        apply mem_argminRec_in_some
        · exact keep_of_strict hkeep fun r hr => by
            rw [Array.mem_append] at hr
            rcases hr with hr | hr
            · exact hbase r hr
            · exact hstrict r hr
        · rw [hnr] at hm
          simpa using hm
    · -- the term `j` is OUT
      simp only [hjS, ↓reduceIte, List.append_nil] at hij
      have hsplit := S.length_eq_length_filter_add (fun x => decide (x < j))
      have hrest : (S.filter fun x => !decide (x < j)).length ≤ terms.length - (j + 1) := by
        apply length_le_of_nodup_Ico (hnd.filter _)
        intro x hx
        rw [List.mem_filter] at hx
        have hxN := hSlt x hx.1
        have hxj : ¬ x < j := by simpa using hx.2
        have hxne : x ≠ j := fun he => hjS (he ▸ hx.1)
        omega
      cases hins : insAt S j with
      | nil =>
        rw [hins] at hij
        obtain ⟨rows', hm, hr'⟩ := hij rows hrows
        refine ⟨rows', ?_, hr'⟩
        apply mem_argminRec_out_none
        · have h0 : (S.filter fun x => decide (x < j)).length = 0 := by
            have : insAt S j = S.filter fun x => decide (x < j) := rfl
            rw [← this, hins]
            rfl
          omega
        · simpa using hm
      | cons f rest =>
        rw [hins] at hij
        have hf : f ∈ S := (mem_insAt.mp (hins ▸ List.mem_cons_self : f ∈ insAt S j)).1
        set nrows := rows.push (rowGt (fsub terms[j]! terms[f]!)) with hnr
        have hstrict : ∀ r ∈ nrows, r.StrictHolds nv h := by
          intro r hr
          rw [hnr, Array.mem_push] at hr
          rcases hr with hr | rfl
          · exact hrows r hr
          · rw [strict_rowGt, hdiff j f hjN (hSlt f hf), sub_pos]
            exact hlt f j hf hjN hjS
        obtain ⟨rows', hm, hr'⟩ := hij nrows hstrict
        refine ⟨rows', ?_, hr'⟩
        apply mem_argminRec_out_some
        · have hlenins : (f :: rest).length = (S.filter fun x => decide (x < j)).length := by
            have : insAt S j = S.filter fun x => decide (x < j) := rfl
            rw [← this, hins]
          omega
        · exact keep_of_strict hkeep fun r hr => by
            rw [Array.mem_append] at hr
            rcases hr with hr | hr
            · exact hbase r hr
            · exact hstrict r hr
        · rw [hnr] at hm
          simpa using hm

/-- Two distinct positions of the least value: the set of positions of the least value has at least two elements. -/
theorem two_le_argminPos {l : List ℚ} (hl : MinTwice l) : 2 ≤ (argminPos l).length := by
  obtain ⟨i, k, hi, hk, hik, heq, hmin⟩ := hl
  have hi' : i ∈ argminPos l := mem_argminPos.mpr ⟨hi, hmin⟩
  have hk' : k ∈ argminPos l := mem_argminPos.mpr ⟨hk, fun m hm => heq ▸ hmin m hm⟩
  calc 2 = ({i, k} : Finset Nat).card := (Finset.card_pair hik).symm
    _ ≤ (argminPos l).toFinset.card := Finset.card_le_card (by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [List.mem_toFinset]
        rcases hx with rfl | rfl
        · exact hi'
        · exact hk')
    _ ≤ (argminPos l).length := List.toFinset_card_le _

theorem argminRec_complete (keep : Array Row → Bool) (nv : Nat)
    (hkeep : ∀ rows, keep rows = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h)
    (base : Array Row) (terms : List (Array Int)) (h : ℕ → ℚ)
    (hbase : ∀ r ∈ base, r.StrictHolds nv h) (hsize : ∀ t ∈ terms, t.size = nv)
    (htwice : MinTwice (termVals nv terms h)) :
    ∃ rows, (argminPos (termVals nv terms h), rows) ∈ argminRec keep base terms terms.length 0 none [] [] #[] ∧
      ∀ r ∈ rows, r.StrictHolds nv h := by
  have key := argminRec_true keep nv hkeep base terms h hbase hsize (two_le_argminPos htwice) terms.length 0
    (by omega) #[] (fun r hr => by simp at hr)
  have h0 : insAt (argminPos (termVals nv terms h)) 0 = [] := by
    unfold insAt
    exact List.filter_eq_nil_iff.mpr fun a _ => by simp
  have h1 : outsAt (argminPos (termVals nv terms h)) 0 = [] := by
    unfold outsAt
    simp
  rw [h0, h1] at key
  simpa using key

theorem branchRec_complete (keep : Array Row → Bool) (nv : Nat)
    (hkeep : ∀ rows, keep rows = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h)
    (L0 : Array Row) (h : ℕ → ℚ) (hL0 : ∀ r ∈ L0, r.StrictHolds nv h) :
    ∀ (branch : List SIdent) (extra : Array Row) (chosen : List String), (∀ r ∈ extra, r.StrictHolds nv h) →
      (∀ id ∈ branch, (∀ t ∈ id.terms, t.size = nv) ∧ MinTwice (termVals nv id.terms h)) →
      chosen ++ branch.map (fun id => renderEntry id.name
          ((argminPos (termVals nv id.terms h)).map fun t => id.labels.getD t .E).toArray) ∈
        branchRec keep L0 branch extra chosen := by
  intro branch
  induction branch with
  | nil =>
    intro extra chosen _ _
    simp [branchRec]
  | cons id rest ih =>
    intro extra chosen hextra hids
    obtain ⟨hsz, htw⟩ := hids id List.mem_cons_self
    have hbase : ∀ r ∈ L0 ++ extra, r.StrictHolds nv h := by
      intro r hr
      rw [Array.mem_append] at hr
      rcases hr with hr | hr
      · exact hL0 r hr
      · exact hextra r hr
    obtain ⟨rows, hm, hrows⟩ := argminRec_complete keep nv hkeep (L0 ++ extra) id.terms h hbase hsz htw
    have hextra' : ∀ r ∈ extra ++ rows, r.StrictHolds nv h := by
      intro r hr
      rw [Array.mem_append] at hr
      rcases hr with hr | hr
      · exact hextra r hr
      · exact hrows r hr
    have hrec := ih (extra ++ rows)
      (chosen ++ [renderEntry id.name
        ((argminPos (termVals nv id.terms h)).map fun t => id.labels.getD t .E).toArray])
      hextra' (fun id' hid' => hids id' (List.mem_cons_of_mem _ hid'))
    rw [branchRec, List.mem_flatMap]
    refine ⟨(argminPos (termVals nv id.terms h), rows), hm, ?_⟩
    simpa [List.map_cons, List.append_assoc] using hrec

end L6.F2S
