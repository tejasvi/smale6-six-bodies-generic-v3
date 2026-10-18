import L6Sound.F2S.SearchL
import L6F2S.SearchN

/-!
# Completeness of the search with the rows of each cell, newest first

`searchN_complete`: for a decision `keep` on linear programs that discards a program only if it has no solution of
its strict form (`KeepSoundL`, which does not depend on the order of the rows), an insertion order listing the six
bodies, and every pair of complete trees with heights satisfying `Cond D`, the search `searchN` lists a cell with the
same trees (as sorted node sets, equivalent to the trees of the pair) and the argmin sets `argminIdx D Xz Xw`, all of
whose rows hold strictly at the heights read off the complete trees. The argmin recursion is that of `L6F2S.Search`
read through `Array.toList` and reversed (`argminRecN_eq`); the rest follows the proofs of `SearchL`.
-/

namespace L6.F2S

open L6.F2 (renderEntry Label IdName)

theorem argminRecN_eq (keep : List Row → Bool) (baseA : Array Row) (terms : List (Array Int)) :
    ∀ (fuel j : Nat) (first : Option Nat) (ins outs : List Nat) (rowsA : Array Row),
      argminRecN keep terms fuel j first ins outs (baseA ++ rowsA).toList.reverse =
        (argminRec (fun a => keep a.toList.reverse) baseA terms fuel j first ins outs rowsA).map
          (fun p => (p.1, (baseA ++ p.2).toList.reverse)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j first ins outs rowsA
    simp only [argminRecN, argminRec]
    split_ifs <;> simp
  | succ fuel ih =>
    intro j first ins outs rowsA
    cases first with
    | none =>
      have e1 : (outs.map fun o => rowGt (fsub terms[o]! terms[j]!)).reverse ++ (baseA ++ rowsA).toList.reverse =
          (baseA ++ (rowsA ++ (outs.map fun o => rowGt (fsub terms[o]! terms[j]!)).toArray)).toList.reverse := by
        simp [List.reverse_append, List.append_assoc]
      simp only [argminRecN, argminRec, List.map_append]
      congr 1
      · rw [e1]
        split_ifs
        · exact ih _ _ _ _ _
        · rfl
      · split_ifs
        · exact ih _ _ _ _ _
        · rfl
    | some f =>
      have e2 : ∀ r : Row, r :: (baseA ++ rowsA).toList.reverse = (baseA ++ rowsA.push r).toList.reverse :=
        fun r => by simp [List.reverse_append]
      simp only [argminRecN, argminRec, List.map_append]
      congr 1
      · rw [e2]
        split_ifs
        · exact ih _ _ _ _ _
        · rfl
      · rw [e2]
        split_ifs
        · exact ih _ _ _ _ _
        · rfl
        · rfl

theorem argminRecN_complete (keep : List Row → Bool) (nv : Nat)
    (hkeep : ∀ rows, keep rows = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h)
    (state : List Row) (terms : List (Array Int)) (h : ℕ → ℚ)
    (hstate : ∀ r ∈ state, r.StrictHolds nv h) (hsize : ∀ t ∈ terms, t.size = nv)
    (htwice : MinTwice (termVals nv terms h)) :
    ∃ rows, (argminPos (termVals nv terms h), rows) ∈ argminRecN keep terms terms.length 0 none [] [] state ∧
      ∀ r ∈ rows, r.StrictHolds nv h := by
  obtain ⟨rowsA, hm, hs⟩ := argminRec_complete (fun a => keep a.toList.reverse) nv
    (fun rows hc h' hall => hkeep rows.toList.reverse hc h' fun r hr => hall r (by simpa using hr))
    state.reverse.toArray terms h (fun r hr => hstate r (by simpa using hr)) hsize htwice
  have e := argminRecN_eq keep state.reverse.toArray terms terms.length 0 none [] [] #[]
  have hst : (state.reverse.toArray ++ #[]).toList.reverse = state := by simp
  rw [hst] at e
  refine ⟨(state.reverse.toArray ++ rowsA).toList.reverse, ?_, fun r hr => ?_⟩
  · rw [e]
    exact List.mem_map.mpr ⟨_, hm, rfl⟩
  · simp only [List.mem_reverse, Array.toList_append, List.mem_append] at hr
    rcases hr with hr | hr
    · exact hstate r (by simpa using hr)
    · exact hs r (by simpa using hr)

theorem branchRecN_complete (keep : List Row → Bool) (nv : Nat)
    (hkeep : ∀ rows, keep rows = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h) (h : ℕ → ℚ) :
    ∀ (branch : List SIdent) (state : List Row) (chosen : List (Nat × List Nat)),
      (∀ r ∈ state, r.StrictHolds nv h) →
      (∀ id ∈ branch, (∀ t ∈ id.terms, t.size = nv) ∧ MinTwice (termVals nv id.terms h)) →
      ∃ rows, (chosen ++ branch.map (fun id => (idCode id.name, argminPos (termVals nv id.terms h))), rows) ∈
        branchRecN keep branch state chosen ∧ ∀ r ∈ rows, r.StrictHolds nv h := by
  intro branch
  induction branch with
  | nil =>
    intro state chosen hs _
    exact ⟨state, by simp [branchRecN], hs⟩
  | cons id rest ih =>
    intro state chosen hs hids
    obtain ⟨hsz, htw⟩ := hids id List.mem_cons_self
    obtain ⟨rows, hm, hrows⟩ := argminRecN_complete keep nv hkeep state id.terms h hs hsz htw
    obtain ⟨rows', hrec, hrows'⟩ := ih rows (chosen ++ [(idCode id.name, argminPos (termVals nv id.terms h))])
      hrows (fun id' hid' => hids id' (List.mem_cons_of_mem _ hid'))
    refine ⟨rows', ?_, hrows'⟩
    rw [branchRecN, List.mem_flatMap]
    refine ⟨(argminPos (termVals nv id.terms h), rows), hm, ?_⟩
    simpa [List.map_cons, List.append_assoc] using hrec

theorem cellsBelowN_complete {keep : List Row → Nat → Bool} (hk : KeepSoundL keep) {D : L6.F2.Diag}
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) (P : Pair) (hz : P.tz.Equiv Xz.T) (hzn : P.tz.nodes.Nodup)
    (hw : P.tw.Equiv Xw.T) (hwn : P.tw.nodes.Nodup) :
    ∃ rows, (argminIdx D Xz Xw, rows) ∈ cellsBelowN keep D P ∧
      ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P) := by
  have hall : all < 128 := by decide
  have hOall : mem O all = true := by decide
  have lz := levelFacts hX.gz hX.root_z hall hOall (hz.trans (restrict_all hX.gz).symm) hzn
  have lw := levelFacts hX.gw hX.root_w hall hOall (hw.trans (restrict_all hX.gw).symm) hwn
  have hcz : comOk P.tz all = true := (comOk_equiv hz hzn hX.gz.1.nodup all).trans hX.com_z
  have hcw : comOk P.tw all = true := (comOk_equiv hw hwn hX.gw.1.nodup all).trans hX.com_w
  obtain ⟨L0, hL0, hL0s⟩ := partialRowsL_strict hX hall hOall P lz lw
  obtain ⟨ids, hids, hlen, hmeta, hfacts⟩ := idents_eval hX P lz lw
  have hforced := forced_facts hX P lz lw hids
  have hget : ∀ id ∈ ids, ∃ i < ids.length, ids[i]! = id := by
    intro id hid
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hid
    exact ⟨i, hi, getElem!_pos ids i hi⟩
  have hf2 : ∀ id ∈ ids, ∀ f, id.forced = some f → 2 ≤ f.length := by
    intro id hid f hf
    obtain ⟨i, hi, rfl⟩ := hget id hid
    exact (hforced i hi f hf).1
  have hextra : ∀ r ∈ CompleteAux.extraOf ids, r.StrictHolds P.nv (heightVec Xz Xw P) := by
    intro r hr
    obtain ⟨id, hid, f, hf, hr⟩ := CompleteAux.mem_extraOf hr
    obtain ⟨i, hi, rfl⟩ := hget id hid
    exact (hforced i hi f hf).2.2 r hr
  -- the values of the terms are twice the exponents
  have htv : ∀ i < ids.length,
      termVals P.nv ids[i]!.terms (heightVec Xz Xw P) = ((baseExps Xz Xw)[i]!).map (2 * ·) := by
    intro i hi
    obtain ⟨hl, -, -, hv⟩ := hfacts i hi
    apply List.ext_getElem
    · simp only [termVals, List.length_map]
      exact hl
    · intro t h1 h2
      have ht : t < ids[i]!.terms.length := by simpa [termVals] using h1
      have hv' := hv t ht
      rw [getElem!_pos ids[i]!.terms t ht, getElem!_pos ((baseExps Xz Xw)[i]!) t (by rw [← hl]; exact ht)] at hv'
      simpa [termVals] using hv'
  have hbranch : ∀ id ∈ ids.filter (fun id => id.forced.isNone),
      (∀ t ∈ id.terms, t.size = P.nv) ∧ MinTwice (termVals P.nv id.terms (heightVec Xz Xw P)) := by
    intro id hid
    obtain ⟨i, hi, rfl⟩ := hget id (List.mem_of_mem_filter hid)
    obtain ⟨-, -, hsz, -⟩ := hfacts i hi
    refine ⟨hsz, ?_⟩
    rw [htv i hi, CompleteAux.minTwice_two_mul]
    apply hX.twice
    rw [getElem!_pos (baseExps Xz Xw) i (by rw [← hlen]; exact hi)]
    exact List.getElem_mem _
  have hstate : ∀ r ∈ (L0 ++ CompleteAux.extraOf ids).reverse, r.StrictHolds P.nv (heightVec Xz Xw P) := by
    intro r hr
    rcases List.mem_append.mp (List.mem_reverse.mp hr) with hr | hr
    · exact hL0s r hr
    · exact hextra r hr
  obtain ⟨brows, hbr, hbrs⟩ := branchRecN_complete (fun r => keep r P.nv) P.nv
    (fun rows hc h' => hk rows P.nv hc h') (heightVec Xz Xw P) (ids.filter fun id => id.forced.isNone)
    (L0 ++ CompleteAux.extraOf ids).reverse [] hstate hbranch
  have hk0 : keep L0.reverse P.nv = true := keepL_true hk fun r hr => hL0s r (List.mem_reverse.mp hr)
  have hk1 : keep (L0 ++ CompleteAux.extraOf ids).reverse P.nv = true := keepL_true hk hstate
  -- the argmin sets of the other identities are those of the exponents
  have hzip : ∀ a b, (a, b) ∈ ids.zip (baseExps Xz Xw) →
      argminPos (termVals P.nv a.terms (heightVec Xz Xw P)) = argminPos b := by
    intro a b hab
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hab
    rw [List.getElem_zip, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hi' : i < ids.length := by simp at hi; omega
    have h1 := htv i hi'
    rw [getElem!_pos ids i hi', getElem!_pos (baseExps Xz Xw) i (by omega)] at h1
    rw [h1, CompleteAux.argminPos_two_mul]
  refine ⟨brows, ?_, hbrs⟩
  unfold cellsBelowN
  rw [hcz, hcw, hL0, hids]
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false, hk0]
  rw [splitForcedL_eq ids hf2]
  simp only [hk1, Bool.not_true, Bool.false_eq_true, ite_false]
  refine List.mem_map.mpr ⟨_, hbr, ?_⟩
  rw [List.nil_append, Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  unfold argminIdx
  dsimp only
  rw [← hz.2, ← hw.2, ← hmeta]
  congr 1
  · exact (CompleteAux.map_filter_zip (fun id : SIdent => (id.name, id.labels, id.forced))
      (fun ie => ie.1.2.2.isSome) (fun id => id.forced.isSome)
      (fun ie => (idCode ie.1.1, ie.1.2.2.getD [])) entryFL ids (baseExps Xz Xw) hlen.le
      fun _ _ _ => ⟨rfl, rfl⟩).symm
  · exact (CompleteAux.map_filter_zip (fun id : SIdent => (id.name, id.labels, id.forced))
      (fun ie => ie.1.2.2.isNone) (fun id => id.forced.isNone)
      (fun ie => (idCode ie.1.1, argminPos ie.2))
      (fun id => (idCode id.name, argminPos (termVals P.nv id.terms (heightVec Xz Xw P))))
      ids (baseExps Xz Xw) hlen.le fun a b hab => ⟨rfl, by dsimp only; rw [hzip a b hab]⟩).symm


/-! ## The search -/

/-- **Completeness of the search with the rows of each cell.** For an insertion order listing the six bodies, every
pair of complete trees with heights satisfying `Cond D` has a cell of `searchN` with the same trees (equivalent, with
distinct nodes) and the argmin sets `argminIdx D Xz Xw`, all of whose rows hold strictly at the heights read off the
complete trees. -/
theorem searchN_complete {keep : List Row → Nat → Bool} (hk : KeepSoundL keep) {D : L6.F2.Diag} {ord : List Nat}
    (hord : ord.Perm (List.range 6)) {Xz Xw : ExpTree} (hX : Cond D Xz Xw) :
    ∃ c ∈ searchN keep D ord, c.key = (Xz.T.key, Xw.T.key, argminIdx D Xz Xw) ∧
      c.tz.Equiv Xz.T ∧ c.tz.nodes.Nodup ∧ c.tw.Equiv Xw.T ∧ c.tw.nodes.Nodup ∧
      ∀ r ∈ c.rows, r.StrictHolds c.pair.nv (heightVec Xz Xw c.pair) := by
  have hnd : ord.Nodup := hord.nodup_iff.mpr List.nodup_range
  have hmem : ∀ p ∈ ord, p < 6 ∧ mem p (single O) = false := by
    intro p hp
    have hp6 : p < 6 := List.mem_range.mp (hord.subset hp)
    refine ⟨hp6, ?_⟩
    rw [mem_single]
    exact decide_eq_false (by unfold O; omega)
  obtain ⟨x, hx, -, hxz, hxzn, hxw, hxwn⟩ := treeLevelL_complete hk hX ord (single O) TS.init TS.init
    (by decide) (by decide) hnd hmem (CompleteAux.foldl_ins_range hord) (restrict_init hX.gz) List.nodup_nil
    (restrict_init hX.gw) List.nodup_nil
  obtain ⟨rows, hc, hrows⟩ := cellsBelowN_complete hk hX ⟨x.2.1, x.2.2⟩ hxz hxzn hxw hxwn
  refine ⟨⟨x.2.1, x.2.2, argminIdx D Xz Xw, rows⟩, ?_, ?_, hxz, hxzn, hxw, hxwn, hrows⟩
  · unfold searchN
    rw [List.mem_flatMap]
    exact ⟨x, hx, List.mem_map.mpr ⟨_, hc, rfl⟩⟩
  · unfold SCellN.key
    rw [key_equiv hxz hxzn hX.gz.1.nodup, key_equiv hxw hxwn hX.gw.1.nodup]

theorem searchN_split (keep : List Row → Nat → Bool) (D : L6.F2.Diag) (ord : List Nat) (d : Nat) :
    searchN keep D ord = (prefixPairsL keep D ord d).flatMap (belowN keep D ord d) := by
  have h := treeLevelL_append keep D (ord.take d) (ord.drop d) (single O) TS.init TS.init
  rw [List.take_append_drop] at h
  rw [searchN, h, List.flatMap_assoc]
  rfl

end L6.F2S
