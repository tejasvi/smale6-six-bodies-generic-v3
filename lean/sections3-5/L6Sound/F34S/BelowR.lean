import L6Sound.F2S.Complete
import L6Sound.F34S.Defs

/-!
# The cells of a complete pair with their rows

`branchRecR`, `cellsBelowR` (`L6F34S.Check`) are `branchRec`, `cellsBelow` of the specification search keeping the
rows of each cell. For a pair of complete trees with heights satisfying `Cond`, and a pair of trees with the same
nodes, the cell of `(Xz, Xw)` is listed with rows that all hold strictly at the heights read off the complete trees
(`cellsBelowR_complete`; the proof is that of `cellsBelow_complete`).
-/

namespace L6.F34S

open L6.F2S
open L6.F2 (renderEntry Label)

theorem branchRecR_complete (keep : Array Row → Bool) (nv : Nat)
    (hkeep : ∀ rows, keep rows = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h)
    (L0 : Array Row) (h : ℕ → ℚ) (hL0 : ∀ r ∈ L0, r.StrictHolds nv h) :
    ∀ (branch : List SIdent) (extra : Array Row) (chosen : List String), (∀ r ∈ extra, r.StrictHolds nv h) →
      (∀ id ∈ branch, (∀ t ∈ id.terms, t.size = nv) ∧ MinTwice (termVals nv id.terms h)) →
      ∃ rows, (chosen ++ branch.map (fun id => renderEntry id.name
          ((argminPos (termVals nv id.terms h)).map fun t => id.labels.getD t .E).toArray), rows) ∈
        branchRecR keep L0 branch extra chosen ∧ ∀ r ∈ rows, r.StrictHolds nv h := by
  intro branch
  induction branch with
  | nil =>
    intro extra chosen hextra _
    exact ⟨extra, by simp [branchRecR], hextra⟩
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
    obtain ⟨rows', hrec, hrows'⟩ := ih (extra ++ rows)
      (chosen ++ [renderEntry id.name
        ((argminPos (termVals nv id.terms h)).map fun t => id.labels.getD t .E).toArray])
      hextra' (fun id' hid' => hids id' (List.mem_cons_of_mem _ hid'))
    refine ⟨rows', ?_, hrows'⟩
    rw [branchRecR, List.mem_flatMap]
    refine ⟨(argminPos (termVals nv id.terms h), rows), hm, ?_⟩
    simpa [List.map_cons, List.append_assoc] using hrec

end L6.F34S

namespace L6.F2S

open L6.F2 (renderEntry Label)

theorem cellsBelowR_complete {keep : Array Row → Nat → Bool} (hk : KeepSound keep) {D : L6.F2.Diag}
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) (P : Pair) (hz : P.tz.Equiv Xz.T) (hzn : P.tz.nodes.Nodup)
    (hw : P.tw.Equiv Xw.T) (hwn : P.tw.nodes.Nodup) :
    ∃ rows, (argminString D Xz Xw, rows) ∈ L6.F34S.cellsBelowR keep D P ∧
      ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P) := by
  have hall : all < 128 := by decide
  have hOall : mem O all = true := by decide
  have lz := levelFacts hX.gz hX.root_z hall hOall (hz.trans (restrict_all hX.gz).symm) hzn
  have lw := levelFacts hX.gw hX.root_w hall hOall (hw.trans (restrict_all hX.gw).symm) hwn
  have hcz : comOk P.tz all = true := (comOk_equiv hz hzn hX.gz.1.nodup all).trans hX.com_z
  have hcw : comOk P.tw all = true := (comOk_equiv hw hwn hX.gw.1.nodup all).trans hX.com_w
  obtain ⟨L0, hL0, hL0s⟩ := partialRows_strict hX hall hOall P lz lw
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
  have hextra : ∀ r ∈ (CompleteAux.extraOf ids).toArray, r.StrictHolds P.nv (heightVec Xz Xw P) := by
    intro r hr
    obtain ⟨id, hid, f, hf, hr⟩ := CompleteAux.mem_extraOf (by simpa using hr)
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
  obtain ⟨brows, hbr, hbrs⟩ := L6.F34S.branchRecR_complete (fun r => keep r P.nv) P.nv
    (fun rows hc h' => hk rows P.nv hc h') L0 (heightVec Xz Xw P) hL0s (ids.filter fun id => id.forced.isNone)
    (CompleteAux.extraOf ids).toArray [] hextra hbranch
  have hk0 : keep L0 P.nv = true := keep_true hk hL0s
  have hk1 : keep (L0 ++ (CompleteAux.extraOf ids).toArray) P.nv = true := keep_true hk (by
    intro r hr
    rcases Array.mem_append.mp hr with hr | hr
    · exact hL0s r hr
    · exact hextra r hr)
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
  refine ⟨L0 ++ brows, ?_, fun r hr => ?_⟩
  swap
  · rcases Array.mem_append.mp hr with hr | hr
    · exact hL0s r hr
    · exact hbrs r hr
  unfold L6.F34S.cellsBelowR
  rw [hcz, hcw, hL0, hids]
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false, hk0]
  rw [CompleteAux.splitForced_eq ids hf2]
  simp only [hk1, Bool.not_true, Bool.false_eq_true, ite_false]
  refine List.mem_map.mpr ⟨_, hbr, ?_⟩
  rw [List.nil_append, Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  unfold argminString
  dsimp only
  rw [← hz.2, ← hw.2, ← hmeta]
  congr 1
  congr 1
  · exact (CompleteAux.map_filter_zip (fun id : SIdent => (id.name, id.labels, id.forced))
      (fun ie => ie.1.2.2.isSome) (fun id => id.forced.isSome)
      (fun ie => renderEntry ie.1.1 ((ie.1.2.2.getD []).map fun t => ie.1.2.1.getD t .E).toArray)
      CompleteAux.entryF ids (baseExps Xz Xw) hlen.le fun _ _ _ => ⟨rfl, rfl⟩).symm
  · exact (CompleteAux.map_filter_zip (fun id : SIdent => (id.name, id.labels, id.forced))
      (fun ie => ie.1.2.2.isNone) (fun id => id.forced.isNone)
      (fun ie => renderEntry ie.1.1 ((argminPos ie.2).map fun t => ie.1.2.1.getD t .E).toArray)
      (fun id => renderEntry id.name
        ((argminPos (termVals P.nv id.terms (heightVec Xz Xw P))).map fun t => id.labels.getD t .E).toArray)
      ids (baseExps Xz Xw) hlen.le fun a b hab => ⟨rfl, by dsimp only; rw [hzip a b hab]⟩).symm

end L6.F2S
