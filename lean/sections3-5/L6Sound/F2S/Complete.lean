import L6Sound.F2S.CompleteAux

/-!
# Completeness of the specification search (Proposition 4.5)

`search_complete`: for a representative `D` whose insertion order lists the six bodies, every pair of complete trees
with heights satisfying the conditions of Lemma 4.3 and `ℓ(x) ≤ 0` (`Cond`) is listed by the specification search,
with its trees (up to the order of the nodes) and its argmin sets. The only property of the decisions on linear
programs that is used is that a discarded program has no solution of its strict form (`KeepSound`), which holds for
`keepLP` by Lemma 4.6 (`keepLP_sound`).
-/

namespace L6.F2S

open L6.F2 (renderEntry Label)

/-- A discarded program has no solution of its strict form. -/
def KeepSound (keep : Array Row → Nat → Bool) : Prop :=
  ∀ rows nv, keep rows nv = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h

theorem keepLP_sound : KeepSound keepLP := by
  intro rows nv hk h hrows
  have hc : Farkas.check nv rows (LP.decide rows nv).cert = true := by
    simp only [keepLP] at hk
    revert hk
    generalize (LP.decide rows nv).kept = a
    generalize Farkas.check nv rows (LP.decide rows nv).cert = b
    cases a <;> cases b <;> simp
  exact Farkas.check_sound_strict_all hc h hrows

/-- A program whose rows all hold strictly is kept. -/
theorem keep_true {keep : Array Row → Nat → Bool} (hk : KeepSound keep) {rows : Array Row} {nv : Nat}
    {h : ℕ → ℚ} (hr : ∀ r ∈ rows, r.StrictHolds nv h) : keep rows nv = true := by
  cases hc : keep rows nv with
  | false => exact absurd hr (hk rows nv hc h)
  | true => rfl

theorem treeLevel_complete {keep : Array Row → Nat → Bool} (hk : KeepSound keep) {D : L6.F2.Diag}
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) :
    ∀ (rest : List Nat) (S : Nat) (tz tw : TS), S < 128 → mem O S = true → rest.Nodup →
      (∀ p ∈ rest, p < 6 ∧ mem p S = false) → rest.foldl (fun s p => ins p s) S = all →
      tz.Equiv (restrict Xz.T S) → tz.nodes.Nodup → tw.Equiv (restrict Xw.T S) → tw.nodes.Nodup →
      ∃ x ∈ treeLevel keep D rest S tz tw, x.1 = all ∧ x.2.1.Equiv Xz.T ∧ x.2.1.nodes.Nodup ∧
        x.2.2.Equiv Xw.T ∧ x.2.2.nodes.Nodup := by
  intro rest
  induction rest with
  | nil =>
    intro S tz tw _ _ _ _ hfold htz htzn htw htwn
    simp only [List.foldl_nil] at hfold
    subst hfold
    exact ⟨(all, tz, tw), by simp [treeLevel], rfl, htz.trans (restrict_all hX.gz), htzn,
      htw.trans (restrict_all hX.gw), htwn⟩
  | cons p rest ih =>
    intro S tz tw hS hO hnd hrest hfold htz htzn htw htwn
    obtain ⟨hp6, hpS⟩ := hrest p List.mem_cons_self
    have hS' : ins p S < 128 := CompleteAux.ins_lt hS hp6
    have hO' : mem O (ins p S) = true := by rw [mem_ins, hO]; rfl
    obtain ⟨tz', htz'm, htz'e, htz'n⟩ := options_complete hX.gz hS hO hp6 hpS htz htzn
    obtain ⟨tw', htw'm, htw'e, htw'n⟩ := options_complete hX.gw hS hO hp6 hpS htw htwn
    have lz := levelFacts hX.gz hX.root_z hS' hO' htz'e htz'n
    have lw := levelFacts hX.gw hX.root_w hS' hO' htw'e htw'n
    obtain ⟨rows, hrows, hstrict⟩ := partialRows_strict hX hS' hO' ⟨tz', tw'⟩ lz lw
    have hkeep : keep rows (Pair.nv ⟨tz', tw'⟩) = true := keep_true hk hstrict
    have hnd' := List.nodup_cons.mp hnd
    have hrest' : ∀ q ∈ rest, q < 6 ∧ mem q (ins p S) = false := by
      intro q hq
      obtain ⟨hq6, hqS⟩ := hrest q (List.mem_cons_of_mem _ hq)
      refine ⟨hq6, ?_⟩
      rw [mem_ins, hqS]
      have hpq : p ≠ q := fun e => hnd'.1 (e ▸ hq)
      simp [hpq]
    rw [List.foldl_cons] at hfold
    obtain ⟨x, hx, hx1⟩ := ih (ins p S) tz' tw' hS' hO' hnd'.2 hrest' hfold htz'e htz'n htw'e htw'n
    refine ⟨x, ?_, hx1⟩
    rw [treeLevel, List.mem_flatMap]
    refine ⟨tz', htz'm, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨tw', htw'm, ?_⟩
    rw [hrows]
    simp only [hkeep, ite_true]
    exact hx

theorem cellsBelow_complete {keep : Array Row → Nat → Bool} (hk : KeepSound keep) {D : L6.F2.Diag}
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) (P : Pair) (hz : P.tz.Equiv Xz.T) (hzn : P.tz.nodes.Nodup)
    (hw : P.tw.Equiv Xw.T) (hwn : P.tw.nodes.Nodup) :
    argminString D Xz Xw ∈ cellsBelow keep D P := by
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
  have hbr := branchRec_complete (fun r => keep r P.nv) P.nv (fun rows hc h' => hk rows P.nv hc h') L0
    (heightVec Xz Xw P) hL0s (ids.filter fun id => id.forced.isNone) (CompleteAux.extraOf ids).toArray [] hextra
    hbranch
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
  unfold cellsBelow
  rw [hcz, hcw, hL0, hids]
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false, hk0]
  rw [CompleteAux.splitForced_eq ids hf2]
  simp only [hk1, Bool.not_true, Bool.false_eq_true, ite_false]
  refine List.mem_map.mpr ⟨_, hbr, ?_⟩
  rw [List.nil_append]
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

/-- **Completeness of the search (Proposition 4.5).** -/
theorem search_complete {keep : Array Row → Nat → Bool} (hk : KeepSound keep) {D : L6.F2.Diag}
    (hord : (order D).Perm (List.range 6)) {Xz Xw : ExpTree} (hX : Cond D Xz Xw) :
    ∃ c ∈ search keep D, c.tz.key = Xz.T.key ∧ c.tw.key = Xw.T.key ∧ c.argmin = argminString D Xz Xw := by
  have hnd : (order D).Nodup := hord.nodup_iff.mpr List.nodup_range
  have hmem : ∀ p ∈ order D, p < 6 ∧ mem p (single O) = false := by
    intro p hp
    have hp6 : p < 6 := List.mem_range.mp (hord.subset hp)
    refine ⟨hp6, ?_⟩
    rw [mem_single]
    exact decide_eq_false (by unfold O; omega)
  obtain ⟨x, hx, -, hxz, hxzn, hxw, hxwn⟩ := treeLevel_complete hk hX (order D) (single O) TS.init TS.init
    (by decide) (by decide) hnd hmem (CompleteAux.foldl_ins_range hord) (restrict_init hX.gz) List.nodup_nil
    (restrict_init hX.gw) List.nodup_nil
  have hc := cellsBelow_complete hk hX ⟨x.2.1, x.2.2⟩ hxz hxzn hxw hxwn
  refine ⟨⟨x.2.1, x.2.2, argminString D Xz Xw⟩, ?_, key_equiv hxz hxzn hX.gz.1.nodup,
    key_equiv hxw hxwn hX.gw.1.nodup, rfl⟩
  unfold search
  rw [List.mem_flatMap]
  exact ⟨x, hx, List.mem_map.mpr ⟨_, hc, rfl⟩⟩

end L6.F2S
