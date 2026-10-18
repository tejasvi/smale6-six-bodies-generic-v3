import L6Sound.F2S.StoredSem
import L6F2S.SearchL

/-!
# Completeness of the specification search with lists of rows and structured argmin sets

The variant `searchL` of the specification search (`L6F2S.SearchL`: rows as lists, the argmin part of a cell as the
codes of the base identities with the positions of their terms of least exponent, the insertion order as a
parameter) is complete in the same sense as `search` (`searchL_complete`): for every pair of complete trees with
heights satisfying `Cond D`, it lists a cell with the same two trees (up to the order of the nodes) and the argmin
sets `argminIdx D Xz Xw`. The only property of the decisions on linear programs that is used is that a discarded
program has no solution of its strict form (`KeepSoundL`). The rendering of `argminIdx` with the names and labels of
the base identities is `argminString` (`argminString_eq_renderIdx`).

The proofs reuse those of `search_complete`: the tree level and the argmin recursion are the same functions on arrays
read as lists (`treeLevel_eq_L`, `argminRecL_eq`), and the cells below a complete pair follow the proof of
`cellsBelow_complete`.
-/

namespace L6.F2S

open L6.F2 (renderEntry Label IdName)

/-- A discarded program (rows as a list) has no solution of its strict form. -/
def KeepSoundL (keep : List Row → Nat → Bool) : Prop :=
  ∀ rows nv, keep rows nv = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h

theorem keepSound_of_L {keep : List Row → Nat → Bool} (hk : KeepSoundL keep) :
    KeepSound (fun rows nv => keep rows.toList nv) := by
  intro rows nv hc h hr
  exact hk rows.toList nv hc h fun r hr' => hr r (by simpa using hr')

theorem keepL_true {keep : List Row → Nat → Bool} (hk : KeepSoundL keep) {rows : List Row} {nv : Nat}
    {h : ℕ → ℚ} (hr : ∀ r ∈ rows, r.StrictHolds nv h) : keep rows nv = true := by
  cases hc : keep rows nv with
  | false => exact absurd hr (hk rows nv hc h)
  | true => rfl

/-! ## Rows as lists -/

theorem partialRows_eq_L (D : L6.F2.Diag) (P : Pair) (S : Nat) :
    partialRows D P S = (partialRowsL D P S).map List.toArray := by
  unfold partialRows partialRowsL
  cases pairRows D P S <;> cases posRows D P S <;> cases thresholdRow D P S <;> rfl

theorem partialRowsL_strict {D : L6.F2.Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {S : Nat} (hS : S < 128)
    (hO : mem O S = true) (P : Pair) (hz : LevelFacts Xz P.tz S) (hw : LevelFacts Xw P.tw S) :
    ∃ rows, partialRowsL D P S = some rows ∧ ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P) := by
  obtain ⟨rows, hr, hs⟩ := partialRows_strict hX hS hO P hz hw
  rw [partialRows_eq_L] at hr
  cases h : partialRowsL D P S with
  | none => rw [h] at hr; simp at hr
  | some l =>
    rw [h] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    subst hr
    exact ⟨l, rfl, fun r hr' => hs r (by simpa using hr')⟩

theorem treeLevel_eq_L (keep : List Row → Nat → Bool) (D : L6.F2.Diag) :
    ∀ (rest : List Nat) (S : Nat) (tz tw : TS),
      treeLevel (fun rows nv => keep rows.toList nv) D rest S tz tw = treeLevelL keep D rest S tz tw
  | [], _, _, _ => rfl
  | p :: rest, S, tz, tw => by
    simp only [treeLevel, treeLevelL]
    congr 1
    funext tz'
    congr 1
    funext tw'
    rw [partialRows_eq_L]
    cases partialRowsL D ⟨tz', tw'⟩ (ins p S) with
    | none => rfl
    | some L =>
      simp only [Option.map_some, List.toList_toArray]
      split_ifs
      · exact treeLevel_eq_L keep D rest _ tz' tw'
      · rfl

theorem treeLevelL_complete {keep : List Row → Nat → Bool} (hk : KeepSoundL keep) {D : L6.F2.Diag}
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) :
    ∀ (rest : List Nat) (S : Nat) (tz tw : TS), S < 128 → mem O S = true → rest.Nodup →
      (∀ p ∈ rest, p < 6 ∧ mem p S = false) → rest.foldl (fun s p => ins p s) S = all →
      tz.Equiv (restrict Xz.T S) → tz.nodes.Nodup → tw.Equiv (restrict Xw.T S) → tw.nodes.Nodup →
      ∃ x ∈ treeLevelL keep D rest S tz tw, x.1 = all ∧ x.2.1.Equiv Xz.T ∧ x.2.1.nodes.Nodup ∧
        x.2.2.Equiv Xw.T ∧ x.2.2.nodes.Nodup := by
  intro rest S tz tw h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [← treeLevel_eq_L]
  exact treeLevel_complete (keepSound_of_L hk) hX rest S tz tw h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem treeLevelL_append (keep : List Row → Nat → Bool) (D : L6.F2.Diag) (l1 l2 : List Nat) (S : Nat)
    (tz tw : TS) :
    treeLevelL keep D (l1 ++ l2) S tz tw =
      (treeLevelL keep D l1 S tz tw).flatMap fun x => treeLevelL keep D l2 x.1 x.2.1 x.2.2 := by
  rw [← treeLevel_eq_L, treeLevel_append, ← treeLevel_eq_L]
  congr 1
  funext x
  rw [treeLevel_eq_L]

/-! ## The argmin recursion on lists -/

theorem argminRecL_eq (keep : List Row → Bool) (baseA : Array Row) (terms : List (Array Int)) :
    ∀ (fuel j : Nat) (first : Option Nat) (ins outs : List Nat) (rowsA : Array Row),
      argminRecL keep baseA.toList terms fuel j first ins outs rowsA.toList =
        (argminRec (fun a => keep a.toList) baseA terms fuel j first ins outs rowsA).map
          (fun p => (p.1, p.2.toList)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro j first ins outs rowsA
    simp only [argminRecL, argminRec]
    split_ifs <;> simp
  | succ fuel ih =>
    intro j first ins outs rowsA
    cases first with
    | none =>
      have e1 : rowsA.toList ++ (outs.map fun o => rowGt (fsub terms[o]! terms[j]!)) =
          (rowsA ++ (outs.map fun o => rowGt (fsub terms[o]! terms[j]!)).toArray).toList := by simp
      simp only [argminRecL, argminRec, List.map_append]
      congr 1
      · rw [e1, ← Array.toList_append]
        split_ifs
        · exact ih _ _ _ _ _
        · rfl
      · split_ifs
        · exact ih _ _ _ _ _
        · rfl
    | some f =>
      have e2 : ∀ r : Row, rowsA.toList ++ [r] = (rowsA.push r).toList := fun r => by simp
      simp only [argminRecL, argminRec, List.map_append]
      congr 1
      · rw [e2, ← Array.toList_append]
        split_ifs
        · exact ih _ _ _ _ _
        · rfl
      · rw [e2, ← Array.toList_append]
        split_ifs
        · exact ih _ _ _ _ _
        · rfl
        · rfl

theorem argminRecL_complete (keep : List Row → Bool) (nv : Nat)
    (hkeep : ∀ rows, keep rows = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h)
    (base : List Row) (terms : List (Array Int)) (h : ℕ → ℚ)
    (hbase : ∀ r ∈ base, r.StrictHolds nv h) (hsize : ∀ t ∈ terms, t.size = nv)
    (htwice : MinTwice (termVals nv terms h)) :
    ∃ rows, (argminPos (termVals nv terms h), rows) ∈ argminRecL keep base terms terms.length 0 none [] [] [] ∧
      ∀ r ∈ rows, r.StrictHolds nv h := by
  obtain ⟨rowsA, hm, hs⟩ := argminRec_complete (fun a => keep a.toList) nv
    (fun rows hc h' hall => hkeep rows.toList hc h' fun r hr => hall r (by simpa using hr)) base.toArray terms h
    (fun r hr => hbase r (by simpa using hr)) hsize htwice
  have e := argminRecL_eq keep base.toArray terms terms.length 0 none [] [] #[]
  simp only [List.toList_toArray, Array.toList_empty] at e
  refine ⟨rowsA.toList, ?_, fun r hr => hs r (by simpa using hr)⟩
  rw [e]
  exact List.mem_map.mpr ⟨_, hm, rfl⟩

theorem branchRecL_complete (keep : List Row → Bool) (nv : Nat)
    (hkeep : ∀ rows, keep rows = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h)
    (L0 : List Row) (h : ℕ → ℚ) (hL0 : ∀ r ∈ L0, r.StrictHolds nv h) :
    ∀ (branch : List SIdent) (extra : List Row) (chosen : List (Nat × List Nat)),
      (∀ r ∈ extra, r.StrictHolds nv h) →
      (∀ id ∈ branch, (∀ t ∈ id.terms, t.size = nv) ∧ MinTwice (termVals nv id.terms h)) →
      chosen ++ branch.map (fun id => (idCode id.name, argminPos (termVals nv id.terms h))) ∈
        branchRecL keep L0 branch extra chosen := by
  intro branch
  induction branch with
  | nil =>
    intro extra chosen _ _
    simp [branchRecL]
  | cons id rest ih =>
    intro extra chosen hextra hids
    obtain ⟨hsz, htw⟩ := hids id List.mem_cons_self
    have hbase : ∀ r ∈ L0 ++ extra, r.StrictHolds nv h := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hL0 r hr
      · exact hextra r hr
    obtain ⟨rows, hm, hrows⟩ := argminRecL_complete keep nv hkeep (L0 ++ extra) id.terms h hbase hsz htw
    have hextra' : ∀ r ∈ extra ++ rows, r.StrictHolds nv h := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hextra r hr
      · exact hrows r hr
    have hrec := ih (extra ++ rows) (chosen ++ [(idCode id.name, argminPos (termVals nv id.terms h))])
      hextra' (fun id' hid' => hids id' (List.mem_cons_of_mem _ hid'))
    rw [branchRecL, List.mem_flatMap]
    refine ⟨(argminPos (termVals nv id.terms h), rows), hm, ?_⟩
    simpa [List.map_cons, List.append_assoc] using hrec

/-! ## The forced identities -/

/-- The structured entry of a forced identity. -/
def entryFL (id : SIdent) : Nat × List Nat := (idCode id.name, id.forced.getD [])

/-- One step of `splitForcedL` when it does not fail. -/
def stepFL (b : List Row × List (Nat × List Nat) × List SIdent) (id : SIdent) :
    List Row × List (Nat × List Nat) × List SIdent :=
  match id.forced with
  | some f => (b.1 ++ forcedRows id.terms f, b.2.1 ++ [(idCode id.name, f)], b.2.2)
  | none => (b.1, b.2.1, b.2.2 ++ [id])

theorem foldl_stepFL : ∀ (ids : List SIdent) (b : List Row × List (Nat × List Nat) × List SIdent),
    ids.foldl stepFL b = (b.1 ++ CompleteAux.extraOf ids, b.2.1 ++ (ids.filter fun id => id.forced.isSome).map entryFL,
      b.2.2 ++ ids.filter fun id => id.forced.isNone)
  | [], b => by simp [CompleteAux.extraOf]
  | id :: ids, b => by
    rw [List.foldl_cons, foldl_stepFL ids]
    cases hf : id.forced with
    | none => simp [stepFL, hf, CompleteAux.extraOf]
    | some f =>
      simp only [stepFL, hf, CompleteAux.extraOf, List.flatMap_cons, List.filter_cons, Option.isSome_some, ite_true,
        Option.isNone_some, Bool.false_eq_true, ite_false, List.map_cons, entryFL, Option.getD_some]
      simp [List.append_assoc]

theorem splitForcedL_eq (ids : List SIdent) (h : ∀ id ∈ ids, ∀ f, id.forced = some f → 2 ≤ f.length) :
    splitForcedL ids = some (CompleteAux.extraOf ids, (ids.filter fun id => id.forced.isSome).map entryFL,
      ids.filter fun id => id.forced.isNone) := by
  unfold splitForcedL
  rw [CompleteAux.foldl_some _ stepFL (fun id => ∀ f, id.forced = some f → 2 ≤ f.length) ?_ ids _ h, foldl_stepFL]
  · simp
  · rintro ⟨rows, fixed, branch⟩ id hid
    cases hf : id.forced with
    | none => simp [stepFL, hf]
    | some f =>
      have hn : ¬ f.length < 2 := by have := hid f hf; omega
      simp [stepFL, hf, hn]

/-! ## The cells below a complete pair -/

/-- The structured argmin part of the cell of `(Xz, Xw)`: for the identities whose argmin set the diagram forces, then
for the other base identities, the code of the identity and the positions of its terms of least exponent. -/
noncomputable def argminIdx (D : L6.F2.Diag) (Xz Xw : ExpTree) : List (Nat × List Nat) :=
  let es := (identsMeta D Xz.T.leafO Xw.T.leafO).zip (baseExps Xz Xw)
  (es.filter fun ie => ie.1.2.2.isSome).map (fun ie => (idCode ie.1.1, ie.1.2.2.getD [])) ++
    (es.filter fun ie => ie.1.2.2.isNone).map (fun ie => (idCode ie.1.1, argminPos ie.2))

theorem cellsBelowL_complete {keep : List Row → Nat → Bool} (hk : KeepSoundL keep) {D : L6.F2.Diag}
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) (P : Pair) (hz : P.tz.Equiv Xz.T) (hzn : P.tz.nodes.Nodup)
    (hw : P.tw.Equiv Xw.T) (hwn : P.tw.nodes.Nodup) :
    argminIdx D Xz Xw ∈ cellsBelowL keep D P := by
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
  have hbr := branchRecL_complete (fun r => keep r P.nv) P.nv (fun rows hc h' => hk rows P.nv hc h') L0
    (heightVec Xz Xw P) hL0s (ids.filter fun id => id.forced.isNone) (CompleteAux.extraOf ids) [] hextra
    hbranch
  have hk0 : keep L0 P.nv = true := keepL_true hk hL0s
  have hk1 : keep (L0 ++ CompleteAux.extraOf ids) P.nv = true := keepL_true hk (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
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
  unfold cellsBelowL
  rw [hcz, hcw, hL0, hids]
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false, hk0]
  rw [splitForcedL_eq ids hf2]
  simp only [hk1, Bool.not_true, Bool.false_eq_true, ite_false]
  refine List.mem_map.mpr ⟨_, hbr, ?_⟩
  rw [List.nil_append]
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

/-- **Completeness of the search with lists of rows (Proposition 4.5).** For an insertion order listing the six
bodies, every pair of complete trees with heights satisfying `Cond D` has a cell of `searchL` with the same trees (as
sorted node sets) and the argmin sets `argminIdx D Xz Xw`. -/
theorem searchL_complete {keep : List Row → Nat → Bool} (hk : KeepSoundL keep) {D : L6.F2.Diag} {ord : List Nat}
    (hord : ord.Perm (List.range 6)) {Xz Xw : ExpTree} (hX : Cond D Xz Xw) :
    ∃ c ∈ searchL keep D ord, c.key = (Xz.T.key, Xw.T.key, argminIdx D Xz Xw) := by
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
  have hc := cellsBelowL_complete hk hX ⟨x.2.1, x.2.2⟩ hxz hxzn hxw hxwn
  refine ⟨⟨x.2.1, x.2.2, argminIdx D Xz Xw⟩, ?_, ?_⟩
  · unfold searchL
    rw [List.mem_flatMap]
    exact ⟨x, hx, List.mem_map.mpr ⟨_, hc, rfl⟩⟩
  · unfold SCellL.key
    rw [key_equiv hxz hxzn hX.gz.1.nodup, key_equiv hxw hxwn hX.gw.1.nodup]

theorem searchL_split (keep : List Row → Nat → Bool) (D : L6.F2.Diag) (ord : List Nat) (d : Nat) :
    searchL keep D ord = (prefixPairsL keep D ord d).flatMap (belowL keep D ord d) := by
  have h := treeLevelL_append keep D (ord.take d) (ord.drop d) (single O) TS.init TS.init
  rw [List.take_append_drop] at h
  rw [searchL, h, List.flatMap_assoc]
  rfl

/-- **The stored keys contain the key of every pair.** If every cell of `searchL` has its key in `ks`, then for
every pair of complete trees with heights satisfying `Cond D`, the key `(Xz.T.key, Xw.T.key, argminIdx D Xz Xw)`
is in `ks`. -/
theorem cellL_stored {keep : List Row → Nat → Bool} (hk : KeepSoundL keep) {D : L6.F2.Diag} {ord : List Nat}
    (hord : ord.Perm (List.range 6))
    {ks : List ((List Nat × Option Nat) × (List Nat × Option Nat) × List (Nat × List Nat))}
    (hkeys : ∀ c ∈ searchL keep D ord, c.key ∈ ks) {Xz Xw : ExpTree} (hX : Cond D Xz Xw) :
    (Xz.T.key, Xw.T.key, argminIdx D Xz Xw) ∈ ks := by
  obtain ⟨c, hc, hkey⟩ := searchL_complete hk hord hX
  rw [← hkey]
  exact hkeys c hc

/-! ## The rendering of the structured argmin sets -/

theorem identsMeta_codes (D : L6.F2.Diag) (lz lw : Option Nat) :
    (identsMeta D lz lw).map (fun m => idCode m.1) = List.range 14 := by
  simp only [identsMeta, bodyMeta, uMeta, iMeta, List.map_append, List.map_map, Function.comp_def, idCode,
    List.map_cons, List.map_nil]
  decide

theorem identsMeta_getD_code (D : L6.F2.Diag) (lz lw : Option Nat) {m : IdName × List Label × Option (List Nat)}
    (hm : m ∈ identsMeta D lz lw) : (identsMeta D lz lw).getD (idCode m.1) default = m := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
  have h := congrArg (fun l => l[i]?) (identsMeta_codes D lz lw)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some] at h
  have hi14 : i < 14 := by
    have := congrArg List.length (identsMeta_codes D lz lw)
    simp only [List.length_map, List.length_range] at this
    omega
  rw [List.getElem?_range hi14, Option.some.injEq] at h
  rw [h, List.getD_eq_getElem _ _ hi]

/-- **`argminString` is the rendering of `argminIdx`** with the names and labels of the base identities. -/
theorem argminString_eq_renderIdx (D : L6.F2.Diag) (Xz Xw : ExpTree) :
    argminString D Xz Xw = renderIdx (identsMeta D Xz.T.leafO Xw.T.leafO) (argminIdx D Xz Xw) := by
  unfold argminString renderIdx argminIdx
  dsimp only
  rw [List.map_append, List.map_map, List.map_map]
  congr 2
  · refine List.map_congr_left fun ie hie => ?_
    have hm := (List.of_mem_zip (List.mem_of_mem_filter hie)).1
    simp only [Function.comp_def, identsMeta_getD_code _ _ _ hm]
  · refine List.map_congr_left fun ie hie => ?_
    have hm := (List.of_mem_zip (List.mem_of_mem_filter hie)).1
    simp only [Function.comp_def, identsMeta_getD_code _ _ _ hm]

end L6.F2S
