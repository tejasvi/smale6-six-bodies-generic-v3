import L6SoundK.F34K.Meaning
import L6SoundK.F2S.KeepR
import L6Sound.F2S.SearchL

/-!
# From the kernel checks of the units and levels to the exclusion of Proposition 5.3

* `branchRecRL_complete`, `cellsBelowRL_complete`: the search with rows lists the cell of `(Xz, Xw)` with rows that
  hold strictly at its heights (the proofs of lean6's `branchRecL_complete` and `cellsBelowL_complete`, keeping the
  rows, as `L6Sound.F34S.BelowR` does for the search on arrays);
* `treeLevelL_step`: one level of the tree search keeps the pair of trees on the path of `(Xz, Xw)`;
* `unit_covers`: a unit whose claims pass gives `ClaimMeaning Xz Xw` for every node of the unit on the path;
* `level_covers`: a level whose children are listed gives the child on the path;
* `NodeOK`: the conditions of a node of the search (`S` and the remaining bodies), kept along a level (`nodeOK_step`).
-/

namespace L6K.F34K

open L6 L6.F2S L6.F34S L6K.F2S

/-! ## The search with rows -/

theorem branchRecRL_complete (keep : List Row → Bool) (nv : Nat)
    (hkeep : ∀ rows, keep rows = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h)
    (L0 : List Row) (h : ℕ → ℚ) (hL0 : ∀ r ∈ L0, r.StrictHolds nv h) :
    ∀ (branch : List SIdent) (extra : List Row) (chosen : List (Nat × List Nat)),
      (∀ r ∈ extra, r.StrictHolds nv h) →
      (∀ id ∈ branch, (∀ t ∈ id.terms, t.size = nv) ∧ MinTwice (termVals nv id.terms h)) →
      ∃ rows, (chosen ++ branch.map (fun id => (idCode id.name, argminPos (termVals nv id.terms h))), rows) ∈
        branchRecRL keep L0 branch extra chosen ∧ ∀ r ∈ rows, r.StrictHolds nv h := by
  intro branch
  induction branch with
  | nil =>
    intro extra chosen hextra _
    exact ⟨extra, by simp [branchRecRL], hextra⟩
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
    obtain ⟨rows', hrec, hrows'⟩ := ih (extra ++ rows)
      (chosen ++ [(idCode id.name, argminPos (termVals nv id.terms h))])
      hextra' (fun id' hid' => hids id' (List.mem_cons_of_mem _ hid'))
    refine ⟨rows', ?_, hrows'⟩
    rw [branchRecRL, List.mem_flatMap]
    refine ⟨(argminPos (termVals nv id.terms h), rows), hm, ?_⟩
    simpa [List.map_cons, List.append_assoc] using hrec

theorem cellsBelowRL_complete {keep : List Row → Nat → Bool} (hk : KeepSoundL keep) {D : L6.F2.Diag}
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) (P : Pair) (hz : P.tz.Equiv Xz.T) (hzn : P.tz.nodes.Nodup)
    (hw : P.tw.Equiv Xw.T) (hwn : P.tw.nodes.Nodup) :
    ∃ rows, (argminIdx D Xz Xw, rows) ∈ cellsBelowRL keep D P ∧
      ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P) := by
  have hall : all < 128 := by decide
  have hOall : mem L6.F2S.O all = true := by decide
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
  obtain ⟨brows, hbr, hbrs⟩ := branchRecRL_complete (fun r => keep r P.nv) P.nv
    (fun rows hc h' => hk rows P.nv hc h') L0 (heightVec Xz Xw P) hL0s (ids.filter fun id => id.forced.isNone)
    (CompleteAux.extraOf ids) [] hextra hbranch
  have hk0 : keep L0 P.nv = true := keepL_true hk hL0s
  have hk1 : keep (L0 ++ CompleteAux.extraOf ids) P.nv = true := keepL_true hk (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hL0s r hr
    · exact hextra r hr)
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
  · rcases List.mem_append.mp hr with hr | hr
    · exact hL0s r hr
    · exact hbrs r hr
  unfold cellsBelowRL
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

/-! ## Nodes of the search -/

/-- The node `x` (set of inserted points and the two trees) lies on the path of `(Xz, Xw)`. -/
def OnPath (Xz Xw : ExpTree) (x : Nat × TS × TS) : Prop :=
  x.2.1.Equiv (restrict Xz.T x.1) ∧ x.2.1.nodes.Nodup ∧ x.2.2.Equiv (restrict Xw.T x.1) ∧ x.2.2.nodes.Nodup

/-- The conditions of the search at a node with the points `S` and the remaining bodies `rest`. -/
def NodeOK (S : Nat) (rest : List Nat) : Prop :=
  S < 128 ∧ mem L6.F2S.O S = true ∧ rest.Nodup ∧ (∀ p ∈ rest, p < 6 ∧ mem p S = false) ∧
    rest.foldl (fun s p => ins p s) S = all

/-- `NodeOK` as a test. -/
def nodeOKB (S : Nat) (rest : List Nat) : Bool :=
  decide (S < 128) && mem L6.F2S.O S && decide rest.Nodup && rest.all (fun p => decide (p < 6) && !mem p S) &&
    rest.foldl (fun s p => ins p s) S == all

theorem nodeOKB_spec {S : Nat} {rest : List Nat} (h : nodeOKB S rest = true) : NodeOK S rest := by
  simp only [nodeOKB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, fun p hp => ⟨(h4 p hp).1, (h4 p hp).2⟩, h5⟩

theorem nodeOK_step {S p : Nat} {rest : List Nat} (h : NodeOK S (p :: rest)) : NodeOK (ins p S) rest := by
  obtain ⟨hS, hO, hnd, hrest, hfold⟩ := h
  obtain ⟨hp6, hpS⟩ := hrest p List.mem_cons_self
  have hnd' := List.nodup_cons.mp hnd
  refine ⟨CompleteAux.ins_lt hS hp6, by rw [mem_ins, hO]; rfl, hnd'.2, fun q hq => ?_, by simpa using hfold⟩
  obtain ⟨hq6, hqS⟩ := hrest q (List.mem_cons_of_mem _ hq)
  refine ⟨hq6, ?_⟩
  rw [mem_ins, hqS]
  have hpq : p ≠ q := fun e => hnd'.1 (e ▸ hq)
  simp [hpq]

/-- One level of the tree search keeps the node on the path. -/
theorem treeLevelL_step {keep : List Row → Nat → Bool} (hk : KeepSoundL keep) {D : L6.F2.Diag}
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {p : Nat} {rest : List Nat} {x : Nat × TS × TS}
    (hn : NodeOK x.1 (p :: rest)) (hp : OnPath Xz Xw x) :
    ∃ y ∈ treeLevelL keep D [p] x.1 x.2.1 x.2.2, y.1 = ins p x.1 ∧ OnPath Xz Xw y := by
  obtain ⟨hS, hO, -, hrest, -⟩ := hn
  obtain ⟨hp6, hpS⟩ := hrest p List.mem_cons_self
  obtain ⟨htz, htzn, htw, htwn⟩ := hp
  have hS' : ins p x.1 < 128 := CompleteAux.ins_lt hS hp6
  have hO' : mem L6.F2S.O (ins p x.1) = true := by rw [mem_ins, hO]; rfl
  obtain ⟨tz', htz'm, htz'e, htz'n⟩ := options_complete hX.gz hS hO hp6 hpS htz htzn
  obtain ⟨tw', htw'm, htw'e, htw'n⟩ := options_complete hX.gw hS hO hp6 hpS htw htwn
  have lz := levelFacts hX.gz hX.root_z hS' hO' htz'e htz'n
  have lw := levelFacts hX.gw hX.root_w hS' hO' htw'e htw'n
  obtain ⟨rows, hrows, hstrict⟩ := partialRowsL_strict hX hS' hO' ⟨tz', tw'⟩ lz lw
  have hkeep : keep rows (Pair.nv ⟨tz', tw'⟩) = true := keepL_true hk hstrict
  refine ⟨(ins p x.1, tz', tw'), ?_, rfl, htz'e, htz'n, htw'e, htw'n⟩
  rw [treeLevelL, List.mem_flatMap]
  refine ⟨tz', htz'm, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨tw', htw'm, ?_⟩
  rw [hrows]
  simp [hkeep, treeLevelL]

/-! ## Units and levels -/

/-- **A unit.** If the claims of the cells below the nodes of a unit pass, then for every node of the unit on the path
of `(Xz, Xw)`, `ClaimMeaning Xz Xw`. -/
theorem unit_covers {certs : List CertKey}
    (hcerts : ∀ g ∈ certs, ∃ c : L6.Poly.Cert, L6.Poly.CertMeaning c ∧ c.nvar = g.1 ∧ c.fixed = g.2.1 ∧ c.gens = g.2.2)
    {T : CTree} {D : L6.F2.Diag} {ord : List Nat} {t : Nat} {nodes : List (Nat × TS × TS)} {claims : List ClaimK}
    (hok : checkCells certs (nodes.flatMap (belowRL (keepR T) D ord t)) claims = true)
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {x : Nat × TS × TS} (hx : x ∈ nodes)
    (hn : NodeOK x.1 (ord.drop t)) (hp : OnPath Xz Xw x) : ClaimMeaning Xz Xw := by
  obtain ⟨hS, hO, hnd, hrest, hfold⟩ := hn
  obtain ⟨htz, htzn, htw, htwn⟩ := hp
  obtain ⟨y, hy, -, hyz, hyzn, hyw, hywn⟩ := treeLevelL_complete (keepR_sound T) hX (ord.drop t) x.1 x.2.1 x.2.2
    hS hO hnd hrest hfold htz htzn htw htwn
  obtain ⟨rows, hmem, hrows⟩ := cellsBelowRL_complete (keepR_sound T) hX ⟨y.2.1, y.2.2⟩ hyz hyzn hyw hywn
  have hcell : (⟨y.2.1, y.2.2, argminIdx D Xz Xw, rows⟩ : RCell) ∈ nodes.flatMap (belowRL (keepR T) D ord t) := by
    rw [List.mem_flatMap]
    refine ⟨x, hx, ?_⟩
    unfold belowRL
    rw [List.mem_flatMap]
    refine ⟨y, hy, ?_⟩
    unfold cellsOfRL
    exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  obtain ⟨k, hk⟩ := checkCells_spec hok _ hcell
  have hall : all < 128 := by decide
  have hOall : mem L6.F2S.O all = true := by decide
  have lz := levelFacts hX.gz hX.root_z hall hOall (hyz.trans (restrict_all hX.gz).symm) hyzn
  have lw := levelFacts hX.gw hX.root_w hall hOall (hyw.trans (restrict_all hX.gw).symm) hywn
  exact claimK_meaning (P := ⟨y.2.1, y.2.2⟩) hcerts lz lw (hX.gz.1.of_equiv hyz hyzn) hyz
    (hX.gw.1.of_equiv hyw hywn) hyw (fun r hr => hrows r (by simpa using hr)) hk

/-- **A level.** If one level below `x` lists the children `children`, the child on the path of `(Xz, Xw)` is one of
them. -/
theorem level_covers {T : CTree} {D : L6.F2.Diag} {p : Nat} {rest : List Nat} {x : Nat × TS × TS}
    {children : List (Nat × TS × TS)} (hlv : treeLevelL (keepR T) D [p] x.1 x.2.1 x.2.2 = children)
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) (hn : NodeOK x.1 (p :: rest)) (hp : OnPath Xz Xw x) :
    ∃ y ∈ children, y.1 = ins p x.1 ∧ OnPath Xz Xw y := by
  rw [← hlv]
  exact treeLevelL_step (keepR_sound T) hX hn hp

/-- The root of the search is on every path. -/
theorem onPath_root (Xz Xw : ExpTree) {D : L6.F2.Diag} (hX : Cond D Xz Xw) :
    OnPath Xz Xw (single L6.F2S.O, TS.init, TS.init) :=
  ⟨restrict_init hX.gz, List.nodup_nil, restrict_init hX.gw, List.nodup_nil⟩

end L6K.F34K
