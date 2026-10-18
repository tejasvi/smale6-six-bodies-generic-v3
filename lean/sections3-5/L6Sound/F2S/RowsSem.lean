import L6Sound.F2S.RowsAux3

/-!
# The rows of the specification search at the heights of a pair of complete trees

Under the conditions `Cond D Xz Xw` and the facts `LevelFacts` of a pair of partial trees on a set `S` (the bodies of
`S` inserted, and `O`), every row of the pair holds strictly at the heights read off the complete trees
(`partialRows_strict`): the tree rows by the strict increase of the heights, (O1), (O2) and (C) by the conditions of
Lemma 4.3 (a), and the relaxation of `ℓ(x) ≤ 0` because `x_kl` is at least `1` on a `zw`-edge, `0` on a stroke and
`−2` always (from (O1), (O2) and the root heights `≥ −2`).

On complete trees (`S` = all seven points), the forms of the terms of the base identities have the values `2 ×` the
exponents of `baseExps` (`idents_eval`), and the forced argmin sets are the argmin sets of those exponents, with at
least two terms, and their rows hold strictly (`forced_facts`).
-/

namespace L6.F2S

theorem lin_eq_formVal (nv : Nat) (r : Row) (h : ℕ → ℚ) : r.lin nv h = formVal nv r.a h := rfl

theorem partialRows_strict {D : L6.F2.Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {S : Nat} (hS : S < 128)
    (hO : mem O S = true) (P : Pair) (hz : LevelFacts Xz P.tz S) (hw : LevelFacts Xw P.tw S) :
    ∃ rows, partialRows D P S = some rows ∧ ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P) := by
  obtain ⟨pr, hpr, hprs⟩ := RS.pairRows_strict hX hz hw
  obtain ⟨qr, hqr, hqrs⟩ := RS.posRows_strict hX hO hz hw
  obtain ⟨th, hth, hths⟩ := RS.thresholdRow_strict hX hz hw
  refine ⟨(treeRows P.tz 0 P.nv ++ treeRows P.tw P.nz P.nv ++ pr ++ qr ++ [th]).toArray, ?_, ?_⟩
  · unfold partialRows
    rw [hpr, hqr, hth]
    rfl
  · intro r hr
    rw [List.mem_toArray] at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (((hr | hr) | hr) | hr) | rfl
    · exact RS.treeRows_strict hz (fun C hC => by rw [Nat.zero_add]; exact RS.vz_lt hC)
        (fun C hC => by rw [Nat.zero_add]; exact RS.heightVec_vz hC) r hr
    · exact RS.treeRows_strict hw (fun C hC => RS.vw_lt hC) (fun C hC => RS.heightVec_vw hC) r hr
    · exact hprs r hr
    · exact hqrs r hr
    · exact hths

theorem idents_eval {D : L6.F2.Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) (P : Pair)
    (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) :
    ∃ ids, idents D P = some ids ∧ ids.length = (baseExps Xz Xw).length ∧
      ids.map (fun id => (id.name, id.labels, id.forced)) = identsMeta D P.tz.leafO P.tw.leafO ∧
      ∀ i < ids.length, (ids[i]!.terms.length = ((baseExps Xz Xw)[i]!).length ∧
        ids[i]!.labels.length = ids[i]!.terms.length ∧
        (∀ t ∈ ids[i]!.terms, t.size = P.nv) ∧
        ∀ t < ids[i]!.terms.length,
          formVal P.nv ids[i]!.terms[t]! (heightVec Xz Xw P) = 2 * ((baseExps Xz Xw)[i]!)[t]!) := by
  obtain ⟨ids, hids, hF⟩ := RS.idents_facts hX P hz hw
  have hlen := hF.length_eq
  have hE : ∀ i < ids.length,
      (baseExps Xz Xw)[i]! = ((RS.baseEM D Xz Xw P.tz.leafO P.tw.leafO)[i]!).1 := fun i hi => by
    rw [← RS.baseEM_fst D Xz Xw P.tz.leafO P.tw.leafO, RS.getElem!_map_of_lt Prod.fst (hlen ▸ hi)]
  refine ⟨ids, hids, ?_, ?_, fun i hi => ?_⟩
  · rw [hlen, ← RS.baseEM_fst D Xz Xw P.tz.leafO P.tw.leafO, List.length_map]
  · exact (RS.forall₂_map_eq (g := Prod.snd) (fun a b h => h.1) hF).trans (RS.baseEM_snd _ _ _ _ _)
  · obtain ⟨-, h2, h3, h4, h5, -⟩ := RS.forall₂_getElem! hF i hi
    rw [hE i hi]
    exact ⟨h2, h3, h4, h5⟩

theorem forced_facts {D : L6.F2.Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) (P : Pair)
    (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {ids : List SIdent}
    (hids : idents D P = some ids) :
    ∀ i < ids.length, ∀ f, ids[i]!.forced = some f →
      2 ≤ f.length ∧ argminPos ((baseExps Xz Xw)[i]!) = f ∧
      ∀ r ∈ forcedRows ids[i]!.terms f, r.StrictHolds P.nv (heightVec Xz Xw P) := by
  obtain ⟨ids', hids', hF⟩ := RS.idents_facts hX P hz hw
  rw [hids] at hids'
  cases hids'
  have hlen := hF.length_eq
  intro i hi f hf
  obtain ⟨-, h2, -, h4, h5, h6⟩ := RS.forall₂_getElem! hF i hi
  obtain ⟨hlen2, hamin⟩ := h6 f hf
  have hE : (baseExps Xz Xw)[i]! = ((RS.baseEM D Xz Xw P.tz.leafO P.tw.leafO)[i]!).1 := by
    rw [← RS.baseEM_fst D Xz Xw P.tz.leafO P.tw.leafO, RS.getElem!_map_of_lt Prod.fst (hlen ▸ hi)]
  rw [hE]
  exact ⟨hlen2, hamin, RS.forcedRows_strict h2 h4 h5 hamin⟩

end L6.F2S
