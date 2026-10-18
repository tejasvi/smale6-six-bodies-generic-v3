import CC6Compose.ExclusionImports
import CC6Compose.ClaimCore

/-!
# Bridge: the meaning of the checks of Proposition 5.3, with the certificate of each core named

The certificate project states the meaning of its checks of Proposition 5.3 on the cells of the specification search
as `L6.F34S.ClaimMeaning Xz Xw` (`L6.F34S.chunkS_meaning`, `L6.F34S.Checks.f34s_excluded`): a single-term identity,
or a core with a certificate that has `CertMeaning`. For the exclusion of a class at generic masses two more facts are
needed, which the checks give but `ClaimMeaning` does not record:

* the certificate is one of the certificate texts of the chunk (so that the polynomials `h` of all the germs of a
  class come from a finite list);
* the argmin set of each initial form of the core has no repetition (it is the list of positions computed by
  `L6.F34S.guessArgminS`, a filter of `List.range`), so that the value `itemVal` of the item is the initial form.

This file proves the meaning of the checks in this form, from the same pieces of the certificate project
(`L6.F34S.constant_meaning`, `L6.F34S.itemPoly_spec`, `L6.F34S.distPoly_spec`, `L6.F34S.single_meaning`,
`L6.F34S.itemVal_congr`, `L6.F2S.cellsBelowR_complete`, ...), following the proofs of `L6.F34S.genItem_meaning`,
`L6.F34S.link_meaning`, `L6.F34S.claimHolds_meaning` and `L6.F34S.chunkS_meaning`.

* `ItemOK Xz Xw it`: the item holds at `(Xz, Xw)` (`L6.F34S.ItemX.Holds`), and an initial form has an argmin set
  without repetition.
* `ClaimIn certs Xz Xw`: `ClaimMeaning` with the certificate read by `L6.Poly.parseCert` from one of the texts of
  `certs`, and the items `ItemOK`.
* `chunkS_meaning'`: a passing chunk whose certificate texts pass `checkCert`: every cell is open or `ClaimIn certs`
  holds at every pair satisfying `Cond` with its key.
* `ClassClaim k n certs`: the certificate texts `certs` pass `checkCert`, and each of the first `n` stored lines of
  class `k` is open or has `ClaimIn certs` at every pair satisfying `Cond` with its key; `ClassClaim.zero`,
  `ClassClaim.extend` (one more chunk).
-/

namespace CC6Compose

open L6.F2S (ExpTree Pair Cond LevelFacts heightVec keyOfLine argminString all TS)
open L6.F34S (XId ItemX VarM PCtx ETree ChunkDataS IsArgminX itemVal phiOf genItem genForS checkLinkS claimHolds
  guessArgminS constantArgminS termForm pairOfKeys checkChunkS prepareS cellKindS)

/-! ## The claim of a cell, with the certificate named -/

/-- **The claim of a cell**, as `L6.F34S.ClaimMeaning`, with the certificate of a core read from one of the texts
`certs` and the items `ItemOK`: a good identity with a term of strictly least exponent (Lemma 5.1), or a certificate
with `CertMeaning` each of whose generators is, at the point `phiOf vars X Y P E m` (`m_F = 1` when the mass `F` is
fixed), `1` or `2` times the value of an item of the initial system at `(Xz, Xw)` (Lemma 5.2). -/
def ClaimIn (certs : List (String × String)) (Xz Xw : ExpTree) : Prop :=
  (∃ I : XId, I.good = true ∧ ∃ i, IsArgminX I.terms Xz Xw [i]) ∨
  (∃ (c : L6.Poly.Cert) (vars : Array VarM), (∃ p ∈ certs, L6.Poly.parseCert p.2 = some c) ∧
    L6.Poly.CertMeaning c ∧ c.fixed < 6 ∧ vars.size = c.nvar ∧
    ∀ j < c.gens.length, ∃ it : ItemX, ItemOK Xz Xw it ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P : ℕ → ℕ → R) (E : R) (m : ℕ → R),
        (0 ≤ c.fixed → m c.fixed.toNat = 1) →
        (s : R) * L6.Poly.eval (6 + c.nvar) (phiOf vars X Y P E m) c.gens[j]! = itemVal Xz.T Xw.T X Y P E m it)

theorem ClaimIn.mono {certs certs' : List (String × String)} (h : ∀ p ∈ certs, p ∈ certs') {Xz Xw : ExpTree}
    (hc : ClaimIn certs Xz Xw) : ClaimIn certs' Xz Xw := by
  rcases hc with hs | ⟨c, vars, ⟨p, hp, hparse⟩, rest⟩
  · exact Or.inl hs
  · exact Or.inr ⟨c, vars, ⟨p, h p hp, hparse⟩, rest⟩

theorem guessArgminS_nodup (pt : Array Float) (fs : List (Option (Array Int))) : (guessArgminS pt fs).Nodup := by
  unfold guessArgminS
  exact (List.nodup_range).filter _

/-! ## Generators and links -/

section meaning

variable {Xz Xw : ExpTree} {P : Pair}

theorem genItem_meaning' (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array L6.Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {pt : Array Float}
    {fixed : Int} (hF6 : fixed < 6) {nm : L6.F34.IdName} {g : L6.Poly.Poly} (h : genItem x rows pt fixed nm = some g) :
    ∃ it : ItemX, ItemOK Xz Xw it ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P' : ℕ → ℕ → R) (E : R) (m : ℕ → R), (0 ≤ fixed → m fixed.toNat = 1) →
        (s : R) * L6.Poly.eval (6 + x.vars.size) (phiOf x.vars X Y P' E m) g =
          itemVal x.P.tz x.P.tw X Y P' E m it := by
  unfold genItem at h
  cases hI : XId.ofName nm with
  | none => rw [hI] at h; exact absurd h (by simp)
  | some I =>
    rw [hI] at h
    dsimp only at h
    by_cases hg : I.good = true
    · rw [ite_eq_left hg] at h
      by_cases hc : constantArgminS x.P.nv rows (I.terms.map (termForm x.P))
          (guessArgminS pt (I.terms.map (termForm x.P))) = true
      · rw [ite_eq_left hc] at h
        subst hxP
        refine ⟨.init I (guessArgminS pt (I.terms.map (termForm x.P))),
          ⟨⟨hg, L6.F34S.constant_meaning hz hw hrows hg hc⟩, guessArgminS_nodup _ _⟩, ?_⟩
        exact L6.F34S.itemPoly_spec x I _ fixed hg hF6 h
      · rw [ite_eq_right hc] at h
        exact absurd h (by simp)
    · rw [ite_eq_right hg] at h
      exact absurd h (by simp)

theorem genForS_meaning' (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array L6.Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {pt : Array Float}
    {fixed : Int} (hF6 : fixed < 6) {nmS : String} {g : L6.Poly.Poly} (h : genForS x rows pt fixed nmS = some g) :
    ∃ it : ItemX, ItemOK Xz Xw it ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P' : ℕ → ℕ → R) (E : R) (m : ℕ → R), (0 ≤ fixed → m fixed.toNat = 1) →
        (s : R) * L6.Poly.eval (6 + x.vars.size) (phiOf x.vars X Y P' E m) g =
          itemVal x.P.tz x.P.tw X Y P' E m it := by
  unfold genForS at h
  split at h
  · exact absurd h (by simp)
  · rename_i k l _
    by_cases hkl : (k < l && l < 6) = true
    · rw [ite_eq_left hkl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hkl
      refine ⟨.dist k l, hkl, 1, Or.inl rfl, fun X Y P' E m _ => ?_⟩
      rw [Nat.cast_one, one_mul]
      exact L6.F34S.distPoly_spec x k l hkl.1.le h X Y P' E m
    · rw [ite_eq_right hkl] at h
      exact absurd h (by simp)
  · exact genItem_meaning' hz hw hrows hxP hF6 h

/-- **F4, a link**, with the items `ItemOK`. -/
theorem link_meaning' (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array L6.Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {pt : Array Float}
    {lk : L6.F34.Link} {cert : L6.Poly.Cert} (h : checkLinkS x rows pt lk cert = true)
    (hvars : x.vars.size = lk.vars.size) :
    cert.fixed < 6 ∧ x.vars.size = cert.nvar ∧
      ∀ j < cert.gens.length, ∃ it : ItemX, ItemOK Xz Xw it ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
        ∀ {R : Type} [CommRing R] (X Y P' : ℕ → ℕ → R) (E : R) (m : ℕ → R),
          (0 ≤ cert.fixed → m cert.fixed.toNat = 1) →
          (s : R) * L6.Poly.eval (6 + cert.nvar) (phiOf x.vars X Y P' E m) cert.gens[j]! =
            itemVal x.P.tz x.P.tw X Y P' E m it := by
  unfold checkLinkS at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hnv, hfx⟩, hf6⟩, hlen⟩, hgen⟩ := h
  have hsz : x.vars.size = cert.nvar := by rw [hvars, hnv]
  refine ⟨by rw [hfx]; exact hf6, hsz, fun j hj => ?_⟩
  have hj' : j < lk.names.size := by rw [← hlen]; exact hj
  obtain ⟨it, hit, s, hs, heq⟩ := genForS_meaning' hz hw hrows hxP hf6 (hgen j hj')
  refine ⟨it, hit, s, hs, fun X Y P' E m hm1 => ?_⟩
  have := heq X Y P' E m (fun h0 => by rw [← hfx]; exact hm1 (by rw [hfx]; exact h0))
  rw [L6.Poly.eval_normalize, hsz] at this
  exact this

/-- **The claim of a cell**, with the certificate named: if the claim holds on a cell of the search whose rows hold
strictly at the heights read off `(Xz, Xw)`, then `ClaimIn certs Xz Xw`, for any list `certs` containing the texts
of the certificates of the chunk. -/
theorem claimHolds_meaning' {certs : List (String × String)} {cd : ChunkDataS} {idx : ℕ} {ez ew : ETree}
    {rows : Array L6.Row} (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all)
    (hzW : L6.F2S.WF P.tz all) (hzE : P.tz.Equiv Xz.T) (hwW : L6.F2S.WF P.tw all) (hwE : P.tw.Equiv Xw.T)
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P))
    (hcerts : ∀ id c, cd.certs.lookup id = some c →
      L6.Poly.CertMeaning c ∧ ∃ p ∈ certs, L6.Poly.parseCert p.2 = some c)
    (h : claimHolds cd idx P ez ew rows = true) : ClaimIn certs Xz Xw := by
  unfold claimHolds at h
  cases hs : cd.single.getD idx none with
  | some nl =>
    obtain ⟨nm, lab⟩ := nl
    rw [hs] at h
    dsimp only at h
    exact Or.inl (L6.F34S.single_meaning hz hw hrows h)
  | none =>
    rw [hs] at h
    cases hl : cd.links.getD idx none with
    | none => rw [hl] at h; exact absurd h (by simp)
    | some lk =>
      rw [hl] at h
      dsimp only at h
      cases hc : cd.certs.lookup lk.cert with
      | none => rw [hc] at h; exact absurd h (by simp)
      | some cert =>
        cases hpt : L6.F34.interiorPoint rows P.nv with
        | none => rw [hc, hpt] at h; exact absurd h (by simp)
        | some pt =>
          rw [hc, hpt] at h
          dsimp only at h
          have hvars : (lk.vars.map (L6.F34S.readVar ez ew)).size = lk.vars.size := Array.size_map ..
          obtain ⟨hf6, hsz, hgen⟩ := link_meaning' (x := { P, ez, ew, vars := lk.vars.map (L6.F34S.readVar ez ew) })
            hz hw hrows rfl h hvars
          obtain ⟨hm, hmem⟩ := hcerts _ _ hc
          refine Or.inr ⟨cert, lk.vars.map (L6.F34S.readVar ez ew), hmem, hm, hf6, hsz, fun j hj => ?_⟩
          obtain ⟨it, hit, s, hs, heq⟩ := hgen j hj
          refine ⟨it, hit, s, hs, fun X Y P' E m hm1 => ?_⟩
          have := heq X Y P' E m hm1
          rw [← L6.F34S.itemVal_congr hzW hzE hwW hwE]
          exact this

end meaning

/-! ## The chunk -/

theorem certs_of_prepare {cls : ℕ} {D : L6.F2.Diag} {cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {cd : ChunkDataS}
    (hp : prepareS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs = some cd)
    (hcerts : ∀ p ∈ certs, L6.Poly.checkCert p.2 = true) :
    ∀ id c, cd.certs.lookup id = some c → L6.Poly.CertMeaning c ∧ ∃ p ∈ certs, L6.Poly.parseCert p.2 = some c := by
  intro id c hl
  refine ⟨L6.F34S.certMeaning_of_prepare hp hcerts id c hl, ?_⟩
  unfold prepareS at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨parsed, hpa, ⟨single, links, pass⟩, _, hcd⟩ := hp
  simp only [Option.some.injEq] at hcd
  subst hcd
  obtain ⟨txt, hmem, hparse⟩ := L6.F34.parseAll_lookup hpa hl
  exact ⟨(id, txt), hmem, hparse⟩

/-- **F3/F4 on a chunk, with the certificates named.** If the check of a chunk passes and its certificate texts pass
`checkCert`, every cell `lo ≤ idx < hi` is listed as open, or `ClaimIn certs` holds at every pair of complete trees
with heights satisfying `Cond D` whose key is that of the stored line `idx`. -/
theorem chunkS_meaning' {cls : ℕ} {D : L6.F2.Diag} {cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {lo hi : ℕ} {expected : L6.F34.Counts}
    (h : checkChunkS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs lo hi expected = true)
    (hcerts : ∀ p ∈ certs, L6.Poly.checkCert p.2 = true) :
    ∀ idx, lo ≤ idx → idx < hi →
      (L6.F34.openCells cls openTxt).contains idx = true ∨
      ∀ Xz Xw : ExpTree, Cond D Xz Xw →
        keyOfLine ((cellsTxt.splitOn "\n").toArray.getD idx "") = some (Xz.T.key, Xw.T.key, argminString D Xz Xw) →
        ClaimIn certs Xz Xw := by
  obtain ⟨cd, hp, hk⟩ := L6.F34S.checkChunkS_spec h
  obtain ⟨hD, hcells, hopens⟩ := L6.F34S.prepareS_spec hp
  have hcm := certs_of_prepare hp hcerts
  intro idx h1 h2
  have hk' := hk idx h1 h2
  unfold L6.F34S.kindOf at hk'
  cases hpk : L6.F34S.pairKeyOf (cd.cells.getD idx "") with
  | none => rw [hpk] at hk'; exact absurd rfl hk'
  | some pk =>
    rw [hpk] at hk'
    dsimp only at hk'
    rcases L6.F34S.cellKindS_spec hk' with ho | ⟨kz, kw, am, ez, ew, hkey, het, hcl⟩
    · left; rw [← hopens]; exact ho
    · right
      intro Xz Xw hX hkeyX
      rw [← hcells] at hkeyX
      rw [hkey] at hkeyX
      simp only [Option.some.injEq, Prod.mk.injEq] at hkeyX
      obtain ⟨rfl, rfl, rfl⟩ := hkeyX
      have hpk' : pk = (Xz.T.key, Xw.T.key) := by
        unfold L6.F34S.pairKeyOf at hpk
        rw [hkey] at hpk
        simp only [Option.map_some, Option.some.injEq] at hpk
        exact hpk.symm
      subst hpk'
      rw [hD] at hk'
      set P := pairOfKeys Xz.T.key Xw.T.key with hP
      have hall : all < 128 := by decide
      have hOall : L6.F2S.mem L6.F2S.O all = true := by decide
      have hzn : P.tz.nodes.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr hX.gz.1.nodup
      have hwn : P.tw.nodes.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr hX.gw.1.nodup
      have hzE : P.tz.Equiv Xz.T := ⟨List.toFinset_eq_of_perm _ _ (List.mergeSort_perm _ _), rfl⟩
      have hwE : P.tw.Equiv Xw.T := ⟨List.toFinset_eq_of_perm _ _ (List.mergeSort_perm _ _), rfl⟩
      have lz := L6.F2S.levelFacts hX.gz hX.root_z hall hOall (hzE.trans (L6.F2S.restrict_all hX.gz).symm) hzn
      have lw := L6.F2S.levelFacts hX.gw hX.root_w hall hOall (hwE.trans (L6.F2S.restrict_all hX.gw).symm) hwn
      obtain ⟨rows, hmem, hrows⟩ := L6.F2S.cellsBelowR_complete L6.F2S.keepLP_sound hX P hzE hzn hwE hwn
      have hclaim := hcl _ (by rw [hD]; exact hmem) rfl
      exact claimHolds_meaning' lz lw (hX.gz.1.of_equiv hzE hzn) hzE (hX.gw.1.of_equiv hwE hwn) hwE hrows hcm hclaim

/-! ## The stored lines of a class -/

/-- The certificate texts `certs` pass `checkCert`, and each of the first `n` stored lines of class `k` is one of the
open cells, or `ClaimIn certs` holds at every pair of complete trees with heights satisfying `Cond (diagOf k)` with
the key of the line. -/
def ClassClaim (k n : ℕ) (certs : List (String × String)) : Prop :=
  (∀ p ∈ certs, L6.Poly.checkCert p.2 = true) ∧
  ∀ idx, idx < n → (L6.F34.openCells k L6.F34.Data.open43).contains idx = true ∨
    ∀ Xz Xw : ExpTree, Cond (L6.F2.diagOf k) Xz Xw →
      keyOfLine (((L6.F2.Checks.cellsOf k).splitOn "\n").toArray.getD idx "") =
        some (Xz.T.key, Xw.T.key, argminString (L6.F2.diagOf k) Xz Xw) →
      ClaimIn certs Xz Xw

theorem ClassClaim.zero (k : ℕ) : ClassClaim k 0 [] :=
  ⟨fun _ hp => absurd hp List.not_mem_nil, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- One more chunk: the lines `lo ≤ idx < hi` of a passing chunk of class `k`. -/
theorem ClassClaim.extend {k lo hi : ℕ} {certs certs' : List (String × String)} {txt single links pass : String}
    {expected : L6.F34.Counts} (h : ClassClaim k lo certs)
    (hc : checkChunkS k (L6.F2.diagOf k) txt single links pass L6.F34.Data.open43 certs' lo hi expected = true)
    (hok : ∀ p ∈ certs', L6.Poly.checkCert p.2 = true) (htxt : L6.F2.Checks.cellsOf k = txt) :
    ClassClaim k hi (certs ++ certs') := by
  refine ⟨fun p hp => ?_, fun idx hidx => ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · exact h.1 p hp
    · exact hok p hp
  · by_cases hlo : idx < lo
    · rcases h.2 idx hlo with ho | hcl
      · exact Or.inl ho
      · exact Or.inr fun Xz Xw hX hkey =>
          (hcl Xz Xw hX hkey).mono fun p hp => List.mem_append_left _ hp
    · rcases chunkS_meaning' hc hok idx (by omega) hidx with ho | hcl
      · exact Or.inl ho
      · refine Or.inr fun Xz Xw hX hkey => ?_
        rw [htxt] at hkey
        exact (hcl Xz Xw hX hkey).mono fun p hp => List.mem_append_right _ hp

end CC6Compose
