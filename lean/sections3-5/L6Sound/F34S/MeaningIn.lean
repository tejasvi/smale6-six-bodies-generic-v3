import L6Sound.F34S.MeaningOf

/-!
# The meaning of the checks of F3, F4 on the cells of the specification search, with the certificates named

`ClaimMeaningIn certs Xz Xw` is `ClaimMeaning Xz Xw` with the certificate of a core parsed from one of the texts of
the list `certs`, and the argmin sets of the initial forms without repetition (`ItemX.HoldsN`). For the exclusion of
a class at generic masses this gives finitely many polynomials `h`, fixed before the pair: one for each text of the
list of the class. `chunkS_meaningIn` is `chunkS_meaning_of` with this conclusion.
-/

namespace L6.F34S

open L6.F2S
open L6.F34 (Lab IdName Link prunedWith)

variable {Xz Xw : ExpTree} {P : Pair}

/-- The item holds at `(Xz, Xw)` (`ItemX.Holds`), and the argmin set of an initial form has no repetition. -/
def ItemX.HoldsN (Xz Xw : ExpTree) : ItemX → Prop
  | .init I S => I.good = true ∧ IsArgminX I.terms Xz Xw S ∧ S.Nodup
  | .dist k l => k < l ∧ l < 6

/-- **The claim of a cell, with the certificate named**: a good identity with a term of strictly least exponent
(Lemma 5.1), or a certificate parsed from one of the texts of `certs`, with `CertMeaning`, each of whose generators is
`1` or `2` times the value of an item holding at `(Xz, Xw)` with an argmin set without repetition (Lemma 5.2). -/
def ClaimMeaningIn (certs : List (String × String)) (Xz Xw : ExpTree) : Prop :=
  (∃ I : XId, I.good = true ∧ ∃ i, IsArgminX I.terms Xz Xw [i]) ∨
  (∃ p ∈ certs, ∃ (c : L6.Poly.Cert) (vars : Array VarM),
    L6.Poly.parseCert p.2 = some c ∧ L6.Poly.CertMeaning c ∧ c.fixed < 6 ∧ vars.size = c.nvar ∧
    ∀ j < c.gens.length, ∃ it : ItemX, it.HoldsN Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P : Nat → Nat → R) (E : R) (m : Nat → R),
        (0 ≤ c.fixed → m c.fixed.toNat = 1) →
        (s : R) * L6.Poly.eval (6 + c.nvar) (phiOf vars X Y P E m) c.gens[j]! =
          itemVal Xz.T Xw.T X Y P E m it)

theorem claimMeaningIn_mono {l l' : List (String × String)} (hl : ∀ p ∈ l, p ∈ l') :
    ClaimMeaningIn l Xz Xw → ClaimMeaningIn l' Xz Xw := by
  rintro (h | ⟨p, hp, rest⟩)
  · exact Or.inl h
  · exact Or.inr ⟨p, hl p hp, rest⟩

theorem guessArgminS_nodup (pt : Array Float) (fs : List (Option (Array Int))) : (guessArgminS pt fs).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem certIn_of_prepare {cls : Nat} {D : L6.F2.Diag} {cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {cd : ChunkDataS}
    (hp : prepareS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs = some cd)
    (hcerts : ∀ p ∈ certs, ∃ c, L6.Poly.parseCert p.2 = some c ∧ L6.Poly.CertMeaning c) :
    ∀ id c, cd.certs.lookup id = some c →
      ∃ p ∈ certs, L6.Poly.parseCert p.2 = some c ∧ L6.Poly.CertMeaning c := by
  intro id c hl
  unfold prepareS at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨parsed, hpa, ⟨single, links, pass⟩, _, hcd⟩ := hp
  simp only [Option.some.injEq] at hcd
  subst hcd
  obtain ⟨txt, hmem, hpc⟩ := L6.F34.parseAll_lookup hpa hl
  obtain ⟨c', hc', hm⟩ := hcerts _ hmem
  rw [hpc, Option.some.injEq] at hc'
  refine ⟨(id, txt), hmem, hpc, ?_⟩
  rw [hc']
  exact hm

theorem genItem_meaningN (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {pt : Array Float}
    {fixed : Int} (hF6 : fixed < 6) {nm : IdName} {g : L6.Poly.Poly} (h : genItem x rows pt fixed nm = some g) :
    ∃ it : ItemX, it.HoldsN Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P' : Nat → Nat → R) (E : R) (m : Nat → R), (0 ≤ fixed → m fixed.toNat = 1) →
        (s : R) * L6.Poly.eval (6 + x.vars.size) (phiOf x.vars X Y P' E m) g =
          itemVal x.P.tz x.P.tw X Y P' E m it := by
  unfold genItem at h
  cases hI : XId.ofName nm with
  | none => rw [hI] at h; exact absurd h (by simp)
  | some I =>
    rw [hI] at h
    dsimp only at h
    by_cases hg : I.good = true
    · rw [if_pos hg] at h
      by_cases hc : constantArgminS x.P.nv rows (I.terms.map (termForm x.P))
          (guessArgminS pt (I.terms.map (termForm x.P))) = true
      · rw [if_pos hc] at h
        subst hxP
        refine ⟨.init I (guessArgminS pt (I.terms.map (termForm x.P))), ⟨hg, constant_meaning hz hw hrows hg hc, guessArgminS_nodup _ _⟩, ?_⟩
        exact itemPoly_spec x I _ fixed hg hF6 h
      · rw [if_neg hc] at h
        exact absurd h (by simp)
    · rw [if_neg hg] at h
      exact absurd h (by simp)

theorem genForS_meaningN (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {pt : Array Float}
    {fixed : Int} (hF6 : fixed < 6) {nmS : String} {g : L6.Poly.Poly} (h : genForS x rows pt fixed nmS = some g) :
    ∃ it : ItemX, it.HoldsN Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P' : Nat → Nat → R) (E : R) (m : Nat → R), (0 ≤ fixed → m fixed.toNat = 1) →
        (s : R) * L6.Poly.eval (6 + x.vars.size) (phiOf x.vars X Y P' E m) g =
          itemVal x.P.tz x.P.tw X Y P' E m it := by
  unfold genForS at h
  split at h
  · exact absurd h (by simp)
  · rename_i k l _
    by_cases hkl : (k < l && l < 6) = true
    · rw [if_pos hkl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hkl
      refine ⟨.dist k l, hkl, 1, Or.inl rfl, fun X Y P' E m _ => ?_⟩
      rw [Nat.cast_one, one_mul]
      exact distPoly_spec x k l hkl.1.le h X Y P' E m
    · rw [if_neg hkl] at h
      exact absurd h (by simp)
  · exact genItem_meaningN hz hw hrows hxP hF6 h

/-- **F4, a link**, with argmin sets without repetition. -/
theorem link_meaningN (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {pt : Array Float}
    {lk : Link} {cert : L6.Poly.Cert} (h : checkLinkS x rows pt lk cert = true) (hm : L6.Poly.CertMeaning cert)
    (hvars : x.vars.size = lk.vars.size) :
    L6.Poly.CertMeaning cert ∧ cert.fixed < 6 ∧ x.vars.size = cert.nvar ∧
      ∀ j < cert.gens.length, ∃ it : ItemX, it.HoldsN Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
        ∀ {R : Type} [CommRing R] (X Y P' : Nat → Nat → R) (E : R) (m : Nat → R),
          (0 ≤ cert.fixed → m cert.fixed.toNat = 1) →
          (s : R) * L6.Poly.eval (6 + cert.nvar) (phiOf x.vars X Y P' E m) cert.gens[j]! =
            itemVal x.P.tz x.P.tw X Y P' E m it := by
  unfold checkLinkS at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hnv, hfx⟩, hf6⟩, hlen⟩, hgen⟩ := h
  have hsz : x.vars.size = cert.nvar := by rw [hvars, hnv]
  refine ⟨hm, by rw [hfx]; exact hf6, hsz, fun j hj => ?_⟩
  have hj' : j < lk.names.size := by rw [← hlen]; exact hj
  obtain ⟨it, hit, s, hs, heq⟩ := genForS_meaningN hz hw hrows hxP hf6 (hgen j hj')
  refine ⟨it, hit, s, hs, fun X Y P' E m hm1 => ?_⟩
  have := heq X Y P' E m (fun h0 => by rw [← hfx]; exact hm1 (by rw [hfx]; exact h0))
  rw [L6.Poly.eval_normalize, hsz] at this
  exact this

theorem claimHolds_meaningIn {certs : List (String × String)} {cd : ChunkDataS} {idx : Nat} {ez ew : ETree} {rows : Array Row}
    (hP : P = pairOfKeys Xz.T.key Xw.T.key) (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all)
    (hzW : WF P.tz all) (hzE : P.tz.Equiv Xz.T) (hwW : WF P.tw all) (hwE : P.tw.Equiv Xw.T)
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P))
    (hcerts : ∀ id c, cd.certs.lookup id = some c →
      ∃ p ∈ certs, L6.Poly.parseCert p.2 = some c ∧ L6.Poly.CertMeaning c)
    (h : claimHolds cd idx P ez ew rows = true) : ClaimMeaningIn certs Xz Xw := by
  unfold claimHolds at h
  cases hs : cd.single.getD idx none with
  | some nl =>
    obtain ⟨nm, lab⟩ := nl
    rw [hs] at h
    dsimp only at h
    exact Or.inl (single_meaning hz hw hrows h)
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
          have hvars : (lk.vars.map (readVar ez ew)).size = lk.vars.size := Array.size_map ..
          obtain ⟨p, hpc, hparse, hm0⟩ := hcerts _ _ hc
          obtain ⟨hm, hf6, hsz, hgen⟩ := link_meaningN (x := { P, ez, ew, vars := lk.vars.map (readVar ez ew) })
            hz hw hrows rfl h hm0 hvars
          refine Or.inr ⟨p, hpc, cert, lk.vars.map (readVar ez ew), hparse, hm, hf6, hsz, fun j hj => ?_⟩
          obtain ⟨it, hit, s, hs, heq⟩ := hgen j hj
          refine ⟨it, hit, s, hs, fun X Y P' E m hm1 => ?_⟩
          have := heq X Y P' E m hm1
          rw [← itemVal_congr hzW hzE hwW hwE]
          exact this

theorem chunkS_meaningIn {cls : Nat} {D : L6.F2.Diag} {cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {lo hi : Nat} {expected : L6.F34.Counts}
    (h : checkChunkS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs lo hi expected = true)
    (hcerts : ∀ p ∈ certs, ∃ c, L6.Poly.parseCert p.2 = some c ∧ L6.Poly.CertMeaning c) :
    ∀ idx, lo ≤ idx → idx < hi →
      (L6.F34.openCells cls openTxt).contains idx = true ∨
      ∀ Xz Xw : ExpTree, Cond D Xz Xw →
        keyOfLine ((cellsTxt.splitOn "\n").toArray.getD idx "") = some (Xz.T.key, Xw.T.key, argminString D Xz Xw) →
        ClaimMeaningIn certs Xz Xw := by
  obtain ⟨cd, hp, hk⟩ := checkChunkS_spec h
  obtain ⟨hD, hcells, hopens⟩ := prepareS_spec hp
  have hcm := certIn_of_prepare hp hcerts
  intro idx h1 h2
  have hk' := hk idx h1 h2
  unfold kindOf at hk'
  cases hpk : pairKeyOf (cd.cells.getD idx "") with
  | none => rw [hpk] at hk'; exact absurd rfl hk'
  | some pk =>
    rw [hpk] at hk'
    dsimp only at hk'
    rcases cellKindS_spec hk' with ho | ⟨kz, kw, am, ez, ew, hkey, het, hcl⟩
    · left; rw [← hopens]; exact ho
    · right
      intro Xz Xw hX hkeyX
      rw [← hcells] at hkeyX
      rw [hkey] at hkeyX
      simp only [Option.some.injEq, Prod.mk.injEq] at hkeyX
      obtain ⟨rfl, rfl, rfl⟩ := hkeyX
      have hpk' : pk = (Xz.T.key, Xw.T.key) := by
        unfold pairKeyOf at hpk
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
      have lz := levelFacts hX.gz hX.root_z hall hOall (hzE.trans (restrict_all hX.gz).symm) hzn
      have lw := levelFacts hX.gw hX.root_w hall hOall (hwE.trans (restrict_all hX.gw).symm) hwn
      obtain ⟨rows, hmem, hrows⟩ := cellsBelowR_complete keepLP_sound hX P hzE hzn hwE hwn
      have hclaim := hcl _ (by rw [hD]; exact hmem) rfl
      exact claimHolds_meaningIn hP lz lw (hX.gz.1.of_equiv hzE hzn) hzE (hX.gw.1.of_equiv hwE hwn) hwE hrows hcm hclaim

end L6.F34S
