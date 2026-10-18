import L6Sound.F34S.Meaning

/-!
# The meaning of the checks of F3, F4 on the cells of the specification search, from the meaning of the certificates

`chunkS_meaning_of`: `chunkS_meaning` with the hypothesis on the certificate texts of the chunk stated as their
meaning, `∀ p ∈ certs, ∃ c, parseCert p.2 = some c ∧ CertMeaning c`, instead of `checkCert p.2 = true` (which gives
it, `checkCert_meaning`). The meaning of a certificate may then come from a check in the kernel.
-/

namespace L6.F34S

open L6.F2S

theorem certMeaning_of_prepare_of {cls : Nat} {D : L6.F2.Diag}
    {cellsTxt singleTxt linksTxt passTxt openTxt : String} {certs : List (String × String)} {cd : ChunkDataS}
    (hp : prepareS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs = some cd)
    (hcerts : ∀ p ∈ certs, ∃ c, L6.Poly.parseCert p.2 = some c ∧ L6.Poly.CertMeaning c) :
    ∀ id c, cd.certs.lookup id = some c → L6.Poly.CertMeaning c := by
  intro id c hl
  unfold prepareS at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨parsed, hpa, ⟨single, links, pass⟩, _, hcd⟩ := hp
  simp only [Option.some.injEq] at hcd
  subst hcd
  obtain ⟨txt, hmem, hpc⟩ := L6.F34.parseAll_lookup hpa hl
  obtain ⟨c', hc', hm⟩ := hcerts _ hmem
  rw [hpc, Option.some.injEq] at hc'
  rw [hc']
  exact hm

theorem chunkS_meaning_of {cls : Nat} {D : L6.F2.Diag} {cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {lo hi : Nat} {expected : L6.F34.Counts}
    (h : checkChunkS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs lo hi expected = true)
    (hcerts : ∀ p ∈ certs, ∃ c, L6.Poly.parseCert p.2 = some c ∧ L6.Poly.CertMeaning c) :
    ∀ idx, lo ≤ idx → idx < hi →
      (L6.F34.openCells cls openTxt).contains idx = true ∨
      ∀ Xz Xw : ExpTree, Cond D Xz Xw →
        keyOfLine ((cellsTxt.splitOn "\n").toArray.getD idx "") = some (Xz.T.key, Xw.T.key, argminString D Xz Xw) →
        ClaimMeaning Xz Xw := by
  obtain ⟨cd, hp, hk⟩ := checkChunkS_spec h
  obtain ⟨hD, hcells, hopens⟩ := prepareS_spec hp
  have hcm := certMeaning_of_prepare_of hp hcerts
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
      exact claimHolds_meaning hP lz lw (hX.gz.1.of_equiv hzE hzn) hzE (hX.gw.1.of_equiv hwE hwn) hwE hrows hcm hclaim

end L6.F34S
