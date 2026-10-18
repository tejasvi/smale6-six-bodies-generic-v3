import L6SoundK.F34K.Assembly
import L6K.F34K.Nodup

/-!
# The claim of a cell with the certificate from a list

`ClaimMeaningFinK cs Xz Xw` is `L6.F34S.ClaimMeaning Xz Xw` with the certificate of a core taken from the list `cs`
and the items `ItemOKK`: holding at `(Xz, Xw)`, with the argmin set of an initial form without repetition. This is the
form in which Lemma 5.2 is applied at generic masses: the polynomials of the certificates of a class come from a finite
list, and the value `itemVal` of an item is its initial form.

* `claimK_meaningF`: as `claimK_meaning`, for a claim whose argmin sets have no repetition (`claimNodupB`) and whose
  certificate keys are those of certificates of `cs` with `CertMeaning`;
* `unit_coversF`: as `unit_covers`, with the test `claimNodupB` on the claims of the unit.
-/

namespace L6K.F34K

open L6 L6.F2S L6.F34S L6.Poly L6K.F2S

variable {Xz Xw : ExpTree} {P : Pair}

/-- The item holds at `(Xz, Xw)`, and the argmin set of an initial form has no repetition. -/
def ItemOKK (Xz Xw : ExpTree) : ItemX → Prop
  | .init I S => (ItemX.init I S).Holds Xz Xw ∧ S.Nodup
  | .dist k l => (ItemX.dist k l).Holds Xz Xw

/-- **The claim of a cell, with the certificate from the list `cs`**: a good identity with a term of strictly least
exponent (Lemma 5.1), or a certificate of `cs` with `CertMeaning` each of whose generators is, at the point
`phiOf vars X Y P E m` (`m_F = 1` when the mass `F` is fixed), `1` or `2` times the value of an item `ItemOKK` at
`(Xz, Xw)` (Lemma 5.2). -/
def ClaimMeaningFinK (cs : List Cert) (Xz Xw : ExpTree) : Prop :=
  (∃ I : XId, I.good = true ∧ ∃ i, IsArgminX I.terms Xz Xw [i]) ∨
  (∃ c ∈ cs, ∃ vars : Array VarM, CertMeaning c ∧ c.fixed < 6 ∧ vars.size = c.nvar ∧
    ∀ j < c.gens.length, ∃ it : ItemX, ItemOKK Xz Xw it ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P : ℕ → ℕ → R) (E : R) (m : ℕ → R),
        (0 ≤ c.fixed → m c.fixed.toNat = 1) →
        (s : R) * eval (6 + c.nvar) (phiOf vars X Y P E m) c.gens[j]! = itemVal Xz.T Xw.T X Y P E m it)

theorem nodupB_spec : ∀ {l : List Nat}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun ha => ?_, nodupB_spec h.2⟩
    rw [List.contains_iff_mem.mpr ha] at h
    exact absurd h.1 (by simp)

/-! ## Generators and links -/

theorem genItemK_meaningF (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P)
    {fixed : Int} (hF6 : fixed < 6) {it : ItemK} (hnd : it.S.Nodup) {g : Poly}
    (h : genItemK x rows fixed it = some g) :
    ∃ it' : ItemX, ItemOKK Xz Xw it' ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P' : Nat → Nat → R) (E : R) (m : Nat → R), (0 ≤ fixed → m fixed.toNat = 1) →
        (s : R) * eval (6 + x.vars.size) (phiOf x.vars X Y P' E m) g =
          itemVal x.P.tz x.P.tw X Y P' E m it' := by
  unfold genItemK at h
  cases hI : XId.ofName it.nm with
  | none => rw [hI] at h; exact absurd h (by simp)
  | some I =>
    rw [hI] at h
    dsimp only at h
    by_cases hg : I.good = true
    · rw [if_pos hg] at h
      by_cases hc : constantArgminK x.P.nv rows (I.terms.map (termForm x.P)) it.S it.cA it.cB = true
      · rw [if_pos hc] at h
        subst hxP
        refine ⟨.init I it.S, ⟨⟨hg, constantK_meaning hz hw hrows hg hc⟩, hnd⟩, ?_⟩
        exact itemPolyK_spec x I _ fixed hg hF6 h
      · rw [if_neg hc] at h
        exact absurd h (by simp)
    · rw [if_neg hg] at h
      exact absurd h (by simp)

theorem genForSK_meaningF (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P)
    {fixed : Int} (hF6 : fixed < 6) {it : ItemK} (hnd : it.S.Nodup) {g : Poly}
    (h : genForSK x rows fixed it = some g) :
    ∃ it' : ItemX, ItemOKK Xz Xw it' ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P' : Nat → Nat → R) (E : R) (m : Nat → R), (0 ≤ fixed → m fixed.toNat = 1) →
        (s : R) * eval (6 + x.vars.size) (phiOf x.vars X Y P' E m) g =
          itemVal x.P.tz x.P.tw X Y P' E m it' := by
  unfold genForSK at h
  split at h
  · rename_i k l _
    by_cases hkl : (k < l && l < 6) = true
    · rw [if_pos hkl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hkl
      refine ⟨.dist k l, hkl, 1, Or.inl rfl, fun X Y P' E m _ => ?_⟩
      rw [Nat.cast_one, one_mul]
      exact distPolyK_spec x k l hkl.1.le h X Y P' E m
    · rw [if_neg hkl] at h
      exact absurd h (by simp)
  · exact genItemK_meaningF hz hw hrows hxP hF6 hnd h

/-- `linkK_meaning` with items `ItemOKK`. -/
theorem linkK_meaningF (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {fixed : Int}
    {items : List ItemK} (hnd : ∀ it ∈ items, it.S.Nodup) {cert : Cert}
    (h : checkLinkK x rows fixed items cert = true) (hm : CertMeaning cert) :
    CertMeaning cert ∧ cert.fixed < 6 ∧ x.vars.size = cert.nvar ∧
      ∀ j < cert.gens.length, ∃ it : ItemX, ItemOKK Xz Xw it ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
        ∀ {R : Type} [CommRing R] (X Y P' : Nat → Nat → R) (E : R) (m : Nat → R),
          (0 ≤ cert.fixed → m cert.fixed.toNat = 1) →
          (s : R) * eval (6 + cert.nvar) (phiOf x.vars X Y P' E m) cert.gens[j]! =
            itemVal x.P.tz x.P.tw X Y P' E m it := by
  unfold checkLinkK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hnv, hfx⟩, hf6⟩, hlen⟩, hgen⟩ := h
  have hsz : x.vars.size = cert.nvar := hnv.symm
  refine ⟨hm, by rw [hfx]; exact hf6, hsz, fun j hj => ?_⟩
  have hj' : j < items.length := by rw [← hlen]; exact hj
  have hndj : (items.getD j default).S.Nodup := by
    rw [List.getD_eq_getElem _ _ hj']
    exact hnd _ (List.getElem_mem hj')
  obtain ⟨it, hit, s, hs, heq⟩ := genForSK_meaningF hz hw hrows hxP hf6 hndj (hgen j hj')
  refine ⟨it, hit, s, hs, fun X Y P' E m hm1 => ?_⟩
  have := heq X Y P' E m (fun h0 => by rw [← hfx]; exact hm1 (by rw [hfx]; exact h0))
  rw [eval_normalizeK, hsz] at this
  exact this

/-! ## The claim -/

/-- **The claim of a cell checked by the kernel, with the certificate from `cs`.** As `claimK_meaning`, for a claim
whose argmin sets have no repetition and whose certificate keys are those of certificates of `cs` with
`CertMeaning`. -/
theorem claimK_meaningF {cs : List Cert} {certs : List CertKey}
    (hcerts : ∀ g ∈ certs, ∃ c ∈ cs, CertMeaning c ∧ c.nvar = g.1 ∧ c.fixed = g.2.1 ∧ c.gens = g.2.2)
    {rows : Array Row} {cd : ClaimK}
    (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all)
    (hzW : WF P.tz all) (hzE : P.tz.Equiv Xz.T) (hwW : WF P.tw all) (hwE : P.tw.Equiv Xw.T)
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P))
    (h : claimK certs P rows cd = true) (hnd : claimNodupB cd = true) : ClaimMeaningFinK cs Xz Xw := by
  cases cd with
  | single nm lab cs' => exact Or.inl (singleK_meaning hz hw hrows h)
  | core j fixed vars ez ew items =>
    simp only [claimK] at h
    have hnd' : ∀ it ∈ items, it.S.Nodup := by
      simp only [claimNodupB, List.all_eq_true] at hnd
      exact fun it hit => nodupB_spec (hnd it hit)
    cases hc : certs[j]? with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some g =>
      rw [hc] at h
      dsimp only at h
      obtain ⟨c, hcs, hm, h1, h2, h3⟩ := hcerts g (List.mem_of_getElem? hc)
      have h' : checkLinkK { P, ez, ew, vars } rows fixed items c = true := by
        rw [← h1, ← h2, ← h3] at h
        exact h
      obtain ⟨hm, hf6, hsz, hgen⟩ := linkK_meaningF (x := { P, ez, ew, vars }) hz hw hrows rfl hnd' h' hm
      refine Or.inr ⟨c, hcs, vars, hm, hf6, hsz, fun j hj => ?_⟩
      obtain ⟨it, hit, s, hs, heq⟩ := hgen j hj
      refine ⟨it, hit, s, hs, fun X Y P' E m hm1 => ?_⟩
      have := heq X Y P' E m hm1
      rw [← itemVal_congr hzW hzE hwW hwE]
      exact this

/-- The claims of all cells pass and have argmin sets without repetition: so does each cell's claim. -/
theorem checkCells_specF {certs : List CertKey} :
    ∀ {cells : List RCell} {ks : List ClaimK}, checkCells certs cells ks = true → ks.all claimNodupB = true →
      ∀ c ∈ cells, ∃ k, claimK certs ⟨c.tz, c.tw⟩ (Array.mk c.rows) k = true ∧ claimNodupB k = true
  | [], [], _, _ => fun c hc => absurd hc (by simp)
  | [], _ :: _, h, _ => absurd h (by simp [checkCells])
  | _ :: _, [], h, _ => absurd h (by simp [checkCells])
  | c :: cs, k :: ks, h, hn => by
    simp only [checkCells, Bool.and_eq_true] at h
    simp only [List.all_cons, Bool.and_eq_true] at hn
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact ⟨k, h.1, hn.1⟩
    · exact checkCells_specF h.2 hn.2 c' hc'

/-! ## Units -/

/-- **A unit, with the certificates from `cs`.** If the claims of the cells below the nodes of a unit pass and their
argmin sets have no repetition, and the certificate keys of the unit are those of certificates of `cs` with
`CertMeaning`, then for every node of the unit on the path of `(Xz, Xw)`, `ClaimMeaningFinK cs Xz Xw`. -/
theorem unit_coversF {cs : List Cert} {certs : List CertKey}
    (hcerts : ∀ g ∈ certs, ∃ c ∈ cs, CertMeaning c ∧ c.nvar = g.1 ∧ c.fixed = g.2.1 ∧ c.gens = g.2.2)
    {T : CTree} {D : L6.F2.Diag} {ord : List Nat} {t : Nat} {nodes : List (Nat × TS × TS)} {claims : List ClaimK}
    (hok : checkCells certs (nodes.flatMap (belowRL (keepR T) D ord t)) claims = true)
    (hnd : claims.all claimNodupB = true)
    {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {x : Nat × TS × TS} (hx : x ∈ nodes)
    (hn : NodeOK x.1 (ord.drop t)) (hp : OnPath Xz Xw x) : ClaimMeaningFinK cs Xz Xw := by
  obtain ⟨hS, hO, hnd', hrest, hfold⟩ := hn
  obtain ⟨htz, htzn, htw, htwn⟩ := hp
  obtain ⟨y, hy, -, hyz, hyzn, hyw, hywn⟩ := treeLevelL_complete (keepR_sound T) hX (ord.drop t) x.1 x.2.1 x.2.2
    hS hO hnd' hrest hfold htz htzn htw htwn
  obtain ⟨rows, hmem, hrows⟩ := cellsBelowRL_complete (keepR_sound T) hX ⟨y.2.1, y.2.2⟩ hyz hyzn hyw hywn
  have hcell : (⟨y.2.1, y.2.2, argminIdx D Xz Xw, rows⟩ : RCell) ∈ nodes.flatMap (belowRL (keepR T) D ord t) := by
    rw [List.mem_flatMap]
    refine ⟨x, hx, ?_⟩
    unfold belowRL
    rw [List.mem_flatMap]
    refine ⟨y, hy, ?_⟩
    unfold cellsOfRL
    exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  obtain ⟨k, hk, hkn⟩ := checkCells_specF hok hnd _ hcell
  have hall : all < 128 := by decide
  have hOall : mem L6.F2S.O all = true := by decide
  have lz := levelFacts hX.gz hX.root_z hall hOall (hyz.trans (restrict_all hX.gz).symm) hyzn
  have lw := levelFacts hX.gw hX.root_w hall hOall (hyw.trans (restrict_all hX.gw).symm) hywn
  exact claimK_meaningF (P := ⟨y.2.1, y.2.2⟩) hcerts lz lw (hX.gz.1.of_equiv hyz hyzn) hyz
    (hX.gw.1.of_equiv hyw hywn) hyw (fun r hr => hrows r (by simpa using hr)) hk hkn

end L6K.F34K
