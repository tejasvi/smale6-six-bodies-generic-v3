import L6Sound.F34S.Forms
import L6Sound.F34S.BelowR
import L6Sound.F34S.PolySem
import L6Sound.F34S.Congr
import L6Sound.Composed

/-!
# The meaning of the checks of F3, F4 on the cells of the specification search

* `single_meaning`: a passing single-term check gives, at every pair of complete trees with heights whose heights
  satisfy the rows of the cell strictly, an identity with a term of strictly least exponent (`IsArgminX … [i]`);
* `constant_meaning`: a certified argmin set is the argmin set of the identity there;
* `link_meaning`: a passing link gives the core part of `ClaimMeaning`;
* `chunkS_meaning`: for a passing chunk whose certificate texts pass `checkCert`, every cell of the chunk is one of
  the open cells, or `ClaimMeaning` holds at every pair `(Xz, Xw)` satisfying `Cond` whose key is that of the cell.
-/

namespace L6.F34S

open L6.F2S
open L6.F34 (Lab IdName Link prunedWith)

variable {Xz Xw : ExpTree} {P : Pair}

/-! ## Rows that fail -/

theorem pruned_fail {nv : Nat} {rows : Array Row} {r : Row} (h : prunedWith nv rows r = true) {hgt : ℕ → ℚ}
    (hrows : ∀ q ∈ rows, q.StrictHolds nv hgt) : ¬ r.StrictHolds nv hgt :=
  L6.push_no_solution h hgt hrows

theorem rowLe_fail {nv : Nat} {a b : Array Int} (ha : a.size = nv) (hb : b.size = nv) {h : ℕ → ℚ}
    (hn : ¬ (rowLe a b).StrictHolds nv h) : formVal nv b h < formVal nv a h := by
  unfold Row.StrictHolds rowLe at hn
  simp only [ite_true, reduceCtorEq, false_implies, implies_true, Option.some.injEq, forall_eq', true_and] at hn
  rw [lin_eq_formVal, RS.formVal_sub ha hb] at hn
  push_cast at hn
  linarith

theorem rowGeS_fail {nv : Nat} {a b : Array Int} (ha : a.size = nv) (hb : b.size = nv) {h : ℕ → ℚ}
    (hn : ¬ (rowGeS a b).StrictHolds nv h) : formVal nv a h ≤ formVal nv b h := by
  unfold Row.StrictHolds rowGeS at hn
  simp only [show (-2 : Int) ≠ 0 by decide, ite_false, show (-2 : Int) < 0 by decide, ite_true, Option.some.injEq,
    forall_eq', and_true] at hn
  rw [lin_eq_formVal, RS.formVal_sub ha hb] at hn
  push_cast at hn
  linarith

/-! ## Single terms and argmin sets -/

theorem getD_map_termForm (ts : List XTerm) (k : Nat) (hk : k < ts.length) :
    (ts.map (termForm P)).getD k none = termForm P ts[k]! := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk, getElem!_pos ts k hk]
  rfl

theorem getD_map_termForm_ge (ts : List XTerm) (k : Nat) (hk : ts.length ≤ k) :
    (ts.map (termForm P)).getD k none = none := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none hk]
  rfl

theorem good_get {I : XId} (hI : I.good = true) {k : Nat} (hk : k < I.terms.length) : (I.terms[k]!).good = true := by
  unfold XId.good at hI
  simp only [Bool.and_eq_true, List.all_eq_true] at hI
  exact hI.1.2 _ (by rw [getElem!_pos I.terms k hk]; exact List.getElem_mem hk)

/-- **F3 (Lemma 5.1).** A passing single-term check gives, wherever the rows of the cell hold strictly at the heights
read off the complete trees, a good identity with a term of strictly least exponent. -/
theorem single_meaning (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {nm : IdName} {lab : Lab}
    (h : checkSingleS P rows nm lab = true) :
    ∃ I : XId, I.good = true ∧ ∃ i, IsArgminX I.terms Xz Xw [i] := by
  unfold checkSingleS at h
  cases hI : XId.ofName nm with
  | none => rw [hI] at h; exact absurd h (by simp)
  | some I =>
    rw [hI] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hg, h⟩ := h
    refine ⟨I, hg, ?_⟩
    cases hi : findLabX I.terms lab with
    | none => rw [hi] at h; exact absurd h (by simp)
    | some i =>
      rw [hi] at h
      dsimp only at h
      unfold strictlyLeastS at h
      cases hfi : (I.terms.map (termForm P)).getD i none with
      | none => rw [hfi] at h; exact absurd h (by simp)
      | some fi =>
        rw [hfi] at h
        simp only [List.all_eq_true, List.mem_range, List.length_map, Bool.or_eq_true, beq_iff_eq] at h
        have hil : i < I.terms.length := by
          by_contra hc
          rw [getD_map_termForm_ge _ _ (by omega)] at hfi
          exact absurd hfi (by simp)
        rw [getD_map_termForm _ _ hil] at hfi
        rcases termForm_spec hz hw (good_get hg hil) with ⟨hn, _⟩ | ⟨f, hf, hsz, he⟩
        · rw [hn] at hfi; exact absurd hfi (by simp)
        · rw [hf] at hfi
          cases hfi
          refine ⟨i, by simp, fun j hj => by simp at hj; omega, formVal P.nv fi (heightVec Xz Xw P) / 2,
            fun j hj => by simp at hj; subst hj; exact he, fun k hk hki => ?_⟩
          have hki' : k ≠ i := by simpa using hki
          rcases h k hk with hk' | hk'
          · exact absurd hk' hki'
          · rw [getD_map_termForm _ _ hk] at hk'
            rcases termForm_spec hz hw (good_get hg hk) with ⟨hn, ht⟩ | ⟨f', hf', hsz', he'⟩
            · rw [ht]; exact WithTop.coe_lt_top _
            · rw [hf'] at hk'
              simp only at hk'
              have := rowLe_fail hsz' hsz (pruned_fail hk' hrows)
              rw [he', WithTop.coe_lt_coe]
              linarith

/-- **F4, argmin sets.** A certified argmin set is the argmin set of the identity, wherever the rows of the cell hold
strictly at the heights read off the complete trees. -/
theorem constant_meaning (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {I : XId} (hg : I.good = true) {S : List Nat}
    (h : constantArgminS P.nv rows (I.terms.map (termForm P)) S = true) :
    IsArgminX I.terms Xz Xw S := by
  unfold constantArgminS at h
  cases S with
  | nil => exact absurd h (by simp)
  | cons i0 rest =>
    simp only at h
    cases hf0 : (I.terms.map (termForm P)).getD i0 none with
    | none => rw [hf0] at h; exact absurd h (by simp)
    | some f0 =>
      rw [hf0] at h
      simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.length_map, Bool.or_eq_true,
        beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨hlt, hk⟩ := h
      have hi0 : i0 < I.terms.length := hlt i0 List.mem_cons_self
      rw [getD_map_termForm _ _ hi0] at hf0
      rcases termForm_spec hz hw (good_get hg hi0) with ⟨hn, _⟩ | ⟨f, hf, hsz, he⟩
      · rw [hn] at hf0; exact absurd hf0 (by simp)
      · rw [hf] at hf0
        cases hf0
        refine ⟨by simp, hlt, formVal P.nv f0 (heightVec Xz Xw P) / 2, fun j hj => ?_, fun k hkl hkS => ?_⟩
        · by_cases hji : j = i0
          · subst hji; exact he
          · have hjl := hlt j hj
            rcases hk j hjl with h1 | h1
            · exact absurd h1 hji
            · rw [getD_map_termForm _ _ hjl] at h1
              rcases termForm_spec hz hw (good_get hg hjl) with ⟨hn, _⟩ | ⟨f', hf', hsz', he'⟩
              · rw [hn] at h1
                simp only [List.contains_iff_mem, Bool.not_eq_true'] at h1
                simp at h1
                exact absurd hj (by simpa using h1)
              · rw [hf'] at h1
                simp only [List.contains_iff_mem, hj, ite_true, decide_true, Bool.and_eq_true] at h1
                obtain ⟨h2, h3⟩ := h1
                have a1 := rowGeS_fail hsz' hsz (pruned_fail h2 hrows)
                have a2 := rowGeS_fail hsz hsz' (pruned_fail h3 hrows)
                rw [he', WithTop.coe_eq_coe]
                linarith
        · have hki : k ≠ i0 := fun e => hkS (e ▸ List.mem_cons_self)
          rcases hk k hkl with h1 | h1
          · exact absurd h1 hki
          · rw [getD_map_termForm _ _ hkl] at h1
            rcases termForm_spec hz hw (good_get hg hkl) with ⟨hn, ht⟩ | ⟨f', hf', hsz', he'⟩
            · rw [ht]; exact WithTop.coe_lt_top _
            · rw [hf'] at h1
              have hkS' : (i0 :: rest).contains k = false := by simpa using hkS
              simp only [hkS', Bool.false_eq_true, ite_false] at h1
              have := rowLe_fail hsz' hsz (pruned_fail h1 hrows)
              rw [he', WithTop.coe_lt_coe]
              linarith

/-! ## Generators and links -/

theorem genItem_meaning (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {pt : Array Float}
    {fixed : Int} (hF6 : fixed < 6) {nm : IdName} {g : L6.Poly.Poly} (h : genItem x rows pt fixed nm = some g) :
    ∃ it : ItemX, it.Holds Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
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
        refine ⟨.init I (guessArgminS pt (I.terms.map (termForm x.P))), ⟨hg, constant_meaning hz hw hrows hg hc⟩, ?_⟩
        exact itemPoly_spec x I _ fixed hg hF6 h
      · rw [if_neg hc] at h
        exact absurd h (by simp)
    · rw [if_neg hg] at h
      exact absurd h (by simp)

theorem genForS_meaning (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {pt : Array Float}
    {fixed : Int} (hF6 : fixed < 6) {nmS : String} {g : L6.Poly.Poly} (h : genForS x rows pt fixed nmS = some g) :
    ∃ it : ItemX, it.Holds Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
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
  · exact genItem_meaning hz hw hrows hxP hF6 h

/-- **F4, a link.** A passing link with a certificate that has `CertMeaning` gives the core part of
`ClaimMeaning`, with the trees of the pair. -/
theorem link_meaning (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {pt : Array Float}
    {lk : Link} {cert : L6.Poly.Cert} (h : checkLinkS x rows pt lk cert = true) (hm : L6.Poly.CertMeaning cert)
    (hvars : x.vars.size = lk.vars.size) :
    L6.Poly.CertMeaning cert ∧ cert.fixed < 6 ∧ x.vars.size = cert.nvar ∧
      ∀ j < cert.gens.length, ∃ it : ItemX, it.Holds Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
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
  obtain ⟨it, hit, s, hs, heq⟩ := genForS_meaning hz hw hrows hxP hf6 (hgen j hj')
  refine ⟨it, hit, s, hs, fun X Y P' E m hm1 => ?_⟩
  have := heq X Y P' E m (fun h0 => by rw [← hfx]; exact hm1 (by rw [hfx]; exact h0))
  rw [L6.Poly.eval_normalize, hsz] at this
  exact this

/-! ## Claims -/

theorem certMeaning_of_prepare {cls : Nat} {D : L6.F2.Diag} {cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {cd : ChunkDataS}
    (hp : prepareS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs = some cd)
    (hcerts : ∀ p ∈ certs, L6.Poly.checkCert p.2 = true) :
    ∀ id c, cd.certs.lookup id = some c → L6.Poly.CertMeaning c := by
  intro id c hl
  unfold prepareS at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨parsed, hpa, ⟨single, links, pass⟩, _, hcd⟩ := hp
  simp only [Option.some.injEq] at hcd
  subst hcd
  obtain ⟨txt, hmem, hpc⟩ := L6.F34.parseAll_lookup hpa hl
  have hok : L6.Poly.checkParsed c = true := by
    have := hcerts _ hmem
    unfold L6.Poly.checkCert at this
    rw [hpc] at this
    exact this
  exact L6.Poly.checkParsed_meaning hok

theorem canon_pairOfKeys (Tz Tw : TS) : (pairOfKeys Tz.key Tw.key).tz = canon Tz ∧
    (pairOfKeys Tz.key Tw.key).tw = canon Tw := ⟨rfl, rfl⟩

/-- **The claim of a cell.** If the claim holds on a cell of the search whose rows hold strictly at the heights read
off `(Xz, Xw)` (with the pair of trees of the keys of `Xz`, `Xw`), then `ClaimMeaning Xz Xw`. -/
theorem claimHolds_meaning {cd : ChunkDataS} {idx : Nat} {ez ew : ETree} {rows : Array Row}
    (hP : P = pairOfKeys Xz.T.key Xw.T.key) (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all)
    (hzW : WF P.tz all) (hzE : P.tz.Equiv Xz.T) (hwW : WF P.tw all) (hwE : P.tw.Equiv Xw.T)
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P))
    (hcerts : ∀ id c, cd.certs.lookup id = some c → L6.Poly.CertMeaning c)
    (h : claimHolds cd idx P ez ew rows = true) : ClaimMeaning Xz Xw := by
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
          obtain ⟨hm, hf6, hsz, hgen⟩ := link_meaning (x := { P, ez, ew, vars := lk.vars.map (readVar ez ew) })
            hz hw hrows rfl h (hcerts _ _ hc) hvars
          refine Or.inr ⟨cert, lk.vars.map (readVar ez ew), hm, hf6, hsz, fun j hj => ?_⟩
          obtain ⟨it, hit, s, hs, heq⟩ := hgen j hj
          refine ⟨it, hit, s, hs, fun X Y P' E m hm1 => ?_⟩
          have := heq X Y P' E m hm1
          rw [← itemVal_congr hzW hzE hwW hwE]
          exact this

/-! ## The chunk -/

/-- The cache of `kindsRun` holds the cells of the search below its pair. -/
def CacheOK (cd : ChunkDataS)
    (cache : Option (((List Nat × Option Nat) × (List Nat × Option Nat)) × List (String × Array Row))) : Prop :=
  ∀ pk es, cache = some (pk, es) → es = cellsBelowR keepLP cd.D (pairOfKeys pk.1 pk.2)

/-- The kind of a cell, with the cells of the search below its pair. -/
def kindOf (cd : ChunkDataS) (idx : Nat) : Nat :=
  match pairKeyOf (cd.cells.getD idx "") with
  | none => 0
  | some pk => cellKindS cd idx (cellsBelowR keepLP cd.D (pairOfKeys pk.1 pk.2))

theorem kindsRun_eq (cd : ChunkDataS) :
    ∀ (idxs : List Nat) cache, CacheOK cd cache → kindsRun cd idxs cache = idxs.map (kindOf cd) := by
  intro idxs
  induction idxs with
  | nil => intro _ _; rfl
  | cons idx rest ih =>
    intro cache hc
    unfold kindsRun
    cases hpk : pairKeyOf (cd.cells.getD idx "") with
    | none =>
      dsimp only
      rw [ih cache hc, List.map_cons]
      congr 1
      unfold kindOf
      rw [hpk]
    | some pk =>
      have hnew : ∀ es, es = cellsBelowR keepLP cd.D (pairOfKeys pk.1 pk.2) → CacheOK cd (some (pk, es)) := by
        intro es hes pk' es' h'
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact hes
      cases cache with
      | none =>
        dsimp only
        rw [ih _ (hnew _ rfl), List.map_cons]
        congr 1
        unfold kindOf
        rw [hpk]
      | some pe =>
        obtain ⟨pk', es⟩ := pe
        dsimp only
        by_cases he : (pk' == pk) = true
        · have hes : es = cellsBelowR keepLP cd.D (pairOfKeys pk.1 pk.2) := by
            rw [beq_iff_eq] at he
            subst he
            exact hc pk' es rfl
          rw [if_pos he, ih _ (hnew es hes), List.map_cons, hes]
          congr 1
          unfold kindOf
          rw [hpk]
        · rw [if_neg he, ih _ (hnew _ rfl), List.map_cons]
          congr 1
          unfold kindOf
          rw [hpk]

theorem cellKindS_spec {cd : ChunkDataS} {idx : Nat} {entries : List (String × Array Row)}
    (h : cellKindS cd idx entries ≠ 0) :
    cd.opens.contains idx = true ∨
    ∃ kz kw am ez ew, keyOfLine (cd.cells.getD idx "") = some (kz, kw, am) ∧
      etreesOfLine (cd.cells.getD idx "") = some (ez, ew) ∧
      ∀ e ∈ entries, e.1 = am → claimHolds cd idx (pairOfKeys kz kw) ez ew e.2 = true := by
  unfold cellKindS at h
  by_cases h1 : (kindsOfS cd idx != 1) = true
  · rw [if_pos h1] at h; exact absurd rfl h
  · rw [if_neg h1] at h
    by_cases h2 : cd.opens.contains idx = true
    · exact Or.inl h2
    · rw [if_neg h2] at h
      right
      cases hk : keyOfLine (cd.cells.getD idx "") with
      | none => rw [hk] at h; exact absurd rfl h
      | some k =>
        obtain ⟨kz, kw, am⟩ := k
        cases he : etreesOfLine (cd.cells.getD idx "") with
        | none => rw [hk, he] at h; exact absurd rfl h
        | some ee =>
          obtain ⟨ez, ew⟩ := ee
          rw [hk, he] at h
          dsimp only at h
          refine ⟨kz, kw, am, ez, ew, rfl, rfl, fun e he' hea => ?_⟩
          by_cases hc : ((!(entries.filter (·.1 == am)).isEmpty) &&
              (entries.filter (·.1 == am)).all (fun e => claimHolds cd idx (pairOfKeys kz kw) ez ew e.2)) = true
          · simp only [Bool.and_eq_true, List.all_eq_true] at hc
            exact hc.2 e (List.mem_filter.mpr ⟨he', by simp [hea]⟩)
          · rw [if_neg hc] at h
            exact absurd rfl h

theorem prepareS_spec {cls : Nat} {D : L6.F2.Diag} {cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {cd : ChunkDataS}
    (h : prepareS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs = some cd) :
    cd.D = D ∧ cd.cells = (cellsTxt.splitOn "\n").toArray ∧ cd.opens = L6.F34.openCells cls openTxt := by
  unfold prepareS at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨parsed, _, ⟨single, links, pass⟩, _, hcd⟩ := h
  simp only [Option.some.injEq] at hcd
  subst hcd
  exact ⟨rfl, rfl, rfl⟩

theorem checkChunkS_spec {cls : Nat} {D : L6.F2.Diag} {cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {lo hi : Nat} {expected : L6.F34.Counts}
    (h : checkChunkS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs lo hi expected = true) :
    ∃ cd, prepareS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs = some cd ∧
      ∀ idx, lo ≤ idx → idx < hi → kindOf cd idx ≠ 0 := by
  unfold checkChunkS at h
  cases hp : prepareS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some cd =>
    rw [hp] at h
    dsimp only at h
    rw [kindsRun_eq cd _ none (fun _ _ h => by simp at h)] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨_, _⟩, hall⟩, _⟩ := h
    refine ⟨cd, rfl, fun idx h1 h2 => hall _ ⟨idx, List.mem_range'_1.mpr ⟨h1, by omega⟩, rfl⟩⟩

/-- **F3/F4 on a chunk.** If the check of a chunk passes and its certificate texts pass `checkCert`, every cell
`lo ≤ idx < hi` is listed as open, or `ClaimMeaning` holds at every pair of complete trees with heights satisfying
`Cond D` whose key is that of the stored line `idx`. -/
theorem chunkS_meaning {cls : Nat} {D : L6.F2.Diag} {cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {lo hi : Nat} {expected : L6.F34.Counts}
    (h : checkChunkS cls D cellsTxt singleTxt linksTxt passTxt openTxt certs lo hi expected = true)
    (hcerts : ∀ p ∈ certs, L6.Poly.checkCert p.2 = true) :
    ∀ idx, lo ≤ idx → idx < hi →
      (L6.F34.openCells cls openTxt).contains idx = true ∨
      ∀ Xz Xw : ExpTree, Cond D Xz Xw →
        keyOfLine ((cellsTxt.splitOn "\n").toArray.getD idx "") = some (Xz.T.key, Xw.T.key, argminString D Xz Xw) →
        ClaimMeaning Xz Xw := by
  obtain ⟨cd, hp, hk⟩ := checkChunkS_spec h
  obtain ⟨hD, hcells, hopens⟩ := prepareS_spec hp
  have hcm := certMeaning_of_prepare hp hcerts
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
