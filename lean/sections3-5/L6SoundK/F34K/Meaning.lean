import L6K.F34K.Check
import L6SoundK.F2S.KeepR
import L6Sound.F34S.Meaning
import Mathlib.Data.List.Perm.Basic

/-!
# The meaning of the claims checked by the kernel

The proofs of `L6Sound.F34S.Meaning` (lean6), for the checks of `L6K.F34K.Check`: a linear program decided by a given
certificate fails as one decided by `prunedWith` does (`prunedK_fail`, through `checkR_imp` and `push_no_solution`), and
`normalizeK` has the value of its input as `L6.Poly.normalize` has (`eval_normalizeK`).

* `singleK_meaning`, `constantK_meaning`, `genItemK_meaning`, `genForSK_meaning`, `linkK_meaning`: as `single_meaning`,
  `constant_meaning`, `genItem_meaning`, `genForS_meaning`, `link_meaning`;
* **`claimK_meaning`**: a passing claim at a cell whose rows hold strictly at the heights read off `(Xz, Xw)`, on a pair
  of trees with the nodes of `Xz.T`, `Xw.T`, gives `ClaimMeaning Xz Xw`.
-/

namespace L6K.F34K

open L6 L6.F2S L6.F34S L6.Poly
open L6.F34 (Lab IdName)
open L6K.F2S (checkR checkR_imp)

variable {Xz Xw : ExpTree} {P : Pair}

/-! ## The sort and the normal form -/

theorem mergeP_perm : ∀ (f : ℕ) (a b : Poly), (mergeP f a b).Perm (a ++ b)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, x :: a, [] => by
    show (x :: a).Perm ((x :: a) ++ [])
    rw [List.append_nil]
  | f + 1, x :: a, y :: b => by
    show (Bool.rec (motive := fun _ => Poly) (y :: mergeP f (x :: a) b) (x :: mergeP f a (y :: b))
      (Nat.ble x.1 y.1)).Perm _
    cases Nat.ble x.1 y.1
    · exact ((mergeP_perm f (x :: a) b).cons y).trans List.perm_middle.symm
    · exact (mergeP_perm f a (y :: b)).cons x

theorem msortP_perm : ∀ (d : ℕ) (l : Poly), (msortP d l).Perm l
  | 0, _ => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [_] => List.Perm.refl _
  | d + 1, x :: y :: l => by
    show (mergeP (x :: y :: l).length (msortP d ((x :: y :: l).take ((x :: y :: l).length / 2)))
      (msortP d ((x :: y :: l).drop ((x :: y :: l).length / 2)))).Perm _
    refine (mergeP_perm _ _ _).trans (((msortP_perm d _).append (msortP_perm d _)).trans ?_)
    rw [List.take_append_drop]

section Eval

variable {R : Type*} [CommRing R]

theorem eval_normalizeK (nv : ℕ) (φ : ℕ → R) (p : Poly) : eval nv φ (normalizeK p) = eval nv φ p := by
  unfold normalizeK
  rw [eval_combineSorted]
  exact eval_perm nv φ (msortP_perm 40 p)

theorem eval_packK (nv : Nat) (φ : ℕ → R) (p : UPoly) (hs : p.small nv = true) :
    eval nv φ (packK p) = UPoly.eval φ p := by
  have h := eval_pack nv φ p hs
  unfold UPoly.pack at h
  rw [eval_normalize] at h
  unfold packK
  rw [eval_normalizeK]
  exact h

end Eval

/-! ## The generators -/

/-- `itemPoly_spec` for `itemPolyK`. -/
theorem itemPolyK_spec (x : PCtx) (I : XId) (S : List Nat) (fixed : Int) (hI : I.good = true) (hF6 : fixed < 6)
    {g : Poly} (h : itemPolyK x I S fixed = some g) :
    ∃ s : ℕ, (s = 1 ∨ s = 2) ∧ ∀ {R : Type} [CommRing R] (X Y P : Nat → Nat → R) (E : R) (m : Nat → R),
      (0 ≤ fixed → m fixed.toNat = 1) →
      (s : R) * eval (6 + x.vars.size) (phiOf x.vars X Y P E m) g =
        itemVal x.P.tz x.P.tw X Y P E m (.init I S) := by
  unfold XId.good at hI
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hI
  obtain ⟨⟨-, hterms⟩, hscale⟩ := hI
  cases hts : S.mapM (fun i => (I.terms[i]?).bind (termU2 x)) with
  | none => simp [itemPolyK, itemU, hts] at h
  | some ts =>
    set u := ((UPoly.prod (I.scale.map UPoly.var)).mul ts.flatten).substOne fixed with hu
    have hiu : itemU x I S fixed = some u := by simp only [itemU, hts, hu]
    by_cases hsm : u.small (6 + x.vars.size) = true
    · simp only [itemPolyK, hiu, hsm, ite_true, Option.some.injEq] at h
      subst h
      refine ⟨if (halve (packK u)).2 then 2 else 1, by split_ifs <;> simp, ?_⟩
      intro R _ X Y P E m hm
      have hφF : 0 ≤ fixed → phiOf x.vars X Y P E m fixed.toNat = 1 := fun h0 =>
        (phiOf_lt _ _ _ _ _ _ (by omega)).trans (hm h0)
      have hcast : (((if (halve (packK u)).2 then 2 else 1 : ℕ)) : R) =
          (if (halve (packK u)).2 then 2 else 1 : R) := by
        split_ifs <;> simp
      rw [hcast, eval_normalizeK, eval_halve, eval_packK _ _ _ hsm, hu, UPoly.eval_substOne _ _ hφF, UPoly.eval_mul,
        UPoly.eval_prod, UPoly.eval_flatten]
      unfold itemVal
      congr 1
      · rw [List.map_map]
        congr 1
        refine List.map_congr_left fun k hk => ?_
        simp only [Function.comp, UPoly.eval_var]
        exact phiOf_lt _ _ _ _ _ _ (hscale k hk)
      · have hF2 := mapM_spec (fun i => (I.terms[i]?).bind (termU2 x))
          (fun i v => UPoly.eval (phiOf x.vars X Y P E m) v = termVal2 x.P.tz x.P.tw X Y P E m I.terms[i]!)
          (fun i v hv => by
            cases hti : I.terms[i]? with
            | none => simp [hti] at hv
            | some t =>
              simp only [hti, Option.bind_some] at hv
              have hlt : i < I.terms.length := by
                rcases Nat.lt_or_ge i I.terms.length with hl | hl
                · exact hl
                · rw [List.getElem?_eq_none hl] at hti; exact absurd hti (by simp)
              have ht : I.terms[i]! = t := by
                rw [getElem!_pos I.terms i hlt]
                rw [List.getElem?_eq_getElem hlt] at hti
                exact Option.some.inj hti
              rw [ht]
              exact termU2_spec x t (hterms t (List.mem_of_getElem? hti)) hv X Y P E m)
          S ts hts
        exact sum_forall₂ _ _ S ts hF2
    · simp [itemPolyK, hiu, hsm] at h

/-- `distPoly_spec` for `distPolyK`. -/
theorem distPolyK_spec (x : PCtx) (k l : Nat) (hkl : k ≤ l) {g : Poly} (h : distPolyK x k l = some g) :
    ∀ {R : Type} [CommRing R] (X Y P : Nat → Nat → R) (E : R) (m : Nat → R),
      eval (6 + x.vars.size) (phiOf x.vars X Y P E m) g = itemVal x.P.tz x.P.tw X Y P E m (.dist k l) := by
  intro R _ X Y P E m
  cases hd : dU x (k, l) with
  | none => simp [distPolyK, hd] at h
  | some d =>
    cases ha : lcU x true (k, l) with
    | none => simp [distPolyK, hd, ha] at h
    | some a =>
      cases hb : lcU x false (k, l) with
      | none => simp [distPolyK, hd, ha, hb] at h
      | some b =>
        by_cases hsm : (distU d a b).small (6 + x.vars.size) = true
        · simp only [distPolyK, hd, ha, hb, hsm, ite_true, Option.some.injEq] at h
          subst h
          rw [eval_packK _ _ _ hsm]
          unfold distU
          rw [UPoly.eval_append, UPoly.eval_prod]
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rw [dU_spec x (k, l) hd X Y P E m, lcU_spec x true (k, l) ha X Y P E m,
            lcU_spec x false (k, l) hb X Y P E m]
          simp only [min_eq_left hkl, max_eq_right hkl, ite_true, Bool.false_eq_true, ite_false]
          unfold itemVal
          simp only [UPoly.eval, List.map_cons, List.map_nil, List.prod_nil, List.sum_cons, List.sum_nil]
          push_cast
          ring
        · simp [distPolyK, hd, ha, hb, hsm] at h

/-! ## Certified decisions -/

theorem prunedK_fail {nv : Nat} {rows : Array Row} {r : Row} {cert : List (Nat × Int)}
    (h : prunedK nv rows r cert = true) {hgt : ℕ → ℚ} (hrows : ∀ q ∈ rows, q.StrictHolds nv hgt) :
    ¬ r.StrictHolds nv hgt := by
  have hc := checkR_imp h
  have e : (Array.mk (rows.toList ++ [r]) : Array Row) = rows.push r := by
    apply Array.ext'
    simp
  rw [e] at hc
  exact L6.push_no_solution hc hgt hrows

/-- `single_meaning` for `checkSingleK`. -/
theorem singleK_meaning (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {nm : IdName} {lab : Lab}
    {certs : List (List (Nat × Int))} (h : checkSingleK P rows nm lab certs = true) :
    ∃ I : XId, I.good = true ∧ ∃ i, IsArgminX I.terms Xz Xw [i] := by
  unfold checkSingleK at h
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
      unfold strictlyLeastK at h
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
              have := rowLe_fail hsz' hsz (prunedK_fail hk' hrows)
              rw [he', WithTop.coe_lt_coe]
              linarith

/-- `constant_meaning` for `constantArgminK`. -/
theorem constantK_meaning (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {I : XId} (hg : I.good = true) {S : List Nat}
    {cA cB : List (List (Nat × Int))} (h : constantArgminK P.nv rows (I.terms.map (termForm P)) S cA cB = true) :
    IsArgminX I.terms Xz Xw S := by
  unfold constantArgminK at h
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
                have a1 := rowGeS_fail hsz' hsz (prunedK_fail h2 hrows)
                have a2 := rowGeS_fail hsz hsz' (prunedK_fail h3 hrows)
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
              have := rowLe_fail hsz' hsz (prunedK_fail h1 hrows)
              rw [he', WithTop.coe_lt_coe]
              linarith

/-! ## Generators and links -/

theorem genItemK_meaning (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P)
    {fixed : Int} (hF6 : fixed < 6) {it : ItemK} {g : Poly} (h : genItemK x rows fixed it = some g) :
    ∃ it' : ItemX, it'.Holds Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
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
        refine ⟨.init I it.S, ⟨hg, constantK_meaning hz hw hrows hg hc⟩, ?_⟩
        exact itemPolyK_spec x I _ fixed hg hF6 h
      · rw [if_neg hc] at h
        exact absurd h (by simp)
    · rw [if_neg hg] at h
      exact absurd h (by simp)

theorem genForSK_meaning (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P)
    {fixed : Int} (hF6 : fixed < 6) {it : ItemK} {g : Poly} (h : genForSK x rows fixed it = some g) :
    ∃ it' : ItemX, it'.Holds Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
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
  · exact genItemK_meaning hz hw hrows hxP hF6 h

/-- `link_meaning` for `checkLinkK`. -/
theorem linkK_meaning (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {rows : Array Row}
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P)) {x : PCtx} (hxP : x.P = P) {fixed : Int}
    {items : List ItemK} {cert : Cert} (h : checkLinkK x rows fixed items cert = true) (hm : CertMeaning cert) :
    CertMeaning cert ∧ cert.fixed < 6 ∧ x.vars.size = cert.nvar ∧
      ∀ j < cert.gens.length, ∃ it : ItemX, it.Holds Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
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
  obtain ⟨it, hit, s, hs, heq⟩ := genForSK_meaning hz hw hrows hxP hf6 (hgen j hj')
  refine ⟨it, hit, s, hs, fun X Y P' E m hm1 => ?_⟩
  have := heq X Y P' E m (fun h0 => by rw [← hfx]; exact hm1 (by rw [hfx]; exact h0))
  rw [eval_normalizeK, hsz] at this
  exact this

/-! ## The claim -/

/-- **The claim of a cell checked by the kernel.** If the claim passes at a cell of the search whose rows hold
strictly at the heights read off `(Xz, Xw)`, for a pair of trees with the nodes of `Xz.T` and `Xw.T`, and the keys of
the certificates of the cores are those of certificates with `CertMeaning`, then `ClaimMeaning Xz Xw`. -/
theorem claimK_meaning {certs : List CertKey}
    (hcerts : ∀ g ∈ certs, ∃ c : Cert, CertMeaning c ∧ c.nvar = g.1 ∧ c.fixed = g.2.1 ∧ c.gens = g.2.2)
    {rows : Array Row} {cd : ClaimK}
    (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all)
    (hzW : WF P.tz all) (hzE : P.tz.Equiv Xz.T) (hwW : WF P.tw all) (hwE : P.tw.Equiv Xw.T)
    (hrows : ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P))
    (h : claimK certs P rows cd = true) : ClaimMeaning Xz Xw := by
  cases cd with
  | single nm lab cs => exact Or.inl (singleK_meaning hz hw hrows h)
  | core j fixed vars ez ew items =>
    simp only [claimK] at h
    cases hc : certs[j]? with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some g =>
      rw [hc] at h
      dsimp only at h
      obtain ⟨c, hm, h1, h2, h3⟩ := hcerts g (List.mem_of_getElem? hc)
      have h' : checkLinkK { P, ez, ew, vars } rows fixed items c = true := by
        rw [← h1, ← h2, ← h3] at h
        exact h
      obtain ⟨hm, hf6, hsz, hgen⟩ := linkK_meaning (x := { P, ez, ew, vars }) hz hw hrows rfl h' hm
      refine Or.inr ⟨c, vars, hm, hf6, hsz, fun j hj => ?_⟩
      obtain ⟨it, hit, s, hs, heq⟩ := hgen j hj
      refine ⟨it, hit, s, hs, fun X Y P' E m hm1 => ?_⟩
      have := heq X Y P' E m hm1
      rw [← itemVal_congr hzW hzE hwW hwE]
      exact this

/-- The claims of all cells pass: each cell's claim passes. -/
theorem checkCells_spec {certs : List CertKey} :
    ∀ {cells : List L6K.F2S.RCell} {ks : List ClaimK}, checkCells certs cells ks = true →
      ∀ c ∈ cells, ∃ k, claimK certs ⟨c.tz, c.tw⟩ (Array.mk c.rows) k = true
  | [], [], _ => fun c hc => absurd hc (by simp)
  | [], _ :: _, h => absurd h (by simp [checkCells])
  | _ :: _, [], h => absurd h (by simp [checkCells])
  | c :: cs, k :: ks, h => by
    simp only [checkCells, Bool.and_eq_true] at h
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact ⟨k, h.1⟩
    · exact checkCells_spec h.2 c' hc'

end L6K.F34K
