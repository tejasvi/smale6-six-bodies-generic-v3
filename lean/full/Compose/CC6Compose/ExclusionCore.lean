import CC6Compose.ExclusionTerms

/-!
# Bridge: the cores of the checks of Proposition 5.3 at a germ (Lemma 5.2)

The checks give, for a core cell, a certificate whose generators are, at the point `phiOf vars X Y P E m` of the
values `X`, `Y` of the node coordinates (indexed by the masks of a node and of its child, the coordinate of the base
child subtracted), `P` of the leading coefficients of the `p_kl`, `E` and the masses (with `m_F = 1` when a mass is
fixed), multiples of the values `L6.F34S.itemVal` of members of the initial system holding at the trees with heights
(`ClaimIn`). This file evaluates the items at the leading coefficients of a germ realizing the trees, and concludes
that `h` vanishes at the masses (Lemma 5.2 (a)), or at the masses divided by `m_F` (Lemma 5.2 (b), through the germ
`Germ.scale` for the masses `m / m_F`).

* `ptX G htz`, `ptY G htw`, `ptP G`, `ptM m`: the leading coefficients of the germ `G` as the values of the checks:
  `X v c = G.xcoord htz (setOfMask v) (setOfMask c)` (Lemma 4.2), `P k l = lc(p_kl)`, the masses.
* `leafClass_toTS`, `childOf_toTS`: the child of a node containing a point, in the converted tree, is the mask of
  `TreeShape.child`; `lcVal_eq`: `lcVal` at the node coordinates of a realizing tree is `lc(pos_p − pos_q)`
  (Lemma 4.2, `TreeShape.Realizes.lc_eq`; the coordinate of the first child is not used, only differences).
* `termVal2_eq`: `termVal2` of a good term is twice `c_i lc(g_i)` of the converted term at the germ.
* `itemVal_eq_zero`: the value of an item `ItemOK` vanishes: for an initial form, by Lemma 2.10 at the germ
  (`Germ.eval_initForm`, with the argmin set of `isArgmin_of_isArgminX`); for a row, by `p_kl² z_kl w_kl = 1`.
* `eval_h_eq_zero`: with a certificate having `CertMeaning` whose generators are such multiples, `h` vanishes at the
  masses of the germ (`L6.Poly.eval 6 (ptM m) c.h = 0`) if the fixed mass is `1`.
* `core_vanish`: for a germ with positive masses, `h` vanishes at `m` (no fixed mass) or at `m / m_F`.
-/

namespace CC6Compose

open CC6Full Finset

/-! ## The leaf class and the child of a point in a converted tree -/

theorem leafClass_lrep (T : L6.F2S.TS) (x : ℕ) : T.leafClass x = T.leafClass (T.lrep x) := by
  unfold L6.F2S.TS.leafClass L6.F2S.TS.lrep
  rcases h : T.leafO with _ | k
  · rfl
  · dsimp only
    by_cases hx : x = k
    · subst hx
      simp
    · simp [hx]

theorem leafClass_toTS (T : TreeShape 6) (p : Pt 6) :
    (toTS T).leafClass (ptN p) = maskOf (univ.filter (T.SameLeaf p ·)) := by
  set x := ptN (T.lrep p) with hx
  have hxx : (toTS T).lrep x = x := by rw [hx, toTS_lrep, lrep_lrep]
  have hlo : ∀ k, (toTS T).leafO = some k → k ≠ L6.F2S.O := by
    intro k hk
    rw [toTS_leafO, Option.map_eq_some_iff] at hk
    obtain ⟨j, -, rfl⟩ := hk
    have := j.isLt
    unfold L6.F2S.O
    omega
  have h1 : (toTS T).leafClass (ptN p) = (toTS T).leafClass x := by
    rw [hx, ← toTS_lrep]
    exact leafClass_lrep _ _
  rw [h1]
  apply L6.F2S.mask_ext
  intro y
  apply Bool.eq_iff_iff.mpr
  rw [L6.F2S.TreeAux.mem_leafClass hlo hxx, mem_maskOf]
  constructor
  · intro hy
    have hy7 : y < 7 := by
      by_contra hy7
      rw [L6.F2S.TreeAux.lrep_eq] at hy
      split_ifs at hy with hyl
      · rw [toTS_leafO, Option.map_eq_some_iff] at hyl
        obtain ⟨j, -, hj⟩ := hyl
        have := j.isLt
        omega
      · have := ptN_lt (T.lrep p)
        omega
    refine ⟨hy7, Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    rw [← ptN_ptOfN hy7, toTS_lrep, hx, ptN_eq_iff] at hy
    exact hy.symm
  · rintro ⟨hy7, hy⟩
    rw [Finset.mem_filter] at hy
    rw [← ptN_ptOfN hy7, toTS_lrep, hx, ptN_eq_iff]
    exact hy.2.symm

/-- The child of a node containing a point, in the converted tree, is the mask of the child of `T`. -/
theorem childOf_toTS {T : TreeShape 6} (hT : T.WF) {v : Finset (Pt 6)} (hv : v ∈ T.nodes) {p : Pt 6} (hp : p ∈ v) :
    L6.F34S.childOf (toTS T) (maskOf v) (ptN p) = maskOf (T.child v p) := by
  unfold L6.F34S.childOf
  have chain : ∀ C ∈ (toTS T).nodes, ∀ D ∈ (toTS T).nodes,
      (L6.F2S.ssubset C (maskOf v) && L6.F2S.mem (ptN p) C) = true →
      (L6.F2S.ssubset D (maskOf v) && L6.F2S.mem (ptN p) D) = true →
      L6.F2S.subset C D = true ∨ L6.F2S.subset D C = true := by
    intro C hC D hD h1 h2
    obtain ⟨A, hA, rfl⟩ := mem_toTS_nodes.mp hC
    obtain ⟨B, hB, rfl⟩ := mem_toTS_nodes.mp hD
    simp only [Bool.and_eq_true, mem_maskOf_ptN] at h1 h2
    rcases hT.laminar A hA B hB with h | h | h
    · exact Or.inl (subset_maskOf.mpr h)
    · exact Or.inr (subset_maskOf.mpr h)
    · exact absurd h2.2 (Finset.disjoint_left.mp h h1.2)
  rcases L6.F34S.pickMax_spec _ _ chain with ⟨hnone, hall⟩ | ⟨M, hM, hML, hPM, hmax⟩
  · rw [hnone]
    dsimp only
    rw [leafClass_toTS]
    congr 1
    ext r
    rw [Finset.mem_filter, T.mem_child]
    constructor
    · rintro ⟨-, hs⟩
      exact ⟨hT.closed v hv p r hs hp, Or.inl hs⟩
    · rintro ⟨-, hs | hl⟩
      · exact ⟨mem_univ _, hs⟩
      · exfalso
        have h0 := hall _ (maskOf_mem_toTS.mpr (T.lca_mem hT p r))
        have h1 : (L6.F2S.ssubset (maskOf (T.lca p r)) (maskOf v) &&
            L6.F2S.mem (ptN p) (maskOf (T.lca p r))) = true := by
          simp only [Bool.and_eq_true, ssubset_maskOf, mem_maskOf_ptN]
          exact ⟨hl, T.mem_lca_left p r⟩
        rw [h0] at h1
        exact Bool.false_ne_true h1
  · rw [hM]
    dsimp only
    obtain ⟨A, hA, rfl⟩ := mem_toTS_nodes.mp hML
    simp only [Bool.and_eq_true, ssubset_maskOf, mem_maskOf_ptN] at hPM
    obtain ⟨hAv, hpA⟩ := hPM
    congr 1
    ext r
    rw [T.mem_child]
    constructor
    · intro hr
      exact ⟨hAv.subset hr, Or.inr (Finset.ssubset_of_subset_of_ssubset (T.lca_subset hA hpA hr) hAv)⟩
    · rintro ⟨-, hs | hl⟩
      · exact hT.closed A hA p r hs hpA
      · have hsub := hmax _ (maskOf_mem_toTS.mpr (T.lca_mem hT p r))
          (by simp only [Bool.and_eq_true, ssubset_maskOf, mem_maskOf_ptN]; exact ⟨hl, T.mem_lca_left p r⟩)
        rw [subset_maskOf] at hsub
        exact hsub (T.mem_lca_right p r)

/-- **Lemma 4.2 for the values of the checks**: at the node coordinates of a tree realizing `hOf pos`, the value
`lcVal` of the factor `pos_p − pos_q` is its leading coefficient. -/
theorem lcVal_eq {T : TreeShape 6} {pos : Pt 6 → Ser} {hts : Finset (Pt 6) → ℚ} (hR : T.Realizes (hOf pos) hts)
    (p q : Pt 6) :
    L6.F34S.lcVal (toTS T) (fun v c => coordOf pos hts (setOfMask v) (setOfMask c)) (ptN p, ptN q) =
      (pos p - pos q).leadingCoeff := by
  have hT := hR.wf
  unfold L6.F34S.lcVal
  dsimp only
  rw [toTS_lca hT]
  dsimp only
  have hv := T.lca_mem hT p q
  rw [childOf_toTS hT hv (T.mem_lca_left p q), childOf_toTS hT hv (T.mem_lca_right p q), setOfMask_maskOf,
    setOfMask_maskOf, setOfMask_maskOf]
  by_cases hs : T.SameLeaf p q
  · have h0 := hR.same p q hs
    rw [hOf, HahnSeries.orderTop_eq_top] at h0
    rw [h0, HahnSeries.leadingCoeff_zero]
    have hq : q ∈ T.child (T.lca p q) p := T.mem_child.mpr ⟨T.mem_lca_right p q, Or.inl hs⟩
    rw [T.child_eq_of_mem hT hq, sub_self]
  · exact (hR.lc_eq hs).symm

/-! ## The point of the leading coefficients of a germ -/

section point

variable {m : Fin 6 → ℝ}

/-- The node coordinates of the tree of `z` as values of the checks (nodes and children given by masks). -/
noncomputable def ptX (G : Germ 6 m) (htz : Finset (Pt 6) → ℚ) : ℕ → ℕ → ℂ :=
  fun v c => G.xcoord htz (setOfMask v) (setOfMask c)

/-- The node coordinates of the tree of `w` as values of the checks. -/
noncomputable def ptY (G : Germ 6 m) (htw : Finset (Pt 6) → ℚ) : ℕ → ℕ → ℂ :=
  fun v c => G.ycoord htw (setOfMask v) (setOfMask c)

/-- The leading coefficients of the `p_kl`. -/
noncomputable def ptP (G : Germ 6 m) : ℕ → ℕ → ℂ := fun k l => (G.p (fin6 k) (fin6 l)).leadingCoeff

/-- The masses. -/
noncomputable def ptM (m : Fin 6 → ℝ) : ℕ → ℂ := fun i => (m (fin6 i) : ℂ)

variable {G : Germ 6 m} {Tz Tw : TreeShape 6} {htz htw : Finset (Pt 6) → ℚ}

theorem lcVal_z (hRz : Tz.Realizes G.hz htz) {pq : ℕ × ℕ} (h1 : pq.1 < 7) (h2 : pq.2 < 7) :
    L6.F34S.lcVal (toTS Tz) (ptX G htz) pq = (G.zpos (ptOfN pq.1) - G.zpos (ptOfN pq.2)).leadingCoeff := by
  obtain ⟨p, q⟩ := pq
  have h := lcVal_eq (pos := G.zpos) hRz (ptOfN p) (ptOfN q)
  rw [ptN_ptOfN h1, ptN_ptOfN h2] at h
  exact h

theorem lcVal_w (hRw : Tw.Realizes G.hw htw) {pq : ℕ × ℕ} (h1 : pq.1 < 7) (h2 : pq.2 < 7) :
    L6.F34S.lcVal (toTS Tw) (ptY G htw) pq = (G.wpos (ptOfN pq.1) - G.wpos (ptOfN pq.2)).leadingCoeff := by
  obtain ⟨p, q⟩ := pq
  have h := lcVal_eq (pos := G.wpos) hRw (ptOfN p) (ptOfN q)
  rw [ptN_ptOfN h1, ptN_ptOfN h2] at h
  exact h

theorem ptP_minmax (G : Germ 6 m) (a b : ℕ) :
    ptP G (min a b) (max a b) = (G.p (fin6 a) (fin6 b)).leadingCoeff := by
  unfold ptP
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, G.p_symm]

theorem sum_range_ptM (m : Fin 6 → ℝ) : ((List.range 6).map (ptM m)).sum = ∑ k, (m k : ℂ) := by
  rw [range6_eq, List.map_map, Fin.sum_univ_def]
  congr 1

/-- `2 · num / den` in the integers is twice `num / den` when `den ∈ {1, 2}` divides `2 · num`. -/
theorem two_mul_div_cast {num : ℤ} {den : ℕ} (hd : den = 1 ∨ den = 2) (hdiv : (2 * num) % (den : ℤ) = 0) :
    (((2 * num / (den : ℤ) : ℤ)) : ℂ) = 2 * (((num : ℚ) / den : ℚ) : ℂ) := by
  rcases hd with rfl | rfl
  · simp
  · have h2 : (2 * num / ((2 : ℕ) : ℤ) : ℤ) = num := by
      rw [Nat.cast_ofNat, Int.mul_ediv_cancel_left _ (by norm_num)]
    rw [h2]
    push_cast
    ring

/-- **The value of a term at the leading coefficients**: `termVal2` of a good term is twice `c_i lc(g_i)` of the
converted term at the germ. -/
theorem termVal2_eq (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {t : L6.F34S.XTerm}
    (ht : t.good = true) :
    L6.F34S.termVal2 (toTS Tz) (toTS Tw) (ptX G htz) (ptY G htw) (ptP G) G.E (ptM m) t =
      2 * (G.cval (toTerm t).coeff * (toTerm t).lead G) := by
  have ht' := ht
  unfold L6.F34S.XTerm.good at ht'
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at ht'
  obtain ⟨⟨⟨⟨⟨hzs, hws⟩, -⟩, hden⟩, hdiv⟩, -⟩ := ht'
  have hzv : (t.zs.map (L6.F34S.lcVal (toTS Tz) (ptX G htz))).prod =
      ((t.zs.map toPtPair).map fun pq => (G.zpos pq.1 - G.zpos pq.2).leadingCoeff).prod := by
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun pq hpq => ?_
    have hlt := goodSep_lt (hzs pq hpq)
    exact lcVal_z hRz hlt.1 hlt.2
  have hwv : (t.ws.map (L6.F34S.lcVal (toTS Tw) (ptY G htw))).prod =
      ((t.ws.map toPtPair).map fun pq => (G.wpos pq.1 - G.wpos pq.2).leadingCoeff).prod := by
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun pq hpq => ?_
    have hlt := goodSep_lt (hws pq hpq)
    exact lcVal_w hRw hlt.1 hlt.2
  have hpv : (t.ps.map fun kl => ptP G (min kl.1 kl.2) (max kl.1 kl.2)).prod =
      ((t.ps.map toFinPair).map fun kl => (G.p kl.1 kl.2).leadingCoeff).prod := by
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun kl _ => ?_
    exact ptP_minmax G kl.1 kl.2
  unfold L6.F34S.termVal2 L6.F34S.coefVal2 Term.lead
  rw [hzv, hwv, hpv, sum_range_ptM, two_mul_div_cast hden hdiv]
  simp only [toTerm]
  rw [cval_toCoef, show ptM m = fun i => (m (fin6 i) : ℂ) from rfl]
  ring

end point

/-! ## The items at the leading coefficients -/

/-- A sum over the positions `i < n` of a list in a finite set `T` of positions below `n`. -/
theorem sum_fin_filter {M : Type*} [AddCommMonoid M] (n : ℕ) (T : Finset ℕ) (hT : ∀ i ∈ T, i < n) (f : ℕ → M) :
    ∑ i ∈ (univ : Finset (Fin n)).filter (fun i => i.1 ∈ T), f i.1 = ∑ i ∈ T, f i := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i ∈ T then f i else 0) n, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hT i h, h⟩⟩

section items

variable {m : Fin 6 → ℝ} {G : Germ 6 m} {Tz Tw : TreeShape 6} {htz htw : Finset (Pt 6) → ℚ}

/-- **The items of the initial system vanish at the leading coefficients** of a germ realizing the trees: the
initial form of a good identity on its argmin set (Lemma 2.10), and the row `P_kl² lc(z_kl) lc(w_kl) − 1`. -/
theorem itemVal_eq_zero (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {it : L6.F34S.ItemX}
    (hit : ItemOK (toExp Tz htz) (toExp Tw htw) it) :
    L6.F34S.itemVal (toTS Tz) (toTS Tw) (ptX G htz) (ptY G htw) (ptP G) G.E (ptM m) it = 0 := by
  cases it with
  | dist k l =>
    obtain ⟨hkl, hl⟩ : k < l ∧ l < 6 := hit
    have hk : k < 6 := by omega
    have hne : fin6 k ≠ fin6 l := by
      rw [fin6_eq_mk hk, fin6_eq_mk hl]
      exact fun e => hkl.ne (congrArg Fin.val e)
    simp only [L6.F34S.itemVal]
    rw [lcVal_z hRz (pq := (k, l)) (by omega) (by omega), lcVal_w hRw (pq := (k, l)) (by omega) (by omega),
      ptOfN_of_lt hk, ptOfN_of_lt hl, Germ.zpos_some, Germ.zpos_some, Germ.wpos_some, Germ.wpos_some, sub_eq_zero]
    have h := congrArg HahnSeries.leadingCoeff (G.dist (fin6 k) (fin6 l) hne)
    rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_mul, Ser.leadingCoeff_pow,
      HahnSeries.leadingCoeff_one] at h
    exact h
  | init I S =>
    obtain ⟨⟨hg, hS⟩, hnd⟩ := hit
    have hv := valid_of_good hg
    have hlt : ∀ i ∈ S, i < I.terms.length := hS.2.1
    simp only [L6.F34S.itemVal]
    have hsum : (S.map fun i => L6.F34S.termVal2 (toTS Tz) (toTS Tw) (ptX G htz) (ptY G htw) (ptP G) G.E (ptM m)
        I.terms[i]!).sum = 0 := by
      set f : ℕ → ℂ := fun i => G.cval (toTerm I.terms[i]!).coeff * (toTerm I.terms[i]!).lead G with hf
      have h1 : (S.map fun i => L6.F34S.termVal2 (toTS Tz) (toTS Tw) (ptX G htz) (ptY G htw) (ptP G) G.E (ptM m)
          I.terms[i]!).sum = 2 * (S.map f).sum := by
        rw [← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun i hi => ?_
        rw [termVal2_eq hRz hRw (by rw [getElem!_pos I.terms i (hlt i hi)]; exact good_getElem hg (hlt i hi))]
      have h2 : (S.map f).sum = ∑ i ∈ S.toFinset, f i := (List.sum_toFinset f hnd).symm
      have h3 : MvPolynomial.aeval (G.leadPt htz htw) ((xid I).initForm Tz Tw S.toFinset) = ∑ i ∈ S.toFinset, f i := by
        rw [Identity.initForm, map_sum]
        have hT : ∀ i ∈ S.toFinset, i < (xid I).length := fun i hi => by
          rw [xid_length hv]; exact hlt i (List.mem_toFinset.mp hi)
        rw [← sum_fin_filter (xid I).length S.toFinset hT f]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi' : i.1 < I.terms.length := by rw [← xid_length hv]; exact i.2
        rw [Germ.eval_poly hRz hRw, xid_getElem hv i.2]
        simp only [hf]
        rw [getElem!_pos I.terms i.1 hi']
      have h4 := Germ.eval_initForm hRz hRw (xid_holds I) (isArgmin_of_isArgminX hRz hRw hg hS)
      rw [h1, h2, ← h3, h4, mul_zero]
    rw [hsum, mul_zero]

end items

/-! ## The polynomial `h` at the masses -/

theorem monoEval_congr {R : Type*} [CommRing R] {φ ψ : ℕ → R} (h : ∀ i < 6, φ i = ψ i) (k : ℕ) :
    L6.Poly.monoEval 6 φ k = L6.Poly.monoEval 6 ψ k := by
  unfold L6.Poly.monoEval
  exact Finset.prod_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

theorem eval_congr {R : Type*} [CommRing R] {φ ψ : ℕ → R} (h : ∀ i < 6, φ i = ψ i) (p : L6.Poly.Poly) :
    L6.Poly.eval 6 φ p = L6.Poly.eval 6 ψ p := by
  unfold L6.Poly.eval
  congr 1
  exact List.map_congr_left fun t _ => by rw [monoEval_congr h]

section vanish

variable {m : Fin 6 → ℝ} {G : Germ 6 m} {Tz Tw : TreeShape 6} {htz htw : Finset (Pt 6) → ℚ}

/-- **Lemma 5.2 at the converted trees**: if the generators of a certificate with `CertMeaning` are, at the points
`phiOf vars X Y P E m`, multiples of the values of items holding at the trees with heights, then `h` vanishes at the
masses of a germ realizing the trees, provided the fixed mass (if any) of the germ is `1`. -/
theorem eval_h_eq_zero (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {c : L6.Poly.Cert}
    {vars : Array L6.F34S.VarM} (hmean : L6.Poly.CertMeaning c)
    (hgen : ∀ j < c.gens.length, ∃ it : L6.F34S.ItemX, ItemOK (toExp Tz htz) (toExp Tw htw) it ∧
      ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
        ∀ {R : Type} [CommRing R] (X Y P : ℕ → ℕ → R) (E : R) (mm : ℕ → R),
          (0 ≤ c.fixed → mm c.fixed.toNat = 1) →
          (s : R) * L6.Poly.eval (6 + c.nvar) (L6.F34S.phiOf vars X Y P E mm) c.gens[j]! =
            L6.F34S.itemVal (toExp Tz htz).T (toExp Tw htw).T X Y P E mm it)
    (hfix : 0 ≤ c.fixed → ptM m c.fixed.toNat = 1) :
    L6.Poly.eval 6 (ptM m) c.h = 0 := by
  have hg : ∀ g ∈ c.gens, L6.Poly.eval (6 + c.nvar)
      (L6.F34S.phiOf vars (ptX G htz) (ptY G htw) (ptP G) G.E (ptM m)) g = 0 := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨it, hit, s, hs, heq⟩ := hgen j hj
    have h := heq (ptX G htz) (ptY G htw) (ptP G) G.E (ptM m) hfix
    rw [toExp_T, toExp_T, itemVal_eq_zero hRz hRw hit, getElem!_pos c.gens j hj] at h
    have hs0 : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    exact (mul_eq_zero.mp h).resolve_left hs0
  have h := hmean.1 (L6.F34S.phiOf vars (ptX G htz) (ptY G htw) (ptP G) G.E (ptM m)) hg
  rw [eval_congr (ψ := ptM m) (fun i hi => by simp [L6.F34S.phiOf, hi])] at h
  exact h

end vanish

/-- The masses of a core: `m` if no mass is fixed, `m / m_F` if the mass `F` is fixed. -/
noncomputable def massPt (m : Fin 6 → ℝ) (F : ℤ) : Fin 6 → ℝ :=
  if 0 ≤ F then (m (fin6 F.toNat))⁻¹ • m else m

/-- **Lemma 5.2 for the cores of the checks**: for a germ with positive masses realizing the trees, a certificate
with `CertMeaning` whose generators are multiples of the values of items holding at the trees with heights has `h`
vanishing at `m` (no fixed mass) or at `m / m_F` (the mass `F` fixed). -/
theorem core_vanish {m : Fin 6 → ℝ} (hm : ∀ k, 0 < m k) {G : Germ 6 m} {Tz Tw : TreeShape 6}
    {htz htw : Finset (Pt 6) → ℚ} (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {c : L6.Poly.Cert}
    {vars : Array L6.F34S.VarM} (hmean : L6.Poly.CertMeaning c)
    (hgen : ∀ j < c.gens.length, ∃ it : L6.F34S.ItemX, ItemOK (toExp Tz htz) (toExp Tw htw) it ∧
      ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
        ∀ {R : Type} [CommRing R] (X Y P : ℕ → ℕ → R) (E : R) (mm : ℕ → R),
          (0 ≤ c.fixed → mm c.fixed.toNat = 1) →
          (s : R) * L6.Poly.eval (6 + c.nvar) (L6.F34S.phiOf vars X Y P E mm) c.gens[j]! =
            L6.F34S.itemVal (toExp Tz htz).T (toExp Tw htw).T X Y P E mm it) :
    L6.Poly.eval 6 (ptM (massPt m c.fixed)) c.h = 0 := by
  by_cases hF : 0 ≤ c.fixed
  · have hj : 0 < m (fin6 c.fixed.toNat) := hm _
    have ht : 0 < (m (fin6 c.fixed.toNat))⁻¹ := inv_pos.mpr hj
    set G' := G.scale (m (fin6 c.fixed.toNat))⁻¹ ht with hG'
    have hRz' : Tz.Realizes G'.hz htz := by rw [hG', Germ.scale_hz]; exact hRz
    have hRw' : Tw.Realizes G'.hw htw := by rw [hG', Germ.scale_hw]; exact hRw
    have hmp : massPt m c.fixed = (m (fin6 c.fixed.toNat))⁻¹ • m := by rw [massPt, ite_eq_left hF]
    rw [hmp]
    refine eval_h_eq_zero (G := G') hRz' hRw' hmean hgen fun _ => ?_
    simp only [ptM, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_cancel₀ hj.ne', Complex.ofReal_one]
  · have hmp : massPt m c.fixed = m := by rw [massPt, ite_eq_right hF]
    rw [hmp]
    exact eval_h_eq_zero (G := G) hRz hRw hmean hgen fun h => absurd h hF

end CC6Compose
