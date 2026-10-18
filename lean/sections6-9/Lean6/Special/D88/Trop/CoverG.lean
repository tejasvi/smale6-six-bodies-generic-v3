import Lean6.Special.D88.Trop.Cover

/-!
# Lemma 6.19(a), (iii)–(iv), over an ordered abelian group

The soundness of the covering checker `chk` (`Cover.lean`) for weight vectors with values in any linearly ordered
abelian group `Γ`, not only `ℚ`: `cover_soundG`. The weight of a monomial with exponent vector `e` is `Σ_i e_i • w_i`
(`wtG`), the initial form `initialFormG w g` consists of the terms of `g` of least weight, and `TorusEmptyG` says that
the initial forms have no common zero in the torus `(K^*)^{17}` of any field `K` of characteristic `p`. This is the
form in which a valuation `ν` with values in an arbitrary ordered group (for instance the valuation of a valuation ring
dominating a local ring) enters the proof of Lemma 6.18.

The certificates checked by `chk` (the multipliers of `emptyOK`, `eqOK`, `strictOK`, the cell constraints, the unit
vectors of the leaf `nonneg`) are integer combinations, so the proof is that of `Cover.lean` with `ℤ`-multiples in
`Γ` in place of rational products. `initialFormG_rat` and `torusEmptyG_rat` identify the case `Γ = ℚ` with the
definitions of `Cover.lean`.
-/

namespace Lean6.Special.D88.Trop

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.D88.Trop

section Gamma

variable {Γ : Type*} [AddCommGroup Γ]

/-! ## Weights -/

/-- `⟨v, w⟩ = Σ_k v_k • w_{i+k}` for an integer vector `v` whose first entry belongs to the coordinate `i`. -/
def dotG (w : ℕ → Γ) : List Int → ℕ → Γ
  | [], _ => 0
  | a :: v, i => a • w i + dotG w v (i + 1)

variable {w : ℕ → Γ}

theorem dotG_vadd : ∀ (a b : List Int) (i : ℕ), dotG w (vadd a b) i = dotG w a i + dotG w b i
  | [], b, i => by simp [vadd, dotG]
  | a :: as, [], i => by simp [vadd, dotG]
  | a :: as, b :: bs, i => by
    simp only [vadd, dotG, dotG_vadd as bs (i + 1), add_zsmul]
    abel

theorem dotG_vsmul (c : Int) : ∀ (v : List Int) (i : ℕ), dotG w (vsmul c v) i = c • dotG w v i
  | [], i => by simp [vsmul, dotG]
  | a :: v, i => by
    have := dotG_vsmul c v (i + 1)
    simp only [vsmul, List.map_cons, dotG] at this ⊢
    rw [this, smul_add, ← smul_smul]

theorem dotG_zero_of_isZeroV : ∀ {v : List Int} (i : ℕ), isZeroV v = true → dotG w v i = 0
  | [], _, _ => rfl
  | a :: v, i, h => by
    simp only [isZeroV, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have := dotG_zero_of_isZeroV (v := v) (i + 1) (by simpa [isZeroV] using h.2)
    simp [dotG, h.1, this]

theorem dotG_linS_aux (rows : List (List Int)) (i : ℕ) :
    ∀ (cs : List (Nat × Int)) (acc : List Int),
      dotG w (cs.foldl (fun acc kc => vadd acc (vsmul kc.2 (rows.getD kc.1 []))) acc) i =
        dotG w acc i + (cs.map fun kc => kc.2 • dotG w (rows.getD kc.1 []) i).sum
  | [], acc => by simp
  | kc :: cs, acc => by
    rw [List.foldl_cons, dotG_linS_aux rows i cs, dotG_vadd, dotG_vsmul, List.map_cons, List.sum_cons]
    abel

theorem dotG_linS (rows : List (List Int)) (cs : List (Nat × Int)) (i : ℕ) :
    dotG w (linS rows cs) i = (cs.map fun kc => kc.2 • dotG w (rows.getD kc.1 []) i).sum := by
  rw [linS, dotG_linS_aux, show dotG w [] i = 0 from rfl, zero_add]

/-- The weight `Σ_i e_i • w_i` of a monomial. -/
def wtG (w : ℕ → Γ) (m : Mono) : Γ := dotG w (toZ m) 0

theorem dotG_diffE (g : Poly ℕ) (i j : ℕ) :
    dotG w (diffE g i j) 0 = wtG w (term g i).2 - wtG w (term g j).2 := by
  rw [diffE, dotG_vadd, dotG_vsmul, neg_one_zsmul, ← sub_eq_add_neg]
  rfl

theorem dotG_unitV (i : ℕ) (hi : i < 17) : dotG w (unitV i) 0 = w i := by
  have key : ∀ (n s : ℕ), dotG w ((List.range' s n).map fun k => if k = i then (1 : Int) else 0) s =
      if s ≤ i ∧ i < s + n then w i else 0 := by
    intro n
    induction n with
    | zero => intro s; simp [dotG]
    | succ n ihn =>
      intro s
      rw [List.range'_succ, List.map_cons, dotG, ihn (s + 1)]
      by_cases hs : s = i
      · subst hs; simp
      · simp only [hs, ↓reduceIte, zero_smul, zero_add]
        congr 1
        apply propext
        omega
  rw [unitV, List.range_eq_range', key 17 0]
  simp [hi]

variable [LinearOrder Γ]

/-! ## Cells and certificates -/

/-- `w` lies in the cell `{E w = 0, S w > 0}`. -/
def InCellG (E S : List (List Int)) (w : ℕ → Γ) : Prop :=
  (∀ e ∈ E, dotG w e 0 = 0) ∧ (∀ s ∈ S, 0 < dotG w s 0)

theorem dotG_linS_E {E S : List (List Int)} (h : InCellG E S w) (u : List (Nat × Int)) :
    dotG w (linS E u) 0 = 0 := by
  rw [dotG_linS]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨kc, -, rfl⟩ := List.mem_map.mp hx
  rcases getD_mem_or_nil (rows := E) kc.1 with hm | hm
  · rw [h.1 _ hm, smul_zero]
  · rw [hm]; simp [dotG]

/-! ## Initial forms -/

/-- **The initial form** of `g` at `w`: the terms of least weight (in their order in `g`). -/
def initialFormG (w : ℕ → Γ) (g : Poly ℕ) : Poly ℕ :=
  ((List.range g.length).filter fun i => decide (∀ j < g.length, wtG w (term g i).2 ≤ wtG w (term g j).2)).map
    (term g)

/-- `F` is the set of indices of the terms of least weight. -/
def FaceAtG (g : Poly ℕ) (F : List ℕ) (w : ℕ → Γ) : Prop :=
  F.Nodup ∧ (∀ i ∈ F, i < g.length) ∧
    ∀ i < g.length, (i ∈ F ↔ ∀ j < g.length, wtG w (term g i).2 ≤ wtG w (term g j).2)

theorem perm_initialFormG {g : Poly ℕ} {F : List ℕ} (h : FaceAtG g F w) :
    ((List.range g.length).filter fun i => decide (∀ j < g.length, wtG w (term g i).2 ≤ wtG w (term g j).2)).Perm
      F := by
  rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) h.1]
  intro i
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hi, hmin⟩
    exact (h.2.2 i hi).mpr hmin
  · intro hi
    exact ⟨h.2.1 i hi, (h.2.2 i (h.2.1 i hi)).mp hi⟩

theorem eval_initialFormG {R : Type*} [CommRing R] {C : Coeff ℕ} (hC : C.Hom R) (x : ℕ → R) {g : Poly ℕ}
    {F : List ℕ} (h : FaceAtG g F w) : Poly.eval hC x (initialFormG w g) = Poly.eval hC x (inF g F) := by
  rw [initialFormG, inF_eq_map]
  exact Poly.eval_perm hC x ((perm_initialFormG h).map _)

/-- The torus statement over `Γ`: at no point of `(K^*)^{17}` do all the initial forms at `w` vanish. -/
def TorusEmptyG (p : ℕ) [NeZero p] (Gb : List (Poly ℕ)) (w : ℕ → Γ) : Prop :=
  ∀ (K : Type) [Field K] [CharP K p] (x : ℕ → K), (∀ i < 17, x i ≠ 0) →
    ∃ g ∈ Gb, Poly.eval (modHomK p K) x (initialFormG w g) ≠ 0

variable [IsOrderedAddMonoid Γ]

theorem dotG_linS_S {E S : List (List Int)} (h : InCellG E S w) {y : List (Nat × Int)}
    (hy : posOK S.length y = true) : 0 < dotG w (linS S y) 0 := by
  simp only [posOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hy
  obtain ⟨hnn, kc0, hkc0, hpos, hlt⟩ := hy
  rw [dotG_linS]
  have hterm : ∀ kc ∈ y, 0 ≤ kc.2 • dotG w (S.getD kc.1 []) 0 := by
    intro kc hkc
    rcases getD_mem_or_nil (rows := S) kc.1 with hm | hm
    · exact zsmul_nonneg (h.2 _ hm).le (hnn kc hkc)
    · rw [hm]; simp [dotG]
  have hpos' : 0 < kc0.2 • dotG w (S.getD kc0.1 []) 0 := by
    have hm : S.getD kc0.1 [] ∈ S := by
      rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
    exact zsmul_pos (h.2 _ hm) hpos
  obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hkc0
  rw [hsplit, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  have s1 : 0 ≤ (l1.map fun kc => kc.2 • dotG w (S.getD kc.1 []) 0).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp hx
      exact hterm kc (by rw [hsplit]; exact List.mem_append_left _ hkc)
  have s2 : 0 ≤ (l2.map fun kc => kc.2 • dotG w (S.getD kc.1 []) 0).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp hx
      exact hterm kc (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hkc))
  exact add_pos_of_nonneg_of_pos s1 (add_pos_of_pos_of_nonneg hpos' s2)

theorem not_inCellG_of_emptyOK {E S : List (List Int)} {u y : List (Nat × Int)} (h : emptyOK E S u y = true) :
    ¬ InCellG E S w := by
  intro hc
  simp only [emptyOK, Bool.and_eq_true] at h
  have h0 := dotG_zero_of_isZeroV (w := w) 0 h.2
  rw [dotG_vadd, dotG_linS_E hc, zero_add] at h0
  exact (dotG_linS_S hc h.1).ne' h0

/-- A positive multiple determines the sign. -/
theorem zsmul_eq_zero_of_pos {c : Int} (hc : 0 < c) {g : Γ} (h : c • g = 0) : g = 0 := by
  rcases lt_trichotomy g 0 with hn | hz | hp
  · have := zsmul_pos (neg_pos.mpr hn) hc
    rw [zsmul_neg, h, neg_zero] at this
    exact absurd this (lt_irrefl 0)
  · exact hz
  · have := zsmul_pos hp hc
    rw [h] at this
    exact absurd this (lt_irrefl 0)

theorem pos_of_zsmul_pos {c : Int} (hc : 0 < c) {g : Γ} (h : 0 < c • g) : 0 < g := by
  by_contra hneg
  push Not at hneg
  have := zsmul_nonneg (neg_nonneg.mpr hneg) hc.le
  rw [zsmul_neg] at this
  exact absurd h (not_lt.mpr (neg_nonneg.mp this))

theorem dotG_eq_zero_of_eqOK {E S : List (List Int)} {h : List Int} {c : Int × List (Nat × Int)}
    (hc : InCellG E S w) (hok : eqOK E h c = true) : dotG w h 0 = 0 := by
  simp only [eqOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  have h0 := dotG_zero_of_isZeroV (w := w) 0 hok.2
  rw [dotG_vadd, dotG_vsmul, dotG_vsmul, dotG_linS_E hc, smul_zero, add_zero] at h0
  exact zsmul_eq_zero_of_pos hok.1 h0

theorem dotG_pos_of_strictOK {E S : List (List Int)} {h : List Int}
    {c : Int × List (Nat × Int) × List (Nat × Int)} (hc : InCellG E S w) (hok : strictOK E S h c = true) :
    0 < dotG w h 0 := by
  simp only [strictOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hz, hy⟩, hzero⟩ := hok
  have h0 := dotG_zero_of_isZeroV (w := w) 0 hzero
  rw [dotG_vadd, dotG_vsmul, dotG_vsmul, dotG_vadd, dotG_linS_E hc, add_zero, neg_one_zsmul,
    add_neg_eq_zero] at h0
  have hS := dotG_linS_S hc hy
  rw [← h0] at hS
  exact pos_of_zsmul_pos hz hS

/-! ## The induction -/

variable {p : ℕ} [NeZero p]

theorem chk_soundG {Gb : List (Poly ℕ)} (hGb : gbOK p Gb = true) {hyps : List (List (Poly ℕ))}
    (hH : HypsOK p hyps) :
    ∀ (node : Node) (E S : List (List Int)) (faces : List (ℕ × List ℕ)),
      chk p Gb hyps E S faces node = true → (∀ f ∈ faces, f.1 < Gb.length ∧ ∀ i ∈ f.2, i < (Gb.getD f.1 []).length) →
      ∀ w : ℕ → Γ, InCellG E S w → (∀ f ∈ faces, FaceAtG (Gb.getD f.1 []) f.2 w) → (∃ i < 17, w i < 0) →
        TorusEmptyG p Gb w := by
  intro node
  induction node with
  | empty u y =>
    intro E S faces h _ w hc _ _
    exact absurd hc (not_inCellG_of_emptyOK h)
  | split g i j gt lt eq ihgt ihlt iheq =>
    intro E S faces h hfv w hc hf hneg
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hgt⟩, hlt⟩, heq⟩ := h
    set hh := diffE (Gb.getD g []) i j
    rcases lt_trichotomy (dotG w hh 0) 0 with hn | hz | hp'
    · refine ihlt E _ faces hlt hfv w ⟨hc.1, fun s hs => ?_⟩ hf hneg
      rcases List.mem_append.mp hs with hs | hs
      · exact hc.2 s hs
      · rw [List.mem_singleton.mp hs, dotG_vsmul, neg_one_zsmul]
        exact neg_pos.mpr hn
    · refine iheq _ S faces heq hfv w ⟨fun e he => ?_, hc.2⟩ hf hneg
      rcases List.mem_append.mp he with he | he
      · exact hc.1 e he
      · rw [List.mem_singleton.mp he]; exact hz
    · refine ihgt E _ faces hgt hfv w ⟨hc.1, fun s hs => ?_⟩ hf hneg
      rcases List.mem_append.mp hs with hs | hs
      · exact hc.2 s hs
      · rw [List.mem_singleton.mp hs]; exact hp'
  | face g F eqc strict child ih =>
    intro E S faces h hfv w hc hf hneg
    cases F with
    | nil => simp [chk] at h
    | cons a0 rest =>
      simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hg, hFlt⟩, hnd⟩, hl1⟩, heqc⟩, hl2⟩, hstr⟩, hchild⟩ := h
      set gg := Gb.getD g []
      have hFlt' : ∀ i ∈ a0 :: rest, i < gg.length := fun i hi => hFlt i hi
      have ha0 : a0 < gg.length := hFlt' a0 (List.mem_cons_self ..)
      -- equal weights on F
      have hEq : ∀ i ∈ a0 :: rest, wtG w (term gg i).2 = wtG w (term gg a0).2 := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · rfl
        · obtain ⟨c, hc'⟩ := zip_all_forall hl1 (P := fun t => eqOK E (diffE gg t.1 a0) t.2)
            (List.all_eq_true.mpr heqc) i hi
          have := dotG_eq_zero_of_eqOK hc hc'
          rw [dotG_diffE] at this
          exact sub_eq_zero.mp this
      -- larger weights outside F
      have hGt : ∀ i < gg.length, i ∉ a0 :: rest → wtG w (term gg a0).2 < wtG w (term gg i).2 := by
        intro i hi hni
        have hmem : i ∈ (List.range gg.length).filter fun i => !((a0 :: rest).contains i) := by
          have hc : (a0 :: rest).contains i = false :=
            Bool.eq_false_iff.mpr fun hci => hni (List.contains_iff_mem.mp hci)
          simp only [List.mem_filter, List.mem_range, hc, Bool.not_false, and_true]
          exact hi
        obtain ⟨c, hc'⟩ := zip_all_forall hl2 (P := fun t => strictOK E S (diffE gg t.1 a0) t.2)
          (List.all_eq_true.mpr hstr) i hmem
        have := dotG_pos_of_strictOK hc hc'
        rw [dotG_diffE] at this
        exact sub_pos.mp this
      have hface : FaceAtG gg (a0 :: rest) w := by
        refine ⟨by simpa using hnd, hFlt', fun i hi => ⟨fun hiF j hj => ?_, fun hmin => ?_⟩⟩
        · rw [hEq i hiF]
          by_cases hjF : j ∈ a0 :: rest
          · rw [hEq j hjF]
          · exact (hGt j hj hjF).le
        · by_contra hni
          exact absurd (hmin a0 ha0) (not_le.mpr (hGt i hi hni))
      refine ih E S ((g, a0 :: rest) :: faces) hchild ?_ w hc ?_ hneg
      · intro f hf'
        rcases List.mem_cons.mp hf' with rfl | hf'
        · exact ⟨hg, hFlt'⟩
        · exact hfv f hf'
      · intro f hf'
        rcases List.mem_cons.mp hf' with rfl | hf'
        · exact hface
        · exact hf f hf'
  | mono =>
    intro E S faces h hfv w hc hf hneg K _ _ x hx
    match faces, h, hfv, hf with
    | (g, [i]) :: _, h, hfv, hf =>
      have hgv := hfv (g, [i]) (List.mem_cons_self ..)
      have hface := hf (g, [i]) (List.mem_cons_self ..)
      refine ⟨Gb.getD g [], ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hgv.1]; exact List.getElem_mem hgv.1
      · rw [eval_initialFormG _ x hface]
        have hi := hgv.2 i (List.mem_singleton_self _)
        have hm : (Gb.getD g []).getD i (0, []) ∈ Gb.getD g [] := by
          rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
        have ht := gb_terms hGb (g := g) _ hm
        simp only [inF, List.map_cons, List.map_nil, Poly.eval_cons, Poly.eval_nil, add_zero]
        refine mul_ne_zero ?_ (mono_eval_ne_zero _ 0 fun k _ hk => hx k (by omega))
        show ((((Gb.getD g []).getD i (0, [])).1 : ℕ) : K) ≠ 0
        rw [Ne, CharP.cast_eq_zero_iff K p]
        intro hdvd
        exact ht.2.2 (Nat.eq_zero_of_dvd_of_lt hdvd ht.2.1)
    | [], h, _, _ => simp [chk] at h
    | (g, []) :: _, h, _, _ => simp [chk] at h
    | (g, _ :: _ :: _) :: _, h, _, _ => simp [chk] at h
  | leaf cofs cofR =>
    intro E S faces h hfv w hc hf hneg K _ _ x hx
    classical
    set hK := modHomK p K
    set ins := faces.map fun f => inF (Gb.getD f.1 []) f.2
    have hprod : (∏ k ∈ Finset.range 17, x k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k hk =>
      hx k (Finset.mem_range.mp hk)
    let x' : ℕ → K := fun k => if k < 17 then x k else (∏ k ∈ Finset.range 17, x k)⁻¹
    have hxx' : ∀ k < 17, x' k = x k := fun k hk => by simp [x', hk]
    have h0 := Poly.isZero_sound hK x' h
    rw [Poly.eval_sub, Poly.eval_add, Poly.eval_sum, Poly.eval_mul, Poly.eval_const] at h0
    have hrab : Poly.eval hK x' (rabin p) = 0 := by
      simp only [rabin, Poly.eval_cons, Poly.eval_nil, add_zero, Mono.eval, mul_one, hK.map_neg, hK.map_one]
      rw [mono_eval_replicate_one, Finset.prod_range_succ]
      simp only [zero_add]
      have e1 : (∏ k ∈ Finset.range 17, x' k) = ∏ k ∈ Finset.range 17, x k :=
        Finset.prod_congr rfl fun k hk => hxx' k (Finset.mem_range.mp hk)
      have e2 : x' 17 = (∏ k ∈ Finset.range 17, x k)⁻¹ := by simp [x']
      rw [e1, e2, mul_inv_cancel₀ hprod]
      ring
    have hf1 : hK.f 1 = 1 := by simp [hK, modHomK]
    rw [hrab, mul_zero, add_zero, hf1, sub_eq_zero] at h0
    -- some initial form does not vanish at x'
    have hex : ∃ c ∈ cofs, Poly.eval hK x' (ins.getD c.1 []) ≠ 0 := by
      by_contra hall
      push Not at hall
      have hz : ∀ v ∈ (cofs.map fun c => Poly.mul (modC p) c.2 (ins.getD c.1 [])).map (Poly.eval hK x'), v = 0 := by
        intro v hv
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hq
        rw [Poly.eval_mul, hall c hc', mul_zero]
      have := List.sum_eq_zero hz
      rw [h0] at this
      exact one_ne_zero this
    obtain ⟨c, -, hcne⟩ := hex
    have hlt : c.1 < ins.length := by
      by_contra hge
      push Not at hge
      rw [List.getD_eq_default _ _ hge] at hcne
      exact hcne rfl
    have hins : ins.getD c.1 [] = inF (Gb.getD (faces[c.1]'(by simpa [ins] using hlt)).1 [])
        (faces[c.1]'(by simpa [ins] using hlt)).2 := by
      rw [List.getD_eq_getElem _ _ hlt]; simp [ins]
    set f := faces[c.1]'(by simpa [ins] using hlt)
    have hfmem : f ∈ faces := List.getElem_mem _
    have hgv := hfv f hfmem
    refine ⟨Gb.getD f.1 [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hgv.1]; exact List.getElem_mem hgv.1
    · rw [eval_initialFormG _ x (hf f hfmem)]
      rw [hins] at hcne
      rwa [eval_congr17 hK (fun k hk => (hxx' k hk).symm) _ (inF_terms hGb f.1 f.2 hgv.2)]
  | nonneg certs =>
    intro E S faces h _ w hc _ hneg
    simp only [chk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨i, hi, hwi⟩ := hneg
    have hmem : i ∈ List.range 17 := List.mem_range.mpr hi
    obtain ⟨c, hc'⟩ := zip_all_forall (by simp [h.1]) (P := fun t => eqOK E (unitV t.1) t.2) h.2 i hmem
    have h0 := dotG_eq_zero_of_eqOK hc hc'
    rw [dotG_unitV i hi] at h0
    exact absurd h0 hwi.ne
  | hyp k =>
    intro E S faces h hfv w hc hf hneg K _ _ x hx
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hk, heq⟩ := h
    have hmem : hyps.getD k [] ∈ hyps := by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    obtain ⟨f, hfm, hfne⟩ := hH _ hmem K x hx
    rw [← heq] at hfm
    obtain ⟨fc, hfc, rfl⟩ := List.mem_map.mp hfm
    have hgv := hfv fc hfc
    refine ⟨Gb.getD fc.1 [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hgv.1]; exact List.getElem_mem hgv.1
    · rw [eval_initialFormG _ x (hf fc hfc)]
      exact hfne

/-- **Soundness of the covering, over any linearly ordered abelian group.** -/
theorem cover_soundG {Gb : List (Poly ℕ)} {hyps : List (List (Poly ℕ))} {root : Node} (hGb : gbOK p Gb = true)
    (hH : HypsOK p hyps) (h : chk p Gb hyps [] [] [] root = true) (w : ℕ → Γ) (hneg : ∃ i < 17, w i < 0) :
    TorusEmptyG p Gb w :=
  chk_soundG hGb hH root [] [] [] h (by simp) w ⟨by simp, by simp⟩ (by simp) hneg

end Gamma

/-! ## The case `Γ = ℚ` -/

theorem dotG_rat (w : ℕ → ℚ) : ∀ (v : List Int) (i : ℕ), dotG w v i = dotQ w v i
  | [], _ => rfl
  | a :: v, i => by rw [dotG, dotQ, dotG_rat w v (i + 1), zsmul_eq_mul]

theorem wtG_rat (w : ℕ → ℚ) (m : Mono) : wtG w m = wt w m := dotG_rat w (toZ m) 0

/-- For `Γ = ℚ` the initial form is that of `Cover.lean`. -/
theorem initialFormG_rat (w : ℕ → ℚ) (g : Poly ℕ) : initialFormG w g = initialForm w g := by
  simp only [initialFormG, initialForm, wtG_rat]

/-- For `Γ = ℚ` the torus statement is that of `Cover.lean`. -/
theorem torusEmptyG_rat (p : ℕ) [NeZero p] (Gb : List (Poly ℕ)) (w : ℕ → ℚ) :
    TorusEmptyG p Gb w ↔ TorusEmpty p Gb w := by
  simp only [TorusEmptyG, TorusEmpty, initialFormG_rat]

end Lean6.Special.D88.Trop
