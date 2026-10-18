import L6Sound.F34S.Defs
import L6Sound.F2S.RowsSem

/-!
# The exponent forms of the terms at the heights of a pair of complete trees

Under `LevelFacts` of the two trees of a pair (on all seven points), the form `termForm P t` of a good term is absent
exactly when a factor vanishes (`texp = ⊤`), and otherwise its value at the heights read off the complete trees is
twice the exponent `texp` (`termForm_spec`).
-/

namespace L6.F34S

open L6.F2S
open L6.F2S.RS (heightVec_vz heightVec_vw vz_lt vw_lt lca_mem)

variable {Xz Xw : ExpTree} {P : Pair}

theorem mem_all {p : Nat} (hp : p < 7) : L6.F2S.mem p all = true := by
  have : ∀ q < 7, L6.F2S.mem q all = true := by decide
  exact this p hp

/-- Two distinct bodies never share a leaf. -/
theorem sameLeaf_bodies (T : TS) {k l : Nat} (hk : k < 6) (hl : l < 6) (hkl : k ≠ l) : T.sameLeaf k l = false := by
  unfold TS.sameLeaf TS.lrep
  cases T.leafO with
  | none => simp [hkl]
  | some a =>
    simp only
    by_cases h1 : k = a <;> by_cases h2 : l = a <;> simp [h1, h2, L6.F2S.O] <;> omega

theorem goodSep_cases {pq : Nat × Nat} (h : goodSep pq = true) :
    pq.1 < 6 ∧ (pq.2 = L6.F2S.O ∨ (pq.2 < 6 ∧ pq.1 ≠ pq.2)) := by
  unfold goodSep at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  refine ⟨h.1, ?_⟩
  rcases h.2 with h2 | h2
  · left; rw [h2]; rfl
  · right; exact h2

theorem goodP_cases {kl : Nat × Nat} (h : goodP kl = true) : kl.1 < 6 ∧ kl.2 < 6 ∧ kl.1 ≠ kl.2 := by
  unfold goodP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A factor in the tree of `z`: absent exactly when it vanishes, else of value twice its exponent. -/
theorem sepCoefs_z (hz : LevelFacts Xz P.tz all) {pq : Nat × Nat} (hpq : goodSep pq = true) :
    (Xz.T.sameLeaf pq.1 pq.2 = true → sepCoefs P true pq = none) ∧
    (Xz.T.sameLeaf pq.1 pq.2 = false → ∃ cs, sepCoefs P true pq = some cs ∧ (∀ ic ∈ cs, ic.1 < P.nv) ∧
      (cs.map fun ic => (ic.2 : ℚ) * heightVec Xz Xw P ic.1).sum = 2 * Xz.e pq.1 pq.2) := by
  obtain ⟨p, q⟩ := pq
  obtain ⟨h1, h2⟩ := goodSep_cases hpq
  simp only at h1 h2 ⊢
  have hk7 : p < 7 := by omega
  rcases h2 with h2 | ⟨h2, hne⟩
  · have hsame := hz.same p h1 (mem_all hk7) (mem_all (by unfold L6.F2S.O; omega))
    subst h2
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · unfold sepCoefs
      simp only [ite_true]
      rw [hsame, hs]
      rfl
    · obtain ⟨C, hC, hl, hh⟩ := hz.pos p h1 (mem_all hk7) (mem_all (by unfold L6.F2S.O; omega))
        (hsame.trans hs)
      refine ⟨[(P.vz C, 2)], ?_, ?_, ?_⟩
      · unfold sepCoefs
        simp only [ite_true]
        rw [hsame, hs, hl]
        rfl
      · intro ic hic
        rw [List.mem_singleton] at hic
        subst hic
        exact vz_lt hC
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        unfold Pair.vz
        rw [heightVec_vz hC, hh]
        push_cast
        ring
  · have hsl : Xz.T.sameLeaf p q = false := sameLeaf_bodies _ h1 h2 hne
    have hslP : P.tz.sameLeaf p q = false := sameLeaf_bodies _ h1 h2 hne
    refine ⟨fun hs => by rw [hsl] at hs; exact absurd hs (by simp), fun _ => ?_⟩
    obtain ⟨C, hC, hl, hh⟩ := hz.lca p q h1 h2 hne (mem_all hk7) (mem_all (by omega))
    refine ⟨[(P.vz C, 2)], ?_, ?_, ?_⟩
    · unfold sepCoefs
      simp only [ite_true, hslP, Bool.false_eq_true, ite_false, hl]
    · intro ic hic
      rw [List.mem_singleton] at hic
      subst hic
      exact vz_lt hC
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      unfold Pair.vz
      rw [heightVec_vz hC, hh]
      push_cast
      ring

/-- A factor in the tree of `w`. -/
theorem sepCoefs_w (hw : LevelFacts Xw P.tw all) {pq : Nat × Nat} (hpq : goodSep pq = true) :
    (Xw.T.sameLeaf pq.1 pq.2 = true → sepCoefs P false pq = none) ∧
    (Xw.T.sameLeaf pq.1 pq.2 = false → ∃ cs, sepCoefs P false pq = some cs ∧ (∀ ic ∈ cs, ic.1 < P.nv) ∧
      (cs.map fun ic => (ic.2 : ℚ) * heightVec Xz Xw P ic.1).sum = 2 * Xw.e pq.1 pq.2) := by
  obtain ⟨p, q⟩ := pq
  obtain ⟨h1, h2⟩ := goodSep_cases hpq
  simp only at h1 h2 ⊢
  have hk7 : p < 7 := by omega
  rcases h2 with h2 | ⟨h2, hne⟩
  · have hsame := hw.same p h1 (mem_all hk7) (mem_all (by unfold L6.F2S.O; omega))
    subst h2
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · unfold sepCoefs
      simp only [Bool.false_eq_true, ite_false]
      rw [hsame, hs]
      rfl
    · obtain ⟨C, hC, hl, hh⟩ := hw.pos p h1 (mem_all hk7) (mem_all (by unfold L6.F2S.O; omega))
        (hsame.trans hs)
      refine ⟨[(P.vw C, 2)], ?_, ?_, ?_⟩
      · unfold sepCoefs
        simp only [Bool.false_eq_true, ite_false]
        rw [hsame, hs, hl]
        rfl
      · intro ic hic
        rw [List.mem_singleton] at hic
        subst hic
        exact vw_lt hC
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        unfold Pair.vw
        rw [heightVec_vw hC, hh]
        push_cast
        ring
  · have hsl : Xw.T.sameLeaf p q = false := sameLeaf_bodies _ h1 h2 hne
    have hslP : P.tw.sameLeaf p q = false := sameLeaf_bodies _ h1 h2 hne
    refine ⟨fun hs => by rw [hsl] at hs; exact absurd hs (by simp), fun _ => ?_⟩
    obtain ⟨C, hC, hl, hh⟩ := hw.lca p q h1 h2 hne (mem_all hk7) (mem_all (by omega))
    refine ⟨[(P.vw C, 2)], ?_, ?_, ?_⟩
    · unfold sepCoefs
      simp only [Bool.false_eq_true, ite_false, hslP, hl]
    · intro ic hic
      rw [List.mem_singleton] at hic
      subst hic
      exact vw_lt hC
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      unfold Pair.vw
      rw [heightVec_vw hC, hh]
      push_cast
      ring

/-- A factor `p_kl`: a form of value `2 · (−x_kl)`. -/
theorem pCoefs_spec (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {kl : Nat × Nat}
    (hkl : goodP kl = true) :
    (∀ ic ∈ pCoefs P kl, ic.1 < P.nv) ∧
      ((pCoefs P kl).map fun ic => (ic.2 : ℚ) * heightVec Xz Xw P ic.1).sum = 2 * -xkl Xz Xw kl.1 kl.2 := by
  obtain ⟨h1, h2, hne⟩ := goodP_cases hkl
  obtain ⟨Cz, hCz, hlz, hhz⟩ := hz.lca kl.1 kl.2 h1 h2 hne (mem_all (by omega)) (mem_all (by omega))
  obtain ⟨Cw, hCw, hlw, hhw⟩ := hw.lca kl.1 kl.2 h1 h2 hne (mem_all (by omega)) (mem_all (by omega))
  have hp : pCoefs P kl = [(P.vz Cz, -1), (P.vw Cw, -1)] := by
    unfold pCoefs
    rw [hlz, hlw]
    rfl
  rw [hp]
  refine ⟨fun ic hic => ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hic
    rcases hic with rfl | rfl
    · exact vz_lt hCz
    · exact vw_lt hCw
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold Pair.vz Pair.vw
    rw [heightVec_vz hCz, heightVec_vw hCw, hhz, hhw]
    unfold xkl
    push_cast
    ring

/-- The factors of one colour: absent exactly when a factor vanishes, else of value twice the sum of the exponents. -/
theorem mapM_sep (z : Bool) (X : ExpTree)
    (hsep : ∀ pq, goodSep pq = true →
      (X.T.sameLeaf pq.1 pq.2 = true → sepCoefs P z pq = none) ∧
      (X.T.sameLeaf pq.1 pq.2 = false → ∃ cs, sepCoefs P z pq = some cs ∧ (∀ ic ∈ cs, ic.1 < P.nv) ∧
        (cs.map fun ic => (ic.2 : ℚ) * heightVec Xz Xw P ic.1).sum = 2 * X.e pq.1 pq.2)) :
    ∀ zs : List (Nat × Nat), (∀ pq ∈ zs, goodSep pq = true) →
      (zs.mapM (sepCoefs P z) = none ∧ (zs.map (sepExp X)).sum = ⊤) ∨
      (∃ css, zs.mapM (sepCoefs P z) = some css ∧ (∀ ic ∈ css.flatten, ic.1 < P.nv) ∧
        (zs.map (sepExp X)).sum =
          ((((css.flatten.map fun ic => (ic.2 : ℚ) * heightVec Xz Xw P ic.1).sum / 2 : ℚ)) : WithTop ℚ)) := by
  intro zs
  induction zs with
  | nil =>
    intro _
    right
    exact ⟨[], rfl, by simp, by simp⟩
  | cons pq rest ih =>
    intro hg
    have hpq := hg pq List.mem_cons_self
    have hrest := ih fun x hx => hg x (List.mem_cons_of_mem _ hx)
    obtain ⟨hnone, hsome⟩ := hsep pq hpq
    cases hs : X.T.sameLeaf pq.1 pq.2 with
    | true =>
      left
      refine ⟨?_, ?_⟩
      · rw [List.mapM_cons, hnone hs]
        rfl
      · simp only [List.map_cons, List.sum_cons]
        unfold sepExp
        rw [hs]
        simp
    | false =>
      obtain ⟨cs, hcs, hlt, hval⟩ := hsome hs
      rcases hrest with ⟨hn, ht⟩ | ⟨css, hcss, hlt', hval'⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [List.mapM_cons, hcs, hn]
          rfl
        · simp only [List.map_cons, List.sum_cons, ht]
          exact WithTop.add_top _
      · right
        refine ⟨cs :: css, ?_, ?_, ?_⟩
        · rw [List.mapM_cons, hcs, hcss]
          rfl
        · intro ic hic
          rw [List.flatten_cons, List.mem_append] at hic
          rcases hic with hic | hic
          · exact hlt ic hic
          · exact hlt' ic hic
        · simp only [List.map_cons, List.sum_cons, hval', List.flatten_cons, List.map_append, List.sum_append]
          unfold sepExp
          rw [hs]
          simp only [Bool.false_eq_true, ite_false]
          rw [← WithTop.coe_add, hval]
          congr 1
          ring

/-- **The form of a term.** Absent exactly when the exponent is `⊤`; otherwise of size `nv`, and its value at the
heights read off the complete trees is twice the exponent. -/
theorem termForm_spec (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) {t : XTerm}
    (ht : t.good = true) :
    (termForm P t = none ∧ texp Xz Xw t = ⊤) ∨
      (∃ f, termForm P t = some f ∧ f.size = P.nv ∧
        texp Xz Xw t = ((formVal P.nv f (heightVec Xz Xw P) / 2 : ℚ) : WithTop ℚ)) := by
  unfold XTerm.good at ht
  simp only [Bool.and_eq_true, List.all_eq_true] at ht
  obtain ⟨⟨⟨⟨⟨hzs, hws⟩, hps⟩, -⟩, -⟩, -⟩ := ht
  have hZ := mapM_sep (Xz := Xz) (Xw := Xw) (P := P) true Xz (fun pq h => sepCoefs_z hz h) t.zs hzs
  have hW := mapM_sep (Xz := Xz) (Xw := Xw) (P := P) false Xw (fun pq h => sepCoefs_w hw h) t.ws hws
  rcases hZ with ⟨hzn, hzt⟩ | ⟨zcs, hzc, hzlt, hzv⟩
  · left
    refine ⟨?_, ?_⟩
    · unfold termForm
      rw [hzn]
      rfl
    · unfold texp
      rw [hzt]
      simp
  · rcases hW with ⟨hwn, hwt⟩ | ⟨wcs, hwc, hwlt, hwv⟩
    · left
      refine ⟨?_, ?_⟩
      · unfold termForm
        rw [hzc, hwn]
        rfl
      · unfold texp
        rw [hwt]
        simp
    · right
      have hpl : ∀ ic ∈ (t.ps.map (pCoefs P)).flatten, ic.1 < P.nv := by
        intro ic hic
        obtain ⟨l, hl, hic⟩ := List.mem_flatten.mp hic
        obtain ⟨kl, hkl, rfl⟩ := List.mem_map.mp hl
        exact (pCoefs_spec hz hw (hps kl hkl)).1 ic hic
      have hpv : ((t.ps.map (pCoefs P)).flatten.map fun ic => (ic.2 : ℚ) * heightVec Xz Xw P ic.1).sum =
          2 * (t.ps.map fun kl => -xkl Xz Xw kl.1 kl.2).sum := by
        rw [List.map_flatten, List.sum_flatten, List.map_map, List.map_map, ← List.sum_map_mul_left]
        congr 1
        refine List.map_congr_left fun kl hkl => ?_
        exact (pCoefs_spec hz hw (hps kl hkl)).2
      refine ⟨form P.nv (zcs.flatten ++ wcs.flatten ++ (t.ps.map (pCoefs P)).flatten), ?_, RS.form_size _ _, ?_⟩
      · unfold termForm
        rw [hzc, hwc]
        rfl
      · rw [RS.formVal_form]
        · unfold texp
          rw [hzv, hwv]
          simp only [List.map_append, List.sum_append, hpv]
          rw [← WithTop.coe_add, ← WithTop.coe_add]
          congr 1
          ring
        · intro ic hic
          simp only [List.mem_append] at hic
          rcases hic with (hic | hic) | hic
          · exact hzlt ic hic
          · exact hwlt ic hic
          · exact hpl ic hic

end L6.F34S
