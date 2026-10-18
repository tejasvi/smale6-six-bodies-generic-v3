import L6Sound.F2S.RowsAux

/-!
# Auxiliary facts for the rows of the specification search: a pair of partial trees

Every tree row, pair row and position row of a pair of partial trees with `LevelFacts`, and its threshold row, holds
strictly at the heights read off the complete trees. The lemmas are in the namespace `L6.F2S.RS`.
-/

namespace L6.F2S.RS

open L6.F2 (Diag pairs6)

/-! ## Folds and binds in `Option` -/

/-- A fold in `Option` whose steps succeed and keep an invariant of the folded part of the list succeeds. -/
theorem foldr_inv {α β : Type} (step : α → Option β → Option β) (I : List α → β → Prop) (b0 : β) (L : List α)
    (h0 : I [] b0)
    (hstep : ∀ a ∈ L, ∀ (L' : List α) (b : β), I L' b → ∃ b', step a (some b) = some b' ∧ I (a :: L') b') :
    ∃ b, L.foldr step (some b0) = some b ∧ I L b := by
  induction L with
  | nil => exact ⟨b0, rfl, h0⟩
  | cons a L ih =>
    obtain ⟨b, hb, hI⟩ := ih fun a' ha' => hstep a' (List.mem_cons_of_mem _ ha')
    obtain ⟨b', hb', hI'⟩ := hstep a List.mem_cons_self L b hI
    exact ⟨b', by rw [List.foldr_cons, hb, hb'], hI'⟩

theorem bind_some_of {α β : Type} {x : Option α} {f : α → Option β} {R : α → Prop} {Q : β → Prop}
    (hx : ∃ a, x = some a ∧ R a) (hf : ∀ a, R a → ∃ b, f a = some b ∧ Q b) : ∃ b, (x >>= f) = some b ∧ Q b := by
  obtain ⟨a, rfl, ha⟩ := hx
  exact hf a ha

/-! ## Pairs, bodies, forms -/

theorem pairs6_spec : ∀ kl ∈ pairs6.toList, kl.1 < kl.2 ∧ kl.2 < 6 := by decide

theorem mem_placedPairs {S : Nat} {kl : Nat × Nat} (h : kl ∈ placedPairs S) :
    kl.1 < kl.2 ∧ kl.2 < 6 ∧ mem kl.1 S = true ∧ mem kl.2 S = true := by
  unfold placedPairs at h
  rw [List.mem_filter, Bool.and_eq_true] at h
  exact ⟨(pairs6_spec kl h.1).1, (pairs6_spec kl h.1).2, h.2.1, h.2.2⟩

theorem mem_bodies {S k : Nat} (h : k ∈ bodies S) : k < 6 ∧ mem k S = true := by
  unfold bodies at h
  rw [List.mem_filter, List.mem_range] at h
  exact h

theorem formVal_one {nv v : Nat} (hv : v < nv) (c : Int) (h : ℕ → ℚ) :
    formVal nv (form nv [(v, c)]) h = c * h v := by
  rw [formVal_form nv _ h (by simpa using hv)]
  simp

theorem formVal_two {nv v w : Nat} (hv : v < nv) (hw : w < nv) (c d : Int) (h : ℕ → ℚ) :
    formVal nv (form nv [(v, c), (w, d)]) h = c * h v + d * h w := by
  rw [formVal_form nv _ h (by simp [hv, hw])]
  simp

theorem ite_bool_cases {b : Bool} {p q : Prop} (h : if b = true then p else q) :
    (b = true → p) ∧ (b = false → q) := by
  cases b <;> simp_all

/-- The meets of two inserted bodies are nodes of both trees, with the heights of the exponents of the pair. -/
theorem meets_of_facts {Xz Xw : ExpTree} {P : Pair} {S : Nat} (hz : LevelFacts Xz P.tz S)
    (hw : LevelFacts Xw P.tw S) {k l : Nat} (hk : k < 6) (hl : l < 6) (hkl : k ≠ l) (hkS : mem k S = true)
    (hlS : mem l S = true) :
    ∃ Z ∈ P.tz.nodes, ∃ W ∈ P.tw.nodes, meets P k l = some (P.vz Z, P.vw W) ∧
      heightVec Xz Xw P (P.vz Z) = Xz.e k l ∧ heightVec Xz Xw P (P.vw W) = Xw.e k l := by
  obtain ⟨Z, hZ, hlz, hZe⟩ := hz.lca k l hk hl hkl hkS hlS
  obtain ⟨W, hW, hlw, hWe⟩ := hw.lca k l hk hl hkl hkS hlS
  refine ⟨Z, hZ, W, hW, ?_, ?_, ?_⟩
  · unfold meets
    rw [hlz, hlw]
    rfl
  · unfold Pair.vz
    rw [heightVec_vz hZ, hZe]
  · unfold Pair.vw
    rw [heightVec_vw hW, hWe]

/-! ## Tree rows -/

theorem treeRows_strict {X : ExpTree} {T : TS} {S : Nat} (hf : LevelFacts X T S) {off nv : Nat} {h : ℕ → ℚ}
    (hlt : ∀ C ∈ T.nodes, off + T.idx C < nv) (hval : ∀ C ∈ T.nodes, h (off + T.idx C) = X.hc C) :
    ∀ r ∈ treeRows T off nv, r.StrictHolds nv h := by
  intro r hr
  unfold treeRows at hr
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hr
  rcases hf.par C hC with ⟨hp, hge⟩ | ⟨Q, hQ, hp, hlt'⟩
  · simp only [hp]
    rw [strict_c0, formVal_one (hlt C hC), hval C hC]
    refine ⟨fun x hx => ?_, fun x hx => by simp at hx⟩
    cases hx
    push_cast
    linarith
  · simp only [hp]
    rw [strict_gt, formVal_two (hlt C hC) (hlt Q hQ), hval C hC, hval Q hQ]
    push_cast
    linarith

/-! ## Pair rows -/

theorem pairRowsAt_strict {D : Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {nv Z W k l : Nat} {h : ℕ → ℚ}
    (hZ : Z < nv) (hW : W < nv) (hkl : k < l) (hl : l < 6) (hhZ : h Z = Xz.e k l) (hhW : h W = Xw.e k l) :
    ∀ r ∈ pairRowsAt D nv Z W k l, r.StrictHolds nv h := by
  have h1 := hX.O1z k l hkl hl
  have h2 := hX.O1w k l hkl hl
  have e1 := hX.O2z k l hkl hl
  have e2 := hX.O2w k l hkl hl
  intro r hr
  unfold pairRowsAt at hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl
  · cases hs : D.zstroke k l
    · have hne : Xz.e k l + 3 * Xw.e k l ≠ 4 := fun he => by simp [e1.mp he] at hs
      have hlt := lt_of_le_of_ne h1 hne
      simp only [Bool.false_eq_true, ite_false]
      rw [strict_cpos (show (0 : Int) < 2 by norm_num), formVal_two hZ hW, hhZ, hhW]
      push_cast
      linarith
    · have he := e1.mpr hs
      simp only [ite_true]
      rw [strict_c0, formVal_two hZ hW, hhZ, hhW]
      constructor <;> intro x hx <;> cases hx <;> push_cast <;> linarith
  · cases hs : D.wstroke k l
    · have hne : 3 * Xz.e k l + Xw.e k l ≠ 4 := fun he => by simp [e2.mp he] at hs
      have hlt := lt_of_le_of_ne h2 hne
      simp only [Bool.false_eq_true, ite_false]
      rw [strict_cpos (show (0 : Int) < 2 by norm_num), formVal_two hZ hW, hhZ, hhW]
      push_cast
      linarith
    · have he := e2.mpr hs
      simp only [ite_true]
      rw [strict_c0, formVal_two hZ hW, hhZ, hhW]
      constructor <;> intro x hx <;> cases hx <;> push_cast <;> linarith

theorem pairRows_strict {D : Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {S : Nat} {P : Pair}
    (hz : LevelFacts Xz P.tz S) (hw : LevelFacts Xw P.tw S) :
    ∃ rows, pairRows D P S = some rows ∧ ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P) := by
  unfold pairRows
  refine foldr_inv _ (fun _ (rs : List Row) => ∀ r ∈ rs, r.StrictHolds P.nv (heightVec Xz Xw P)) [] _ (by simp) ?_
  intro kl hkl L rs hrs
  obtain ⟨hlt, hl6, hkS, hlS⟩ := mem_placedPairs hkl
  obtain ⟨Z, hZ, W, hW, hm, hZe, hWe⟩ := meets_of_facts hz hw (by omega) hl6 (by omega) hkS hlS
  refine ⟨pairRowsAt D P.nv (P.vz Z) (P.vw W) kl.1 kl.2 ++ rs, ?_, ?_⟩
  · dsimp only
    rw [hm]
    rfl
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact pairRowsAt_strict hX (vz_lt hZ) (vw_lt hW) hlt hl6 hZe hWe r hr
    · exact hrs r hr

/-! ## Position rows -/

theorem posRowsAt_strict {X : ExpTree} {T : TS} {S : Nat} (hf : LevelFacts X T S) {off nv : Nat} {h : ℕ → ℚ}
    (hlt : ∀ C ∈ T.nodes, off + T.idx C < nv) (hval : ∀ C ∈ T.nodes, h (off + T.idx C) = X.hc C)
    {k : Nat} (hk : k < 6) (hkS : mem k S = true) (hO : mem O S = true) {c : Bool}
    (hcirc : if X.T.sameLeaf k O then c = false else (X.e k O = -2 ↔ c = true)) :
    ∃ rs, posRowsAt T off nv c k = some rs ∧ ∀ r ∈ rs, r.StrictHolds nv h := by
  have hsame := hf.same k hk hkS hO
  obtain ⟨hc1, hc2⟩ := ite_bool_cases hcirc
  unfold posRowsAt
  cases hs : T.sameLeaf k O
  · have hc := hc2 (hsame ▸ hs)
    obtain ⟨m, hm, hlca, hme⟩ := hf.pos k hk hkS hO hs
    have hge := hc_ge_of_levelFacts hf m hm
    simp only [Bool.false_eq_true, ite_false]
    rw [hlca]
    cases c
    · refine ⟨_, rfl, ?_⟩
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      rw [strict_cneg (show (-2 : Int) < 0 by norm_num), formVal_one (hlt m hm), hval m hm]
      have hne : X.hc m ≠ -2 := fun he => by simpa using hc.mp (hme ▸ he)
      have := lt_of_le_of_ne hge (Ne.symm hne)
      push_cast
      linarith
    · refine ⟨_, rfl, ?_⟩
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      rw [strict_c0, formVal_one (hlt m hm), hval m hm, hme, hc.mpr rfl]
      constructor <;> intro x hx <;> cases hx <;> norm_num
  · have hc := hc1 (hsame ▸ hs)
    subst hc
    exact ⟨[], rfl, by simp⟩

theorem posRows_strict {D : Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {S : Nat} (hO : mem O S = true)
    {P : Pair} (hz : LevelFacts Xz P.tz S) (hw : LevelFacts Xw P.tw S) :
    ∃ rows, posRows D P S = some rows ∧ ∀ r ∈ rows, r.StrictHolds P.nv (heightVec Xz Xw P) := by
  unfold posRows
  simp only [hO, Bool.not_true, Bool.false_eq_true, ite_false]
  refine foldr_inv _ (fun _ (rs : List Row) => ∀ r ∈ rs, r.StrictHolds P.nv (heightVec Xz Xw P)) [] _ (by simp) ?_
  intro k hk L rs hrs
  obtain ⟨hk6, hkS⟩ := mem_bodies hk
  obtain ⟨rz, hrz, hzs⟩ := posRowsAt_strict hz (off := 0) (nv := P.nv) (h := heightVec Xz Xw P)
    (fun C hC => by rw [Nat.zero_add]; exact vz_lt hC) (fun C hC => by rw [Nat.zero_add]; exact heightVec_vz hC)
    hk6 hkS hO (hX.circ_z k hk6)
  obtain ⟨rw', hrw, hws⟩ := posRowsAt_strict hw (off := P.nz) (nv := P.nv) (h := heightVec Xz Xw P)
    (fun C hC => vw_lt hC) (fun C hC => heightVec_vw hC) hk6 hkS hO (hX.circ_w k hk6)
  refine ⟨rz ++ rw' ++ rs, ?_, ?_⟩
  · rw [hrz, hrw]
    rfl
  · intro r hr
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact hzs r hr
    · exact hws r hr
    · exact hrs r hr

/-! ## The threshold row -/

theorem foldl_add_eq {α : Type} (g : α → Int) : ∀ (L : List α) (a : Int),
    L.foldl (fun acc x => acc + g x) a = a + (L.map g).sum
  | [], a => by simp
  | x :: L, a => by
    rw [List.foldl_cons, foldl_add_eq g L, List.map_cons, List.sum_cons]
    ring

theorem sum_filter_split {α : Type} (L : List α) (p : α → Bool) (f : α → ℚ) :
    (L.map f).sum = ((L.filter p).map f).sum + ((L.filter fun a => !p a).map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    cases hp : p a <;> simp [hp, ih] <;> ring

theorem thresholdRow_strict {D : Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {S : Nat} {P : Pair}
    (hz : LevelFacts Xz P.tz S) (hw : LevelFacts Xw P.tw S) :
    ∃ th, thresholdRow D P S = some th ∧ th.StrictHolds P.nv (heightVec Xz Xw P) := by
  unfold thresholdRow
  refine bind_some_of (R := fun (cs : List (Nat × Int)) => (∀ ic ∈ cs, ic.1 < P.nv) ∧
      (cs.map fun ic => (ic.2 : ℚ) * heightVec Xz Xw P ic.1).sum =
        ((placedPairs S).map fun kl => Xz.e kl.1 kl.2 + Xw.e kl.1 kl.2).sum) ?_ ?_
  · refine foldr_inv _ (fun (L : List (Nat × Nat)) (cs : List (Nat × Int)) => (∀ ic ∈ cs, ic.1 < P.nv) ∧
      (cs.map fun ic => (ic.2 : ℚ) * heightVec Xz Xw P ic.1).sum =
        (L.map fun kl => Xz.e kl.1 kl.2 + Xw.e kl.1 kl.2).sum) [] _ ⟨by simp, by simp⟩ ?_
    intro kl hkl L cs ⟨hlt, hsum⟩
    obtain ⟨hlt', hl6, hkS, hlS⟩ := mem_placedPairs hkl
    obtain ⟨Z, hZ, W, hW, hm, hZe, hWe⟩ := meets_of_facts hz hw (by omega) hl6 (by omega) hkS hlS
    refine ⟨(P.vz Z, 1) :: (P.vw W, 1) :: cs, ?_, ?_, ?_⟩
    · dsimp only
      rw [hm]
      rfl
    · intro ic hic
      simp only [List.mem_cons] at hic
      rcases hic with rfl | rfl | hic
      · exact vz_lt hZ
      · exact vw_lt hW
      · exact hlt ic hic
    · simp only [List.map_cons, List.sum_cons, hsum, hZe, hWe]
      push_cast
      ring
  · intro cs ⟨hlt, hsum⟩
    refine ⟨_, rfl, ?_⟩
    rw [strict_c0, formVal_form _ _ _ hlt, hsum]
    refine ⟨fun x hx => by simp at hx, fun x hx => ?_⟩
    cases hx
    rw [foldl_add_eq, Int.cast_mul, Int.cast_add, Int.cast_list_sum, List.map_map]
    simp only [Int.cast_neg, Int.cast_ofNat, Int.cast_zero, zero_add]
    have hsplit : (pairs6.toList.map fun kl => xkl Xz Xw kl.1 kl.2).sum =
        ((pairs6.toList.filter fun kl => mem kl.1 S && mem kl.2 S).map fun kl => xkl Xz Xw kl.1 kl.2).sum +
        ((pairs6.toList.filter fun kl => !(mem kl.1 S && mem kl.2 S)).map fun kl => xkl Xz Xw kl.1 kl.2).sum :=
      sum_filter_split _ _ _
    have hell := hX.ell
    have hlb : ((pairs6.toList.filter fun kl => !(mem kl.1 S && mem kl.2 S)).map
        (Int.cast ∘ fun kl => lowerX D kl.1 kl.2)).sum ≤
        ((pairs6.toList.filter fun kl => !(mem kl.1 S && mem kl.2 S)).map fun kl => xkl Xz Xw kl.1 kl.2).sum := by
      refine List.sum_le_sum fun kl hkl => ?_
      have hp := pairs6_spec kl (List.mem_filter.mp hkl).1
      exact lowerX_le hX (by omega) (by omega) hp.2
    have hpl : ((placedPairs S).map fun kl => Xz.e kl.1 kl.2 + Xw.e kl.1 kl.2).sum =
        2 * ((pairs6.toList.filter fun kl => mem kl.1 S && mem kl.2 S).map fun kl => xkl Xz Xw kl.1 kl.2).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun kl _ => ?_
      unfold xkl
      ring
    rw [hpl]
    linarith

end L6.F2S.RS
