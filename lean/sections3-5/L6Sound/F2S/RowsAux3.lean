import L6Sound.F2S.RowsAux2

/-!
# Auxiliary facts for the rows of the specification search: the base identities

The identities of the specification (`bodyIdent`, `identU`, `identI`) restated with named pieces (equal to them by
definition), and their facts on a pair of complete trees (`IdFacts`): the names, labels and forced sets of
`identsMeta`, the values `2 ×` the exponents of `baseExps` of their terms, and forced sets equal to the argmin sets of
the exponents, with at least two elements. The lemmas are in the namespace `L6.F2S.RS`.
-/

namespace L6.F2S.RS

open L6.F2 (Diag Label IdName pairs6)

/-! ## Lists -/

theorem getElem!_map_of_lt {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) {l : List α} {n : Nat}
    (hn : n < l.length) : (l.map f)[n]! = f l[n]! := by
  rw [getElem!_pos (l.map f) n (by simpa using hn), getElem!_pos l n hn, List.getElem_map]

theorem getElem!_mem {α : Type} [Inhabited α] {l : List α} {n : Nat} (hn : n < l.length) : l[n]! ∈ l := by
  rw [getElem!_pos l n hn]
  exact List.getElem_mem hn

/-- Two lists with the same image: the images of their entries agree. -/
theorem map_eq_getElem! {α β γ : Type} [Inhabited α] [Inhabited β] {f : α → γ} {g : β → γ}
    {l1 : List α} {l2 : List β} (h : l1.map f = l2.map g) {n : Nat} (hn : n < l1.length) :
    f l1[n]! = g l2[n]! := by
  have hlen : l1.length = l2.length := by simpa using congrArg List.length h
  have hn2 : n < l2.length := hlen ▸ hn
  have h1 := congrArg (fun l => l[n]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hn2] at h1
  rw [getElem!_pos l1 n hn, getElem!_pos l2 n hn2]
  simpa using h1

theorem forall₂_append' {α β : Type} {R : α → β → Prop} {a c : List α} {b d : List β}
    (h1 : List.Forall₂ R a b) (h2 : List.Forall₂ R c d) : List.Forall₂ R (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => simpa using h2
  | cons hab _ ih => exact List.Forall₂.cons hab ih

theorem forall₂_getElem! {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ n < l1.length, R l1[n]! l2[n]!
  | _, _, .nil => fun n hn => by simp at hn
  | _, _, .cons hab hrest => fun n hn => by
    cases n with
    | zero => simpa using hab
    | succ n => simpa using forall₂_getElem! hrest n (by simpa using hn)

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hfg : ∀ a b, R a b → f a = g b) :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → l1.map f = l2.map g
  | _, _, .nil => rfl
  | _, _, .cons hab hrest => by rw [List.map_cons, List.map_cons, hfg _ _ hab, forall₂_map_eq hfg hrest]

theorem mapM_forall₂ {α β γ : Type} (g : α → Option β) (F : α → γ) (R : β → γ → Prop) :
    ∀ L : List α, (∀ a ∈ L, ∃ y, g a = some y ∧ R y (F a)) →
      ∃ ys, L.mapM g = some ys ∧ List.Forall₂ R ys (L.map F)
  | [], _ => ⟨[], rfl, List.Forall₂.nil⟩
  | a :: L, h => by
    obtain ⟨y, hy, hR⟩ := h a List.mem_cons_self
    obtain ⟨ys, hys, hF⟩ := mapM_forall₂ g F R L fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    refine ⟨y :: ys, ?_, List.Forall₂.cons hR hF⟩
    rw [List.mapM_cons, hy, hys]
    rfl

theorem mem_all (p : Nat) (hp : p < 7) : mem p all = true := by
  have : ∀ p < 7, mem p all = true := by decide
  exact this p hp

theorem pairs6_length : pairs6.toList.length = 15 := rfl

theorem pairs6_getElem! : ∀ n < 15, pairs6[n]! = pairs6.toList[n]! := by decide

theorem e_minmax (X : ExpTree) (i j : Nat) : X.e (min i j) (max i j) = X.e i j := by
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, e_comm]

/-- A body shares the leaf of `O` exactly when it is the body on the leaf of `O`. -/
theorem sameLeaf_iff (T : TS) {i : Nat} (hi : i < 6) : T.sameLeaf i O = true ↔ T.leafO = some i := by
  unfold TS.sameLeaf TS.lrep
  cases T.leafO with
  | none =>
    simp only [beq_iff_eq, reduceCtorEq, iff_false]
    unfold O
    omega
  | some k =>
    simp only [beq_iff_eq, Option.some.injEq, ite_self]
    by_cases hik : i = k
    · subst hik
      simp
    · simp only [hik, ite_false]
      unfold O
      omega

/-! ## Argmin sets -/

/-- The argmin set of a list whose entries are at least `m`, with equality exactly at the positions where `q`
holds, and `q` holds somewhere. -/
theorem argmin_eq_filter (E : List ℚ) (q : Nat → Bool) (m : ℚ)
    (hge : ∀ t < E.length, m ≤ E[t]!) (heq : ∀ t < E.length, E[t]! = m ↔ q t = true)
    (hne : (List.range E.length).filter q ≠ []) :
    argminPos E = (List.range E.length).filter q := by
  obtain ⟨t0, ht0⟩ := List.exists_mem_of_ne_nil _ hne
  rw [List.mem_filter, List.mem_range] at ht0
  have hm0 : E[t0]! = m := (heq t0 ht0.1).mpr ht0.2
  unfold argminPos
  refine List.filter_congr fun t ht => ?_
  rw [List.mem_range] at ht
  cases hq : q t
  · rw [decide_eq_false_iff_not]
    intro hall
    have h1 := hall t0 ht0.1
    have h2 : E[t]! ≠ m := fun he => by simp [(heq t ht).mp he] at hq
    have h3 := lt_of_le_of_ne (hge t ht) (Ne.symm h2)
    linarith
  · rw [decide_eq_true_iff]
    intro k hk
    rw [(heq t ht).mpr hq]
    exact hge k hk

/-- The same for a list of (label, value) pairs and a predicate on labels. -/
theorem argmin_of_pairs {α : Type} [Inhabited α] (PL : List (α × ℚ)) (p : α → Bool) (m : ℚ)
    (hge : ∀ x ∈ PL, m ≤ x.2) (heq : ∀ x ∈ PL, x.2 = m ↔ p x.1 = true)
    (hne : (List.range (PL.map Prod.fst).length).filter (fun t => p (PL.map Prod.fst)[t]!) ≠ []) :
    argminPos (PL.map Prod.snd) =
      (List.range (PL.map Prod.fst).length).filter (fun t => p (PL.map Prod.fst)[t]!) := by
  have hlen : (PL.map Prod.fst).length = (PL.map Prod.snd).length := by simp
  rw [hlen] at hne ⊢
  refine argmin_eq_filter _ _ m (fun t ht => ?_) (fun t ht => ?_) hne
  · rw [List.length_map] at ht
    rw [getElem!_map_of_lt Prod.snd ht]
    exact hge _ (getElem!_mem ht)
  · rw [List.length_map] at ht
    rw [getElem!_map_of_lt Prod.snd ht, getElem!_map_of_lt Prod.fst ht]
    exact heq _ (getElem!_mem ht)

theorem two_le_of_minTwice {l : List ℚ} (hl : MinTwice l) : 2 ≤ (argminPos l).length := by
  obtain ⟨i, j, hi, hj, hij, heq, hmin⟩ := hl
  have hmi : i ∈ argminPos l := by
    unfold argminPos
    rw [List.mem_filter, List.mem_range, decide_eq_true_iff]
    exact ⟨hi, hmin⟩
  have hmj : j ∈ argminPos l := by
    unfold argminPos
    rw [List.mem_filter, List.mem_range, decide_eq_true_iff]
    exact ⟨hj, fun k hk => by rw [← heq]; exact hmin k hk⟩
  calc 2 = ({i, j} : Finset Nat).card := (Finset.card_pair hij).symm
    _ ≤ (argminPos l).toFinset.card := Finset.card_le_card (by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [List.mem_toFinset]
        rcases hx with rfl | rfl
        exacts [hmi, hmj])
    _ ≤ (argminPos l).length := List.toFinset_card_le _

/-- The rows of a forced set that is the argmin set of the exponents hold strictly at heights where the terms have
the values `2 ×` the exponents. -/
theorem forcedRows_strict {nv : Nat} {h : ℕ → ℚ} {terms : List (Array Int)} {E : List ℚ} {f : List Nat}
    (hlen : terms.length = E.length) (hsize : ∀ t ∈ terms, t.size = nv)
    (hval : ∀ t < terms.length, formVal nv terms[t]! h = 2 * E[t]!) (hf : argminPos E = f) :
    ∀ r ∈ forcedRows terms f, r.StrictHolds nv h := by
  intro r hr
  have hmem : ∀ s, s ∈ argminPos E ↔ s < E.length ∧ ∀ k < E.length, E[s]! ≤ E[k]! := by
    intro s
    unfold argminPos
    rw [List.mem_filter, List.mem_range, decide_eq_true_iff]
  cases f with
  | nil => simp [forcedRows] at hr
  | cons f0 rest =>
    simp only [forcedRows, List.mem_map, List.mem_filter, List.mem_range, bne_iff_ne, ne_eq] at hr
    obtain ⟨t, ⟨htl, -⟩, rfl⟩ := hr
    obtain ⟨hf0l, hf0min⟩ := (hmem f0).mp (hf ▸ List.mem_cons_self)
    have hf0t : f0 < terms.length := hlen ▸ hf0l
    have htE : t < E.length := hlen ▸ htl
    have hd : formVal nv (fsub terms[t]! terms[f0]!) h = 2 * E[t]! - 2 * E[f0]! := by
      rw [formVal_sub (hsize _ (getElem!_mem htl)) (hsize _ (getElem!_mem hf0t)), hval t htl, hval f0 hf0t]
    cases hc : (f0 :: rest).contains t
    · simp only [Bool.false_eq_true, ite_false]
      rw [strict_gt, hd]
      have htn : t ∉ argminPos E := by
        rw [hf]
        intro hm
        have : (f0 :: rest).contains t = true := by simpa using hm
        rw [hc] at this
        exact absurd this (by decide)
      have hnall : ¬ ∀ k < E.length, E[t]! ≤ E[k]! := fun hall => htn ((hmem t).mpr ⟨htE, hall⟩)
      obtain ⟨k, hk, hlt⟩ : ∃ k, k < E.length ∧ E[k]! < E[t]! := by
        by_contra hcon
        exact hnall fun k hk => le_of_not_gt fun hlt => hcon ⟨k, hk, hlt⟩
      have := hf0min k hk
      linarith
    · simp only [ite_true]
      rw [strict_eq, hd]
      have htm : t ∈ argminPos E := by
        rw [hf]
        simpa using hc
      obtain ⟨-, htmin⟩ := (hmem t).mp htm
      have h1 := htmin f0 hf0l
      have h2 := hf0min t htE
      linarith

/-! ## The identities, restated -/

/-- Whether the label of a term of the equation of a body is forced: a circled position, a stroke of the colour. -/
def labelForced (D : Diag) (colour : Bool) : Label → Bool
  | .pos k => if colour then D.zc[k]! else D.wc[k]!
  | .cross k l => if colour then D.zstroke k l else D.wstroke k l
  | _ => false

/-- The position term of the equation of body `i` in a tree with the offset `off` of its variables. -/
def posTerms (T : TS) (off nv i : Nat) : List (Label × Array Int) :=
  if T.sameLeaf i O then [] else
    match T.lca i O with
    | some m => [(.pos i, form nv [(off + T.idx m, 2)])]
    | none => []

/-- One step of the fold of the cross terms of the equation of body `i`. -/
def crossStep (P : Pair) (colour : Bool) (i j : Nat) (acc : Option (List (Label × Array Int))) :
    Option (List (Label × Array Int)) := do
  let cs ← acc
  let (Z, W) ← meets P (min i j) (max i j)
  let f := if colour then form P.nv [(Z, -1), (W, -3)] else form P.nv [(Z, -3), (W, -1)]
  some ((Label.cross i j, f) :: cs)

/-- The equation of body `i` with the terms `all`. -/
def mkBody (D : Diag) (colour : Bool) (i : Nat) (all : List (Label × Array Int)) : SIdent :=
  let forced := (List.range all.length).filter fun t => labelForced D colour (all.map Prod.fst)[t]!
  { name := .S colour i, labels := all.map Prod.fst, terms := all.map Prod.snd,
    forced := if forced.isEmpty then none else some forced }

/-- The name, labels and forced set of the equation of body `i` with the labels `labs`. -/
def bodyMetaOf (D : Diag) (colour : Bool) (i : Nat) (labs : List Label) : IdName × List Label × Option (List Nat) :=
  let forced := (List.range labs.length).filter fun t => labelForced D colour labs[t]!
  (.S colour i, labs, if forced.isEmpty then none else some forced)

/-- The labels and exponents of the terms of the equation of body `i` at a pair of complete trees. -/
def bodyPL (Xz Xw : ExpTree) (colour : Bool) (i : Nat) : List (Label × ℚ) :=
  (if (if colour then Xz else Xw).T.sameLeaf i O then [] else [(Label.pos i, (if colour then Xz else Xw).e i O)]) ++
    ((List.range 6).filter (· != i)).map fun j =>
      (Label.cross i j, if colour then -(Xz.e i j + 3 * Xw.e i j) / 2 else -(3 * Xz.e i j + Xw.e i j) / 2)

/-- One step of the fold of the terms `p_kl` of `U = E`. -/
def uStep (P : Pair) (kl : Nat × Nat) (acc : Option (List (Label × Array Int))) :
    Option (List (Label × Array Int)) := do
  let cs ← acc
  let (Z, W) ← meets P kl.1 kl.2
  some ((Label.delta kl.1 kl.2, form P.nv [(Z, -1), (W, -1)]) :: cs)

/-- One step of the fold of the terms `z_kl w_kl` of `I = ME`. -/
def iStep (P : Pair) (kl : Nat × Nat) (acc : Option (List (Label × Array Int))) :
    Option (List (Label × Array Int)) := do
  let cs ← acc
  let (Z, W) ← meets P kl.1 kl.2
  some ((Label.zw kl.1 kl.2, form P.nv [(Z, 2), (W, 2)]) :: cs)

/-- The forced set of `U = E`. -/
def uForced (D : Diag) : List Nat :=
  (List.range 15).filter (fun pi => let kl := pairs6[pi]!; D.zstroke kl.1 kl.2 && D.wstroke kl.1 kl.2)
    |>.map (· + 1)

theorem bodyIdent_eq (D : Diag) (P : Pair) (colour : Bool) (i : Nat) : bodyIdent D P colour i =
    (((List.range 6).filter (· != i)).foldr (crossStep P colour i) (some [])).bind fun crosses =>
      some (mkBody D colour i
        (posTerms (if colour then P.tz else P.tw) (if colour then 0 else P.nz) P.nv i ++ crosses)) := by
  rfl

theorem bodyMeta_eq (D : Diag) (lo : Option Nat) (colour : Bool) (i : Nat) : bodyMeta D lo colour i =
    bodyMetaOf D colour i ((if lo = some i then [] else [Label.pos i]) ++
      ((List.range 6).filter (· != i)).map fun j => Label.cross i j) := by
  rfl

theorem identU_eq (D : Diag) (P : Pair) : identU D P = (pairs6.toList.foldr (uStep P) (some [])).bind fun ds =>
    some { name := .U, labels := ((Label.E, Array.replicate P.nv 0) :: ds).map Prod.fst,
           terms := ((Label.E, Array.replicate P.nv 0) :: ds).map Prod.snd,
           forced := if (uForced D).isEmpty then none else some (uForced D) } := by
  rfl

theorem uMeta_eq (D : Diag) : uMeta D = (.U, Label.E :: pairs6.toList.map (fun kl => Label.delta kl.1 kl.2),
    if (uForced D).isEmpty then none else some (uForced D)) := by
  rfl

theorem identI_eq (P : Pair) : identI P = (pairs6.toList.foldr (iStep P) (some [])).bind fun ds =>
    some { name := .I, labels := ((Label.E, Array.replicate P.nv 0) :: ds).map Prod.fst,
           terms := ((Label.E, Array.replicate P.nv 0) :: ds).map Prod.snd, forced := none } := by
  rfl

theorem mkBody_meta (D : Diag) (colour : Bool) (i : Nat) (all : List (Label × Array Int)) :
    ((mkBody D colour i all).name, (mkBody D colour i all).labels, (mkBody D colour i all).forced) =
      bodyMetaOf D colour i (all.map Prod.fst) := by
  unfold mkBody bodyMetaOf
  simp only [List.length_map]

theorem bodyMetaOf_forced {D : Diag} {colour : Bool} {i : Nat} {labs : List Label} {f : List Nat}
    (h : (bodyMetaOf D colour i labs).2.2 = some f) :
    f = (List.range labs.length).filter (fun t => labelForced D colour labs[t]!) ∧ f ≠ [] := by
  unfold bodyMetaOf at h
  dsimp only at h
  split_ifs at h with hemp
  cases h
  exact ⟨rfl, fun h0 => hemp (by rw [h0]; rfl)⟩

theorem bodyExps_eq (Xz Xw : ExpTree) (colour : Bool) (i : Nat) :
    bodyExps Xz Xw colour i = (bodyPL Xz Xw colour i).map Prod.snd := by
  unfold bodyExps bodyPL
  dsimp only
  rw [List.map_append, List.map_map]
  congr 1
  split_ifs <;> rfl

/-! ## The facts of an identity -/

/-- The facts about an identity of the specification at the heights `h`, given its exponents `em.1` and its names,
labels and forced set `em.2`. -/
def IdFacts (nv : Nat) (h : ℕ → ℚ) (id : SIdent) (em : List ℚ × (IdName × List Label × Option (List Nat))) :
    Prop :=
  (id.name, id.labels, id.forced) = em.2 ∧ id.terms.length = em.1.length ∧ id.labels.length = id.terms.length ∧
    (∀ t ∈ id.terms, t.size = nv) ∧ (∀ t < id.terms.length, formVal nv id.terms[t]! h = 2 * em.1[t]!) ∧
    ∀ f, id.forced = some f → 2 ≤ f.length ∧ argminPos em.1 = f

theorem terms_facts {nv : Nat} {h : ℕ → ℚ} {all : List (Label × Array Int)} {E : List ℚ}
    (hsize : ∀ x ∈ all, x.2.size = nv) (hval : all.map (fun x => formVal nv x.2 h) = E.map (2 * ·)) :
    (all.map Prod.snd).length = E.length ∧ (∀ t ∈ all.map Prod.snd, t.size = nv) ∧
      ∀ t < (all.map Prod.snd).length, formVal nv (all.map Prod.snd)[t]! h = 2 * E[t]! := by
  have hlen : all.length = E.length := by simpa using congrArg List.length hval
  refine ⟨by simpa using hlen, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    exact hsize x hx
  · have hval' : (all.map Prod.snd).map (fun t => formVal nv t h) = E.map (2 * ·) := by
      rw [List.map_map]
      exact hval
    exact map_eq_getElem! hval' ht

/-! ## The equations of the bodies -/

/-- The tree, the complete tree and the offset of the variables of one colour. -/
theorem side_facts {Xz Xw : ExpTree} {P : Pair} (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all)
    (colour : Bool) :
    LevelFacts (if colour then Xz else Xw) (if colour then P.tz else P.tw) all ∧
    (∀ C ∈ (if colour then P.tz else P.tw).nodes,
      (if colour then 0 else P.nz) + (if colour then P.tz else P.tw).idx C < P.nv) ∧
    (∀ C ∈ (if colour then P.tz else P.tw).nodes,
      heightVec Xz Xw P ((if colour then 0 else P.nz) + (if colour then P.tz else P.tw).idx C) =
        (if colour then Xz else Xw).hc C) := by
  cases colour
  · exact ⟨hw, fun C hC => vw_lt hC, fun C hC => heightVec_vw hC⟩
  · exact ⟨hz, fun C hC => by simpa using vz_lt hC, fun C hC => by simpa using heightVec_vz hC⟩

theorem posTerms_facts {X : ExpTree} {T : TS} (hf : LevelFacts X T all) {off nv : Nat} {h : ℕ → ℚ}
    (hlt : ∀ C ∈ T.nodes, off + T.idx C < nv) (hval : ∀ C ∈ T.nodes, h (off + T.idx C) = X.hc C)
    {i : Nat} (hi : i < 6) :
    (posTerms T off nv i).map Prod.fst = (if X.T.sameLeaf i O then [] else [Label.pos i]) ∧
    (∀ x ∈ posTerms T off nv i, x.2.size = nv) ∧
    (posTerms T off nv i).map (fun x => formVal nv x.2 h) = (if X.T.sameLeaf i O then [] else [2 * X.e i O]) := by
  have hsame := hf.same i hi (mem_all i (by omega)) (mem_all O (by decide))
  unfold posTerms
  cases hs : X.T.sameLeaf i O
  · rw [hs] at hsame
    obtain ⟨m, hm, hlca, hme⟩ := hf.pos i hi (mem_all i (by omega)) (mem_all O (by decide)) hsame
    simp only [hsame, hlca, Bool.false_eq_true, ite_false]
    refine ⟨rfl, ?_, ?_⟩
    · intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact form_size _ _
    · simp only [List.map_cons, List.map_nil]
      rw [formVal_one (hlt m hm), hval m hm, hme]
      norm_num
  · rw [hs] at hsame
    simp only [hsame, ite_true]
    exact ⟨rfl, by simp, rfl⟩

theorem crosses_facts {Xz Xw : ExpTree} {P : Pair} (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all)
    (colour : Bool) {i : Nat} (hi : i < 6) :
    ∃ cs, ((List.range 6).filter (· != i)).foldr (crossStep P colour i) (some []) = some cs ∧
      cs.map Prod.fst = ((List.range 6).filter (· != i)).map (fun j => Label.cross i j) ∧
      (∀ x ∈ cs, x.2.size = P.nv) ∧
      cs.map (fun x => formVal P.nv x.2 (heightVec Xz Xw P)) = ((List.range 6).filter (· != i)).map
        (fun j => 2 * (if colour then -(Xz.e i j + 3 * Xw.e i j) / 2 else -(3 * Xz.e i j + Xw.e i j) / 2)) := by
  refine foldr_inv (crossStep P colour i) (fun (L : List Nat) (cs : List (Label × Array Int)) =>
      cs.map Prod.fst = L.map (fun j => Label.cross i j) ∧ (∀ x ∈ cs, x.2.size = P.nv) ∧
      cs.map (fun x => formVal P.nv x.2 (heightVec Xz Xw P)) = L.map
        (fun j => 2 * (if colour then -(Xz.e i j + 3 * Xw.e i j) / 2 else -(3 * Xz.e i j + Xw.e i j) / 2)))
    [] _ ⟨rfl, by simp, rfl⟩ ?_
  intro j hj L cs ⟨h1, h2, h3⟩
  rw [List.mem_filter, List.mem_range, bne_iff_ne] at hj
  obtain ⟨hj6, hji⟩ := hj
  obtain ⟨Z, hZ, W, hW, hm, hZe, hWe⟩ := meets_of_facts hz hw (k := min i j) (l := max i j) (by omega) (by omega)
    (by omega) (mem_all _ (by omega)) (mem_all _ (by omega))
  rw [e_minmax] at hZe hWe
  refine ⟨(Label.cross i j, if colour then form P.nv [(P.vz Z, -1), (P.vw W, -3)]
    else form P.nv [(P.vz Z, -3), (P.vw W, -1)]) :: cs, ?_, ?_, ?_, ?_⟩
  · unfold crossStep
    rw [hm]
    rfl
  · simp only [List.map_cons, h1]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · cases colour <;> exact form_size _ _
    · exact h2 x hx
  · simp only [List.map_cons, h3]
    congr 1
    cases colour
    · simp only [Bool.false_eq_true, ite_false]
      rw [formVal_two (v := P.vz Z) (w := P.vw W) (vz_lt hZ) (vw_lt hW), hZe, hWe]
      push_cast
      ring
    · simp only [ite_true]
      rw [formVal_two (v := P.vz Z) (w := P.vw W) (vz_lt hZ) (vw_lt hW), hZe, hWe]
      push_cast
      ring

theorem bodyPL_facts {D : Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) (colour : Bool) {i : Nat} (hi : i < 6) :
    ∀ x ∈ bodyPL Xz Xw colour i, -2 ≤ x.2 ∧ (x.2 = -2 ↔ labelForced D colour x.1 = true) := by
  intro x hx
  unfold bodyPL at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · cases colour
    · simp only [Bool.false_eq_true, ite_false] at hx
      have hc := hX.circ_w i hi
      split_ifs at hx with hs
      · simp at hx
      · rw [List.mem_singleton] at hx
        subst hx
        simp only [hs, Bool.false_eq_true, ite_false] at hc
        simp only [labelForced, Bool.false_eq_true, ite_false]
        exact ⟨e_ge hX.gw hX.root_w i O, hc⟩
    · simp only [ite_true] at hx
      have hc := hX.circ_z i hi
      split_ifs at hx with hs
      · simp at hx
      · rw [List.mem_singleton] at hx
        subst hx
        simp only [hs, Bool.false_eq_true, ite_false] at hc
        simp only [labelForced, ite_true]
        exact ⟨e_ge hX.gz hX.root_z i O, hc⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_filter, List.mem_range, bne_iff_ne] at hj
    obtain ⟨hj6, hji⟩ := hj
    have hij : i ≠ j := Ne.symm hji
    cases colour
    · have h1 := O1w' hX hij hi hj6
      have e1 := O2w' hX hij hi hj6
      simp only [labelForced, Bool.false_eq_true, ite_false]
      refine ⟨by linarith, ?_⟩
      rw [← e1]
      constructor <;> intro h <;> linarith
    · have h1 := O1z' hX hij hi hj6
      have e1 := O2z' hX hij hi hj6
      simp only [labelForced, ite_true]
      refine ⟨by linarith, ?_⟩
      rw [← e1]
      constructor <;> intro h <;> linarith

theorem bodyExps_mem (Xz Xw : ExpTree) (colour : Bool) {i : Nat} (hi : i < 6) :
    bodyExps Xz Xw colour i ∈ baseExps Xz Xw := by
  unfold baseExps
  cases colour
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hi)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr hi)))

theorem bodyIdent_facts {D : Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {P : Pair}
    (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) (colour : Bool) {i : Nat} (hi : i < 6) :
    ∃ id, bodyIdent D P colour i = some id ∧
      IdFacts P.nv (heightVec Xz Xw P) id
        (bodyExps Xz Xw colour i, bodyMeta D (if colour then P.tz.leafO else P.tw.leafO) colour i) := by
  obtain ⟨cs, hcs, hc1, hc2, hc3⟩ := crosses_facts hz hw colour hi
  have hlo : (if colour then P.tz.leafO else P.tw.leafO) = (if colour then P.tz else P.tw).leafO := by
    cases colour <;> rfl
  have hE := bodyExps_eq Xz Xw colour i
  have hPL := bodyPL_facts hX colour hi
  have htw := hX.twice _ (bodyExps_mem Xz Xw colour hi)
  obtain ⟨hf, hlt, hval⟩ := side_facts hz hw colour
  rw [hlo, bodyIdent_eq, hcs, bodyMeta_eq]
  generalize (if colour then P.tz else P.tw) = T at hf hlt hval ⊢
  generalize (if colour then 0 else P.nz) = off at hlt hval ⊢
  obtain ⟨hp1, hp2, hp3⟩ := posTerms_facts hf hlt hval hi
  have hsl := sameLeaf_iff T hi
  have hsame := hf.same i hi (mem_all i (by omega)) (mem_all O (by decide))
  have hlab : (posTerms T off P.nv i ++ cs).map Prod.fst = (bodyPL Xz Xw colour i).map Prod.fst := by
    rw [List.map_append, hp1, hc1]
    unfold bodyPL
    rw [List.map_append, List.map_map]
    congr 1
    split_ifs <;> rfl
  have hlabM : ((if T.leafO = some i then [] else [Label.pos i]) ++
      ((List.range 6).filter (· != i)).map fun j => Label.cross i j) = (bodyPL Xz Xw colour i).map Prod.fst := by
    rw [← hlab, List.map_append, hp1, hc1]
    congr 1
    have hcond : T.leafO = some i ↔ (if colour then Xz else Xw).T.sameLeaf i O = true := by rw [← hsl, hsame]
    by_cases hs : (if colour then Xz else Xw).T.sameLeaf i O = true
    · simp [hs, hcond.mpr hs]
    · have hs' : ¬ T.leafO = some i := fun h => hs (hcond.mp h)
      simp [hs, hs']
  have hsizeAll : ∀ x ∈ posTerms T off P.nv i ++ cs, x.2.size = P.nv := fun x hx =>
    (List.mem_append.mp hx).elim (hp2 x) (hc2 x)
  have hvalAll : (posTerms T off P.nv i ++ cs).map (fun x => formVal P.nv x.2 (heightVec Xz Xw P)) =
      (bodyExps Xz Xw colour i).map (2 * ·) := by
    rw [List.map_append, hp3, hc3, hE]
    unfold bodyPL
    rw [List.map_append, List.map_append]
    congr 1
    · split_ifs <;> rfl
    · rw [List.map_map, List.map_map]
      rfl
  obtain ⟨ht1, ht2, ht3⟩ := terms_facts hsizeAll hvalAll
  refine ⟨mkBody D colour i (posTerms T off P.nv i ++ cs), rfl, ?_⟩
  unfold IdFacts
  refine ⟨?_, ht1, by simp [mkBody], ht2, ht3, ?_⟩
  · rw [mkBody_meta, hlab, hlabM]
  · intro f hf'
    have hmeta := congrArg (fun x => x.2.2) (mkBody_meta D colour i (posTerms T off P.nv i ++ cs))
    simp only at hmeta
    rw [hf', hlab] at hmeta
    obtain ⟨hfeq, hne⟩ := bodyMetaOf_forced hmeta.symm
    have hamin : argminPos (bodyExps Xz Xw colour i) = f := by
      rw [hE, hfeq]
      exact argmin_of_pairs _ (labelForced D colour) (-2) (fun x hx => (hPL x hx).1) (fun x hx => (hPL x hx).2)
        (hfeq ▸ hne)
    refine ⟨?_, hamin⟩
    have := two_le_of_minTwice htw
    rwa [hamin] at this

/-! ## `U = E` and `I = ME` -/

theorem uds_facts {Xz Xw : ExpTree} {P : Pair} (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) :
    ∃ ds, pairs6.toList.foldr (uStep P) (some []) = some ds ∧
      ds.map Prod.fst = pairs6.toList.map (fun kl => Label.delta kl.1 kl.2) ∧ (∀ x ∈ ds, x.2.size = P.nv) ∧
      ds.map (fun x => formVal P.nv x.2 (heightVec Xz Xw P)) =
        pairs6.toList.map (fun kl => 2 * -xkl Xz Xw kl.1 kl.2) := by
  refine foldr_inv (uStep P) (fun (L : List (Nat × Nat)) (ds : List (Label × Array Int)) =>
      ds.map Prod.fst = L.map (fun kl => Label.delta kl.1 kl.2) ∧ (∀ x ∈ ds, x.2.size = P.nv) ∧
      ds.map (fun x => formVal P.nv x.2 (heightVec Xz Xw P)) = L.map (fun kl => 2 * -xkl Xz Xw kl.1 kl.2))
    [] _ ⟨rfl, by simp, rfl⟩ ?_
  intro kl hkl L ds ⟨h1, h2, h3⟩
  have hp := pairs6_spec kl hkl
  obtain ⟨Z, hZ, W, hW, hm, hZe, hWe⟩ := meets_of_facts hz hw (k := kl.1) (l := kl.2) (by omega) hp.2 (by omega)
    (mem_all _ (by omega)) (mem_all _ (by omega))
  refine ⟨(Label.delta kl.1 kl.2, form P.nv [(P.vz Z, -1), (P.vw W, -1)]) :: ds, ?_, ?_, ?_, ?_⟩
  · unfold uStep
    rw [hm]
    rfl
  · simp only [List.map_cons, h1]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact form_size _ _
    · exact h2 x hx
  · simp only [List.map_cons, h3]
    congr 1
    rw [formVal_two (v := P.vz Z) (w := P.vw W) (vz_lt hZ) (vw_lt hW), hZe, hWe]
    unfold xkl
    push_cast
    ring

theorem zws_facts {Xz Xw : ExpTree} {P : Pair} (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) :
    ∃ ds, pairs6.toList.foldr (iStep P) (some []) = some ds ∧
      ds.map Prod.fst = pairs6.toList.map (fun kl => Label.zw kl.1 kl.2) ∧ (∀ x ∈ ds, x.2.size = P.nv) ∧
      ds.map (fun x => formVal P.nv x.2 (heightVec Xz Xw P)) =
        pairs6.toList.map (fun kl => 2 * (2 * xkl Xz Xw kl.1 kl.2)) := by
  refine foldr_inv (iStep P) (fun (L : List (Nat × Nat)) (ds : List (Label × Array Int)) =>
      ds.map Prod.fst = L.map (fun kl => Label.zw kl.1 kl.2) ∧ (∀ x ∈ ds, x.2.size = P.nv) ∧
      ds.map (fun x => formVal P.nv x.2 (heightVec Xz Xw P)) = L.map (fun kl => 2 * (2 * xkl Xz Xw kl.1 kl.2)))
    [] _ ⟨rfl, by simp, rfl⟩ ?_
  intro kl hkl L ds ⟨h1, h2, h3⟩
  have hp := pairs6_spec kl hkl
  obtain ⟨Z, hZ, W, hW, hm, hZe, hWe⟩ := meets_of_facts hz hw (k := kl.1) (l := kl.2) (by omega) hp.2 (by omega)
    (mem_all _ (by omega)) (mem_all _ (by omega))
  refine ⟨(Label.zw kl.1 kl.2, form P.nv [(P.vz Z, 2), (P.vw W, 2)]) :: ds, ?_, ?_, ?_, ?_⟩
  · unfold iStep
    rw [hm]
    rfl
  · simp only [List.map_cons, h1]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact form_size _ _
    · exact h2 x hx
  · simp only [List.map_cons, h3]
    congr 1
    rw [formVal_two (v := P.vz Z) (w := P.vw W) (vz_lt hZ) (vw_lt hW), hZe, hWe]
    unfold xkl
    push_cast
    ring

theorem uExps_length (Xz Xw : ExpTree) : (uExps Xz Xw).length = 16 := by
  unfold uExps
  rw [List.length_cons, List.length_map, pairs6_length]

theorem uForced_eq (D : Diag) : uForced D = (List.range 16).filter fun t =>
    t != 0 && (D.zstroke (pairs6[t - 1]!).1 (pairs6[t - 1]!).2 && D.wstroke (pairs6[t - 1]!).1 (pairs6[t - 1]!).2) := by
  rw [List.range_succ_eq_map, List.filter_cons_of_neg (by simp), List.filter_map]
  unfold uForced
  have hfun : (fun x => x + 1 : Nat → Nat) = Nat.succ := rfl
  rw [hfun]
  congr 1

theorem uForced_facts {D : Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {f : List Nat}
    (hf : (if (uForced D).isEmpty then none else some (uForced D)) = some f) :
    2 ≤ f.length ∧ argminPos (uExps Xz Xw) = f := by
  split_ifs at hf with hemp
  cases hf
  have hne : uForced D ≠ [] := fun h0 => hemp (by rw [h0]; rfl)
  have hamin : argminPos (uExps Xz Xw) = uForced D := by
    rw [uForced_eq] at hne ⊢
    rw [← uExps_length Xz Xw] at hne ⊢
    refine argmin_eq_filter _ _ (-1) (fun t ht => ?_) (fun t ht => ?_) hne
    · rw [uExps_length] at ht
      rcases t with _ | n
      · simp [uExps]
      · have hn : n < 15 := by omega
        have hkl := pairs6_spec _ (getElem!_mem (l := pairs6.toList) (by rw [pairs6_length]; exact hn))
        have hx := x_le_one hX (k := (pairs6.toList[n]!).1) (l := (pairs6.toList[n]!).2) (by omega) (by omega)
          hkl.2
        unfold uExps
        rw [List.getElem!_cons_succ, getElem!_map_of_lt _ (by rw [pairs6_length]; exact hn)]
        linarith
    · rw [uExps_length] at ht
      rcases t with _ | n
      · simp [uExps]
      · have hn : n < 15 := by omega
        have hkl := pairs6_spec _ (getElem!_mem (l := pairs6.toList) (by rw [pairs6_length]; exact hn))
        unfold uExps
        rw [List.getElem!_cons_succ, getElem!_map_of_lt _ (by rw [pairs6_length]; exact hn)]
        have h1 : n + 1 - 1 = n := by omega
        have h2 : (n + 1 != 0) = true := by simp
        rw [h1, h2, Bool.true_and, pairs6_getElem! n hn, ← x_eq_one_iff hX (by omega) (by omega) hkl.2]
        constructor <;> intro h <;> linarith
  refine ⟨?_, hamin⟩
  have := two_le_of_minTwice (hX.twice (uExps Xz Xw) (by simp [baseExps]))
  rwa [hamin] at this

theorem identU_facts {D : Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) {P : Pair}
    (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) :
    ∃ id, identU D P = some id ∧ IdFacts P.nv (heightVec Xz Xw P) id (uExps Xz Xw, uMeta D) := by
  obtain ⟨ds, hds, h1, h2, h3⟩ := uds_facts hz hw
  have hsizeAll : ∀ x ∈ (Label.E, Array.replicate P.nv (0 : Int)) :: ds, x.2.size = P.nv := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · exact h2 x hx
  have hvalAll : ((Label.E, Array.replicate P.nv (0 : Int)) :: ds).map
      (fun x => formVal P.nv x.2 (heightVec Xz Xw P)) = (uExps Xz Xw).map (2 * ·) := by
    unfold uExps
    rw [List.map_cons, List.map_cons, h3, formVal_replicate, List.map_map, mul_zero]
    rfl
  obtain ⟨ht1, ht2, ht3⟩ := terms_facts hsizeAll hvalAll
  rw [identU_eq, hds]
  refine ⟨_, rfl, ?_⟩
  unfold IdFacts
  refine ⟨?_, ht1, by simp, ht2, ht3, fun f hf => uForced_facts hX hf⟩
  simp only [uMeta_eq, List.map_cons, h1]

theorem identI_facts {Xz Xw : ExpTree} {P : Pair} (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) :
    ∃ id, identI P = some id ∧ IdFacts P.nv (heightVec Xz Xw P) id (iExps Xz Xw, iMeta) := by
  obtain ⟨ds, hds, h1, h2, h3⟩ := zws_facts hz hw
  have hsizeAll : ∀ x ∈ (Label.E, Array.replicate P.nv (0 : Int)) :: ds, x.2.size = P.nv := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · exact h2 x hx
  have hvalAll : ((Label.E, Array.replicate P.nv (0 : Int)) :: ds).map
      (fun x => formVal P.nv x.2 (heightVec Xz Xw P)) = (iExps Xz Xw).map (2 * ·) := by
    unfold iExps
    rw [List.map_cons, List.map_cons, h3, formVal_replicate, List.map_map, mul_zero]
    rfl
  obtain ⟨ht1, ht2, ht3⟩ := terms_facts hsizeAll hvalAll
  rw [identI_eq, hds]
  refine ⟨_, rfl, ?_⟩
  unfold IdFacts
  refine ⟨?_, ht1, by simp, ht2, ht3, fun f hf => by cases hf⟩
  simp only [iMeta, List.map_cons, h1]

/-! ## All base identities -/

/-- The exponents and the names, labels and forced sets of the fourteen base identities. -/
def baseEM (D : Diag) (Xz Xw : ExpTree) (lz lw : Option Nat) :
    List (List ℚ × (IdName × List Label × Option (List Nat))) :=
  (List.range 6).map (fun a => (bodyExps Xz Xw true a, bodyMeta D lz true a)) ++
    (List.range 6).map (fun a => (bodyExps Xz Xw false a, bodyMeta D lw false a)) ++
    [(uExps Xz Xw, uMeta D), (iExps Xz Xw, iMeta)]

theorem baseEM_fst (D : Diag) (Xz Xw : ExpTree) (lz lw : Option Nat) :
    (baseEM D Xz Xw lz lw).map Prod.fst = baseExps Xz Xw := by
  unfold baseEM baseExps
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  rfl

theorem baseEM_snd (D : Diag) (Xz Xw : ExpTree) (lz lw : Option Nat) :
    (baseEM D Xz Xw lz lw).map Prod.snd = identsMeta D lz lw := by
  unfold baseEM identsMeta
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  rfl

theorem idents_facts {D : Diag} {Xz Xw : ExpTree} (hX : Cond D Xz Xw) (P : Pair)
    (hz : LevelFacts Xz P.tz all) (hw : LevelFacts Xw P.tw all) :
    ∃ ids, idents D P = some ids ∧
      List.Forall₂ (IdFacts P.nv (heightVec Xz Xw P)) ids (baseEM D Xz Xw P.tz.leafO P.tw.leafO) := by
  obtain ⟨zs, hzs, hzF⟩ := mapM_forall₂ (bodyIdent D P true)
    (fun a => (bodyExps Xz Xw true a, bodyMeta D P.tz.leafO true a)) (IdFacts P.nv (heightVec Xz Xw P))
    (List.range 6) fun a ha => bodyIdent_facts hX hz hw true (List.mem_range.mp ha)
  obtain ⟨ws, hws, hwF⟩ := mapM_forall₂ (bodyIdent D P false)
    (fun a => (bodyExps Xz Xw false a, bodyMeta D P.tw.leafO false a)) (IdFacts P.nv (heightVec Xz Xw P))
    (List.range 6) fun a ha => bodyIdent_facts hX hz hw false (List.mem_range.mp ha)
  obtain ⟨u, hu, huF⟩ := identU_facts hX hz hw
  obtain ⟨ii, hii, hiF⟩ := identI_facts hz hw
  refine ⟨zs ++ ws ++ [u, ii], ?_, ?_⟩
  · unfold idents
    rw [hzs, hws, hu, hii]
    rfl
  · unfold baseEM
    exact forall₂_append' (forall₂_append' hzF hwF) (List.Forall₂.cons huF (List.Forall₂.cons hiF List.Forall₂.nil))

end L6.F2S.RS
