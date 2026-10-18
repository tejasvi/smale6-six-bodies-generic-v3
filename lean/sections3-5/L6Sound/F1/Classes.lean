import L6Sound.F1.Complete
import L6Sound.F1.Orbit

/-!
# From the checks to the statement of Proposition 3.1

* `list_of_perm`, `perm_of_list`: if `checkPerms n` holds, the lists of `perms n` are exactly the permutations of
  `0, …, n - 1` (each list gives one, and by counting every permutation is given by a list), so `orbitList n d`
  enumerates `orbit n d` (`mem_orbitList_iff`);
* `canonKey_actP`: **the canonical key is invariant on orbits**; `canonKey_spec`: it is the least key of the orbit;
* `classification_of_check`: the statement of Proposition 3.1 for `n ≤ 6` bodies from `checkAll n … = true`: the
  number of labelled diagrams satisfying the rules, the number of kind assignments satisfying (E2), (E3), (E6), and
  the decomposition of the set of labelled diagrams satisfying the rules into the pairwise disjoint orbits of the
  representatives listed in the class file, with the listed orbit sizes, each representative having the least key of
  its orbit, in increasing order of the keys.
-/

namespace L6F1

/-! ## The labelled diagrams as a finite set -/

/-- **The labelled diagrams on `n` bodies**: the codes `e < 4 ^ numPairs n`, `zc, wc < 2 ^ n`. (Irreducible, so that
the elaborator never tries to evaluate this large finite set.) -/
@[irreducible] def allDiagrams (n : ℕ) : Finset Diagram :=
  ((Finset.range (4 ^ numPairs n) ×ˢ Finset.range (2 ^ n)) ×ˢ Finset.range (2 ^ n)).image
    fun x => ⟨x.1.1, x.1.2, x.2⟩

theorem mem_allDiagrams {n : ℕ} {d : Diagram} : d ∈ allDiagrams n ↔ inRange n d = true := by
  obtain ⟨e, zc, wc⟩ := d
  unfold allDiagrams
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, inRange, Bool.and_eq_true,
    decide_eq_true_eq, Prod.exists, Diagram.mk.injEq]
  constructor
  · rintro ⟨a, b, c, ⟨⟨ha, hb⟩, hc⟩, rfl, rfl, rfl⟩
    exact ⟨⟨ha, hb⟩, hc⟩
  · rintro ⟨⟨ha, hb⟩, hc⟩
    exact ⟨e, zc, wc, ⟨⟨ha, hb⟩, hc⟩, rfl, rfl, rfl⟩

/-! ## Codes of diagrams -/

theorem dcode_inj {n : ℕ} {d d' : Diagram} (hd : inRange n d = true) (hd' : inRange n d' = true)
    (h : dcode n d = dcode n d') : d = d' := by
  obtain ⟨e, zc, wc⟩ := d
  obtain ⟨e', zc', wc'⟩ := d'
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hd hd'
  simp only [dcode] at h
  have hP : 0 < 4 ^ numPairs n := by positivity
  have hQ : 0 < 2 ^ n := by positivity
  have h1 : e = e' := by
    have := congrArg (· % 4 ^ numPairs n) h
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd.1.1, Nat.mod_eq_of_lt hd'.1.1] using this
  subst h1
  have h2 : zc + 2 ^ n * wc = zc' + 2 ^ n * wc' := Nat.eq_of_mul_eq_mul_left hP (Nat.add_left_cancel h)
  have h3 : zc = zc' := by
    have := congrArg (· % 2 ^ n) h2
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd.1.2, Nat.mod_eq_of_lt hd'.1.2] using this
  subst h3
  rw [Nat.eq_of_mul_eq_mul_left hQ (Nat.add_left_cancel h2)]

/-! ## The permutations -/

theorem fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fact, ih, Nat.factorial_succ]

theorem checkPerms_spec {n : ℕ} (h : checkPerms n = true) :
    (perms n).length = n.factorial ∧ (perms n).Nodup ∧ ∀ p ∈ perms n, p.Perm (List.range n) := by
  simp only [checkPerms, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by rw [h1, fact_eq], (nodup_of_strictSorted_sortNat h3).of_map _, fun p hp => ?_⟩
  have := h2 p hp
  simp only [isPermOf, beq_iff_eq] at this
  rw [← this]
  exact (sortNat_perm p).symm

/-- A list that is a permutation of `0, …, n - 1` gives the permutation `σ` with `σ⁻¹ k = p[k]`. -/
theorem perm_of_list {n : ℕ} {p : List ℕ} (hp : p.Perm (List.range n)) :
    ∃ σ : Equiv.Perm (Fin n), ∀ k < n, invMap σ k = p.getD k k := by
  have hlen : p.length = n := by rw [hp.length_eq, List.length_range]
  have hnd : p.Nodup := hp.nodup_iff.mpr List.nodup_range
  have hlt : ∀ x ∈ p, x < n := fun x hx => List.mem_range.mp (hp.mem_iff.mp hx)
  let f : Fin n → Fin n := fun k => ⟨p[k.1]'(by omega), hlt _ (List.getElem_mem _)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have : p[a.1]'(by omega) = p[b.1]'(by omega) := congrArg Fin.val hab
    exact Fin.ext ((hnd.getElem_inj_iff).mp this)
  have hb : Function.Bijective f := Finite.injective_iff_bijective.mp hf
  refine ⟨(Equiv.ofBijective f hb).symm, fun k hk => ?_⟩
  simp only [invMap, hk, dite_eq_left, Equiv.symm_symm, Equiv.ofBijective_apply, f]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- **Every permutation of the bodies is given by a list of `perms n`** (by counting: `perms n` has `n!` distinct
entries, each a permutation). -/
theorem list_of_perm {n : ℕ} (h : checkPerms n = true) (σ : Equiv.Perm (Fin n)) :
    ∃ p ∈ perms n, ∀ k < n, invMap σ k = p.getD k k := by
  obtain ⟨hl, hnd, hp⟩ := checkPerms_spec h
  let F : Equiv.Perm (Fin n) → List ℕ := fun τ => (List.range n).map (invMap τ)
  have hF : Function.Injective F := by
    intro a b hab
    have h1 : ∀ k < n, invMap a k = invMap b k := by
      intro k hk
      have := congrArg (fun l => l[k]?) hab
      simpa [F, List.getElem?_map, hk] using this
    have h2 : a.symm = b.symm := by
      ext x
      have := h1 x.1 x.2
      simpa [invMap, x.2] using this
    have := congrArg Equiv.symm h2
    simpa using this
  have hsub : (perms n).toFinset ⊆ Finset.univ.image F := by
    intro p hp'
    have hpp := hp p (List.mem_toFinset.mp hp')
    obtain ⟨τ, hτ⟩ := perm_of_list hpp
    have hlen : p.length = n := by rw [hpp.length_eq, List.length_range]
    refine Finset.mem_image.mpr ⟨τ, Finset.mem_univ _, ?_⟩
    apply List.ext_getElem
    · simp [F, hlen]
    · intro k h1 h2
      have hk : k < n := by simpa [F] using h1
      simp only [F, List.getElem_map, List.getElem_range]
      rw [hτ k hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  have hcard : (Finset.univ.image F).card ≤ (perms n).toFinset.card := by
    rw [Finset.card_image_of_injective _ hF, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      List.toFinset_card_of_nodup hnd, hl]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : F σ ∈ (perms n).toFinset := by
    rw [heq]
    exact Finset.mem_image_of_mem F (Finset.mem_univ σ)
  refine ⟨F σ, List.mem_toFinset.mp hmem, fun k hk => ?_⟩
  simp [F, List.getD_eq_getElem?_getD, hk]

theorem act_eq_actP {n : ℕ} (hn : n ≤ 6) {p : List ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ∀ k < n, invMap σ k = p.getD k k) (s : Bool) (d : Diagram) : act n p s d = actP n σ s d := by
  simp only [act, actP]
  rw [relabel_congr (fun k hk => (h k hk).symm) hn d]

theorem inRange_act (n : ℕ) (p : List ℕ) (s : Bool) (d : Diagram) : inRange n (act n p s d) = true := by
  simp only [act]
  cases s
  · exact inRange_relabel _ _ _
  · exact inRange_swap (inRange_relabel _ _ _)

/-- **The list `orbitList n d` enumerates the orbit of `d`.** -/
theorem mem_orbitList_iff {n : ℕ} (hn : n ≤ 6) (hp : checkPerms n = true) {d d' : Diagram} :
    d' ∈ orbitList n d ↔ d' ∈ orbit n d := by
  unfold orbitList orbit
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp', h⟩
    obtain ⟨σ, hσ⟩ := perm_of_list ((checkPerms_spec hp).2.2 p hp')
    rcases h with rfl | rfl
    · exact ⟨σ, false, act_eq_actP hn hσ false d⟩
    · exact ⟨σ, true, act_eq_actP hn hσ true d⟩
  · rintro ⟨σ, s, rfl⟩
    obtain ⟨p, hp', hσ⟩ := list_of_perm hp σ
    refine ⟨p, hp', ?_⟩
    cases s
    · exact Or.inl (act_eq_actP hn hσ false d).symm
    · exact Or.inr (act_eq_actP hn hσ true d).symm

theorem inRange_of_mem_orbitList {n : ℕ} {d d' : Diagram} (h : d' ∈ orbitList n d) : inRange n d' = true := by
  unfold orbitList at h
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨p, -, h | h⟩ := h <;> rw [h] <;> exact inRange_act _ _ _ _

theorem mem_orbitCodes {n : ℕ} {r : Diagram} {c : ℕ} : c ∈ orbitCodes n r ↔ ∃ d ∈ orbitList n r, dcode n d = c := by
  unfold orbitCodes
  rw [mem_dedupSorted, mem_sortNat, List.mem_map]

/-- The number of elements of an orbit is the length of its list of codes. -/
theorem ncard_orbit {n : ℕ} (hn : n ≤ 6) (hp : checkPerms n = true) {r : Diagram}
    (hs : strictSorted (orbitCodes n r) = true) : (orbit n r).ncard = (orbitCodes n r).length := by
  have e1 : orbit n r = ↑((orbitList n r).toFinset) := by
    ext d
    simp [mem_orbitList_iff hn hp]
  have e2 : (orbitList n r).toFinset.image (dcode n) = (orbitCodes n r).toFinset := by
    ext c
    simp [mem_orbitCodes]
  have hinj : Set.InjOn (dcode n) ↑((orbitList n r).toFinset) := by
    intro a ha b hb hab
    exact dcode_inj (inRange_of_mem_orbitList (List.mem_toFinset.mp ha))
      (inRange_of_mem_orbitList (List.mem_toFinset.mp hb)) hab
  rw [e1, Set.ncard_coe_finset, ← Finset.card_image_of_injOn hinj, e2,
    List.toFinset_card_of_nodup (nodup_of_strictSorted hs)]

/-! ## The canonical key -/

theorem foldl_min_spec {α : Type} (f : α → ℕ) : ∀ (l : List α) (a : ℕ),
    l.foldl (fun m x => min m (f x)) a ≤ a ∧ (∀ x ∈ l, l.foldl (fun m x => min m (f x)) a ≤ f x) ∧
      (l.foldl (fun m x => min m (f x)) a = a ∨ ∃ x ∈ l, l.foldl (fun m x => min m (f x)) a = f x)
  | [], a => by simp
  | y :: l, a => by
    obtain ⟨h1, h2, h3⟩ := foldl_min_spec f l (min a (f y))
    simp only [List.foldl_cons]
    refine ⟨le_trans h1 (min_le_left _ _), fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact le_trans h1 (min_le_right _ _)
      · exact h2 x hx
    · rcases h3 with h | ⟨x, hx, h⟩
      · rw [h]
        rcases min_choice a (f y) with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨y, List.mem_cons_self, h'⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h⟩

/-- **The canonical key is the least key of the orbit**: it is at most the key of every element of the orbit, and it
is the key of an element of the orbit. -/
theorem canonKey_spec {n : ℕ} (hn : n ≤ 6) (hp : checkPerms n = true) (lex : Bool) {d : Diagram}
    (hd : inRange n d = true) :
    (∀ x ∈ orbit n d, canonKey n lex d ≤ keyOf n lex x) ∧ ∃ x ∈ orbit n d, canonKey n lex d = keyOf n lex x := by
  obtain ⟨-, h2, h3⟩ := foldl_min_spec (keyOf n lex) (orbitList n d) (keyOf n lex d)
  refine ⟨fun x hx => h2 x ((mem_orbitList_iff hn hp).mpr hx), ?_⟩
  rcases h3 with h | ⟨x, hx, h⟩
  · exact ⟨d, self_mem_orbit hn hd, h⟩
  · exact ⟨x, (mem_orbitList_iff hn hp).mp hx, h⟩

/-- **The canonical key is invariant on orbits.** -/
theorem canonKey_actP {n : ℕ} (hn : n ≤ 6) (hp : checkPerms n = true) (lex : Bool) {d : Diagram}
    (hd : inRange n d = true) (σ : Equiv.Perm (Fin n)) (s : Bool) :
    canonKey n lex (actP n σ s d) = canonKey n lex d := by
  have ho := orbit_actP hn d σ s
  obtain ⟨a1, x, hx, hxa⟩ := canonKey_spec hn hp lex (inRange_actP σ s d)
  obtain ⟨b1, y, hy, hyb⟩ := canonKey_spec hn hp lex hd
  rw [ho] at a1 hx
  apply le_antisymm
  · rw [hyb]
    exact a1 y hy
  · rw [hxa]
    exact b1 x hx

/-- The canonical key is constant on each orbit. -/
theorem canonKey_eq_of_mem_orbit {n : ℕ} (hn : n ≤ 6) (hp : checkPerms n = true) (lex : Bool) {d d' : Diagram}
    (hd : inRange n d = true) (h : d' ∈ orbit n d) : canonKey n lex d' = canonKey n lex d := by
  obtain ⟨σ, s, rfl⟩ := h
  exact canonKey_actP hn hp lex hd σ s

/-! ## The checks -/

theorem checkEdges_spec {n numEdge : ℕ} {EL : List ℕ} (h : checkEdges n numEdge EL = true) :
    EL.length = numEdge ∧ EL.Nodup ∧ ∀ e ∈ EL, e < 4 ^ numPairs n ∧ edgeRules n e = true := by
  simp only [checkEdges, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, nodup_of_strictSorted_sortNat h2, h3⟩

theorem checkSearch_spec {n numLabelled : ℕ} {L : List Diagram} (h : checkSearch n numLabelled L = true) :
    L.length = numLabelled ∧ (L.map (dcode n)).Nodup ∧ ∀ d ∈ L, inRange n d = true ∧ okRules n d = true := by
  simp only [checkSearch, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, nodup_of_strictSorted_sortNat h2, h3⟩

theorem checkClass_spec {n : ℕ} {lex : Bool} {x : Diagram × ℕ} (h : checkClass n lex x = true) :
    inRange n x.1 = true ∧ strictSorted (orbitCodes n x.1) = true ∧ (orbitCodes n x.1).length = x.2 ∧
      ∀ d ∈ orbitList n x.1, keyOf n lex x.1 ≤ keyOf n lex d := by
  simp only [checkClass, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem checkFile_spec {n : ℕ} {lex : Bool} {json : String} {numLabelled numClasses : ℕ} {L : List Diagram}
    (h : checkFile n lex json numLabelled numClasses L = true) :
    ∃ cls : List (Diagram × ℕ), parseFile json = some (n, numLabelled, cls) ∧
      renderFile n numLabelled cls = json ∧ cls.length = numClasses ∧ (∀ x ∈ cls, checkClass n lex x = true) ∧
      strictSorted (cls.map fun x => keyOf n lex x.1) = true ∧
      sortNat (cls.flatMap fun x => orbitCodes n x.1) = sortNat (L.map (dcode n)) := by
  unfold checkFile at h
  split at h
  · exact absurd h (by simp)
  · rename_i n' total cls hparse
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    subst h2 h3
    exact ⟨cls, hparse, h1, h4, h5, h6, h7⟩

theorem checkAll_spec {n : ℕ} {lex : Bool} {json : String} {numEdge numLabelled numClasses : ℕ}
    (h : checkAll n lex json numEdge numLabelled numClasses = true) :
    checkEdges n numEdge (edgeLeaves n) = true ∧ checkSearch n numLabelled (search n) = true ∧
      checkPerms n = true ∧ checkFile n lex json numLabelled numClasses (search n) = true := by
  simp only [checkAll, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-! ## Proposition 3.1 from the checks -/

/-- The labelled diagrams satisfying the rules are those listed by the search. -/
theorem filter_okRules_eq {n : ℕ} (hs : ∀ d ∈ search n, inRange n d = true ∧ okRules n d = true) :
    (allDiagrams n).filter (fun d => okRules n d = true) = (search n).toFinset := by
  ext d
  simp only [Finset.mem_filter, mem_allDiagrams, List.mem_toFinset]
  exact ⟨fun h => mem_search h.1 h.2, fun h => hs d h⟩

/-- The kind assignments satisfying (E2), (E3), (E6) are the leaves of the edge stage. -/
theorem filter_edgeRules_eq {n : ℕ} (hs : ∀ e ∈ edgeLeaves n, e < 4 ^ numPairs n ∧ edgeRules n e = true) :
    (Finset.range (4 ^ numPairs n)).filter (fun e => edgeRules n e = true) = (edgeLeaves n).toFinset := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨he, hr⟩
    simp only [edgeRules, Bool.and_eq_true] at hr
    exact mem_edgeLeaves he hr.1.1 hr.1.2 hr.2
  · exact fun h => hs e h

/-- **Proposition 3.1 for `n ≤ 6` bodies, from the checks**: if `checkAll n lex json numEdge numLabelled
numClasses` holds, then exactly `numLabelled` labelled diagrams on `n` bodies satisfy the rules in both colours,
exactly `numEdge` assignments of kinds to the pairs satisfy (E2), (E3), (E6), and the class file `json` lists
`numClasses` classes `(r, k)` such that the labelled diagrams satisfying the rules are the disjoint union of the orbits
of the representatives `r`, the orbit of `r` has `k` elements, `r` has the least key of its orbit, and the keys of the
representatives increase along the file. -/
theorem classification_of_check {n : ℕ} (hn : n ≤ 6) {lex : Bool} {json : String}
    {numEdge numLabelled numClasses : ℕ} (h : checkAll n lex json numEdge numLabelled numClasses = true) :
    ((allDiagrams n).filter (fun d => okRules n d = true)).card = numLabelled ∧
    ((Finset.range (4 ^ numPairs n)).filter (fun e => edgeRules n e = true)).card = numEdge ∧
    ∃ cls : List (Diagram × ℕ), parseFile json = some (n, numLabelled, cls) ∧
      renderFile n numLabelled cls = json ∧ cls.length = numClasses ∧ (∀ x ∈ cls, inRange n x.1 = true) ∧
      (∀ d, (d ∈ allDiagrams n ∧ okRules n d = true) ↔ ∃ x ∈ cls, d ∈ orbit n x.1) ∧
      cls.Pairwise (fun x y => Disjoint (orbit n x.1) (orbit n y.1)) ∧
      (∀ x ∈ cls, (orbit n x.1).ncard = x.2) ∧
      (∀ x ∈ cls, ∀ d ∈ orbit n x.1, keyOf n lex x.1 ≤ keyOf n lex d) ∧
      (cls.map fun x => keyOf n lex x.1).Pairwise (· < ·) := by
  obtain ⟨hE, hS, hP, hF⟩ := checkAll_spec h
  obtain ⟨hE1, hE2, hE3⟩ := checkEdges_spec hE
  obtain ⟨hS1, hS2, hS3⟩ := checkSearch_spec hS
  obtain ⟨cls, hparse, hrender, hlen, hcls, hsorted, hcodes⟩ := checkFile_spec hF
  have hLnd : (search n).Nodup := hS2.of_map _
  -- the orbit codes of the classes, put together, are the codes of the search
  have hperm : (cls.flatMap fun x => orbitCodes n x.1).Perm ((search n).map (dcode n)) :=
    (sortNat_perm _).symm.trans (hcodes ▸ sortNat_perm _)
  have hnd : (cls.flatMap fun x => orbitCodes n x.1).Nodup := hperm.nodup_iff.mpr hS2
  have hdisj := (List.nodup_flatMap.mp hnd).2
  -- membership in an orbit through the codes
  have hcode : ∀ x ∈ cls, ∀ d, inRange n d = true → (d ∈ orbit n x.1 ↔ dcode n d ∈ orbitCodes n x.1) := by
    intro x _ d hd
    rw [mem_orbitCodes, ← mem_orbitList_iff hn hP]
    constructor
    · exact fun h => ⟨d, h, rfl⟩
    · rintro ⟨d', hd', he⟩
      rwa [dcode_inj (inRange_of_mem_orbitList hd') hd he] at hd'
  refine ⟨?_, ?_, cls, hparse, hrender, hlen, fun x hx => (checkClass_spec (hcls x hx)).1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [filter_okRules_eq hS3, List.toFinset_card_of_nodup hLnd, hS1]
  · rw [filter_edgeRules_eq hE3, List.toFinset_card_of_nodup hE2, hE1]
  · intro d
    rw [mem_allDiagrams]
    constructor
    · rintro ⟨hd, hok⟩
      have h1 : dcode n d ∈ cls.flatMap fun x => orbitCodes n x.1 :=
        hperm.mem_iff.mpr (List.mem_map_of_mem (mem_search hd hok))
      obtain ⟨x, hx, hdx⟩ := List.mem_flatMap.mp h1
      exact ⟨x, hx, (hcode x hx d hd).mpr hdx⟩
    · rintro ⟨x, hx, hdx⟩
      have hd := inRange_of_mem_orbit hdx
      have h1 : dcode n d ∈ (search n).map (dcode n) :=
        hperm.mem_iff.mp (List.mem_flatMap.mpr ⟨x, hx, (hcode x hx d hd).mp hdx⟩)
      obtain ⟨d', hd', he⟩ := List.mem_map.mp h1
      rw [dcode_inj (hS3 d' hd').1 hd he] at hd'
      exact hS3 d hd'
  · refine List.Pairwise.imp_of_mem ?_ hdisj
    intro x y hx hy hxy
    rw [Set.disjoint_left]
    intro d hdx hdy
    have hd := inRange_of_mem_orbit hdx
    exact hxy ((hcode x hx d hd).mp hdx) ((hcode y hy d hd).mp hdy)
  · intro x hx
    obtain ⟨-, h2, h3, -⟩ := checkClass_spec (hcls x hx)
    rw [ncard_orbit hn hP h2, h3]
  · intro x hx d hd
    exact (checkClass_spec (hcls x hx)).2.2.2 d ((mem_orbitList_iff hn hP).mpr hd)
  · rw [List.pairwise_map]
    have := pairwise_of_strictSorted hsorted
    rwa [List.pairwise_map] at this

end L6F1
