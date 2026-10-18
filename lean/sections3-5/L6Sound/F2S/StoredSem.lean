import L6Sound.F2S.Complete
import L6F2S.Stored

/-!
# The stored cells contain the cell of every pair of complete trees (Proposition 4.5)

* `search_split`: the search is the union, over the pairs of partial trees after the first `d` insertions, of the
  cells below them.
* `checkBelow_sound`: the meaning of a check `checkBelow keep D d text xs = true`: the stored lines parse, to the keys
  `ks`, and every cell of the specification below the pairs `xs` has its key in `ks`; `mem_storedKeys`: a key in `ks`
  is the key of a stored line.
* `keys_whole`, `keys_slices`: the checks of a class, on all the pairs after the first `d` insertions or on their
  slices of `8`, give the keys `ks` of its stored lines and: every cell of `search keepLP D` has its key in `ks`.
* `cells_sound`: with `search_complete`, for every pair of complete trees with heights satisfying `Cond D`, the key
  `(Xz.T.key, Xw.T.key, argminString D Xz Xw)` is the key of a stored line.
-/

namespace L6.F2S

/-! ## The search below the pairs after `d` insertions -/

theorem treeLevel_append (keep : Array Row → Nat → Bool) (D : L6.F2.Diag) :
    ∀ (l1 l2 : List Nat) (S : Nat) (tz tw : TS),
      treeLevel keep D (l1 ++ l2) S tz tw =
        (treeLevel keep D l1 S tz tw).flatMap fun x => treeLevel keep D l2 x.1 x.2.1 x.2.2
  | [], l2, S, tz, tw => by simp [treeLevel]
  | p :: l1, l2, S, tz, tw => by
    rw [List.cons_append]
    simp only [treeLevel, List.flatMap_assoc]
    congr 1
    funext tz'
    congr 1
    funext tw'
    cases partialRows D ⟨tz', tw'⟩ (ins p S) with
    | none => rfl
    | some L =>
      dsimp only
      cases keep L (Pair.nv ⟨tz', tw'⟩)
      · simp
      · simp [treeLevel_append keep D l1 l2]

theorem search_split (keep : Array Row → Nat → Bool) (D : L6.F2.Diag) (d : Nat) :
    search keep D = (prefixPairs keep D d).flatMap (below keep D d) := by
  have h := treeLevel_append keep D ((order D).take d) ((order D).drop d) (single O) TS.init TS.init
  rw [List.take_append_drop] at h
  rw [search, h, List.flatMap_assoc]
  rfl

/-! ## The meaning of a check -/

theorem checkBelow_sound {keep : Array Row → Nat → Bool} {D : L6.F2.Diag} {d : Nat} {text : String}
    {xs : List (Nat × TS × TS)} (hc : checkBelow keep D d text xs = true) :
    ∃ ks, storedKeys text = some ks ∧ ∀ x ∈ xs, ∀ c ∈ below keep D d x, c.key ∈ ks := by
  unfold checkBelow at hc
  cases hks : storedKeys text with
  | none => rw [hks] at hc; exact absurd hc (by simp)
  | some ks =>
    rw [hks] at hc
    refine ⟨ks, rfl, fun x hx c hcx => ?_⟩
    simp only [List.all_eq_true] at hc
    have h := hc x hx c hcx
    rw [Std.HashSet.contains_ofList] at h
    exact List.contains_iff_mem.mp h

theorem mem_of_mapM_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (ks : List β), l.mapM f = some ks → ∀ k ∈ ks, ∃ a ∈ l, f a = some k
  | [], ks, h, k, hk => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp at hk
  | a :: l, ks, h, k, hk => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hk with rfl | hk
        · exact ⟨a, List.mem_cons_self, hfa⟩
        · obtain ⟨a', ha', hfa'⟩ := mem_of_mapM_some f l bs hl k hk
          exact ⟨a', List.mem_cons_of_mem _ ha', hfa'⟩

/-- A key of the stored keys is the key of a (non-empty) stored line. -/
theorem mem_storedKeys {text : String} {ks : List ((List Nat × Option Nat) × (List Nat × Option Nat) × String)}
    (hks : storedKeys text = some ks) {k : (List Nat × Option Nat) × (List Nat × Option Nat) × String}
    (hk : k ∈ ks) : ∃ line ∈ (text.splitOn "\n").filter (· != ""), keyOfLine line = some k :=
  mem_of_mapM_some keyOfLine _ ks hks k hk

/-! ## The checks of a class -/

/-- The check of a class on all the pairs after the first `d` insertions. -/
theorem keys_whole {keep : Array Row → Nat → Bool} {D : L6.F2.Diag} {d : Nat} {text : String}
    (hc : checkBelow keep D d text (prefixPairs keep D d) = true) :
    ∃ ks, storedKeys text = some ks ∧ ∀ c ∈ search keep D, c.key ∈ ks := by
  obtain ⟨ks, hks, h⟩ := checkBelow_sound hc
  refine ⟨ks, hks, fun c hcs => ?_⟩
  rw [search_split keep D d, List.mem_flatMap] at hcs
  obtain ⟨x, hx, hcx⟩ := hcs
  exact h x hx c hcx

theorem mem_slice {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    l[i] ∈ (l.drop (8 * (i / 8))).take 8 := by
  have h1 : i % 8 < ((l.drop (8 * (i / 8))).take 8).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have h2 : ((l.drop (8 * (i / 8))).take 8)[i % 8] = l[i] := by
    simp only [List.getElem_take, List.getElem_drop, Nat.div_add_mod]
  rw [← h2]
  exact List.getElem_mem h1

/-- The checks of a class on the slices `((prefixPairs keep D d).drop (8 * j)).take 8`, `j < m`, of the `8 m` pairs
after the first `d` insertions. -/
theorem keys_slices {keep : Array Row → Nat → Bool} {D : L6.F2.Diag} {d : Nat} {text : String} (m : Nat)
    (hm : 0 < m) (hlen : (prefixPairs keep D d).length = 8 * m)
    (hc : ∀ j < m, checkBelow keep D d text (((prefixPairs keep D d).drop (8 * j)).take 8) = true) :
    ∃ ks, storedKeys text = some ks ∧ ∀ c ∈ search keep D, c.key ∈ ks := by
  obtain ⟨ks, hks, -⟩ := checkBelow_sound (hc 0 hm)
  refine ⟨ks, hks, fun c hcs => ?_⟩
  rw [search_split keep D d, List.mem_flatMap] at hcs
  obtain ⟨x, hx, hcx⟩ := hcs
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨ks', hks', h⟩ := checkBelow_sound (hc (i / 8) (by omega))
  rw [hks, Option.some.injEq] at hks'
  subst hks'
  exact h _ (mem_slice _ i hi) c hcx

/-! ## Every cell is stored -/

/-- **The stored cells (Proposition 4.5).** If every cell of the search of `D` has the key of a stored line and the
insertion order of `D` lists the six bodies, then for every pair of complete trees with heights satisfying `Cond D`,
the trees (as node sets with the body on the leaf of `O`) and the argmin part of the line of the cell form the key of
a stored line. -/
theorem cells_sound {D : L6.F2.Diag} {text : String}
    (hkeys : ∃ ks, storedKeys text = some ks ∧ ∀ c ∈ search keepLP D, c.key ∈ ks)
    (hord : (order D).Perm (List.range 6)) {Xz Xw : ExpTree} (hX : Cond D Xz Xw) :
    ∃ ks, storedKeys text = some ks ∧ (Xz.T.key, Xw.T.key, argminString D Xz Xw) ∈ ks := by
  obtain ⟨ks, hks, h⟩ := hkeys
  obtain ⟨c, hc, h1, h2, h3⟩ := search_complete keepLP_sound hord hX
  refine ⟨ks, hks, ?_⟩
  have hk := h c hc
  rwa [SCell.key, h1, h2, h3] at hk

/-- The same, as a stored line. -/
theorem cell_stored {D : L6.F2.Diag} {text : String}
    (hkeys : ∃ ks, storedKeys text = some ks ∧ ∀ c ∈ search keepLP D, c.key ∈ ks)
    (hord : (order D).Perm (List.range 6)) {Xz Xw : ExpTree} (hX : Cond D Xz Xw) :
    ∃ line ∈ (text.splitOn "\n").filter (· != ""), keyOfLine line = some (Xz.T.key, Xw.T.key, argminString D Xz Xw) := by
  obtain ⟨ks, hks, hk⟩ := cells_sound hkeys hord hX
  exact mem_storedKeys hks hk

end L6.F2S
