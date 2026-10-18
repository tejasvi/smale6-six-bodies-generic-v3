import L6CheckK.F1.Global
import L6CheckK.F1.Codes.All
import L6SoundK
import L6Sound.F1.Classes

/-!
# Proposition 3.1 with the standard axioms only

`F1_main_k` states the combinatorial content of `L6F1.F1_main` (the counts 82,712 and 932,677, the classes as
the disjoint union of orbits with their sizes, least keys and increasing keys) for the classes `classes6L` given
as data. It is proved from the `decide +kernel` checks of `L6CheckK.F1` (the shards of the search, the classes, the
global comparisons) and the soundness lemmas of `L6Sound.F1` and `L6SoundK.F1`, without `native_decide`. The reading
of `n6.json` into `classes6L` is the version-1 check (`classes6 = classes6L`), which needs strings.
-/

namespace L6CheckK.F1

open L6F1 L6K.F1

theorem keyOf_false_k (n : ℕ) (d : Diagram) : keyOf n false d = rawKey n d := by simp [keyOf]

theorem shard_spec {x : ℕ × ℕ × List ℕ} (hx : x ∈ allShards) :
    (extendFrom level x.1).length = x.2.1 ∧
    (∀ e ∈ extendFrom level x.1, e < 4 ^ 15 ∧ edgeRules 6 e = true) ∧
    (extendFrom level x.1).Nodup ∧
    (∀ d ∈ searchFrom 6 (extendFrom level x.1), inRange 6 d = true ∧ okRules 6 d = true) ∧
    ((searchFrom 6 (extendFrom level x.1)).map (dcode 6)).Perm x.2.2 := by
  have h := List.all_eq_true.mp allShards_ok x hx
  simp only [shardOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, (msort_perm 20 _).nodup_iff.mp (nodup_of_strictSorted h3), h4, ?_⟩
  rw [← h5]
  exact (msort_perm 20 _).symm

theorem level_le : level ≤ 15 := by decide

theorem edgeLeaves_shards : edgeLeaves 6 = allShards.flatMap fun x => extendFrom level x.1 := by
  rw [edgeLeaves_eq level_le, ← g_prefixes, List.flatMap_map]

theorem search_shards : L6F1.search 6 = allShards.flatMap fun x => searchFrom 6 (extendFrom level x.1) := by
  rw [search_eq level_le, ← g_prefixes, List.flatMap_map]

theorem prefix_mem {x : ℕ × ℕ × List ℕ} (hx : x ∈ allShards) : x.1 ∈ edgesUpTo 6 level := by
  rw [← g_prefixes]
  exact List.mem_map_of_mem hx

theorem prefixes_nodup : (allShards.map (·.1)).Nodup :=
  (msortR_perm 20 _).nodup_iff.mp (nodup_of_strictSorted g_prefixes_nodup)

theorem perm_flatMap {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).Perm (g x)) → (l.flatMap f).Perm (l.flatMap g)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact (h a List.mem_cons_self).append (perm_flatMap fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The leaves of the edge stage: their number, no repetition, the rules (E2), (E3), (E6). -/
theorem leaves_spec : (edgeLeaves 6).length = 932677 ∧ (edgeLeaves 6).Nodup ∧
    ∀ e ∈ edgeLeaves 6, e < 4 ^ numPairs 6 ∧ edgeRules 6 e = true := by
  rw [edgeLeaves_shards]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_flatMap, List.map_congr_left fun x hx => (shard_spec hx).1]
    exact g_sum
  · rw [List.nodup_flatMap]
    refine ⟨fun x hx => (shard_spec hx).2.2.1, ?_⟩
    have h : allShards.Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.mp prefixes_nodup
    refine List.Pairwise.imp_of_mem ?_ h
    intro x y hx hy hxy e hex hey
    exact hxy ((mod_of_mem_extendFrom (prefix_mem hx) hex).symm.trans (mod_of_mem_extendFrom (prefix_mem hy) hey))
  · intro e he
    obtain ⟨x, hx, hex⟩ := List.mem_flatMap.mp he
    exact (shard_spec hx).2.1 e hex

/-- The codes of the labelled diagrams found by the search are, up to order, the codes listed in the shards. -/
theorem search_codes_perm : ((L6F1.search 6).map (dcode 6)).Perm (allShards.flatMap (·.2.2)) := by
  rw [search_shards, List.map_flatMap]
  exact perm_flatMap fun x hx => (shard_spec hx).2.2.2.2

/-- The codes of the shards have no repetition and are, up to order, the orbit codes of the classes. -/
theorem codes_spec : codesAll.Nodup ∧ codesAll.Perm repCodes.flatten := nodup_perm_of_ivls g_chain g_ivls

/-- The labelled diagrams found by the search: their number, no repetition, the rules. -/
theorem search_spec : (L6F1.search 6).length = 82712 ∧ ((L6F1.search 6).map (dcode 6)).Nodup ∧
    ∀ d ∈ L6F1.search 6, inRange 6 d = true ∧ okRules 6 d = true := by
  have hp : ((L6F1.search 6).map (dcode 6)).Perm codesAll := search_codes_perm
  refine ⟨?_, hp.nodup_iff.mpr codes_spec.1, ?_⟩
  · have h := hp.length_eq
    rw [List.length_map] at h
    rw [h, g_codes_len]
  · intro d hd
    rw [search_shards] at hd
    obtain ⟨x, hx, hdx⟩ := List.mem_flatMap.mp hd
    exact (shard_spec hx).2.2.2.1 d hdx

theorem flatten_map {α : Type} {f : α → List ℕ} : ∀ {l : List α}, (l.map f).flatten = l.flatMap f
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.flatten_cons, List.flatMap_cons, flatten_map]

/-- The orbit codes of the classes, put together, are the codes of the search up to order. -/
theorem classes_codes_perm :
    (classes6L.flatMap fun x => orbitCodes 6 x.1).Perm ((L6F1.search 6).map (dcode 6)) := by
  have e : (classes6L.flatMap fun x => orbitCodes 6 x.1) = repCodes.flatten := by
    rw [← repCodes_eq, flatten_map]
    simp only [orbitCodesK_eq]
  rw [e]
  exact codes_spec.2.symm.trans search_codes_perm.symm

/-- **Proposition 3.1, with the standard axioms only**: exactly 82,712 labelled diagrams on six bodies satisfy the
rules in both colours; exactly 932,677 assignments of kinds to the fifteen pairs satisfy (E2), (E3), (E6); the 191
classes `classes6L` are such that the labelled diagrams satisfying the rules are the disjoint union of the orbits of
the representatives, with the listed orbit sizes, each representative having the least key of its orbit (and that key
is its canonical key), in increasing order of the keys. -/
theorem F1_main_k :
    ((allDiagrams 6).filter (fun d => okRules 6 d = true)).card = 82712 ∧
    ((Finset.range (4 ^ 15)).filter (fun e => edgeRules 6 e = true)).card = 932677 ∧
    classes6L.length = 191 ∧
    (∀ d, (d ∈ allDiagrams 6 ∧ okRules 6 d = true) ↔ ∃ x ∈ classes6L, d ∈ orbit 6 x.1) ∧
    classes6L.Pairwise (fun x y => Disjoint (orbit 6 x.1) (orbit 6 y.1)) ∧
    (∀ x ∈ classes6L, (orbit 6 x.1).ncard = x.2) ∧
    (∀ x ∈ classes6L, ∀ d ∈ orbit 6 x.1, rawKey 6 x.1 ≤ rawKey 6 d) ∧
    (∀ x ∈ classes6L, canonKey 6 false x.1 = rawKey 6 x.1) ∧
    (classes6L.map fun x => rawKey 6 x.1).Pairwise (· < ·) := by
  obtain ⟨hE1, hE2, hE3⟩ := leaves_spec
  obtain ⟨hS1, hS2, hS3⟩ := search_spec
  have hn : (6 : ℕ) ≤ 6 := le_refl 6
  have hP : checkPerms 6 = true := by
    rw [← checkPermsK_eq]
    exact g_perms
  have hcls : ∀ x ∈ classes6L, checkClass 6 false x = true := by
    intro x hx
    rw [← checkClassK_eq]
    exact List.all_eq_true.mp classes_all x hx
  have hperm := classes_codes_perm
  have hLnd : (L6F1.search 6).Nodup := hS2.of_map _
  have hnd : (classes6L.flatMap fun x => orbitCodes 6 x.1).Nodup := hperm.nodup_iff.mpr hS2
  have hdisj := (List.nodup_flatMap.mp hnd).2
  have hin : ∀ x ∈ classes6L, inRange 6 x.1 = true := fun x hx => (checkClass_spec (hcls x hx)).1
  -- membership in an orbit through the codes
  have hcode : ∀ x ∈ classes6L, ∀ d, inRange 6 d = true → (d ∈ orbit 6 x.1 ↔ dcode 6 d ∈ orbitCodes 6 x.1) := by
    intro x _ d hd
    rw [mem_orbitCodes, ← mem_orbitList_iff hn hP]
    constructor
    · exact fun h => ⟨d, h, rfl⟩
    · rintro ⟨d', hd', he⟩
      rwa [dcode_inj (inRange_of_mem_orbitList hd') hd he] at hd'
  have hk : ∀ x ∈ classes6L, ∀ d ∈ orbit 6 x.1, rawKey 6 x.1 ≤ rawKey 6 d := by
    intro x hx d hd
    have h := (checkClass_spec (hcls x hx)).2.2.2 d ((mem_orbitList_iff hn hP).mpr hd)
    rwa [keyOf_false_k, keyOf_false_k] at h
  have hedge : ((Finset.range (4 ^ numPairs 6)).filter (fun e => edgeRules 6 e = true)).card = 932677 := by
    rw [filter_edgeRules_eq hE3, List.toFinset_card_of_nodup hE2, hE1]
  refine ⟨?_, hedge, g_len, ?_, ?_, ?_, hk, ?_, pairwise_of_strictSorted g_keys⟩
  · rw [filter_okRules_eq hS3, List.toFinset_card_of_nodup hLnd, hS1]
  · intro d
    rw [mem_allDiagrams]
    constructor
    · rintro ⟨hd, hok⟩
      have h1 : dcode 6 d ∈ classes6L.flatMap fun x => orbitCodes 6 x.1 :=
        hperm.mem_iff.mpr (List.mem_map_of_mem (mem_search hd hok))
      obtain ⟨x, hx, hdx⟩ := List.mem_flatMap.mp h1
      exact ⟨x, hx, (hcode x hx d hd).mpr hdx⟩
    · rintro ⟨x, hx, hdx⟩
      have hd := inRange_of_mem_orbit hdx
      have h1 : dcode 6 d ∈ (L6F1.search 6).map (dcode 6) :=
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
  · intro x hx
    obtain ⟨hle, y, hy, hyk⟩ := canonKey_spec hn hP false (hin x hx)
    simp only [keyOf_false_k] at hle hyk
    apply le_antisymm
    · exact hle x.1 (self_mem_orbit hn (hin x hx))
    · rw [hyk]
      exact hk x hx y hy

end L6CheckK.F1
