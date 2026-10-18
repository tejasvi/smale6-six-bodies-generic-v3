import L6Check.F1.N6
import L6Check.F1.N5
import L6Check.F1.N4
import L6Check.F1.Sha
import L6Sound.F1.Classes

/-!
# Proposition 3.1

`F1_main` is Proposition 3.1 in ordinary terms: the labelled diagrams on six bodies (`allDiagrams 6`: an edge code
`e < 4 ^ 15` giving the kinds of the fifteen pairs, and two circle masks below `2 ^ 6`) that satisfy the rules (E1)–(E6),
(C1)–(C4) of Lemma 2.11 in both colours (`okRules 6`, `L6F1.Rules`) are 82,712; the assignments of kinds satisfying
(E2), (E3), (E6) are 932,677; and the labelled diagrams satisfying the rules are the disjoint union of the orbits, under
the relabellings and the exchange of the colours (`orbit 6`), of the 191 representatives listed in `n6.json`, with the
listed orbit sizes, each representative having the least key (`rawKey 6`, the key of the program that wrote the file)
of its orbit, in increasing order of the keys. `F1_one_representative`: each orbit of a labelled diagram satisfying the
rules contains exactly one representative, and `F1_reps_distinct_orbits`: the representatives lie in pairwise
different orbits. `F1_canonKey_invariant`: the canonical key is invariant on orbits.
`F1_n5`, `F1_n4`: the same for five and four bodies (1376 labelled diagrams in 24 classes; 41 in 5 classes).

The computations are `check_n6`, `check_n5`, `check_n4` (`native_decide`); the digests of the embedded files are
`n6json_sha256`, `n5json_sha256`, `n4json_sha256`; the rest is proved in `L6Sound.F1`.
-/

namespace L6F1

/-- The classes `(representative, number of labelled diagrams)` read from a class file. -/
def classesOf (json : String) : List (Diagram × ℕ) :=
  match parseFile json with
  | some (_, _, cls) => cls
  | none => []

/-- The classes of `n6.json` (irreducible, so that it is never unfolded and evaluated during elaboration). -/
@[irreducible] def classes6 : List (Diagram × ℕ) := classesOf n6json

theorem classesOf_eq {json : String} {n t : ℕ} {cls : List (Diagram × ℕ)} (h : parseFile json = some (n, t, cls)) :
    classesOf json = cls := by
  unfold classesOf
  rw [h]

theorem keyOf_false (n : ℕ) (d : Diagram) : keyOf n false d = rawKey n d := by simp [keyOf]

theorem keyOf_true (n : ℕ) (d : Diagram) : keyOf n true d = rawKeyLex n d := by simp [keyOf]

theorem perms6 : checkPerms 6 = true := (checkAll_spec check_n6).2.2.1

theorem classes6_inRange : ∀ x ∈ classes6, inRange 6 x.1 = true := by
  obtain ⟨-, -, cls, hp, -, -, hin, -⟩ := classification_of_check (by norm_num) check_n6
  have e : classes6 = cls := by unfold classes6; exact classesOf_eq hp
  rw [e]
  exact hin

/-- **Proposition 3.1.** -/
theorem F1_main :
    -- exactly 82,712 labelled diagrams on six bodies satisfy the rules (E1)–(E6), (C1)–(C4) in both colours
    ((allDiagrams 6).filter (fun d => okRules 6 d = true)).card = 82712 ∧
    -- exactly 932,677 assignments of kinds to the fifteen pairs satisfy (E2), (E3), (E6)
    ((Finset.range (4 ^ 15)).filter (fun e => edgeRules 6 e = true)).card = 932677 ∧
    -- `n6.json` is read as 191 classes and written back identically from them
    parseFile n6json = some (6, 82712, classes6) ∧ renderFile 6 82712 classes6 = n6json ∧
    classes6.length = 191 ∧
    -- the labelled diagrams satisfying the rules are the union of the orbits of the representatives
    (∀ d, (d ∈ allDiagrams 6 ∧ okRules 6 d = true) ↔ ∃ x ∈ classes6, d ∈ orbit 6 x.1) ∧
    -- these orbits are pairwise disjoint
    classes6.Pairwise (fun x y => Disjoint (orbit 6 x.1) (orbit 6 y.1)) ∧
    -- the orbit of each representative has the listed number of labelled diagrams
    (∀ x ∈ classes6, (orbit 6 x.1).ncard = x.2) ∧
    -- each representative has the least key of its orbit
    (∀ x ∈ classes6, ∀ d ∈ orbit 6 x.1, rawKey 6 x.1 ≤ rawKey 6 d) ∧
    (∀ x ∈ classes6, canonKey 6 false x.1 = rawKey 6 x.1) ∧
    -- the keys of the representatives increase strictly along the file
    (classes6.map fun x => rawKey 6 x.1).Pairwise (· < ·) := by
  obtain ⟨h1, h2, cls, hp, hr, hl, hin, hu, hd, hc, hk, hs⟩ := classification_of_check (by norm_num) check_n6
  have e : classes6 = cls := by unfold classes6; exact classesOf_eq hp
  rw [e]
  simp only [keyOf_false] at hk hs
  refine ⟨h1, h2, hp, hr, hl, hu, hd, hc, hk, fun x hx => ?_, hs⟩
  obtain ⟨hle, y, hy, hyk⟩ := canonKey_spec (by norm_num) perms6 false (hin x hx)
  simp only [keyOf_false] at hle hyk
  apply le_antisymm
  · exact hle x.1 (self_mem_orbit (by norm_num) (hin x hx))
  · rw [hyk]
    exact hk x hx y hy

/-- The orbit relation is symmetric. -/
theorem mem_orbit_comm {n : ℕ} (hn : n ≤ 6) {d d' : Diagram} (hd : inRange n d = true) (hd' : inRange n d' = true) :
    d' ∈ orbit n d ↔ d ∈ orbit n d' := by
  constructor
  · intro h
    rw [orbit_eq_of_mem hn h]
    exact self_mem_orbit hn hd
  · intro h
    rw [orbit_eq_of_mem hn h]
    exact self_mem_orbit hn hd'

/-- **Each orbit of a labelled diagram on six bodies satisfying the rules contains exactly one of the representatives
of `n6.json`.** -/
theorem F1_one_representative {d : Diagram} (hd : d ∈ allDiagrams 6) (hok : okRules 6 d = true) :
    ∃! i : Fin classes6.length, (classes6.get i).1 ∈ orbit 6 d := by
  obtain ⟨-, -, hp, -, -, hu, hdisj, -⟩ := F1_main
  obtain ⟨-, -, cls, hp', -, -, hin, -⟩ := classification_of_check (by norm_num) check_n6
  have e : classes6 = cls := by unfold classes6; exact classesOf_eq hp'
  have hin6 : ∀ x ∈ classes6, inRange 6 x.1 = true := by rw [e]; exact hin
  have hdr : inRange 6 d = true := mem_allDiagrams.mp hd
  have key : ∀ i : Fin classes6.length, (classes6.get i).1 ∈ orbit 6 d ↔ d ∈ orbit 6 (classes6.get i).1 :=
    fun i => mem_orbit_comm (by norm_num) hdr (hin6 _ (List.get_mem _ _))
  obtain ⟨x, hx, hdx⟩ := (hu d).mp ⟨hd, hok⟩
  obtain ⟨i, rfl⟩ := List.get_of_mem hx
  refine ⟨i, (key i).mpr hdx, fun j hj' => ?_⟩
  have hj := (key j).mp hj'
  by_contra hne
  have hpw := List.pairwise_iff_get.mp hdisj
  rcases lt_or_gt_of_ne hne with h | h
  · exact Set.disjoint_left.mp (hpw j i h) hj hdx
  · exact Set.disjoint_left.mp (hpw i j h) hdx hj

/-- **The representatives of `n6.json` lie in pairwise different orbits.** -/
theorem F1_reps_distinct_orbits (i j : Fin classes6.length) (hij : i ≠ j) :
    (classes6.get i).1 ∉ orbit 6 (classes6.get j).1 := by
  obtain ⟨-, -, -, -, -, -, hdisj, -⟩ := F1_main
  intro h
  have hi := self_mem_orbit (by norm_num) (classes6_inRange _ (List.get_mem classes6 i))
  have hpw := List.pairwise_iff_get.mp hdisj
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact Set.disjoint_left.mp (hpw i j h') hi h
  · exact Set.disjoint_left.mp (hpw j i h') h hi

/-- **The canonical key is invariant on orbits**: it does not change under the relabellings and the exchange of the
colours. -/
theorem F1_canonKey_invariant {d : Diagram} (hd : inRange 6 d = true) (σ : Equiv.Perm (Fin 6)) (s : Bool) :
    canonKey 6 false (actP 6 σ s d) = canonKey 6 false d :=
  canonKey_actP (by norm_num) perms6 false hd σ s

/-- Proposition 3.1's check for five bodies: 1376 labelled diagrams, 18,918 kind assignments passing (E2), (E3), (E6),
and the 24 classes of `n5.json` (ordered by `rawKeyLex`). -/
theorem F1_n5 :
    ((allDiagrams 5).filter (fun d => okRules 5 d = true)).card = 1376 ∧
    ((Finset.range (4 ^ 10)).filter (fun e => edgeRules 5 e = true)).card = 18918 ∧
    ∃ cls : List (Diagram × ℕ), parseFile n5json = some (5, 1376, cls) ∧ renderFile 5 1376 cls = n5json ∧
      cls.length = 24 ∧ (∀ x ∈ cls, inRange 5 x.1 = true) ∧
      (∀ d, (d ∈ allDiagrams 5 ∧ okRules 5 d = true) ↔ ∃ x ∈ cls, d ∈ orbit 5 x.1) ∧
      cls.Pairwise (fun x y => Disjoint (orbit 5 x.1) (orbit 5 y.1)) ∧
      (∀ x ∈ cls, (orbit 5 x.1).ncard = x.2) ∧
      (∀ x ∈ cls, ∀ d ∈ orbit 5 x.1, rawKeyLex 5 x.1 ≤ rawKeyLex 5 d) ∧
      (cls.map fun x => rawKeyLex 5 x.1).Pairwise (· < ·) := by
  have h := classification_of_check (by norm_num) check_n5
  simp only [keyOf_true] at h
  exact h

/-- Proposition 3.1's check for four bodies: 41 labelled diagrams, 633 kind assignments passing (E2), (E3), (E6), and
the 5 classes of `n4.json` (ordered by `rawKeyLex`). -/
theorem F1_n4 :
    ((allDiagrams 4).filter (fun d => okRules 4 d = true)).card = 41 ∧
    ((Finset.range (4 ^ 6)).filter (fun e => edgeRules 4 e = true)).card = 633 ∧
    ∃ cls : List (Diagram × ℕ), parseFile n4json = some (4, 41, cls) ∧ renderFile 4 41 cls = n4json ∧
      cls.length = 5 ∧ (∀ x ∈ cls, inRange 4 x.1 = true) ∧
      (∀ d, (d ∈ allDiagrams 4 ∧ okRules 4 d = true) ↔ ∃ x ∈ cls, d ∈ orbit 4 x.1) ∧
      cls.Pairwise (fun x y => Disjoint (orbit 4 x.1) (orbit 4 y.1)) ∧
      (∀ x ∈ cls, (orbit 4 x.1).ncard = x.2) ∧
      (∀ x ∈ cls, ∀ d ∈ orbit 4 x.1, rawKeyLex 4 x.1 ≤ rawKeyLex 4 d) ∧
      (cls.map fun x => rawKeyLex 4 x.1).Pairwise (· < ·) := by
  have h := classification_of_check (by norm_num) check_n4
  simp only [keyOf_true] at h
  exact h

end L6F1
