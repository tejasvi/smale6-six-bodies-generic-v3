import L6F34.Check
import Mathlib.Tactic

/-!
# F3, F4: what a passing chunk check means

The theorems `L6.F34.Checks.F34_c<N>_k<k>` state `checkChunk … = true` (by `native_decide`). This module proves what
that means, about the code of `L6F34.Check`, without any evaluation:

* `checkChunk_spec`: the inputs parse (`prepare`), the chunk lies in the file, every cell `lo ≤ idx < hi` passes
  (`cellKind ≠ 0`), and the counts of the kinds are the stated ones;
* `cellKind_spec`: a passing cell is in exactly one of the three lists (open, single term, core link), and
  - if it is open, nothing more is claimed;
  - if it has a single term `(nm, lab)`: its cell and rows are read, and `checkSingle` holds;
  - if it has a core link: the named certificate is among the given ones (read by `parseCert`), and `checkLink`
    holds;
* `checkSingle_spec`: the identity is one of §5.1 with the named term `i`, and for every other term `k` the system
  `Π + {e_k − e_i ≤ 0}` has a certificate accepted by `Farkas.check` (with Lemma 4.6: on `Π` the term `i` has strictly
  the least exponent);
* `checkLink_spec`, `genFor_spec`, `constantArgmin_spec`: the certificate's generators are, in order, the initial
  forms of the named identities computed from the cell; for a secondary identity the argmin set is certified
  constant on `Π` by accepted certificates;
* `parseAll_lookup`, `prepare_certs`: every certificate used is the reading by `parseCert` of one of the given texts.
-/

namespace L6.F34

open L6 L6.Poly

theorem checkChunk_spec {cls : Nat} {n6 cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {lo hi : Nat} {expected : Counts}
    (h : checkChunk cls n6 cellsTxt singleTxt linksTxt passTxt openTxt certs lo hi expected = true) :
    ∃ cd, prepare cls n6 cellsTxt singleTxt linksTxt passTxt openTxt certs = some cd ∧ lo ≤ hi ∧ hi ≤ cd.ncells ∧
      (∀ idx, lo ≤ idx → idx < hi → cellKind cd idx ≠ 0) ∧
      countKinds ((List.range' lo (hi - lo)).map (cellKind cd)) = expected := by
  unfold checkChunk at h
  split at h
  · exact absurd h (by simp)
  · rename_i cd hcd
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map, List.mem_range'] at h
    obtain ⟨⟨⟨hlo, hhi⟩, hall⟩, hcnt⟩ := h
    refine ⟨cd, hcd, hlo, hhi, ?_, hcnt⟩
    intro idx h1 h2
    have := hall (cellKind cd idx) ⟨idx, ⟨idx - lo, by omega, by omega⟩, rfl⟩
    simpa using this

/-- What a passing cell is. -/
theorem cellKind_spec {cd : ChunkData} {idx : Nat} (h : cellKind cd idx ≠ 0) :
    kindsOf cd idx = 1 ∧
    (cd.opens.contains idx = true ∨
     (∃ nm lab x c rows pt, cd.single.getD idx none = some (nm, lab) ∧
        cellCtx cd idx = some (x, c, rows, pt) ∧ checkSingle x rows nm lab = true) ∨
     (∃ lk cert x c rows pt, cd.links.getD idx none = some lk ∧ cd.certs.lookup lk.cert = some cert ∧
        cellCtx cd idx = some (x, c, rows, pt) ∧ checkLink x c rows pt lk cert = true)) := by
  unfold cellKind at h
  by_cases hk : (kindsOf cd idx != 1) = true
  · rw [if_pos hk] at h
    exact absurd rfl h
  · rw [if_neg hk] at h
    have hk1 : kindsOf cd idx = 1 := by simpa using hk
    refine ⟨hk1, ?_⟩
    by_cases hop : cd.opens.contains idx = true
    · exact Or.inl hop
    · rw [if_neg hop] at h
      right
      split at h
      · exact absurd rfl h
      · rename_i x c rows pt hctx
        cases hsg : cd.single.getD idx none with
        | some p =>
          obtain ⟨nm, lab⟩ := p
          rw [hsg] at h
          by_cases hs : checkSingle x rows nm lab = true
          · exact Or.inl ⟨nm, lab, x, c, rows, pt, rfl, hctx, hs⟩
          · simp only [hs] at h
            exact absurd rfl h
        | none =>
          rw [hsg] at h
          cases hlk : cd.links.getD idx none with
          | none =>
            rw [hlk] at h
            exact absurd rfl h
          | some lk =>
            rw [hlk] at h
            cases hcert : cd.certs.lookup lk.cert with
            | none =>
              simp only [hcert] at h
              exact absurd rfl h
            | some cert =>
              simp only [hcert] at h
              by_cases hl : checkLink x c rows pt lk cert = true
              · exact Or.inr ⟨lk, cert, x, c, rows, pt, rfl, hcert, hctx, hl⟩
              · simp only [hl] at h
                exact absurd rfl h

theorem checkSingle_spec {x : Ctx} {rows : Array Row} {nm : IdName} {lab : Lab}
    (h : checkSingle x rows nm lab = true) :
    ∃ ts i, x.secTerms nm = some ts ∧ findLab ts lab = some i ∧
      ∀ k, k < ts.size → k ≠ i →
        Farkas.check x.nh (rows.push (rowLe ts k i)) (L6.LP.decide (rows.push (rowLe ts k i)) x.nh).cert = true := by
  unfold checkSingle at h
  split at h
  · exact absurd h (by simp)
  · rename_i ts hts
    split at h
    · exact absurd h (by simp)
    · rename_i i hi
      refine ⟨ts, i, hts, hi, fun k hk hki => ?_⟩
      unfold strictlyLeast at h
      simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
      rcases h k hk with h' | h'
      · exact absurd h' hki
      · simpa [prunedWith] using h'

theorem constantArgmin_spec {nh : Nat} {rows : Array Row} {ts : Array Term} {S : List Nat}
    (h : constantArgmin nh rows ts S = true) :
    ∃ i0 rest, S = i0 :: rest ∧ ∀ k, k < ts.size → k ≠ i0 →
      (k ∈ S → Farkas.check nh (rows.push (rowGeS ts k i0)) (L6.LP.decide (rows.push (rowGeS ts k i0)) nh).cert = true ∧
               Farkas.check nh (rows.push (rowGeS ts i0 k)) (L6.LP.decide (rows.push (rowGeS ts i0 k)) nh).cert = true) ∧
      (k ∉ S → Farkas.check nh (rows.push (rowLe ts k i0)) (L6.LP.decide (rows.push (rowLe ts k i0)) nh).cert = true) := by
  unfold constantArgmin at h
  split at h
  · exact absurd h (by simp)
  · rename_i i0 rest
    refine ⟨i0, rest, rfl, fun k hk hki => ?_⟩
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
    rcases h k hk with h' | h'
    · exact absurd h' hki
    · by_cases hm : k ∈ i0 :: rest
      · have hc : (i0 :: rest).contains k = true := List.contains_iff_mem.mpr hm
        rw [if_pos hc] at h'
        simp only [Bool.and_eq_true] at h'
        exact ⟨fun _ => ⟨by simpa [prunedWith] using h'.1, by simpa [prunedWith] using h'.2⟩, fun hn => absurd hm hn⟩
      · have hc : ¬(i0 :: rest).contains k = true := fun hc => hm (List.contains_iff_mem.mp hc)
        rw [if_neg hc] at h'
        exact ⟨fun hn => absurd hn hm, fun _ => by simpa [prunedWith] using h'⟩

theorem checkLink_spec {x : Ctx} {c : Cell} {rows : Array Row} {pt : Array Float} {lk : Link} {cert : Cert}
    (h : checkLink x c rows pt lk cert = true) :
    cert.nvar = lk.vars.size ∧ cert.fixed = lk.fixed ∧ cert.gens.length = lk.names.size ∧
      ∀ i, i < lk.names.size → genFor x c rows pt lk lk.names[i]! = some (normalize cert.gens[i]!) := by
  unfold checkLink at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, fun i hi => by simpa using h4 i hi⟩

/-- A secondary identity's generator comes with the certificate that its argmin set is constant on `Π`. -/
theorem genSec_spec {x : Ctx} {rows : Array Row} {pt : Array Float} {lk : Link} {nm : IdName} {g : Poly}
    (h : genSec x rows pt lk nm = some g) :
    ∃ ts, x.secTerms nm = some ts ∧ constantArgmin x.nh rows ts (guessArgmin pt ts) = true ∧
      x.genOf lk.vars ts (guessArgmin pt ts) lk.fixed = some g := by
  unfold genSec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ts, hts, hg⟩ := h
  by_cases hca : constantArgmin x.nh rows ts (guessArgmin pt ts) = true
  · rw [if_pos hca] at hg
    exact ⟨ts, hts, hca, hg⟩
  · rw [if_neg hca] at hg
    exact absurd hg (by simp)

/-- A base identity's generator is the initial form on the cell's own argmin set. -/
theorem genBase_spec {x : Ctx} {c : Cell} {lk : Link} {nm : IdName} {g : Poly} (h : genBase x c lk nm = some g) :
    ∃ ts labs S, x.baseTerms nm = some ts ∧ (nm, labs) ∈ c.argmin ∧ labs.mapM (findLab ts) = some S ∧
      x.genOf lk.vars ts S.toList lk.fixed = some g := by
  unfold genBase at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ts, hts, ⟨nm', labs⟩, hfind, S, hS, hg⟩ := h
  have hmem := Array.mem_of_find?_eq_some hfind
  have hnm : nm' = nm := by simpa using Array.find?_some hfind
  subst hnm
  exact ⟨ts, labs, S, hts, hmem, hS, hg⟩

/-- The generator of a name: a row `D` built from the trees, a base identity on the cell's argmin set, or a secondary
identity whose argmin set is certified constant on `Π`. -/
theorem genFor_spec {x : Ctx} {c : Cell} {rows : Array Row} {pt : Array Float} {lk : Link} {nmS : String} {g : Poly}
    (h : genFor x c rows pt lk nmS = some g) :
    ∃ nm, IdName.parse nmS = some nm ∧
      ((∃ k l, nm = .dist k l ∧ k < l ∧ l < 6 ∧ x.distGen lk.vars k l = some g) ∨
       (isBase nm = true ∧ genBase x c lk nm = some g) ∨
       (isBase nm = false ∧ (∀ k l, nm ≠ .dist k l) ∧ genSec x rows pt lk nm = some g)) := by
  unfold genFor at h
  split at h
  · exact absurd h (by simp)
  · rename_i k l hp
    refine ⟨.dist k l, hp, Or.inl ?_⟩
    by_cases hkl : (k < l && l < 6) = true
    · rw [if_pos hkl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hkl
      exact ⟨k, l, rfl, hkl.1, hkl.2, h⟩
    · rw [if_neg hkl] at h
      exact absurd h (by simp)
  · rename_i nm hnd hp
    refine ⟨nm, hp, Or.inr ?_⟩
    by_cases hb : isBase nm = true
    · rw [if_pos hb] at h
      exact Or.inl ⟨hb, h⟩
    · rw [if_neg hb] at h
      exact Or.inr ⟨by simpa using hb, fun k l he => hnd k l (by rw [he]), h⟩

theorem parseAll_lookup : ∀ {certs : List (String × String)} {ps : List (String × Cert)},
    parseAll certs = some ps → ∀ {id : String} {c : Cert}, ps.lookup id = some c →
      ∃ txt, (id, txt) ∈ certs ∧ parseCert txt = some c
  | [], ps, h, id, c, hl => by
    simp [parseAll] at h
    subst h
    simp at hl
  | (id', txt) :: rest, ps, h, id, c, hl => by
    simp only [parseAll, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨c', hc', r, hr, rfl⟩ := h
    by_cases hid : id = id'
    · subst hid
      simp only [List.lookup, beq_self_eq_true] at hl
      cases hl
      exact ⟨txt, by simp, hc'⟩
    · have hne : (id == id') = false := by simpa using hid
      simp only [List.lookup, hne] at hl
      obtain ⟨t, ht, hp⟩ := parseAll_lookup hr hl
      exact ⟨t, List.mem_cons_of_mem _ ht, hp⟩

/-- The certificates of a chunk are the readings by `parseCert` of the given texts, and the open cells are those of
the list. -/
theorem prepare_spec {cls : Nat} {n6 cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {cd : ChunkData}
    (h : prepare cls n6 cellsTxt singleTxt linksTxt passTxt openTxt certs = some cd) :
    parseAll certs = some cd.certs ∧ cd.opens = openCells cls openTxt ∧
      cd.cells = (cellsTxt.splitOn "\n").toArray := by
  unfold prepare at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨n6j, _, dg, _, parsed, hp, ⟨single, links, pass⟩, _, hcd⟩ := h
  cases hcd
  exact ⟨hp, rfl, rfl⟩

end L6.F34
