import L6Sound.Common.Farkas
import L6Sound.Poly.Sound
import L6Sound.F2.Oracle
import L6Sound.F34.Meaning

/-!
# The checkers composed with Lemma 4.6 and with the soundness of the cofactor certificates

* `F2.discard_no_solution`: every linear program that the search of F2 discards has no solution of its strict form
  (the cell, or the partial cell with the relaxation of `ℓ(x) ≤ 0`, is empty).
* `F34.single_strict`: at a single-term cell (Lemma 5.1), at every point of the cell polyhedron `Π`, every other term
  of the named identity has a strictly larger exponent (its row `e_k − e_i ≤ 0` fails at every point of `Π`).
* `F34.constantArgmin_strict`: the argmin set of a secondary identity used in a core is constant on `Π`.
* `F34.core_cell_excluded`: at a core cell, if the certificate text passes `checkCert`, its polynomial `h(m)` is
  nonzero at the point `hPoint F` and vanishes, in every commutative ring, wherever the initial forms of the named
  identities (computed in Lean from the cell, with `m_F = 1` if `F ≥ 0`) vanish (Lemma 5.2).
* `F34.chunk_meaning`: for a chunk of cells whose check passes, and whose certificate texts all pass `checkCert`,
  every cell of the chunk is one of the 43 open cells, a single-term cell with the conclusion of `single_strict`, or a
  core cell with the conclusion of `core_cell_excluded`.

The interpretation of the rows (exponent forms of the terms), of `genFor` (initial forms) and of the trees is the
framework of Sections 2–5 of the paper, stated there; these statements are about the Lean functions that implement it.
-/

namespace L6

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **F2.** A program discarded by the search (`decideLP … = (false, _)`) has no solution of its strict form. -/
theorem F2.discard_no_solution {rows : Array Row} {nv : Nat} (h : (F2.decideLP rows nv).1 = false)
    (hgt : ℕ → K) : ¬ ∀ r ∈ rows, r.StrictHolds nv hgt :=
  fun hall => Farkas.check_sound_strict_all (F2.decideLP_discard h) hgt hall

/-- An accepted certificate for `rows.push r` shows that `r` fails at every point of the strict form of `rows`. -/
theorem push_no_solution {nh : Nat} {rows : Array Row} {r : Row} {cert : List (ℕ × Int)}
    (hc : Farkas.check nh (rows.push r) cert = true) (hgt : ℕ → K)
    (hrows : ∀ q ∈ rows, q.StrictHolds nh hgt) : ¬ r.StrictHolds nh hgt := by
  intro hr
  refine Farkas.check_sound_strict_all hc hgt fun q hq => ?_
  rcases Array.mem_push.mp hq with hq | hq
  · exact hrows q hq
  · subst hq; exact hr

/-- **F3 (Lemma 5.1).** At a single-term cell, at every point of the strict form of `Π`, no other term of the named
identity has an exponent at most that of the named term. -/
theorem F34.single_strict {x : F34.Ctx} {rows : Array Row} {nm : F34.IdName} {lab : F34.Lab}
    (h : F34.checkSingle x rows nm lab = true) :
    ∃ ts i, x.secTerms nm = some ts ∧ F34.findLab ts lab = some i ∧
      ∀ k, k < ts.size → k ≠ i → ∀ hgt : ℕ → K, (∀ r ∈ rows, r.StrictHolds x.nh hgt) →
        ¬ (F34.rowLe ts k i).StrictHolds x.nh hgt := by
  obtain ⟨ts, i, hts, hi, hk⟩ := F34.checkSingle_spec h
  exact ⟨ts, i, hts, hi, fun k hk' hki hgt hrows => push_no_solution (hk k hk' hki) hgt hrows⟩

/-- **F4, argmin sets.** For a secondary identity used in a core, on the strict form of `Π` the terms of `S` have
equal exponents (neither `e_k − e_{i₀} > 0` nor `e_{i₀} − e_k > 0` is possible) and every other term has a strictly
larger exponent (`e_k − e_{i₀} ≤ 0` is impossible). -/
theorem F34.constantArgmin_strict {nh : Nat} {rows : Array Row} {ts : Array F34.Term} {S : List Nat}
    (h : F34.constantArgmin nh rows ts S = true) :
    ∃ i0 rest, S = i0 :: rest ∧ ∀ k, k < ts.size → k ≠ i0 → ∀ hgt : ℕ → K, (∀ r ∈ rows, r.StrictHolds nh hgt) →
      (k ∈ S → ¬ (F34.rowGeS ts k i0).StrictHolds nh hgt ∧ ¬ (F34.rowGeS ts i0 k).StrictHolds nh hgt) ∧
      (k ∉ S → ¬ (F34.rowLe ts k i0).StrictHolds nh hgt) := by
  obtain ⟨i0, rest, hS, hk⟩ := F34.constantArgmin_spec h
  refine ⟨i0, rest, hS, fun k hk' hki hgt hrows => ⟨fun hm => ?_, fun hm => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := (hk k hk' hki).1 hm
    exact ⟨push_no_solution h1 hgt hrows, push_no_solution h2 hgt hrows⟩
  · exact push_no_solution ((hk k hk' hki).2 hm) hgt hrows

/-- **F4, the cores, from the meaning of the certificate** (the form shared with later versions): at a core cell
whose link passes, a certificate with `Poly.CertMeaning` gives `h(m)`, nonzero at `hPoint F`, vanishing wherever the
Lean initial forms of the named identities vanish. -/
theorem F34.core_cell_excluded_of_meaning {x : F34.Ctx} {c : F34.Cell} {rows : Array Row} {pt : Array Float}
    {lk : F34.Link} {cert : Poly.Cert} (hlink : F34.checkLink x c rows pt lk cert = true)
    (hm : Poly.CertMeaning cert) :
    (∀ {R : Type} [CommRing R] (φ : ℕ → R),
      (∀ i, i < lk.names.size → ∀ g, F34.genFor x c rows pt lk lk.names[i]! = some g →
        Poly.eval (6 + cert.nvar) φ g = 0) → Poly.eval 6 φ cert.h = 0) ∧
    Poly.eval 6 (fun i => (Poly.hPoint cert.fixed).getD i (0 : ℤ)) cert.h ≠ 0 := by
  obtain ⟨_, _, hlen, hgen⟩ := F34.checkLink_spec hlink
  refine ⟨fun φ hz => hm.1 φ fun g hg => ?_, hm.2⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hi' : i < lk.names.size := by rw [← hlen]; exact hi
  have := hz i hi' _ (hgen i hi')
  rwa [Poly.eval_normalize, getElem!_pos cert.gens i hi] at this

/-- **F4, the cores (Lemma 5.2).** At a core cell whose link passes, a certificate that passes `checkParsed` gives
`h(m)`, nonzero at `hPoint F`, vanishing wherever the Lean initial forms of the named identities vanish. -/
theorem F34.core_cell_excluded {x : F34.Ctx} {c : F34.Cell} {rows : Array Row} {pt : Array Float} {lk : F34.Link}
    {cert : Poly.Cert} (hlink : F34.checkLink x c rows pt lk cert = true) (hok : Poly.checkParsed cert = true) :
    (∀ {R : Type} [CommRing R] (φ : ℕ → R),
      (∀ i, i < lk.names.size → ∀ g, F34.genFor x c rows pt lk lk.names[i]! = some g →
        Poly.eval (6 + cert.nvar) φ g = 0) → Poly.eval 6 φ cert.h = 0) ∧
    Poly.eval 6 (fun i => (Poly.hPoint cert.fixed).getD i (0 : ℤ)) cert.h ≠ 0 := by
  obtain ⟨_, _, hlen, hgen⟩ := F34.checkLink_spec hlink
  refine ⟨fun φ hz => ?_, Poly.checkParsed_nonzero hok⟩
  rw [← Poly.eval_h_masses hok φ]
  refine Poly.checkParsed_vanish hok φ fun g hg => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hi' : i < lk.names.size := by rw [← hlen]; exact hi
  have := hz i hi' _ (hgen i hi')
  rwa [Poly.eval_normalize, getElem!_pos cert.gens i hi] at this

/-- **F3/F4, one chunk.** If the check of a chunk passes and all its certificate texts pass `checkCert`, every cell
of the chunk is open, or a single-term cell (conclusion of `single_strict`), or a core cell (conclusion of
`core_cell_excluded`). -/
theorem F34.chunk_meaning {cls : Nat} {n6 cellsTxt singleTxt linksTxt passTxt openTxt : String}
    {certs : List (String × String)} {lo hi : Nat} {expected : F34.Counts}
    (h : F34.checkChunk cls n6 cellsTxt singleTxt linksTxt passTxt openTxt certs lo hi expected = true)
    (hcerts : ∀ p ∈ certs, Poly.checkCert p.2 = true) :
    ∃ cd, F34.prepare cls n6 cellsTxt singleTxt linksTxt passTxt openTxt certs = some cd ∧
      ∀ idx, lo ≤ idx → idx < hi →
        cd.opens.contains idx = true ∨
        (∃ nm lab x c rows pt, cd.single.getD idx none = some (nm, lab) ∧
          F34.cellCtx cd idx = some (x, c, rows, pt) ∧
          ∃ ts i, x.secTerms nm = some ts ∧ F34.findLab ts lab = some i ∧
            ∀ k, k < ts.size → k ≠ i → ∀ hgt : ℕ → ℚ, (∀ r ∈ rows, r.StrictHolds x.nh hgt) →
              ¬ (F34.rowLe ts k i).StrictHolds x.nh hgt) ∨
        (∃ lk cert x c rows pt, cd.links.getD idx none = some lk ∧ cd.certs.lookup lk.cert = some cert ∧
          F34.cellCtx cd idx = some (x, c, rows, pt) ∧
          (∀ {R : Type} [CommRing R] (φ : ℕ → R),
            (∀ i, i < lk.names.size → ∀ g, F34.genFor x c rows pt lk lk.names[i]! = some g →
              Poly.eval (6 + cert.nvar) φ g = 0) → Poly.eval 6 φ cert.h = 0) ∧
          Poly.eval 6 (fun i => (Poly.hPoint cert.fixed).getD i (0 : ℤ)) cert.h ≠ 0) := by
  obtain ⟨cd, hcd, _, _, hall, _⟩ := F34.checkChunk_spec h
  refine ⟨cd, hcd, fun idx h1 h2 => ?_⟩
  obtain ⟨_, hk⟩ := F34.cellKind_spec (hall idx h1 h2)
  rcases hk with ho | ⟨nm, lab, x, c, rows, pt, hs, hctx, hchk⟩ | ⟨lk, cert, x, c, rows, pt, hl, hcert, hctx, hlink⟩
  · exact Or.inl ho
  · exact Or.inr (Or.inl ⟨nm, lab, x, c, rows, pt, hs, hctx, F34.single_strict hchk⟩)
  · refine Or.inr (Or.inr ⟨lk, cert, x, c, rows, pt, hl, hcert, hctx, ?_⟩)
    have hparse := (F34.prepare_spec hcd).1
    obtain ⟨txt, hmem, hp⟩ := F34.parseAll_lookup hparse hcert
    have hok : Poly.checkParsed cert = true := by
      have := hcerts _ hmem
      unfold Poly.checkCert at this
      rw [hp] at this
      exact this
    exact F34.core_cell_excluded hlink hok

end L6
