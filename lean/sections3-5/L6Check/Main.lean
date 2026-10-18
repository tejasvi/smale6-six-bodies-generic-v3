import L6Check.F1.Axioms
import L6Check.F2.Axioms
import L6Check.F34.Axioms
import L6Check.F34.All
import L6Check.F34.AllCerts
import L6Check.F5.Axioms
import L6Check.F5.Print
import L6Check.Poly.Axioms
import L6Check.F2S.Axioms
import L6Check.F2S.AxiomsL
import L6Check.F2S.AxiomsN
import L6Check.F34S.Axioms
import L6Check.F34S.AxiomsOf
import L6Check.F34S.AxiomsIn
import L6Sound.Composed

/-!
# Lean checks of the computations of Sections 3–5 (v1): the entry point

Building this module builds every check of the five families (each `native_decide` theorem is evaluated when its
module is built) and prints the axioms of the main theorems. See `LEAN_CHECKS.md`.

* F1 (Proposition 3.1): `L6F1.F1_main` and its corollaries (`L6Check.F1.Main`).
* F2 (Proposition 4.5): `L6.F2.f2_all`, `L6.F2.f2_totals`, `L6.F2.f2_classes_with_cells`, `L6.F2.tree_counts`.
* F3/F4 (Proposition 5.3): the chunk theorems `L6.F34.Checks.F34_c<class>_k<k>`, `F34_cover`, `F34_chunks_cover`,
  `F34_totals`, and the 1,928 certificate checks `L6.Poly.Checks.cert_<certid>`.
* F5 (Proposition 5.9): `L6F5.F5_main` and the facts after it.
* Soundness: `L6.Farkas.check_sound`, `check_sound_strict` (Lemma 4.6), `L6.Poly.checkCert_sound` (Lemma 5.2's
  certificates), and the compositions `L6.F2.discard_no_solution`, `L6.F34.single_strict`,
  `L6.F34.constantArgmin_strict`, `L6.F34.core_cell_excluded`, `L6.F34.chunk_meaning`.
-/

#print axioms L6.Farkas.check_sound
#print axioms L6.Farkas.check_sound_strict
#print axioms L6.Farkas.check_sound_strict_all
#print axioms L6.Poly.checkCert_sound
#print axioms L6.Poly.checkParsed_vanish
#print axioms L6.Poly.checkParsed_nonzero
#print axioms L6.F2.discard_no_solution
#print axioms L6.F34.single_strict
#print axioms L6.F34.constantArgmin_strict
#print axioms L6.F34.core_cell_excluded
#print axioms L6.F34.chunk_meaning
#print axioms L6.F34.Checks.F34_all
#print axioms L6.F34.Checks.F34_all_totals
#print axioms L6.F34.Checks.F34_all_cover
#print axioms L6.F34.Checks.F34_all_certs
#print axioms L6.F34.Checks.F34_all_meaning
#print axioms L6.Poly.checkParsed_meaning
#print axioms L6.Poly.checkCert_meaning
#print axioms L6.F34.core_cell_excluded_of_meaning
