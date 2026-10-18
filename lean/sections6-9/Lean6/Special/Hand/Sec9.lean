import Lean6.Special.Hand.Sec9.Basic
import Lean6.Special.Hand.Sec9.Clique3
import Lean6.Special.Hand.Sec9.Centred
import Lean6.Special.Hand.Sec9.Centred2

/-!
# Algebra inside the hand proofs of Section 9 (items H9.1–H9.15 of `PLAN.md`)

Section 9 of the paper (hand explanations of the cells) proves its lemmas by hand from relations among leading
coefficients; these modules check the algebraic and arithmetic steps of those proofs. The relations themselves come
from the argmin sets, the trees and the identities of §2.3 (hand arguments, not formalized here); where a proof uses
linear algebra (the rank-one argument of Theorem 9.9) or exponent bookkeeping, the algebraic consequence is checked.

* `Basic`: cube roots of unity; Lemma 9.1 (`ssum`), Lemmas 9.2–9.4 (exponent comparisons), 9.5 (`handB0`),
  9.6 (`handK`), 9.7 (`handL_relations`, `handL_impossible`, `handL`), 9.8 (`cliquesum`), 9.16–9.17
  (`clique_x_zero`, `clique_orders`), 9.20 (`handP4`, `handP4_pos`).
* `Clique3`: Theorem 9.9 (`clique3_i`, `clique3_ii_rank`, `clique3_ii_relation`, `clique3_ii`, `clique3_iii`) and the
  polynomial `Q_T` (`QT_identity`, `QT_zero_iff`).
* `Centred`: Lemmas 9.11 (`handR_relations`, the resultant `N`, `N_eval_zero`, `N_special`, `N_ne_zero`,
  `handR_kappa`), 9.12 (`handR6_relation`, `handR6_product`, `H6poly_ne_zero`, `handR6_pos`), 9.13 (`handW3_core`,
  `handW3`).
* `Centred2`: Lemmas 9.14 (`handEQ2`, `handEQ2_pos`), 9.15 (`handQ_signs`, `handQ_prod_ne_zero`,
  `handQ_not_all_equal`, `handQ_two`), 9.22 (`handTQ`).
-/
