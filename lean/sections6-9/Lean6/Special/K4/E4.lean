import Lean6.Special.K4.E4.Final
import Lean6.Special.K4.E4.Resultants
import Lean6.Special.K4.E4.Algebra
import Lean6.Special.Comp.K4.E4.Pat
import Lean6.Special.K4.E4.Rem
import Lean6.Special.K4.E4.Export

/-!
# Section 7: the four-body system `E_4` (Lemma 7.7 and the check after Proposition 7.8)

* `K4.E4.lemma_7_7`, `K4.E4.check_3_5_7_11` (`Final`): the statements, as complete computations.
* `K4.E4.no_zero_T1/T2/T3`, `res12_*`, `res13_*`, `resR_*`, `R1*_zero` (`Resultants`): the resultants of the hand proof
  for the forms `G_σ`.
* `K4.E4.Alg.*` (`AlgebraIds`, `Algebra`): the steps of cases (I)–(III) for the forms `F_ε`.
* `Comp.E4.free`, `orbit_size`, `inv_invariant`, `inv_separates`, `nine_values`, `relabel_triple`, `conj_triple`,
  `reduction`, `score_counts`, `score_determines`, `reduce_tournaments`, `rep_scores` (`Comp.K4.E4.Pat`): the finite
  checks (patterns, orbits, types, tournaments).
* `K4.E4.remark_7_14_1112`, `remark_7_14_5_2_11_3`, `remark_7_14_1234`, `remark_7_14_2357` (`Rem`): Remark 7.14.
* `K4.E4.macF`, `macFpoly`, `macF_row`, `macF_det_ne_zero_3_5_7_11`, `macF_det_ne_zero_1111`, `macFpoly_det_ne_zero`,
  `F_eq_zero_of_macF_det`, and the same for `macG` (`Export`): the Macaulay matrices for every mass vector and the
  determinants certified by the runs.
-/
