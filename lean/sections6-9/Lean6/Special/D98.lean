import Lean6.Special.D98.Shapes
import Lean6.Special.D98.Lemma69Check
import Lean6.Special.D98.P93
import Lean6.Special.D98.Heavy
import Lean6.Special.D98.Check127Final

/-!
# Sections 6.4–6.6: the three-body shapes, diagram 98 and diagram 93

* Lemma 6.9 (`lem:three`): `lagrange_shape`, `lq_*` (the Lagrange case), `Q_eq_F` (the collinear quintics),
  `S_generic` (degree `34`, leading coefficient `(μ₁ + μ₂)⁴`), `lemma69_check_1_2_7`, `lemma69_check_1_2_8`,
  `lemma69_check_2_3_11` (the stored eliminants have the square-free part of `S_μ`).
* Lemma 6.13 (`lem:dominant`) at `(1, 2, 40)`: `lagrange_bounds`, `collinear_tails`, `heavy_roots`,
  `heavy_signed_sums`; the check at `(1, 2, 7)` and `(1, 2, 8)`: `check_1_2_7`, `check_1_2_7_min`, `check_1_2_8`,
  `check_rho_product`.
* Theorem 6.15 (`thm:d93`): `no_common_root_1_2_7`, `P93_eval_1_2_7_ne_zero`.
-/
