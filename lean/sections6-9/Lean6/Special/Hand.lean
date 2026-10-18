import Lean6.Special.Hand.Identities
import Lean6.Special.Hand.Systems
import Lean6.Special.Hand.Sec2
import Lean6.Special.Hand.Sec3
import Lean6.Special.Hand.Sec4
import Lean6.Special.Hand.Sec6
import Lean6.Special.Hand.Sec7
import Lean6.Special.Hand.Sec9

/-!
# The algebra and the finite computations inside the hand proofs

* Section 2 (`Sec2`): the identities of §2.3 for any number of bodies (`subset_sum`, `torque_zero`, `partial_virial`,
  `difference`, `U_eq_sum`, `sep_sum`), Lemma 2.3(a) (`lemma_2_3_a`), the exchange `ι` (`iota_invol`, `iota_rows`,
  `z_iota`, `w_iota`), the exponent arithmetic of Lemmas 2.8 and 2.11 (`edgeF_strictAnti`, `E2_arith`, `E3_arith`,
  `E6_arith`, `C2_arith`, `C4_arith`, …), the fibre bound (`fibre_bound`).
* Section 3 (`Sec3`): `triangle_one_circle`. Section 4 (`Sec4`): Lemma 4.3(b) (`root_coefficient`,
  `root_two_children_ne_zero`).
* Section 6 (`Identities`, `Systems`, `Sec6`): Lemmas 6.1–6.3, Props 6.4–6.8 (`rewrite_identity`, `binary_masses`,
  `prop68_*`, `F1_*`, `F4_*`, `d90_*`, `d89_*`, `d82_exponents`, `d81_exponents`), the steps of Lemma 6.9
  (`shape_positions`, `lagrange_p3`, `lagrange_quadratic_j`, `collinear_shape`, …), Thm 6.12 (`cross_square`,
  `torque_lead_coeff`), Remark 6.14 (`split_signed_sum`), Thm 6.15 (`d93_Phi3_zero`), Lemma 6.17 (`ttest_*`), Sec. 6.7
  (`torque_identity`, `com_identity`, `N4.yeq2_of_S11`, `KC.yeq2_of_KC12`).
* Section 7 (`Sec7`): Lemmas 7.1–7.5 (`sum_mass_Phi`, `const_force`, `d64_*`), Lemma 7.6 (`E4_noncollinear`,
  `E4_collinear`, from the conclusions of its linear-algebra case split), §7.3 (`II_of_iii`, `III_of_eta`,
  `bideg_*`).
* Section 9 (`Sec9`, namespace `Hand.Sec9`): Lemmas 9.1–9.22 and Theorem 9.9 (`ssum_zero`, `handB0`, `handK`, `handL`,
  `cliquesum`, `clique3_i`, `clique3_ii`, `clique3_iii`, `QT_identity`, `QT_zero_iff`, `N_ne_zero`, `handR_kappa`,
  `H6poly_ne_zero`, `handR6_pos`, `handW3`, `handEQ2`, `handQ_prod_ne_zero`, `handP4`, `handTQ`, …).
-/
