import CC6Full

/-! The axioms of the proved theorems (run with `lake env lean Check.lean`). -/

-- Part I: from infinitely many central configurations to a germ with `ℓ ≤ 0`
#print axioms CC6Full.exists_slice_point
#print axioms CC6Full.finitelyManyCC_of_finite
#print axioms CC6Full.r2_fibre_finite
#print axioms CC6Full.exists_curve
#print axioms CC6Full.Expansion_exists
#print axioms CC6Full.degree_zero
#print axioms CC6Full.Curve.U_const
#print axioms CC6Full.Curve.balancing
#print axioms CC6Full.Curve.exists_singular_place_ell_nonpos
#print axioms CC6Full.germOfPlace_ell
#print axioms CC6Full.exists_germ
-- Part II: germs
#print axioms CC6Full.initial
#print axioms CC6Full.Germ.relabel_ell
#print axioms CC6Full.Germ.swap_ell
#print axioms CC6Full.Germ.scale
#print axioms CC6Full.Germ.torque
#print axioms CC6Full.Germ.partialVirial
#print axioms CC6Full.Germ.lagrange
#print axioms CC6Full.Germ.O1
#print axioms CC6Full.Germ.O5_z
#print axioms CC6Full.Germ.O6_z
#print axioms CC6Full.Germ.E3
#print axioms CC6Full.Germ.E5
#print axioms CC6Full.Germ.E6
#print axioms CC6Full.Germ.C3_z
#print axioms CC6Full.Germ.C4_z
-- Section 8
#print axioms CC6Full.main_of_germExclusion
-- Sections 6, 7 (hand parts)
#print axioms CC6Full.Six.d89_excluded
#print axioms CC6Full.Six.d98_lead
#print axioms CC6Full.Six.d93_lead
#print axioms CC6Full.Six.three_shape
#print axioms CC6Full.lem_E4
#print axioms CC6Full.elim_integral_int
-- Sections 6, 7 (from the certificate facts) and the interface
#print axioms CC6Full.Six.d98_poly
#print axioms CC6Full.Six.d93_poly
#print axioms CC6Full.Six.d64_poly
#print axioms CC6Full.Six.d66_poly
#print axioms CC6Full.Six.d88_poly
#print axioms CC6Full.Six.d94_poly
#print axioms CC6Full.goodred
#print axioms CC6Full.encard_complexZeros_le
#print axioms CC6Full.Identity.single
#print axioms CC6Full.core
#print axioms CC6Full.Cell.core_b_int
#print axioms CC6Full.seven_excluded
#print axioms CC6Full.main_of_classesExcluded
#print axioms CC6Full.exists_pos_aeval_ne_zero
