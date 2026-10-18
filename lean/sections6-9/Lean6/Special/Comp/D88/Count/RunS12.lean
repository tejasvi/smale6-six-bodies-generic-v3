import Lean6.Special.Comp.D88.Count.F4
import Lean6.Special.Comp.D88.Count.DimCheck
import Lean6.Special.Comp.D88.Count.Sys

/-!
# Lemma 6.19(b) for S12: the run of the F4 engine (no Mathlib)

The F4 engine of `Comp.Count.F4` computes a Gröbner basis of the engine input `s12Inputs` (the system S12 at
μ₀ = (1, 2, 3, 30) reduced modulo `65521`) in the degree reverse lexicographic order, and `dimCheck` verifies that the
staircase of its leading monomials contains `0`, has at most `20316` elements and is closed under the border. Every
element of the output vanishes at every common zero of the input (`Lean6.Special.D88.Count.f4_good`); with
`count_S12_of` this gives the bound of Lemma 6.19(b) for S12.
-/

namespace Lean6.Special.Comp.Count

/-- The run: `11` unknowns, `p = 65521`, the reduction in `64` parallel chunks. -/
def s12Cfg : Cfg := { n := 11, p := 65521, chunks := 64 }

/-- **The F4 run for S12 passes the dimension check with `N = 20316`.** -/
theorem s12_f4_ok : dimCheck 65521 11 (f4Basis s12Cfg s12Inputs) 20316 = true := by native_decide

end Lean6.Special.Comp.Count
