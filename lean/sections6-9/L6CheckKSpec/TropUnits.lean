import Lean6.Special.Comp.D88.Trop.LitN4
import Lean6.Special.Comp.D88.Trop.LitKC

/-!
# Lemma 6.19(a)(ii) in the kernel

The statements of `Lean6.Special.Comp.D88.Trop.n4_units_ok` and `kc_units_ok` (every coefficient of `G`, a polynomial
in the masses, is nonzero at `μ₀ = (1, 2, 3, 30)` modulo `65521`; the monomials of each polynomial are distinct and have
at most seventeen entries; the coefficients have at most four variables), with `G` the literals `GN4`, `GKC` of
lean6_special (`Comp/D88/Trop/LitN4`, `LitKC`), by kernel evaluation (`decide +kernel`) instead of `native_decide`. The
imports have no `native_decide`. `L6CheckKSpec.TropSame` checks that the statements are those of lean6_special.
-/

namespace Lean6.Special.Comp.D88.TropK

open Lean6.Special.Comp.D88.Trop

/-- **(ii) for `N4`**, by the kernel. -/
theorem n4_units_ok : checkUnits 65521 [1, 2, 3, 30] GN4 = true := by decide +kernel

/-- **(ii) for `KC`**, by the kernel. -/
theorem kc_units_ok : checkUnits 65521 [1, 2, 3, 30] GKC = true := by decide +kernel

end Lean6.Special.Comp.D88.TropK
