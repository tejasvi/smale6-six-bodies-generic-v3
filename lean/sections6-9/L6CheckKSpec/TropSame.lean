import L6CheckKSpec.TropUnits
import L6CheckKSpec.TropMem
import Lean6.Special.D88.Trop.Final

/-!
# The kernel versions of the checks of Lemma 6.19(a) have the statements of lean6_special

Each `example` states that a theorem of `Lean6.Special.Comp.D88.TropK` or `Lean6.Special.D88.TropK` has the type of
the theorem of the same name in `Lean6.Special.Comp.D88.Trop` or `Lean6.Special.D88.Trop` (`native_decide`, or proved
from the compiled runs). No module imports this one: it imports the compiled runs only to compare the statements.
-/

namespace Lean6.Special.Comp.D88.TropK

example : type_of% @Lean6.Special.Comp.D88.Trop.n4_units_ok := n4_units_ok
example : type_of% @Lean6.Special.Comp.D88.Trop.kc_units_ok := kc_units_ok

end Lean6.Special.Comp.D88.TropK

example : type_of% @Lean6.Special.D88.Trop.n4_G_mem := @Lean6.Special.D88.TropK.n4_G_mem
example : type_of% @Lean6.Special.D88.Trop.kc_G_mem := @Lean6.Special.D88.TropK.kc_G_mem
