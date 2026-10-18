import Lean6.Special.D88.Count.Final
import Lean6.Special.D88.Count.F4Sound
import Lean6.Special.Comp.D88.Count.RunKC
import Lean6.Special.Comp.D88.Count.RunS12

/-! The axioms of the F4 engine's soundness theorem and of its runs for KC′ and S12, and the assembly of Lemma 6.19(b)
from them (`lake env lean gen/d88count/f4_axioms.lean`). -/

namespace Lean6.Special.D88.Count

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.Count

/-- Lemma 6.19(b) for KC′ from the F4 run (assembly test). -/
theorem count_KC_f4 : Module.Finite (ZMod 65521) AqKC ∧ Module.finrank (ZMod 65521) AqKC ≤ 4788 :=
  count_KC_of (f4Basis kcCfg kcInputs) kc_f4_ok fun R _ inst x hF =>
    @f4_good kcCfg ⟨by decide⟩ kcInputs R _ inst x hF

/-- Lemma 6.19(b) for S12 from the F4 run (assembly test). -/
theorem count_S12_f4 : Module.Finite (ZMod 65521) AqS12 ∧ Module.finrank (ZMod 65521) AqS12 ≤ 20316 :=
  count_S12_of (f4Basis s12Cfg s12Inputs) s12_f4_ok fun R _ inst x hF =>
    @f4_good s12Cfg ⟨by decide⟩ s12Inputs R _ inst x hF

#print axioms f4_good
#print axioms kc_f4_ok
#print axioms s12_f4_ok
#print axioms count_KC_f4
#print axioms count_S12_f4

end Lean6.Special.D88.Count
