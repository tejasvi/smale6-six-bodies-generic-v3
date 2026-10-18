import Lean6.Special.D88.Count.Final
import Lean6.Special.D88.Count.F4Sound
import Lean6.Special.Comp.D88.Count.RunKC
import Lean6.Special.Comp.D88.Count.RunS12

/-!
# Lemma 6.19(b): the two dimension bounds

`count_KC`, `count_S12`: with the equations of §6.7 at `μ₀ = (1, 2, 3, 30)` over `ZMod 65521`,
`(ZMod 65521)[v] ⧸ ⟨KC′(μ₀)⟩` and `(ZMod 65521)[v] ⧸ ⟨S12(μ₀)⟩` are finite-dimensional of dimension at most `4788` and
`20,316`. The bases come from the F4 engine of `Comp.Count.F4` (runs `kc_f4_ok`, `s12_f4_ok`, `native_decide`), every
element of which lies in the ideal by `f4_good`; `count_KC_of`, `count_S12_of` turn the checked staircase into the
bounds through Mathlib's division algorithm.
-/

namespace Lean6.Special.D88.Count

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.Count

/-- **Lemma 6.19(b) for KC′**: `dim (ZMod 65521)[v′] ⧸ ⟨KC′(μ₀)⟩ ≤ 4788`. -/
theorem count_KC : Module.Finite (ZMod 65521) AqKC ∧ Module.finrank (ZMod 65521) AqKC ≤ 4788 :=
  count_KC_of (f4Basis kcCfg kcInputs) kc_f4_ok fun R _ inst x hF =>
    @f4_good kcCfg ⟨by decide⟩ kcInputs R _ inst x hF

/-- **Lemma 6.19(b) for S12**: `dim (ZMod 65521)[v] ⧸ ⟨S12(μ₀)⟩ ≤ 20,316`. -/
theorem count_S12 : Module.Finite (ZMod 65521) AqS12 ∧ Module.finrank (ZMod 65521) AqS12 ≤ 20316 :=
  count_S12_of (f4Basis s12Cfg s12Inputs) s12_f4_ok fun R _ inst x hF =>
    @f4_good s12Cfg ⟨by decide⟩ s12Inputs R _ inst x hF

end Lean6.Special.D88.Count
