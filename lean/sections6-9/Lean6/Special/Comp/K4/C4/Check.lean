import Lean6.Special.Comp.K4.C4.Sys
import Lean6.Special.Comp.K4.C4.GB

/-!
# The check of Lemma 7.9 and of §7.4 on one chart (no Mathlib)

`chartOK μ p ch`: the Buchberger engine finds a constant `≢ 0 (mod p)` in the ideal generated over `ℤ/p` by the
eleven equations of `Z(μ)` on the chart `ch` (`Lean6.Special.K4.C4.Final` turns this into the absence of common
zeros and into `1 ∈ Ideal.span`). The masses of the paper are `μ₀ = (3, 5, 7, 11)` (Lemma 7.9) and `(1, 1, 1, 1)`
(§7.4); the primes `32003` and `1073741789`.
-/

namespace Lean6.Special.Comp.C4

/-- `μ₀ = (3, 5, 7, 11)`. -/
def mu0 : List Int := [3, 5, 7, 11]

/-- Equal masses. -/
def mu1 : List Int := [1, 1, 1, 1]

/-- The fuel: at most `10⁶` critical pairs and `10⁸` reduction steps per reduction (far more than needed). -/
def chartOK (μ : List Int) (p : Nat) (ch : Nat × Nat) : Bool :=
  GB.unitTest p 9 1000000 100000000 ((chartEqs μ ch).map (toMod p))

theorem charts_eq : charts = [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8)] := rfl

end Lean6.Special.Comp.C4
