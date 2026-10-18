import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The leading systems of Sections 6 and 7

The algebraic systems satisfied by the leading coefficients at a singular place with one of the diagrams of
Table 1. All unknowns are complex; `p` (or `P`) is a symmetric family indexed by the pairs.

* `IsNSys μ z w p`: complex central configurations of `N` bodies in both colours, the system `N(μ)` of §6.4
  (`ss:three`) for `N = 3` and `N₄(μ)` of §6.7 (`ss:d88`) for `N = 4`:
  `z_k = Σ_{l≠k} μ_l p_kl³ (z_k − z_l)`, the same in `w`, and `p_kl² (z_k − z_l)(w_k − w_l) = 1`.
* `IsKC μ X Y p`: the centred system `KC(μ)` of §6.7: `X₄ = 0`, the `X`-equations of `N₄` for the bodies `1, 2, 3`,
  the equation of the centre `0 = Σ_{l≤3} μ_l p_4l³ (X₄ − X_l)`, the `Y`-equations for `1, 2, 3` (none for body
  `4`) and the six distance equations.
* `IsE4 μ ξ η P`: the system `E₄(μ)` of §7.1: complex equilibria of four bodies in both colours,
  `Σ_{l≠k} μ_l P_kl³ (ξ_k − ξ_l) = 0`, the same in `η`, and `P_kl² (ξ_k − ξ_l)(η_k − η_l) = 1`.
* `IsC4 μ ξ η P c`: the system `C₄(μ)` of §7.1: a cluster of four bodies with body `4` at its centre, in
  equilibrium in the colour `ξ` and with the same force `c` on the bodies `1, 2, 3` in the colour `η`:
  the distance equations, `Φ^ξ_k = 0` for all `k`, `Φ^η_k = c` for `k ≤ 3`, `ξ₄ = 0`, `Σ_{k≤3} μ_k ξ_k = 0`.
Bodies are numbered from `0` in Lean: body `4` of the paper's four-body systems is `3 : Fin 4`.
-/

namespace CC6Full

open Finset

/-- A symmetric family indexed by the pairs. -/
def IsSymm {N : ℕ} (p : Fin N → Fin N → ℂ) : Prop := ∀ k l, p k l = p l k

/-- `Φ_k(h) = Σ_{l≠k} μ_l p_kl³ (h_k − h_l)`, the force on body `k` in the colour `h`. -/
def force {N : ℕ} (μ : Fin N → ℂ) (p : Fin N → Fin N → ℂ) (h : Fin N → ℂ) (k : Fin N) : ℂ :=
  ∑ l ∈ univ.erase k, μ l * p k l ^ 3 * (h k - h l)

/-- The distance equations `p_kl² (z_k − z_l)(w_k − w_l) = 1`. -/
def DistEqs {N : ℕ} (p : Fin N → Fin N → ℂ) (z w : Fin N → ℂ) : Prop :=
  ∀ k l, k ≠ l → p k l ^ 2 * (z k - z l) * (w k - w l) = 1

/-- The system `N(μ)` (`N = 3`, §6.4) and `N₄(μ)` (`N = 4`, §6.7): complex central configurations in both colours. -/
def IsNSys {N : ℕ} (μ : Fin N → ℂ) (z w : Fin N → ℂ) (p : Fin N → Fin N → ℂ) : Prop :=
  IsSymm p ∧ (∀ k, z k = force μ p z k) ∧ (∀ k, w k = force μ p w k) ∧ DistEqs p z w

/-- The centred system `KC(μ)` of §6.7 (body `4` of the paper is `3 : Fin 4`). -/
def IsKC (μ : Fin 4 → ℂ) (X Y : Fin 4 → ℂ) (p : Fin 4 → Fin 4 → ℂ) : Prop :=
  IsSymm p ∧ X 3 = 0 ∧ (∀ k : Fin 4, k ≠ 3 → X k = force μ p X k) ∧ force μ p X 3 = 0 ∧
    (∀ k : Fin 4, k ≠ 3 → Y k = force μ p Y k) ∧ DistEqs p X Y

/-- The system `E₄(μ)` of §7.1: complex equilibria of four bodies in both colours. -/
def IsE4 (μ : Fin 4 → ℂ) (ξ η : Fin 4 → ℂ) (P : Fin 4 → Fin 4 → ℂ) : Prop :=
  IsSymm P ∧ (∀ k, force μ P ξ k = 0) ∧ (∀ k, force μ P η k = 0) ∧ DistEqs P ξ η

/-- The system `C₄(μ)` of §7.1, with the force `c` (body `4` of the paper, the centre, is `3 : Fin 4`). -/
def IsC4 (μ : Fin 4 → ℂ) (ξ η : Fin 4 → ℂ) (P : Fin 4 → Fin 4 → ℂ) (c : ℂ) : Prop :=
  IsSymm P ∧ DistEqs P ξ η ∧ (∀ k, force μ P ξ k = 0) ∧ (∀ k : Fin 4, k ≠ 3 → force μ P η k = c) ∧
    ξ 3 = 0 ∧ ∑ k ∈ univ.erase (3 : Fin 4), μ k * ξ k = 0

end CC6Full
