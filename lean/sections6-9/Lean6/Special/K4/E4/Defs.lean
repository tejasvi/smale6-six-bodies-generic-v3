import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# The forms of Lemma 7.6 and the masses, as definitions

The definitions used in the statements of `Final.lean` (`lemma_7_7`, `check_3_5_7_11`), kept apart from the checks
so that a module can state these results without importing a computation.
-/

namespace Lean6.Special.K4.E4

/-! ## The forms, as in the paper -/

/-- `A_k = Σ_{l ≠ k} ε_{kl} μ_l q_l` with `ε_{kl} = ω ^ e_{kl}`. -/
def Aeps (ω : ℂ) (μ : Fin 4 → ℂ) (e : Fin 4 → Fin 4 → ℕ) (q : Fin 4 → ℂ) (k : Fin 4) : ℂ :=
  ∑ l, if l = k then 0 else ω ^ e k l * μ l * q l

/-- `q` is a common zero of the seven cubic forms `F_ε`. -/
def FZero (ω : ℂ) (μ : Fin 4 → ℂ) (e : Fin 4 → Fin 4 → ℕ) (q : Fin 4 → ℂ) : Prop :=
  (∀ j k : Fin 4, j < k → q j ^ 2 * Aeps ω μ e q k - q k ^ 2 * Aeps ω μ e q j = 0) ∧
    ∑ k, μ k * q k ^ 3 = 0

/-- The form `G_σ,k = Σ_{l ≠ k} σ_{kl} μ_l ∏_{j ≠ k, l} (ξ_k − ξ_j)²`. -/
def Gsig (μ : Fin 4 → ℂ) (σ : Fin 4 → Fin 4 → ℤ) (ξ : Fin 4 → ℂ) (k : Fin 4) : ℂ :=
  ∑ l, if l = k then 0 else (σ k l : ℂ) * μ l * ∏ j, if j = k ∨ j = l then 1 else (ξ k - ξ j) ^ 2

/-- `ξ ∈ ℂ³` (the coordinates `ξ_2, ξ_3, ξ_4`, with `ξ_1 = 0`) is a common zero of the four forms `G_σ`. -/
def GZero (μ : Fin 4 → ℂ) (σ : Fin 4 → Fin 4 → ℤ) (ξ : Fin 3 → ℂ) : Prop :=
  ∀ k : Fin 4, Gsig μ σ ![0, ξ 0, ξ 1, ξ 2] k = 0

/-! ## From the paper's forms to the checked lists -/

/-- The masses of a list. -/
def muOf (μl : List ℤ) : Fin 4 → ℂ := fun k => (μl.getD k 0 : ℂ)

/-- The pattern list of a symmetric pattern. -/
def vOf (e : Fin 4 → Fin 4 → ℕ) : List ℕ := [e 0 1 % 3, e 0 2 % 3, e 0 3 % 3, e 1 2 % 3, e 1 3 % 3, e 2 3 % 3]

/-- The sign list of a sign pattern. -/
def wOf (σ : Fin 4 → Fin 4 → ℤ) : List ℤ := [σ 0 1, σ 0 2, σ 0 3, σ 1 2, σ 1 3, σ 2 3]

/-- The point of `ℂ^ℕ` of `q ∈ ℂ⁴`. -/
def xq {n : ℕ} (q : Fin n → ℂ) : ℕ → ℂ := fun i => if h : i < n then q ⟨i, h⟩ else 0

end Lean6.Special.K4.E4
