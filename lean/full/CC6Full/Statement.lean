import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# The statement: generic finiteness of planar central configurations of six bodies

Theorem 1.1 (`thm:main`) of the paper *Smale's sixth problem for six bodies in the plane: finiteness of central
configurations for generic masses*:

> There is a nonzero polynomial `F ∈ ℤ[m₁, …, m₆]` with the following property. For every `m ∈ (ℝ_{>0})⁶` with
> `F(m) ≠ 0`, the planar six-body problem with masses `m` has finitely many central configurations up to
> similarity.

The definitions are stated for any number `n` of bodies; body `k` of the paper is `k - 1 : Fin n`. The plane is
`ℂ`. `IsCC`, `Similar` and `FinitelyManyCC` are those of the formalization of the five-body theorem, with `Fin 5`
replaced by `Fin n`.

* `IsCC m q` is equation (1.1) (`eq:cc`): `q` is collision free and for some `λ ∈ ℝ` and `c ∈ ℂ`,
  `λ m_i (q_i - c) = ∑_{j ≠ i} m_i m_j (q_i - q_j) / |q_i - q_j|³` for every `i`.
* `Similar q q'` admits orientation-reversing similarities. This does not change finiteness: if a finite set `S`
  represents all central configurations up to similarity with reflections, then `S` together with the complex
  conjugates of its elements represents them up to orientation-preserving similarity, since the conjugate of a
  central configuration is one.
* `GenericFiniteness n`: a nonzero `F ∈ ℤ[m₁, …, mₙ]` such that every positive mass vector at which `F` does not
  vanish has finitely many central configurations up to similarity. Integer coefficients are those of the paper;
  rational coefficients would give the same statement after clearing denominators. A nonzero polynomial does not
  vanish on any nonempty open subset of `ℝⁿ`, so the statement concerns a dense open set of positive masses
  (`exists_pos_aeval_ne_zero` in `Sanity.lean`).
-/

namespace CC6Full

open Finset

/-- A planar configuration of `n` bodies. -/
abbrev Conf (n : ℕ) := Fin n → ℂ

/-- The bodies are at distinct points. -/
def CollisionFree {n : ℕ} (q : Conf n) : Prop := ∀ i j, i ≠ j → q i ≠ q j

/-- Equation (1.1) (`eq:cc`): `q` is a central configuration for the masses `m`. -/
def IsCC {n : ℕ} (m : Fin n → ℝ) (q : Conf n) : Prop :=
  CollisionFree q ∧ ∃ (lam : ℝ) (c : ℂ), ∀ i,
    ((lam * m i : ℝ) : ℂ) * (q i - c) =
      ∑ j ∈ univ.erase i, ((m i * m j / ‖q i - q j‖ ^ 3 : ℝ) : ℂ) * (q i - q j)

/-- `q'` is the image of `q` under a similarity `z ↦ a z + b` (`a ≠ 0`) of the plane, possibly composed with the
reflection `z ↦ z̄`. -/
def Similar {n : ℕ} (q q' : Conf n) : Prop :=
  ∃ a b : ℂ, a ≠ 0 ∧ ((∀ i, q' i = a * q i + b) ∨ (∀ i, q' i = a * starRingEnd ℂ (q i) + b))

/-- The planar `n`-body problem with masses `m` has finitely many central configurations up to similarity: finitely
many central configurations represent all of them up to similarity. -/
def FinitelyManyCC {n : ℕ} (m : Fin n → ℝ) : Prop :=
  ∃ F : Finset (Conf n), ∀ q, IsCC m q → ∃ q' ∈ F, Similar q' q

/-- Generic finiteness for `n` bodies: some nonzero `F ∈ ℤ[m₁, …, mₙ]` such that the planar `n`-body problem has
finitely many central configurations up to similarity for every positive mass vector `m` with `F(m) ≠ 0`. -/
def GenericFiniteness (n : ℕ) : Prop :=
  ∃ F : MvPolynomial (Fin n) ℤ, F ≠ 0 ∧
    ∀ m : Fin n → ℝ, (∀ i, 0 < m i) → MvPolynomial.aeval m F ≠ 0 → FinitelyManyCC m

/-- **Theorem 1.1** (`thm:main`): generic finiteness for six bodies in the plane. -/
def MainTheorem : Prop := GenericFiniteness 6

end CC6Full
