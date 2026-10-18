import CC6Compose.Final
import CC6Compose.Dims

/-!
# Theorem 1.1

**Theorem 1.1** (`thm:main`) of the paper *Smale's sixth problem for six bodies in the plane: finiteness of central
configurations for generic masses*: there is a nonzero `F ∈ ℤ[m₁, …, m₆]` such that for every positive mass vector
`m` with `F(m) ≠ 0` the planar six-body problem has finitely many central configurations up to similarity
(`CC6Full.MainTheorem`, `CC6Full/Statement.lean`).

The proof is `main_of_dims` (the theory of `CC6Full` composed with the checks of Sections 3–7) with the dimension
bounds of Lemma 6.19(b) from `count_S12`, `count_KC` (`d88Dim`, `d94Dim`).
-/

namespace CC6Compose

/-- **Theorem 1.1** (`thm:main`). -/
theorem main_theorem : CC6Full.MainTheorem :=
  main_of_dims d88Dim d94Dim

end CC6Compose
