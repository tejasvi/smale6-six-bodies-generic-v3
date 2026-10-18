import Mathlib

/-!
# Computations inside the hand proofs of Section 3

* `triangle_one_circle`: the consequence of (E3) and (O6) used in Section 3: a triangle of strokes of one colour does
  not have exactly one circled vertex of that colour.
-/

namespace Lean6.Special.Hand

/-- **Section 3**: if `k` is the only `z`-circled vertex of a triangle `klj` of `z`-strokes, then `ζ_kl = −2` by (O6)
and `ζ_lj = ζ_kl` by (E3), against `ζ_lj ≥ min(a_l, a_j) > −2` (the bodies `l`, `j` are not circled, so `a > −2`). -/
theorem triangle_one_circle (ζkl ζlj al aj : ℚ) (hO6 : ζkl = -2) (hE3 : ζlj = ζkl) (hmin : min al aj ≤ ζlj)
    (hal : -2 < al) (haj : -2 < aj) : False := by
  have : -2 < min al aj := lt_min hal haj
  linarith

end Lean6.Special.Hand
