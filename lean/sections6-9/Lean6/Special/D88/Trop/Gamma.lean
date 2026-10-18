import Lean6.Special.D88.Trop.CoverG
import Lean6.Special.D88.Trop.Hyp

/-!
# Lemma 6.19(a), (iii)–(iv), for weights in any linearly ordered abelian group

`n4_torus_gamma`, `kc_torus_gamma`: for every linearly ordered abelian group `Γ`, every `w : ℕ → Γ` with a negative
entry among `w 0, …, w 16`, every field `K` of characteristic `65521` and every point of `(K^*)^{17}`, some initial
form at `w` (the terms of least weight `Σ_i e_i • w_i`, `initialFormG`) of some polynomial of `GbN4` (resp. `GbKC`), the
reductions at `μ₀ = (1, 2, 3, 30)` modulo `65521` of `G`, does not vanish at the point. The proof is the soundness of
the covering over `Γ` (`cover_soundG`) applied to the runs of `RunN4`, `RunKC` and the escape-ray systems of `Hyp`; no
new computation. For `Γ = ℚ` these are `n4_torus_all`, `kc_torus_all` (`torusEmptyG_rat`).
-/

namespace Lean6.Special.D88.Trop

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.D88.Trop

/-- **(iii)–(iv) for `S12`, over any linearly ordered abelian group.** -/
theorem n4_torus_gamma {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] (w : ℕ → Γ)
    (hw : ∃ i < 17, w i < 0) : TorusEmptyG 65521 GbN4 w :=
  cover_soundG n4_gb_ok n4_hypsOK n4_cover_ok w hw

/-- **(iii)–(iv) for `KC12`, over any linearly ordered abelian group.** -/
theorem kc_torus_gamma {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] (w : ℕ → Γ)
    (hw : ∃ i < 17, w i < 0) : TorusEmptyG 65521 GbKC w :=
  cover_soundG kc_gb_ok kc_hypsOK kc_cover_ok w hw

/-- The case `Γ = ℚ` gives back `n4_torus_all`. -/
theorem n4_torus_all_of_gamma (w : ℕ → ℚ) (hw : ∃ i < 17, w i < 0) : TorusEmpty 65521 GbN4 w :=
  (torusEmptyG_rat 65521 GbN4 w).mp (n4_torus_gamma w hw)

/-- The case `Γ = ℚ` gives back `kc_torus_all`. -/
theorem kc_torus_all_of_gamma (w : ℕ → ℚ) (hw : ∃ i < 17, w i < 0) : TorusEmpty 65521 GbKC w :=
  (torusEmptyG_rat 65521 GbKC w).mp (kc_torus_gamma w hw)

end Lean6.Special.D88.Trop
