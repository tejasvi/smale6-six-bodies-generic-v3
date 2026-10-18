import Lean6.Special.D88.Trop.Final
import Lean6.Special.K4.C4.GBSound
import Lean6.Special.Comp.D88.Trop.HypRun
import Mathlib.Algebra.Algebra.ZMod

/-!
# Lemma 6.19(a): the systems on the escape ray, and the unconditional statements

The coverings of `Final` assume the torus emptiness of one system each (`hypsN4`, `hypsKC`). The Buchberger engine of
Section 7 (`Lean6.Special.Comp.GB.unitTest`, proved sound in `Lean6.Special.K4.C4.unitTest_sound`) finds a nonzero
constant in the ideal of each (`n4_hyp_ok`, `kc_hyp_ok`), so the systems have no common zero at all over any field of
characteristic `65521` (`hypsOK_of`). With them, `n4_torus_all` and `kc_torus_all` are (iii)–(iv) without hypotheses.
-/

namespace Lean6.Special.D88.Trop

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.D88.Trop

/-- The two coefficient maps of `ℤ/p` into a field of characteristic `p` agree. -/
theorem eval_algH_eq {p : ℕ} [NeZero p] (K : Type) [Field K] [CharP K p] (x : ℕ → K) (f : Poly ℕ) :
    @Poly.eval ℕ (modC p) K _ (@K4.C4.algH p _ K _ (ZMod.algebra K p)) x f = Poly.eval (modHomK p K) x f := by
  unfold Poly.eval
  congr 1
  refine List.map_congr_left fun t _ => ?_
  congr 1
  show (@algebraMap (ZMod p) K _ _ (ZMod.algebra K p)) ((t.1 : ℕ) : ZMod p) = (t.1 : K)
  exact map_natCast _ _

/-- A list of systems on which the engine succeeds satisfies `HypsOK`. -/
theorem hypsOK_of {hyps : List (List (Poly ℕ))} (h : hypOK hyps = true) : HypsOK 65521 hyps := by
  intro s hs K _ _ x _
  have : Fact (Nat.Prime 65521) := ⟨by norm_num⟩
  let _ : Algebra (ZMod 65521) K := ZMod.algebra K 65521
  have hT : GB.unitTest 65521 17 1000000 100000000 s = true := List.all_eq_true.mp h s hs
  by_contra hcon
  push Not at hcon
  exact K4.C4.unitTest_sound 65521 hT K x (fun f hf => by rw [eval_algH_eq]; exact hcon f hf)

/-- The assumed systems of the covering for `S12` have no common zero in the torus. -/
theorem n4_hypsOK : HypsOK 65521 hypsN4 := hypsOK_of n4_hyp_ok

/-- The assumed systems of the covering for `KC12` have no common zero in the torus. -/
theorem kc_hypsOK : HypsOK 65521 hypsKC := hypsOK_of kc_hyp_ok

/-- **(iii)–(iv) for `S12`, without hypotheses**: for every `w ∈ ℚ^17` with a negative entry and every field `K` of
characteristic `65521`, the initial forms at `w` of the reductions of `G` (at `μ₀ = (1, 2, 3, 30)`) have no common zero
in `(K^*)^17`. -/
theorem n4_torus_all (w : ℕ → ℚ) (hw : ∃ i < 17, w i < 0) : TorusEmpty 65521 GbN4 w :=
  n4_torus n4_hypsOK w hw

/-- **(iii)–(iv) for `KC12`, without hypotheses.** -/
theorem kc_torus_all (w : ℕ → ℚ) (hw : ∃ i < 17, w i < 0) : TorusEmpty 65521 GbKC w :=
  kc_torus kc_hypsOK w hw

end Lean6.Special.D88.Trop
