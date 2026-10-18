import Lean6.Special.Comp.D88.Trop.Parse
import Lean6.Special.Comp.D88.Trop.LitKC
import Lean6.Special.Comp.D88.Trop.Sys
import Lean6.Special.Comp.D88.Trop.DataKC
import Lean6.Special.Comp.D88.Trop.TreeKC

/-!
# Lemma 6.19(a), system KC: the runs (`native_decide`)

`GKC` is the set `G` (the literal of `LitKC.lean`; `GKC_eq_parse`: the set read from `DataKC.gStr`), `GbKC` its
reduction at `μ₀ = (1, 2, 3, 30)` modulo `p = 65521`, `rootKC` the covering tree. The four checks: (i) the identities
with the system `KC12`, (ii) the coefficients, the data conditions of the covering, and (iii)–(iv) the covering; and the
comparison with the gfan input of the d88 run.
-/

namespace Lean6.Special.Comp.D88.Trop

open Lean6.Special.Comp

/-- The literal `GKC` (`LitKC.lean`) is the set `G` read from `DataKC.gStr`. -/
theorem GKC_eq_parse : GKC = parseG DataKC.gStr := by native_decide

/-- The reduction of `G` at `μ₀` modulo `p`. -/
def GbKC : List (Poly Nat) := GKC.map (gbar 65521 [1, 2, 3, 30])

/-- The literal `cofKC` (`LitKC.lean`) is the cofactors `c₁, …, c₁₂` read from `DataKC.cofStr`. -/
theorem cofKC_eq_parse : cofKC = (parseCof 13 DataKC.cofStr).map fun l => l.take 12 := by native_decide

/-- The literal `c0KC` (`LitKC.lean`) is the cofactors `c₀` read from `DataKC.cofStr`. -/
theorem c0KC_eq_parse : c0KC = (parseCof 13 DataKC.cofStr).map fun l => l.getD 12 [] := by native_decide

/-- The covering tree. -/
def rootKC : Node := parseTree GbKC treeKC

/-- The systems whose torus emptiness the covering assumes (leaves `hyp`). -/
def hypsKC : List (List (Poly Nat)) := parseHyps DataKC.hypStr

/-- The gfan input of the d88 run. -/
def gfanKC : List (Poly Int) := parsePolys DataKC.gfanStr

/-- The scalars of the comparison. -/
def scalKC : List Nat := (tokens DataKC.scalStr).map tokNat

/-- `Gb = s · gfan` modulo `p`, polynomial by polynomial. -/
def gfanOKKC : Bool :=
  GbKC.length == gfanKC.length && GbKC.length == scalKC.length &&
    ((GbKC.zip (gfanKC.zip scalKC)).all fun t =>
      Poly.isZero (modC 65521) (Poly.sub (modC 65521) t.1
        (t.2.1.map fun u => ((((t.2.2 : Int) * u.1) % 65521).toNat, u.2))))

theorem kc_mem_ok : checkMem kcσ kcF kcrel GKC cofKC c0KC = true := by native_decide

theorem kc_units_ok : checkUnits 65521 [1, 2, 3, 30] GKC = true := by native_decide

theorem kc_gb_ok : gbOK 65521 GbKC = true := by native_decide

theorem kc_cover_ok : chk 65521 GbKC hypsKC [] [] [] rootKC = true := by native_decide

theorem kc_gfan_ok : gfanOKKC = true := by native_decide

theorem kc_hyps_count : hypsKC.length = DataKC.hypCount := by native_decide

theorem kc_terms : (GKC.map List.length).sum = 1133 := by native_decide

theorem kc_count : GKC.length = 101 := by native_decide

end Lean6.Special.Comp.D88.Trop
