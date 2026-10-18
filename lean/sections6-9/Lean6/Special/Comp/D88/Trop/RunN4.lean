import Lean6.Special.Comp.D88.Trop.Parse
import Lean6.Special.Comp.D88.Trop.LitN4
import Lean6.Special.Comp.D88.Trop.Sys
import Lean6.Special.Comp.D88.Trop.DataN4
import Lean6.Special.Comp.D88.Trop.TreeN4

/-!
# Lemma 6.19(a), system N4: the runs (`native_decide`)

`GN4` is the set `G` (the literal of `LitN4.lean`; `GN4_eq_parse`: the set read from `DataN4.gStr`), `GbN4` its
reduction at `μ₀ = (1, 2, 3, 30)` modulo `p = 65521`, `rootN4` the covering tree. The four checks: (i) the identities
with the system `S12`, (ii) the coefficients, the data conditions of the covering, and (iii)–(iv) the covering; and the
comparison with the gfan input of the d88 run.
-/

namespace Lean6.Special.Comp.D88.Trop

open Lean6.Special.Comp

/-- The literal `GN4` (`LitN4.lean`) is the set `G` read from `DataN4.gStr`. -/
theorem GN4_eq_parse : GN4 = parseG DataN4.gStr := by native_decide

/-- The reduction of `G` at `μ₀` modulo `p`. -/
def GbN4 : List (Poly Nat) := GN4.map (gbar 65521 [1, 2, 3, 30])

/-- The literal `cofN4` (`LitN4.lean`) is the cofactors `c₁, …, c₁₂` read from `DataN4.cofStr`. -/
theorem cofN4_eq_parse : cofN4 = (parseCof 13 DataN4.cofStr).map fun l => l.take 12 := by native_decide

/-- The literal `c0N4` (`LitN4.lean`) is the cofactors `c₀` read from `DataN4.cofStr`. -/
theorem c0N4_eq_parse : c0N4 = (parseCof 13 DataN4.cofStr).map fun l => l.getD 12 [] := by native_decide

/-- The covering tree. -/
def rootN4 : Node := parseTree GbN4 treeN4

/-- The systems whose torus emptiness the covering assumes (leaves `hyp`). -/
def hypsN4 : List (List (Poly Nat)) := parseHyps DataN4.hypStr

/-- The gfan input of the d88 run. -/
def gfanN4 : List (Poly Int) := parsePolys DataN4.gfanStr

/-- The scalars of the comparison. -/
def scalN4 : List Nat := (tokens DataN4.scalStr).map tokNat

/-- `Gb = s · gfan` modulo `p`, polynomial by polynomial. -/
def gfanOKN4 : Bool :=
  GbN4.length == gfanN4.length && GbN4.length == scalN4.length &&
    ((GbN4.zip (gfanN4.zip scalN4)).all fun t =>
      Poly.isZero (modC 65521) (Poly.sub (modC 65521) t.1
        (t.2.1.map fun u => ((((t.2.2 : Int) * u.1) % 65521).toNat, u.2))))

theorem n4_mem_ok : checkMem n4σ n4F n4rel GN4 cofN4 c0N4 = true := by native_decide

theorem n4_units_ok : checkUnits 65521 [1, 2, 3, 30] GN4 = true := by native_decide

theorem n4_gb_ok : gbOK 65521 GbN4 = true := by native_decide

theorem n4_cover_ok : chk 65521 GbN4 hypsN4 [] [] [] rootN4 = true := by native_decide

theorem n4_gfan_ok : gfanOKN4 = true := by native_decide

theorem n4_hyps_count : hypsN4.length = DataN4.hypCount := by native_decide

theorem n4_terms : (GN4.map List.length).sum = 354 := by native_decide

theorem n4_count : GN4.length = 30 := by native_decide

end Lean6.Special.Comp.D88.Trop
