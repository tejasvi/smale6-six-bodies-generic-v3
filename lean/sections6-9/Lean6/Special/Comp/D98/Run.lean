import Lean6.Special.Comp.D98.Data

/-!
# The runs of the certificates of Lemma 6.9 and Theorem 6.15 (`native_decide`)

`sqf_*`: at `μ = (1,2,7)`, `(1,2,8)`, `(2,3,11)`, the stored eliminant `g` and `S_μ` (`SUP`, built here from the
definitions) have the square-free part `g₀` (`sqfOK`); `S_μ` has degree `34` and leading coefficient `(μ₁ + μ₂)⁴`,
`g₀` has degree `32`. `bez93`: at `μ = (1,2,7)`, `U S_μ + V Φ₃ = c ≠ 0`; `S_μ` and `Φ₃` have degrees `34` and `4`.
-/

namespace Lean6.Special.Comp.D98

open UP

theorem sqf_1_2_7 : sqfOK (SUP 1 2 7) g_1_2_7 g0_1_2_7 cert_1_2_7 = true := by native_decide
theorem sqf_1_2_8 : sqfOK (SUP 1 2 8) g_1_2_8 g0_1_2_8 cert_1_2_8 = true := by native_decide
theorem sqf_2_3_11 : sqfOK (SUP 2 3 11) g_2_3_11 g0_2_3_11 cert_2_3_11 = true := by native_decide

theorem deg_1_2_7 : degLead (SUP 1 2 7) 34 81 = true ∧ degLead g0_1_2_7 32 (g0_1_2_7.getLast?.getD 0) = true ∧
    degLead g_1_2_7 36 81 = true := by native_decide
theorem deg_1_2_8 : degLead (SUP 1 2 8) 34 81 = true ∧ degLead g0_1_2_8 32 (g0_1_2_8.getLast?.getD 0) = true ∧
    degLead g_1_2_8 36 81 = true := by native_decide
theorem deg_2_3_11 : degLead (SUP 2 3 11) 34 625 = true ∧
    degLead g0_2_3_11 32 (g0_2_3_11.getLast?.getD 0) = true ∧ degLead g_2_3_11 36 625 = true := by native_decide

theorem bez93 : bezOK (SUP 1 2 7) (Phi3UP 1 2 7) bez93_U bez93_V bez93_c = true ∧
    degLead (Phi3UP 1 2 7) 4 6272980 = true := by native_decide

end Lean6.Special.Comp.D98
