import Lean6.Special.Comp.D98.Run
import Lean6.Special.Comp.D98.RootsRun

/-!
# The certificates of Lemma 6.9 and Theorem 6.15, and the root disks, checked by the kernel

The theorems of `Lean6.Special.Comp.D98.Run` and `Lean6.Special.Comp.D98.RootsRun`, with the same statements, by
`decide +kernel` instead of `native_decide`: the checkers (`sqfOK`, `degLead`, `bezOK`, `rootsOK`, `upperOK`) are
structural recursions over lists of integers and rationals, which the kernel evaluates directly. The `example`s at
the end check that the statements are those of the `native_decide` theorems.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Lean6.Special.Comp.D98K

open Lean6.Special.Comp.D98 Lean6.Special.Comp.D98.UP

theorem sqf_1_2_7 : sqfOK (SUP 1 2 7) g_1_2_7 g0_1_2_7 cert_1_2_7 = true := by decide +kernel
theorem sqf_1_2_8 : sqfOK (SUP 1 2 8) g_1_2_8 g0_1_2_8 cert_1_2_8 = true := by decide +kernel
theorem sqf_2_3_11 : sqfOK (SUP 2 3 11) g_2_3_11 g0_2_3_11 cert_2_3_11 = true := by decide +kernel

theorem deg_1_2_7 : degLead (SUP 1 2 7) 34 81 = true ∧ degLead g0_1_2_7 32 (g0_1_2_7.getLast?.getD 0) = true ∧
    degLead g_1_2_7 36 81 = true := by decide +kernel
theorem deg_1_2_8 : degLead (SUP 1 2 8) 34 81 = true ∧ degLead g0_1_2_8 32 (g0_1_2_8.getLast?.getD 0) = true ∧
    degLead g_1_2_8 36 81 = true := by decide +kernel
theorem deg_2_3_11 : degLead (SUP 2 3 11) 34 625 = true ∧
    degLead g0_2_3_11 32 (g0_2_3_11.getLast?.getD 0) = true ∧ degLead g_2_3_11 36 625 = true := by decide +kernel

theorem bez93 : bezOK (SUP 1 2 7) (Phi3UP 1 2 7) bez93_U bez93_V bez93_c = true ∧
    degLead (Phi3UP 1 2 7) 4 6272980 = true := by decide +kernel

theorem roots_1_2_7 : rootsOK 1 2 7 (7641079385 / 10000000000) disks_1_2_7 = true := by decide +kernel

theorem roots_1_2_8 : rootsOK 1 2 8 (7990358445 / 10000000000) disks_1_2_8 = true := by decide +kernel

theorem upper_1_2_7 :
    upperOK 1 2 7 (7641079386 / 10000000000) (1 / (2 : Rat) ^ ((disks_1_2_7.getD minFac_1_2_7 ⟨0, []⟩).m))
      ((disks_1_2_7.getD minFac_1_2_7 ⟨0, []⟩).disks.getD minDisk_1_2_7 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)
      minY_1_2_7.1.toNat minY_1_2_7.2.toNat = true := by decide +kernel

example : type_of% Lean6.Special.Comp.D98.sqf_1_2_7 := Lean6.Special.Comp.D98K.sqf_1_2_7
example : type_of% Lean6.Special.Comp.D98.sqf_1_2_8 := Lean6.Special.Comp.D98K.sqf_1_2_8
example : type_of% Lean6.Special.Comp.D98.sqf_2_3_11 := Lean6.Special.Comp.D98K.sqf_2_3_11
example : type_of% Lean6.Special.Comp.D98.deg_1_2_7 := Lean6.Special.Comp.D98K.deg_1_2_7
example : type_of% Lean6.Special.Comp.D98.deg_1_2_8 := Lean6.Special.Comp.D98K.deg_1_2_8
example : type_of% Lean6.Special.Comp.D98.deg_2_3_11 := Lean6.Special.Comp.D98K.deg_2_3_11
example : type_of% Lean6.Special.Comp.D98.bez93 := Lean6.Special.Comp.D98K.bez93
example : type_of% Lean6.Special.Comp.D98.roots_1_2_7 := Lean6.Special.Comp.D98K.roots_1_2_7
example : type_of% Lean6.Special.Comp.D98.roots_1_2_8 := Lean6.Special.Comp.D98K.roots_1_2_8
example : type_of% Lean6.Special.Comp.D98.upper_1_2_7 := Lean6.Special.Comp.D98K.upper_1_2_7

end Lean6.Special.Comp.D98K
