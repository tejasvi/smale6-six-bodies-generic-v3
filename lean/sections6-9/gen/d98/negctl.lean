import Lean6.Special.Comp.D98.Run
import Lean6.Special.Comp.D98.RootsRun

/-! Negative controls: each line must print `false`. -/

open Lean6.Special.Comp.D98

-- θ above the minimum of ρ at (1,2,7)
#eval rootsOK 1 2 7 (7641079387 / 10000000000) disks_1_2_7
-- one centre moved by 2^-200 (the radius check fails)
#eval rootsOK 1 2 7 (7641079385 / 10000000000)
  (disks_1_2_7.modifyHead fun F => { F with disks := F.disks.modifyHead fun D => { D with a := D.a + 2 ^ 56 } })
-- the disks of (1,2,8) used for (1,2,7)
#eval rootsOK 1 2 7 (7641079385 / 10000000000) disks_1_2_8
-- the upper bound below the minimum
#eval upperOK 1 2 7 (7641079384 / 10000000000) (1 / (2 : Rat) ^ ((disks_1_2_7.getD 3 ⟨0, []⟩).m))
  ((disks_1_2_7.getD 3 ⟨0, []⟩).disks.getD 0 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩) minY_1_2_7.1.toNat minY_1_2_7.2.toNat
-- the eliminant with one coefficient changed
#eval sqfOK (SUP 1 2 7) (g_1_2_7.modifyHead (· + 1)) g0_1_2_7 cert_1_2_7
-- S_μ of another mass point
#eval sqfOK (SUP 1 2 8) g_1_2_7 g0_1_2_7 cert_1_2_7
-- the Bezout constant changed
#eval bezOK (SUP 1 2 7) (Phi3UP 1 2 7) bez93_U bez93_V (bez93_c + 1)
-- Φ₃ at another mass point
#eval bezOK (SUP 1 2 7) (Phi3UP 1 2 8) bez93_U bez93_V bez93_c
