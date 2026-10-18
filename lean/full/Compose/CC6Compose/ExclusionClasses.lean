import CC6Compose.ExclusionClaim

/-!
# Bridge: the claims of the stored cells of each class (Proposition 5.3), with the certificates named

For each class `k < 191`, `classClaim_c<k>`: `ClassClaim k n certs` for the number `n` of stored cells of the
class and the list `certs` of the certificate texts of its chunks, from the chunk theorems
`L6.F34S.Checks.F34S_c<k>_k<j>` and `L6.F34.Checks.certsOK_c<k>_k<j>` of the certificate project, chunk after
chunk (`ClassClaim.extend`), as in its class theorems `L6.F34S.Checks.F34S_class_c<k>`. `classClaim`: all classes,
with the numbers of cells `L6.F34S.Checks.ncellsList`.

Generated from the class theorems of the certificate project (`L6Check/F34S/All.lean`).
-/

namespace CC6Compose

open L6.F34S.Checks L6.F34.Checks

theorem classClaim_c0 : ∃ certs, ClassClaim 0 17 certs :=
  ⟨_, ClassClaim.zero 0
    |>.extend F34S_c0_k0 certsOK_c0_k0 rfl⟩

theorem classClaim_c1 : ∃ certs, ClassClaim 1 0 certs :=
  ⟨_, ClassClaim.zero 1⟩

theorem classClaim_c2 : ∃ certs, ClassClaim 2 0 certs :=
  ⟨_, ClassClaim.zero 2⟩

theorem classClaim_c3 : ∃ certs, ClassClaim 3 44247 certs :=
  ⟨_, ClassClaim.zero 3
    |>.extend F34S_c3_k0 certsOK_c3_k0 rfl
    |>.extend F34S_c3_k1 certsOK_c3_k1 rfl
    |>.extend F34S_c3_k2 certsOK_c3_k2 rfl
    |>.extend F34S_c3_k3 certsOK_c3_k3 rfl
    |>.extend F34S_c3_k4 certsOK_c3_k4 rfl
    |>.extend F34S_c3_k5 certsOK_c3_k5 rfl
    |>.extend F34S_c3_k6 certsOK_c3_k6 rfl
    |>.extend F34S_c3_k7 certsOK_c3_k7 rfl
    |>.extend F34S_c3_k8 certsOK_c3_k8 rfl
    |>.extend F34S_c3_k9 certsOK_c3_k9 rfl
    |>.extend F34S_c3_k10 certsOK_c3_k10 rfl
    |>.extend F34S_c3_k11 certsOK_c3_k11 rfl
    |>.extend F34S_c3_k12 certsOK_c3_k12 rfl
    |>.extend F34S_c3_k13 certsOK_c3_k13 rfl
    |>.extend F34S_c3_k14 certsOK_c3_k14 rfl
    |>.extend F34S_c3_k15 certsOK_c3_k15 rfl
    |>.extend F34S_c3_k16 certsOK_c3_k16 rfl
    |>.extend F34S_c3_k17 certsOK_c3_k17 rfl
    |>.extend F34S_c3_k18 certsOK_c3_k18 rfl
    |>.extend F34S_c3_k19 certsOK_c3_k19 rfl
    |>.extend F34S_c3_k20 certsOK_c3_k20 rfl
    |>.extend F34S_c3_k21 certsOK_c3_k21 rfl
    |>.extend F34S_c3_k22 certsOK_c3_k22 rfl
    |>.extend F34S_c3_k23 certsOK_c3_k23 rfl
    |>.extend F34S_c3_k24 certsOK_c3_k24 rfl
    |>.extend F34S_c3_k25 certsOK_c3_k25 rfl
    |>.extend F34S_c3_k26 certsOK_c3_k26 rfl
    |>.extend F34S_c3_k27 certsOK_c3_k27 rfl
    |>.extend F34S_c3_k28 certsOK_c3_k28 rfl
    |>.extend F34S_c3_k29 certsOK_c3_k29 rfl⟩

theorem classClaim_c4 : ∃ certs, ClassClaim 4 177 certs :=
  ⟨_, ClassClaim.zero 4
    |>.extend F34S_c4_k0 certsOK_c4_k0 rfl⟩

theorem classClaim_c5 : ∃ certs, ClassClaim 5 0 certs :=
  ⟨_, ClassClaim.zero 5⟩

theorem classClaim_c6 : ∃ certs, ClassClaim 6 0 certs :=
  ⟨_, ClassClaim.zero 6⟩

theorem classClaim_c7 : ∃ certs, ClassClaim 7 0 certs :=
  ⟨_, ClassClaim.zero 7⟩

theorem classClaim_c8 : ∃ certs, ClassClaim 8 1 certs :=
  ⟨_, ClassClaim.zero 8
    |>.extend F34S_c8_k0 certsOK_c8_k0 rfl⟩

theorem classClaim_c9 : ∃ certs, ClassClaim 9 0 certs :=
  ⟨_, ClassClaim.zero 9⟩

theorem classClaim_c10 : ∃ certs, ClassClaim 10 10 certs :=
  ⟨_, ClassClaim.zero 10
    |>.extend F34S_c10_k0 certsOK_c10_k0 rfl⟩

theorem classClaim_c11 : ∃ certs, ClassClaim 11 0 certs :=
  ⟨_, ClassClaim.zero 11⟩

theorem classClaim_c12 : ∃ certs, ClassClaim 12 1 certs :=
  ⟨_, ClassClaim.zero 12
    |>.extend F34S_c12_k0 certsOK_c12_k0 rfl⟩

theorem classClaim_c13 : ∃ certs, ClassClaim 13 1 certs :=
  ⟨_, ClassClaim.zero 13
    |>.extend F34S_c13_k0 certsOK_c13_k0 rfl⟩

theorem classClaim_c14 : ∃ certs, ClassClaim 14 865 certs :=
  ⟨_, ClassClaim.zero 14
    |>.extend F34S_c14_k0 certsOK_c14_k0 rfl⟩

theorem classClaim_c15 : ∃ certs, ClassClaim 15 42 certs :=
  ⟨_, ClassClaim.zero 15
    |>.extend F34S_c15_k0 certsOK_c15_k0 rfl⟩

theorem classClaim_c16 : ∃ certs, ClassClaim 16 28 certs :=
  ⟨_, ClassClaim.zero 16
    |>.extend F34S_c16_k0 certsOK_c16_k0 rfl⟩

theorem classClaim_c17 : ∃ certs, ClassClaim 17 0 certs :=
  ⟨_, ClassClaim.zero 17⟩

theorem classClaim_c18 : ∃ certs, ClassClaim 18 0 certs :=
  ⟨_, ClassClaim.zero 18⟩

theorem classClaim_c19 : ∃ certs, ClassClaim 19 0 certs :=
  ⟨_, ClassClaim.zero 19⟩

theorem classClaim_c20 : ∃ certs, ClassClaim 20 13 certs :=
  ⟨_, ClassClaim.zero 20
    |>.extend F34S_c20_k0 certsOK_c20_k0 rfl⟩

theorem classClaim_c21 : ∃ certs, ClassClaim 21 0 certs :=
  ⟨_, ClassClaim.zero 21⟩

theorem classClaim_c22 : ∃ certs, ClassClaim 22 2 certs :=
  ⟨_, ClassClaim.zero 22
    |>.extend F34S_c22_k0 certsOK_c22_k0 rfl⟩

theorem classClaim_c23 : ∃ certs, ClassClaim 23 239 certs :=
  ⟨_, ClassClaim.zero 23
    |>.extend F34S_c23_k0 certsOK_c23_k0 rfl⟩

theorem classClaim_c24 : ∃ certs, ClassClaim 24 72 certs :=
  ⟨_, ClassClaim.zero 24
    |>.extend F34S_c24_k0 certsOK_c24_k0 rfl⟩

theorem classClaim_c25 : ∃ certs, ClassClaim 25 88 certs :=
  ⟨_, ClassClaim.zero 25
    |>.extend F34S_c25_k0 certsOK_c25_k0 rfl⟩

theorem classClaim_c26 : ∃ certs, ClassClaim 26 0 certs :=
  ⟨_, ClassClaim.zero 26⟩

theorem classClaim_c27 : ∃ certs, ClassClaim 27 0 certs :=
  ⟨_, ClassClaim.zero 27⟩

theorem classClaim_c28 : ∃ certs, ClassClaim 28 3 certs :=
  ⟨_, ClassClaim.zero 28
    |>.extend F34S_c28_k0 certsOK_c28_k0 rfl⟩

theorem classClaim_c29 : ∃ certs, ClassClaim 29 1866 certs :=
  ⟨_, ClassClaim.zero 29
    |>.extend F34S_c29_k0 certsOK_c29_k0 rfl
    |>.extend F34S_c29_k1 certsOK_c29_k1 rfl⟩

theorem classClaim_c30 : ∃ certs, ClassClaim 30 273 certs :=
  ⟨_, ClassClaim.zero 30
    |>.extend F34S_c30_k0 certsOK_c30_k0 rfl⟩

theorem classClaim_c31 : ∃ certs, ClassClaim 31 49 certs :=
  ⟨_, ClassClaim.zero 31
    |>.extend F34S_c31_k0 certsOK_c31_k0 rfl⟩

theorem classClaim_c32 : ∃ certs, ClassClaim 32 0 certs :=
  ⟨_, ClassClaim.zero 32⟩

theorem classClaim_c33 : ∃ certs, ClassClaim 33 0 certs :=
  ⟨_, ClassClaim.zero 33⟩

theorem classClaim_c34 : ∃ certs, ClassClaim 34 1 certs :=
  ⟨_, ClassClaim.zero 34
    |>.extend F34S_c34_k0 certsOK_c34_k0 rfl⟩

theorem classClaim_c35 : ∃ certs, ClassClaim 35 1 certs :=
  ⟨_, ClassClaim.zero 35
    |>.extend F34S_c35_k0 certsOK_c35_k0 rfl⟩

theorem classClaim_c36 : ∃ certs, ClassClaim 36 0 certs :=
  ⟨_, ClassClaim.zero 36⟩

theorem classClaim_c37 : ∃ certs, ClassClaim 37 0 certs :=
  ⟨_, ClassClaim.zero 37⟩

theorem classClaim_c38 : ∃ certs, ClassClaim 38 0 certs :=
  ⟨_, ClassClaim.zero 38⟩

theorem classClaim_c39 : ∃ certs, ClassClaim 39 0 certs :=
  ⟨_, ClassClaim.zero 39⟩

theorem classClaim_c40 : ∃ certs, ClassClaim 40 394 certs :=
  ⟨_, ClassClaim.zero 40
    |>.extend F34S_c40_k0 certsOK_c40_k0 rfl⟩

theorem classClaim_c41 : ∃ certs, ClassClaim 41 0 certs :=
  ⟨_, ClassClaim.zero 41⟩

theorem classClaim_c42 : ∃ certs, ClassClaim 42 20 certs :=
  ⟨_, ClassClaim.zero 42
    |>.extend F34S_c42_k0 certsOK_c42_k0 rfl⟩

theorem classClaim_c43 : ∃ certs, ClassClaim 43 0 certs :=
  ⟨_, ClassClaim.zero 43⟩

theorem classClaim_c44 : ∃ certs, ClassClaim 44 154 certs :=
  ⟨_, ClassClaim.zero 44
    |>.extend F34S_c44_k0 certsOK_c44_k0 rfl⟩

theorem classClaim_c45 : ∃ certs, ClassClaim 45 0 certs :=
  ⟨_, ClassClaim.zero 45⟩

theorem classClaim_c46 : ∃ certs, ClassClaim 46 0 certs :=
  ⟨_, ClassClaim.zero 46⟩

theorem classClaim_c47 : ∃ certs, ClassClaim 47 497 certs :=
  ⟨_, ClassClaim.zero 47
    |>.extend F34S_c47_k0 certsOK_c47_k0 rfl⟩

theorem classClaim_c48 : ∃ certs, ClassClaim 48 0 certs :=
  ⟨_, ClassClaim.zero 48⟩

theorem classClaim_c49 : ∃ certs, ClassClaim 49 0 certs :=
  ⟨_, ClassClaim.zero 49⟩

theorem classClaim_c50 : ∃ certs, ClassClaim 50 0 certs :=
  ⟨_, ClassClaim.zero 50⟩

theorem classClaim_c51 : ∃ certs, ClassClaim 51 0 certs :=
  ⟨_, ClassClaim.zero 51⟩

theorem classClaim_c52 : ∃ certs, ClassClaim 52 0 certs :=
  ⟨_, ClassClaim.zero 52⟩

theorem classClaim_c53 : ∃ certs, ClassClaim 53 3 certs :=
  ⟨_, ClassClaim.zero 53
    |>.extend F34S_c53_k0 certsOK_c53_k0 rfl⟩

theorem classClaim_c54 : ∃ certs, ClassClaim 54 0 certs :=
  ⟨_, ClassClaim.zero 54⟩

theorem classClaim_c55 : ∃ certs, ClassClaim 55 24 certs :=
  ⟨_, ClassClaim.zero 55
    |>.extend F34S_c55_k0 certsOK_c55_k0 rfl⟩

theorem classClaim_c56 : ∃ certs, ClassClaim 56 37 certs :=
  ⟨_, ClassClaim.zero 56
    |>.extend F34S_c56_k0 certsOK_c56_k0 rfl⟩

theorem classClaim_c57 : ∃ certs, ClassClaim 57 2 certs :=
  ⟨_, ClassClaim.zero 57
    |>.extend F34S_c57_k0 certsOK_c57_k0 rfl⟩

theorem classClaim_c58 : ∃ certs, ClassClaim 58 2 certs :=
  ⟨_, ClassClaim.zero 58
    |>.extend F34S_c58_k0 certsOK_c58_k0 rfl⟩

theorem classClaim_c59 : ∃ certs, ClassClaim 59 0 certs :=
  ⟨_, ClassClaim.zero 59⟩

theorem classClaim_c60 : ∃ certs, ClassClaim 60 0 certs :=
  ⟨_, ClassClaim.zero 60⟩

theorem classClaim_c61 : ∃ certs, ClassClaim 61 0 certs :=
  ⟨_, ClassClaim.zero 61⟩

theorem classClaim_c62 : ∃ certs, ClassClaim 62 14 certs :=
  ⟨_, ClassClaim.zero 62
    |>.extend F34S_c62_k0 certsOK_c62_k0 rfl⟩

theorem classClaim_c63 : ∃ certs, ClassClaim 63 7 certs :=
  ⟨_, ClassClaim.zero 63
    |>.extend F34S_c63_k0 certsOK_c63_k0 rfl⟩

theorem classClaim_c64 : ∃ certs, ClassClaim 64 162 certs :=
  ⟨_, ClassClaim.zero 64
    |>.extend F34S_c64_k0 certsOK_c64_k0 rfl⟩

theorem classClaim_c65 : ∃ certs, ClassClaim 65 1 certs :=
  ⟨_, ClassClaim.zero 65
    |>.extend F34S_c65_k0 certsOK_c65_k0 rfl⟩

theorem classClaim_c66 : ∃ certs, ClassClaim 66 1 certs :=
  ⟨_, ClassClaim.zero 66
    |>.extend F34S_c66_k0 certsOK_c66_k0 rfl⟩

theorem classClaim_c67 : ∃ certs, ClassClaim 67 2 certs :=
  ⟨_, ClassClaim.zero 67
    |>.extend F34S_c67_k0 certsOK_c67_k0 rfl⟩

theorem classClaim_c68 : ∃ certs, ClassClaim 68 0 certs :=
  ⟨_, ClassClaim.zero 68⟩

theorem classClaim_c69 : ∃ certs, ClassClaim 69 2 certs :=
  ⟨_, ClassClaim.zero 69
    |>.extend F34S_c69_k0 certsOK_c69_k0 rfl⟩

theorem classClaim_c70 : ∃ certs, ClassClaim 70 0 certs :=
  ⟨_, ClassClaim.zero 70⟩

theorem classClaim_c71 : ∃ certs, ClassClaim 71 0 certs :=
  ⟨_, ClassClaim.zero 71⟩

theorem classClaim_c72 : ∃ certs, ClassClaim 72 0 certs :=
  ⟨_, ClassClaim.zero 72⟩

theorem classClaim_c73 : ∃ certs, ClassClaim 73 0 certs :=
  ⟨_, ClassClaim.zero 73⟩

theorem classClaim_c74 : ∃ certs, ClassClaim 74 0 certs :=
  ⟨_, ClassClaim.zero 74⟩

theorem classClaim_c75 : ∃ certs, ClassClaim 75 0 certs :=
  ⟨_, ClassClaim.zero 75⟩

theorem classClaim_c76 : ∃ certs, ClassClaim 76 0 certs :=
  ⟨_, ClassClaim.zero 76⟩

theorem classClaim_c77 : ∃ certs, ClassClaim 77 0 certs :=
  ⟨_, ClassClaim.zero 77⟩

theorem classClaim_c78 : ∃ certs, ClassClaim 78 0 certs :=
  ⟨_, ClassClaim.zero 78⟩

theorem classClaim_c79 : ∃ certs, ClassClaim 79 0 certs :=
  ⟨_, ClassClaim.zero 79⟩

theorem classClaim_c80 : ∃ certs, ClassClaim 80 0 certs :=
  ⟨_, ClassClaim.zero 80⟩

theorem classClaim_c81 : ∃ certs, ClassClaim 81 0 certs :=
  ⟨_, ClassClaim.zero 81⟩

theorem classClaim_c82 : ∃ certs, ClassClaim 82 0 certs :=
  ⟨_, ClassClaim.zero 82⟩

theorem classClaim_c83 : ∃ certs, ClassClaim 83 0 certs :=
  ⟨_, ClassClaim.zero 83⟩

theorem classClaim_c84 : ∃ certs, ClassClaim 84 1 certs :=
  ⟨_, ClassClaim.zero 84
    |>.extend F34S_c84_k0 certsOK_c84_k0 rfl⟩

theorem classClaim_c85 : ∃ certs, ClassClaim 85 0 certs :=
  ⟨_, ClassClaim.zero 85⟩

theorem classClaim_c86 : ∃ certs, ClassClaim 86 0 certs :=
  ⟨_, ClassClaim.zero 86⟩

theorem classClaim_c87 : ∃ certs, ClassClaim 87 0 certs :=
  ⟨_, ClassClaim.zero 87⟩

theorem classClaim_c88 : ∃ certs, ClassClaim 88 0 certs :=
  ⟨_, ClassClaim.zero 88⟩

theorem classClaim_c89 : ∃ certs, ClassClaim 89 0 certs :=
  ⟨_, ClassClaim.zero 89⟩

theorem classClaim_c90 : ∃ certs, ClassClaim 90 0 certs :=
  ⟨_, ClassClaim.zero 90⟩

theorem classClaim_c91 : ∃ certs, ClassClaim 91 0 certs :=
  ⟨_, ClassClaim.zero 91⟩

theorem classClaim_c92 : ∃ certs, ClassClaim 92 0 certs :=
  ⟨_, ClassClaim.zero 92⟩

theorem classClaim_c93 : ∃ certs, ClassClaim 93 0 certs :=
  ⟨_, ClassClaim.zero 93⟩

theorem classClaim_c94 : ∃ certs, ClassClaim 94 0 certs :=
  ⟨_, ClassClaim.zero 94⟩

theorem classClaim_c95 : ∃ certs, ClassClaim 95 0 certs :=
  ⟨_, ClassClaim.zero 95⟩

theorem classClaim_c96 : ∃ certs, ClassClaim 96 0 certs :=
  ⟨_, ClassClaim.zero 96⟩

theorem classClaim_c97 : ∃ certs, ClassClaim 97 0 certs :=
  ⟨_, ClassClaim.zero 97⟩

theorem classClaim_c98 : ∃ certs, ClassClaim 98 0 certs :=
  ⟨_, ClassClaim.zero 98⟩

theorem classClaim_c99 : ∃ certs, ClassClaim 99 0 certs :=
  ⟨_, ClassClaim.zero 99⟩

theorem classClaim_c100 : ∃ certs, ClassClaim 100 0 certs :=
  ⟨_, ClassClaim.zero 100⟩

theorem classClaim_c101 : ∃ certs, ClassClaim 101 0 certs :=
  ⟨_, ClassClaim.zero 101⟩

theorem classClaim_c102 : ∃ certs, ClassClaim 102 0 certs :=
  ⟨_, ClassClaim.zero 102⟩

theorem classClaim_c103 : ∃ certs, ClassClaim 103 0 certs :=
  ⟨_, ClassClaim.zero 103⟩

theorem classClaim_c104 : ∃ certs, ClassClaim 104 0 certs :=
  ⟨_, ClassClaim.zero 104⟩

theorem classClaim_c105 : ∃ certs, ClassClaim 105 0 certs :=
  ⟨_, ClassClaim.zero 105⟩

theorem classClaim_c106 : ∃ certs, ClassClaim 106 0 certs :=
  ⟨_, ClassClaim.zero 106⟩

theorem classClaim_c107 : ∃ certs, ClassClaim 107 0 certs :=
  ⟨_, ClassClaim.zero 107⟩

theorem classClaim_c108 : ∃ certs, ClassClaim 108 0 certs :=
  ⟨_, ClassClaim.zero 108⟩

theorem classClaim_c109 : ∃ certs, ClassClaim 109 0 certs :=
  ⟨_, ClassClaim.zero 109⟩

theorem classClaim_c110 : ∃ certs, ClassClaim 110 1 certs :=
  ⟨_, ClassClaim.zero 110
    |>.extend F34S_c110_k0 certsOK_c110_k0 rfl⟩

theorem classClaim_c111 : ∃ certs, ClassClaim 111 0 certs :=
  ⟨_, ClassClaim.zero 111⟩

theorem classClaim_c112 : ∃ certs, ClassClaim 112 0 certs :=
  ⟨_, ClassClaim.zero 112⟩

theorem classClaim_c113 : ∃ certs, ClassClaim 113 0 certs :=
  ⟨_, ClassClaim.zero 113⟩

theorem classClaim_c114 : ∃ certs, ClassClaim 114 0 certs :=
  ⟨_, ClassClaim.zero 114⟩

theorem classClaim_c115 : ∃ certs, ClassClaim 115 0 certs :=
  ⟨_, ClassClaim.zero 115⟩

theorem classClaim_c116 : ∃ certs, ClassClaim 116 21 certs :=
  ⟨_, ClassClaim.zero 116
    |>.extend F34S_c116_k0 certsOK_c116_k0 rfl⟩

theorem classClaim_c117 : ∃ certs, ClassClaim 117 2 certs :=
  ⟨_, ClassClaim.zero 117
    |>.extend F34S_c117_k0 certsOK_c117_k0 rfl⟩

theorem classClaim_c118 : ∃ certs, ClassClaim 118 0 certs :=
  ⟨_, ClassClaim.zero 118⟩

theorem classClaim_c119 : ∃ certs, ClassClaim 119 1 certs :=
  ⟨_, ClassClaim.zero 119
    |>.extend F34S_c119_k0 certsOK_c119_k0 rfl⟩

theorem classClaim_c120 : ∃ certs, ClassClaim 120 2 certs :=
  ⟨_, ClassClaim.zero 120
    |>.extend F34S_c120_k0 certsOK_c120_k0 rfl⟩

theorem classClaim_c121 : ∃ certs, ClassClaim 121 1 certs :=
  ⟨_, ClassClaim.zero 121
    |>.extend F34S_c121_k0 certsOK_c121_k0 rfl⟩

theorem classClaim_c122 : ∃ certs, ClassClaim 122 10 certs :=
  ⟨_, ClassClaim.zero 122
    |>.extend F34S_c122_k0 certsOK_c122_k0 rfl⟩

theorem classClaim_c123 : ∃ certs, ClassClaim 123 1 certs :=
  ⟨_, ClassClaim.zero 123
    |>.extend F34S_c123_k0 certsOK_c123_k0 rfl⟩

theorem classClaim_c124 : ∃ certs, ClassClaim 124 143 certs :=
  ⟨_, ClassClaim.zero 124
    |>.extend F34S_c124_k0 certsOK_c124_k0 rfl⟩

theorem classClaim_c125 : ∃ certs, ClassClaim 125 0 certs :=
  ⟨_, ClassClaim.zero 125⟩

theorem classClaim_c126 : ∃ certs, ClassClaim 126 27 certs :=
  ⟨_, ClassClaim.zero 126
    |>.extend F34S_c126_k0 certsOK_c126_k0 rfl⟩

theorem classClaim_c127 : ∃ certs, ClassClaim 127 9 certs :=
  ⟨_, ClassClaim.zero 127
    |>.extend F34S_c127_k0 certsOK_c127_k0 rfl⟩

theorem classClaim_c128 : ∃ certs, ClassClaim 128 32864 certs :=
  ⟨_, ClassClaim.zero 128
    |>.extend F34S_c128_k0 certsOK_c128_k0 rfl
    |>.extend F34S_c128_k1 certsOK_c128_k1 rfl
    |>.extend F34S_c128_k2 certsOK_c128_k2 rfl
    |>.extend F34S_c128_k3 certsOK_c128_k3 rfl
    |>.extend F34S_c128_k4 certsOK_c128_k4 rfl
    |>.extend F34S_c128_k5 certsOK_c128_k5 rfl
    |>.extend F34S_c128_k6 certsOK_c128_k6 rfl
    |>.extend F34S_c128_k7 certsOK_c128_k7 rfl
    |>.extend F34S_c128_k8 certsOK_c128_k8 rfl
    |>.extend F34S_c128_k9 certsOK_c128_k9 rfl
    |>.extend F34S_c128_k10 certsOK_c128_k10 rfl
    |>.extend F34S_c128_k11 certsOK_c128_k11 rfl
    |>.extend F34S_c128_k12 certsOK_c128_k12 rfl
    |>.extend F34S_c128_k13 certsOK_c128_k13 rfl
    |>.extend F34S_c128_k14 certsOK_c128_k14 rfl
    |>.extend F34S_c128_k15 certsOK_c128_k15 rfl
    |>.extend F34S_c128_k16 certsOK_c128_k16 rfl
    |>.extend F34S_c128_k17 certsOK_c128_k17 rfl
    |>.extend F34S_c128_k18 certsOK_c128_k18 rfl
    |>.extend F34S_c128_k19 certsOK_c128_k19 rfl
    |>.extend F34S_c128_k20 certsOK_c128_k20 rfl
    |>.extend F34S_c128_k21 certsOK_c128_k21 rfl⟩

theorem classClaim_c129 : ∃ certs, ClassClaim 129 1449 certs :=
  ⟨_, ClassClaim.zero 129
    |>.extend F34S_c129_k0 certsOK_c129_k0 rfl⟩

theorem classClaim_c130 : ∃ certs, ClassClaim 130 630 certs :=
  ⟨_, ClassClaim.zero 130
    |>.extend F34S_c130_k0 certsOK_c130_k0 rfl⟩

theorem classClaim_c131 : ∃ certs, ClassClaim 131 196 certs :=
  ⟨_, ClassClaim.zero 131
    |>.extend F34S_c131_k0 certsOK_c131_k0 rfl⟩

theorem classClaim_c132 : ∃ certs, ClassClaim 132 147 certs :=
  ⟨_, ClassClaim.zero 132
    |>.extend F34S_c132_k0 certsOK_c132_k0 rfl⟩

theorem classClaim_c133 : ∃ certs, ClassClaim 133 49 certs :=
  ⟨_, ClassClaim.zero 133
    |>.extend F34S_c133_k0 certsOK_c133_k0 rfl⟩

theorem classClaim_c134 : ∃ certs, ClassClaim 134 0 certs :=
  ⟨_, ClassClaim.zero 134⟩

theorem classClaim_c135 : ∃ certs, ClassClaim 135 0 certs :=
  ⟨_, ClassClaim.zero 135⟩

theorem classClaim_c136 : ∃ certs, ClassClaim 136 0 certs :=
  ⟨_, ClassClaim.zero 136⟩

theorem classClaim_c137 : ∃ certs, ClassClaim 137 0 certs :=
  ⟨_, ClassClaim.zero 137⟩

theorem classClaim_c138 : ∃ certs, ClassClaim 138 0 certs :=
  ⟨_, ClassClaim.zero 138⟩

theorem classClaim_c139 : ∃ certs, ClassClaim 139 0 certs :=
  ⟨_, ClassClaim.zero 139⟩

theorem classClaim_c140 : ∃ certs, ClassClaim 140 0 certs :=
  ⟨_, ClassClaim.zero 140⟩

theorem classClaim_c141 : ∃ certs, ClassClaim 141 0 certs :=
  ⟨_, ClassClaim.zero 141⟩

theorem classClaim_c142 : ∃ certs, ClassClaim 142 297 certs :=
  ⟨_, ClassClaim.zero 142
    |>.extend F34S_c142_k0 certsOK_c142_k0 rfl⟩

theorem classClaim_c143 : ∃ certs, ClassClaim 143 77 certs :=
  ⟨_, ClassClaim.zero 143
    |>.extend F34S_c143_k0 certsOK_c143_k0 rfl⟩

theorem classClaim_c144 : ∃ certs, ClassClaim 144 0 certs :=
  ⟨_, ClassClaim.zero 144⟩

theorem classClaim_c145 : ∃ certs, ClassClaim 145 0 certs :=
  ⟨_, ClassClaim.zero 145⟩

theorem classClaim_c146 : ∃ certs, ClassClaim 146 81 certs :=
  ⟨_, ClassClaim.zero 146
    |>.extend F34S_c146_k0 certsOK_c146_k0 rfl⟩

theorem classClaim_c147 : ∃ certs, ClassClaim 147 63 certs :=
  ⟨_, ClassClaim.zero 147
    |>.extend F34S_c147_k0 certsOK_c147_k0 rfl⟩

theorem classClaim_c148 : ∃ certs, ClassClaim 148 4777 certs :=
  ⟨_, ClassClaim.zero 148
    |>.extend F34S_c148_k0 certsOK_c148_k0 rfl
    |>.extend F34S_c148_k1 certsOK_c148_k1 rfl
    |>.extend F34S_c148_k2 certsOK_c148_k2 rfl
    |>.extend F34S_c148_k3 certsOK_c148_k3 rfl⟩

theorem classClaim_c149 : ∃ certs, ClassClaim 149 756 certs :=
  ⟨_, ClassClaim.zero 149
    |>.extend F34S_c149_k0 certsOK_c149_k0 rfl⟩

theorem classClaim_c150 : ∃ certs, ClassClaim 150 224 certs :=
  ⟨_, ClassClaim.zero 150
    |>.extend F34S_c150_k0 certsOK_c150_k0 rfl⟩

theorem classClaim_c151 : ∃ certs, ClassClaim 151 0 certs :=
  ⟨_, ClassClaim.zero 151⟩

theorem classClaim_c152 : ∃ certs, ClassClaim 152 0 certs :=
  ⟨_, ClassClaim.zero 152⟩

theorem classClaim_c153 : ∃ certs, ClassClaim 153 0 certs :=
  ⟨_, ClassClaim.zero 153⟩

theorem classClaim_c154 : ∃ certs, ClassClaim 154 0 certs :=
  ⟨_, ClassClaim.zero 154⟩

theorem classClaim_c155 : ∃ certs, ClassClaim 155 0 certs :=
  ⟨_, ClassClaim.zero 155⟩

theorem classClaim_c156 : ∃ certs, ClassClaim 156 0 certs :=
  ⟨_, ClassClaim.zero 156⟩

theorem classClaim_c157 : ∃ certs, ClassClaim 157 0 certs :=
  ⟨_, ClassClaim.zero 157⟩

theorem classClaim_c158 : ∃ certs, ClassClaim 158 0 certs :=
  ⟨_, ClassClaim.zero 158⟩

theorem classClaim_c159 : ∃ certs, ClassClaim 159 0 certs :=
  ⟨_, ClassClaim.zero 159⟩

theorem classClaim_c160 : ∃ certs, ClassClaim 160 0 certs :=
  ⟨_, ClassClaim.zero 160⟩

theorem classClaim_c161 : ∃ certs, ClassClaim 161 0 certs :=
  ⟨_, ClassClaim.zero 161⟩

theorem classClaim_c162 : ∃ certs, ClassClaim 162 0 certs :=
  ⟨_, ClassClaim.zero 162⟩

theorem classClaim_c163 : ∃ certs, ClassClaim 163 0 certs :=
  ⟨_, ClassClaim.zero 163⟩

theorem classClaim_c164 : ∃ certs, ClassClaim 164 0 certs :=
  ⟨_, ClassClaim.zero 164⟩

theorem classClaim_c165 : ∃ certs, ClassClaim 165 0 certs :=
  ⟨_, ClassClaim.zero 165⟩

theorem classClaim_c166 : ∃ certs, ClassClaim 166 0 certs :=
  ⟨_, ClassClaim.zero 166⟩

theorem classClaim_c167 : ∃ certs, ClassClaim 167 72 certs :=
  ⟨_, ClassClaim.zero 167
    |>.extend F34S_c167_k0 certsOK_c167_k0 rfl⟩

theorem classClaim_c168 : ∃ certs, ClassClaim 168 0 certs :=
  ⟨_, ClassClaim.zero 168⟩

theorem classClaim_c169 : ∃ certs, ClassClaim 169 18 certs :=
  ⟨_, ClassClaim.zero 169
    |>.extend F34S_c169_k0 certsOK_c169_k0 rfl⟩

theorem classClaim_c170 : ∃ certs, ClassClaim 170 9 certs :=
  ⟨_, ClassClaim.zero 170
    |>.extend F34S_c170_k0 certsOK_c170_k0 rfl⟩

theorem classClaim_c171 : ∃ certs, ClassClaim 171 19 certs :=
  ⟨_, ClassClaim.zero 171
    |>.extend F34S_c171_k0 certsOK_c171_k0 rfl⟩

theorem classClaim_c172 : ∃ certs, ClassClaim 172 6 certs :=
  ⟨_, ClassClaim.zero 172
    |>.extend F34S_c172_k0 certsOK_c172_k0 rfl⟩

theorem classClaim_c173 : ∃ certs, ClassClaim 173 1 certs :=
  ⟨_, ClassClaim.zero 173
    |>.extend F34S_c173_k0 certsOK_c173_k0 rfl⟩

theorem classClaim_c174 : ∃ certs, ClassClaim 174 0 certs :=
  ⟨_, ClassClaim.zero 174⟩

theorem classClaim_c175 : ∃ certs, ClassClaim 175 0 certs :=
  ⟨_, ClassClaim.zero 175⟩

theorem classClaim_c176 : ∃ certs, ClassClaim 176 0 certs :=
  ⟨_, ClassClaim.zero 176⟩

theorem classClaim_c177 : ∃ certs, ClassClaim 177 0 certs :=
  ⟨_, ClassClaim.zero 177⟩

theorem classClaim_c178 : ∃ certs, ClassClaim 178 0 certs :=
  ⟨_, ClassClaim.zero 178⟩

theorem classClaim_c179 : ∃ certs, ClassClaim 179 0 certs :=
  ⟨_, ClassClaim.zero 179⟩

theorem classClaim_c180 : ∃ certs, ClassClaim 180 0 certs :=
  ⟨_, ClassClaim.zero 180⟩

theorem classClaim_c181 : ∃ certs, ClassClaim 181 0 certs :=
  ⟨_, ClassClaim.zero 181⟩

theorem classClaim_c182 : ∃ certs, ClassClaim 182 0 certs :=
  ⟨_, ClassClaim.zero 182⟩

theorem classClaim_c183 : ∃ certs, ClassClaim 183 1 certs :=
  ⟨_, ClassClaim.zero 183
    |>.extend F34S_c183_k0 certsOK_c183_k0 rfl⟩

theorem classClaim_c184 : ∃ certs, ClassClaim 184 0 certs :=
  ⟨_, ClassClaim.zero 184⟩

theorem classClaim_c185 : ∃ certs, ClassClaim 185 0 certs :=
  ⟨_, ClassClaim.zero 185⟩

theorem classClaim_c186 : ∃ certs, ClassClaim 186 0 certs :=
  ⟨_, ClassClaim.zero 186⟩

theorem classClaim_c187 : ∃ certs, ClassClaim 187 0 certs :=
  ⟨_, ClassClaim.zero 187⟩

theorem classClaim_c188 : ∃ certs, ClassClaim 188 0 certs :=
  ⟨_, ClassClaim.zero 188⟩

theorem classClaim_c189 : ∃ certs, ClassClaim 189 0 certs :=
  ⟨_, ClassClaim.zero 189⟩

theorem classClaim_c190 : ∃ certs, ClassClaim 190 0 certs :=
  ⟨_, ClassClaim.zero 190⟩

/-- **The claims of the stored cells of all classes**, with the certificates of each class named. -/
theorem classClaim : ∀ k < 191, ∃ certs, ClassClaim k (L6.F34S.Checks.ncellsList.getD k 0) certs := by
  intro k hk
  match k, hk with
  | 0, _ => exact classClaim_c0
  | 1, _ => exact classClaim_c1
  | 2, _ => exact classClaim_c2
  | 3, _ => exact classClaim_c3
  | 4, _ => exact classClaim_c4
  | 5, _ => exact classClaim_c5
  | 6, _ => exact classClaim_c6
  | 7, _ => exact classClaim_c7
  | 8, _ => exact classClaim_c8
  | 9, _ => exact classClaim_c9
  | 10, _ => exact classClaim_c10
  | 11, _ => exact classClaim_c11
  | 12, _ => exact classClaim_c12
  | 13, _ => exact classClaim_c13
  | 14, _ => exact classClaim_c14
  | 15, _ => exact classClaim_c15
  | 16, _ => exact classClaim_c16
  | 17, _ => exact classClaim_c17
  | 18, _ => exact classClaim_c18
  | 19, _ => exact classClaim_c19
  | 20, _ => exact classClaim_c20
  | 21, _ => exact classClaim_c21
  | 22, _ => exact classClaim_c22
  | 23, _ => exact classClaim_c23
  | 24, _ => exact classClaim_c24
  | 25, _ => exact classClaim_c25
  | 26, _ => exact classClaim_c26
  | 27, _ => exact classClaim_c27
  | 28, _ => exact classClaim_c28
  | 29, _ => exact classClaim_c29
  | 30, _ => exact classClaim_c30
  | 31, _ => exact classClaim_c31
  | 32, _ => exact classClaim_c32
  | 33, _ => exact classClaim_c33
  | 34, _ => exact classClaim_c34
  | 35, _ => exact classClaim_c35
  | 36, _ => exact classClaim_c36
  | 37, _ => exact classClaim_c37
  | 38, _ => exact classClaim_c38
  | 39, _ => exact classClaim_c39
  | 40, _ => exact classClaim_c40
  | 41, _ => exact classClaim_c41
  | 42, _ => exact classClaim_c42
  | 43, _ => exact classClaim_c43
  | 44, _ => exact classClaim_c44
  | 45, _ => exact classClaim_c45
  | 46, _ => exact classClaim_c46
  | 47, _ => exact classClaim_c47
  | 48, _ => exact classClaim_c48
  | 49, _ => exact classClaim_c49
  | 50, _ => exact classClaim_c50
  | 51, _ => exact classClaim_c51
  | 52, _ => exact classClaim_c52
  | 53, _ => exact classClaim_c53
  | 54, _ => exact classClaim_c54
  | 55, _ => exact classClaim_c55
  | 56, _ => exact classClaim_c56
  | 57, _ => exact classClaim_c57
  | 58, _ => exact classClaim_c58
  | 59, _ => exact classClaim_c59
  | 60, _ => exact classClaim_c60
  | 61, _ => exact classClaim_c61
  | 62, _ => exact classClaim_c62
  | 63, _ => exact classClaim_c63
  | 64, _ => exact classClaim_c64
  | 65, _ => exact classClaim_c65
  | 66, _ => exact classClaim_c66
  | 67, _ => exact classClaim_c67
  | 68, _ => exact classClaim_c68
  | 69, _ => exact classClaim_c69
  | 70, _ => exact classClaim_c70
  | 71, _ => exact classClaim_c71
  | 72, _ => exact classClaim_c72
  | 73, _ => exact classClaim_c73
  | 74, _ => exact classClaim_c74
  | 75, _ => exact classClaim_c75
  | 76, _ => exact classClaim_c76
  | 77, _ => exact classClaim_c77
  | 78, _ => exact classClaim_c78
  | 79, _ => exact classClaim_c79
  | 80, _ => exact classClaim_c80
  | 81, _ => exact classClaim_c81
  | 82, _ => exact classClaim_c82
  | 83, _ => exact classClaim_c83
  | 84, _ => exact classClaim_c84
  | 85, _ => exact classClaim_c85
  | 86, _ => exact classClaim_c86
  | 87, _ => exact classClaim_c87
  | 88, _ => exact classClaim_c88
  | 89, _ => exact classClaim_c89
  | 90, _ => exact classClaim_c90
  | 91, _ => exact classClaim_c91
  | 92, _ => exact classClaim_c92
  | 93, _ => exact classClaim_c93
  | 94, _ => exact classClaim_c94
  | 95, _ => exact classClaim_c95
  | 96, _ => exact classClaim_c96
  | 97, _ => exact classClaim_c97
  | 98, _ => exact classClaim_c98
  | 99, _ => exact classClaim_c99
  | 100, _ => exact classClaim_c100
  | 101, _ => exact classClaim_c101
  | 102, _ => exact classClaim_c102
  | 103, _ => exact classClaim_c103
  | 104, _ => exact classClaim_c104
  | 105, _ => exact classClaim_c105
  | 106, _ => exact classClaim_c106
  | 107, _ => exact classClaim_c107
  | 108, _ => exact classClaim_c108
  | 109, _ => exact classClaim_c109
  | 110, _ => exact classClaim_c110
  | 111, _ => exact classClaim_c111
  | 112, _ => exact classClaim_c112
  | 113, _ => exact classClaim_c113
  | 114, _ => exact classClaim_c114
  | 115, _ => exact classClaim_c115
  | 116, _ => exact classClaim_c116
  | 117, _ => exact classClaim_c117
  | 118, _ => exact classClaim_c118
  | 119, _ => exact classClaim_c119
  | 120, _ => exact classClaim_c120
  | 121, _ => exact classClaim_c121
  | 122, _ => exact classClaim_c122
  | 123, _ => exact classClaim_c123
  | 124, _ => exact classClaim_c124
  | 125, _ => exact classClaim_c125
  | 126, _ => exact classClaim_c126
  | 127, _ => exact classClaim_c127
  | 128, _ => exact classClaim_c128
  | 129, _ => exact classClaim_c129
  | 130, _ => exact classClaim_c130
  | 131, _ => exact classClaim_c131
  | 132, _ => exact classClaim_c132
  | 133, _ => exact classClaim_c133
  | 134, _ => exact classClaim_c134
  | 135, _ => exact classClaim_c135
  | 136, _ => exact classClaim_c136
  | 137, _ => exact classClaim_c137
  | 138, _ => exact classClaim_c138
  | 139, _ => exact classClaim_c139
  | 140, _ => exact classClaim_c140
  | 141, _ => exact classClaim_c141
  | 142, _ => exact classClaim_c142
  | 143, _ => exact classClaim_c143
  | 144, _ => exact classClaim_c144
  | 145, _ => exact classClaim_c145
  | 146, _ => exact classClaim_c146
  | 147, _ => exact classClaim_c147
  | 148, _ => exact classClaim_c148
  | 149, _ => exact classClaim_c149
  | 150, _ => exact classClaim_c150
  | 151, _ => exact classClaim_c151
  | 152, _ => exact classClaim_c152
  | 153, _ => exact classClaim_c153
  | 154, _ => exact classClaim_c154
  | 155, _ => exact classClaim_c155
  | 156, _ => exact classClaim_c156
  | 157, _ => exact classClaim_c157
  | 158, _ => exact classClaim_c158
  | 159, _ => exact classClaim_c159
  | 160, _ => exact classClaim_c160
  | 161, _ => exact classClaim_c161
  | 162, _ => exact classClaim_c162
  | 163, _ => exact classClaim_c163
  | 164, _ => exact classClaim_c164
  | 165, _ => exact classClaim_c165
  | 166, _ => exact classClaim_c166
  | 167, _ => exact classClaim_c167
  | 168, _ => exact classClaim_c168
  | 169, _ => exact classClaim_c169
  | 170, _ => exact classClaim_c170
  | 171, _ => exact classClaim_c171
  | 172, _ => exact classClaim_c172
  | 173, _ => exact classClaim_c173
  | 174, _ => exact classClaim_c174
  | 175, _ => exact classClaim_c175
  | 176, _ => exact classClaim_c176
  | 177, _ => exact classClaim_c177
  | 178, _ => exact classClaim_c178
  | 179, _ => exact classClaim_c179
  | 180, _ => exact classClaim_c180
  | 181, _ => exact classClaim_c181
  | 182, _ => exact classClaim_c182
  | 183, _ => exact classClaim_c183
  | 184, _ => exact classClaim_c184
  | 185, _ => exact classClaim_c185
  | 186, _ => exact classClaim_c186
  | 187, _ => exact classClaim_c187
  | 188, _ => exact classClaim_c188
  | 189, _ => exact classClaim_c189
  | 190, _ => exact classClaim_c190
  | k + 191, h => exact absurd h (by omega)

end CC6Compose
