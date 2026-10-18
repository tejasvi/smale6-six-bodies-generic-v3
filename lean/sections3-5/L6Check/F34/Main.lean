import L6Check.F34.C0K0
import L6Check.F34.C3K0
import L6Check.F34.C3K1
import L6Check.F34.C3K2
import L6Check.F34.C3K3
import L6Check.F34.C3K4
import L6Check.F34.C3K5
import L6Check.F34.C3K6
import L6Check.F34.C3K7
import L6Check.F34.C3K8
import L6Check.F34.C3K9
import L6Check.F34.C3K10
import L6Check.F34.C3K11
import L6Check.F34.C3K12
import L6Check.F34.C3K13
import L6Check.F34.C3K14
import L6Check.F34.C3K15
import L6Check.F34.C3K16
import L6Check.F34.C3K17
import L6Check.F34.C3K18
import L6Check.F34.C3K19
import L6Check.F34.C3K20
import L6Check.F34.C3K21
import L6Check.F34.C3K22
import L6Check.F34.C3K23
import L6Check.F34.C3K24
import L6Check.F34.C3K25
import L6Check.F34.C3K26
import L6Check.F34.C3K27
import L6Check.F34.C3K28
import L6Check.F34.C3K29
import L6Check.F34.C4K0
import L6Check.F34.C8K0
import L6Check.F34.C10K0
import L6Check.F34.C12K0
import L6Check.F34.C13K0
import L6Check.F34.C14K0
import L6Check.F34.C15K0
import L6Check.F34.C16K0
import L6Check.F34.C20K0
import L6Check.F34.C22K0
import L6Check.F34.C23K0
import L6Check.F34.C24K0
import L6Check.F34.C25K0
import L6Check.F34.C28K0
import L6Check.F34.C29K0
import L6Check.F34.C29K1
import L6Check.F34.C30K0
import L6Check.F34.C31K0
import L6Check.F34.C34K0
import L6Check.F34.C35K0
import L6Check.F34.C40K0
import L6Check.F34.C42K0
import L6Check.F34.C44K0
import L6Check.F34.C47K0
import L6Check.F34.C53K0
import L6Check.F34.C55K0
import L6Check.F34.C56K0
import L6Check.F34.C57K0
import L6Check.F34.C58K0
import L6Check.F34.C62K0
import L6Check.F34.C63K0
import L6Check.F34.C64K0
import L6Check.F34.C65K0
import L6Check.F34.C66K0
import L6Check.F34.C67K0
import L6Check.F34.C69K0
import L6Check.F34.C84K0
import L6Check.F34.C110K0
import L6Check.F34.C116K0
import L6Check.F34.C117K0
import L6Check.F34.C119K0
import L6Check.F34.C120K0
import L6Check.F34.C121K0
import L6Check.F34.C122K0
import L6Check.F34.C123K0
import L6Check.F34.C124K0
import L6Check.F34.C126K0
import L6Check.F34.C127K0
import L6Check.F34.C128K0
import L6Check.F34.C128K1
import L6Check.F34.C128K2
import L6Check.F34.C128K3
import L6Check.F34.C128K4
import L6Check.F34.C128K5
import L6Check.F34.C128K6
import L6Check.F34.C128K7
import L6Check.F34.C128K8
import L6Check.F34.C128K9
import L6Check.F34.C128K10
import L6Check.F34.C128K11
import L6Check.F34.C128K12
import L6Check.F34.C128K13
import L6Check.F34.C128K14
import L6Check.F34.C128K15
import L6Check.F34.C128K16
import L6Check.F34.C128K17
import L6Check.F34.C128K18
import L6Check.F34.C128K19
import L6Check.F34.C128K20
import L6Check.F34.C128K21
import L6Check.F34.C129K0
import L6Check.F34.C130K0
import L6Check.F34.C131K0
import L6Check.F34.C132K0
import L6Check.F34.C133K0
import L6Check.F34.C142K0
import L6Check.F34.C143K0
import L6Check.F34.C146K0
import L6Check.F34.C147K0
import L6Check.F34.C148K0
import L6Check.F34.C148K1
import L6Check.F34.C148K2
import L6Check.F34.C148K3
import L6Check.F34.C149K0
import L6Check.F34.C150K0
import L6Check.F34.C167K0
import L6Check.F34.C169K0
import L6Check.F34.C170K0
import L6Check.F34.C171K0
import L6Check.F34.C172K0
import L6Check.F34.C173K0
import L6Check.F34.C183K0
import L6Check.F34.Cover
import L6Check.F34.Sha

/-! F3/F4 (Proposition 5.3): the chunks, their counts, and the totals. Each row `(class, lo, hi, single, core1,
core2, open)` is the statement of the theorem `F34_c<class>_k<k>`; the rows of a class cover its cells
(`F34_cover`, `F34_chunks_cover`). -/

namespace L6.F34.Checks

/-- The chunks and their counts. -/
def chunkTable : List (Nat × Nat × Nat × Nat × Nat × Nat × Nat) := [
  (0, 0, 17, 8, 9, 0, 0),
  (3, 0, 1500, 1243, 213, 44, 0),
  (3, 1500, 3000, 1019, 481, 0, 0),
  (3, 3000, 4500, 797, 703, 0, 0),
  (3, 4500, 6000, 583, 917, 0, 0),
  (3, 6000, 7500, 664, 835, 1, 0),
  (3, 7500, 9000, 40, 1443, 17, 0),
  (3, 9000, 10500, 387, 1110, 3, 0),
  (3, 10500, 12000, 801, 699, 0, 0),
  (3, 12000, 13500, 623, 841, 36, 0),
  (3, 13500, 15000, 670, 824, 6, 0),
  (3, 15000, 16500, 45, 1454, 1, 0),
  (3, 16500, 18000, 304, 1177, 19, 0),
  (3, 18000, 19500, 443, 1057, 0, 0),
  (3, 19500, 21000, 968, 532, 0, 0),
  (3, 21000, 22500, 896, 604, 0, 0),
  (3, 22500, 24000, 499, 1001, 0, 0),
  (3, 24000, 25500, 1204, 252, 44, 0),
  (3, 25500, 27000, 573, 927, 0, 0),
  (3, 27000, 28500, 729, 771, 0, 0),
  (3, 28500, 30000, 1128, 372, 0, 0),
  (3, 30000, 31500, 1242, 214, 44, 0),
  (3, 31500, 33000, 771, 688, 41, 0),
  (3, 33000, 34500, 1208, 251, 41, 0),
  (3, 34500, 36000, 537, 963, 0, 0),
  (3, 36000, 37500, 757, 743, 0, 0),
  (3, 37500, 39000, 1041, 418, 41, 0),
  (3, 39000, 40500, 1148, 267, 85, 0),
  (3, 40500, 42000, 965, 402, 133, 0),
  (3, 42000, 43500, 1240, 216, 44, 0),
  (3, 43500, 44247, 493, 254, 0, 0),
  (4, 0, 177, 154, 23, 0, 0),
  (8, 0, 1, 0, 1, 0, 0),
  (10, 0, 10, 0, 10, 0, 0),
  (12, 0, 1, 0, 1, 0, 0),
  (13, 0, 1, 0, 1, 0, 0),
  (14, 0, 865, 273, 448, 144, 0),
  (15, 0, 42, 29, 13, 0, 0),
  (16, 0, 28, 0, 28, 0, 0),
  (20, 0, 13, 0, 13, 0, 0),
  (22, 0, 2, 0, 2, 0, 0),
  (23, 0, 239, 102, 137, 0, 0),
  (24, 0, 72, 24, 48, 0, 0),
  (25, 0, 88, 18, 70, 0, 0),
  (28, 0, 3, 2, 1, 0, 0),
  (29, 0, 1500, 486, 983, 31, 0),
  (29, 1500, 1866, 84, 262, 20, 0),
  (30, 0, 273, 14, 198, 61, 0),
  (31, 0, 49, 0, 48, 0, 1),
  (34, 0, 1, 0, 1, 0, 0),
  (35, 0, 1, 0, 1, 0, 0),
  (40, 0, 394, 126, 224, 44, 0),
  (42, 0, 20, 0, 20, 0, 0),
  (44, 0, 154, 7, 147, 0, 0),
  (47, 0, 497, 128, 369, 0, 0),
  (53, 0, 3, 2, 1, 0, 0),
  (55, 0, 24, 24, 0, 0, 0),
  (56, 0, 37, 6, 31, 0, 0),
  (57, 0, 2, 0, 2, 0, 0),
  (58, 0, 2, 0, 2, 0, 0),
  (62, 0, 14, 0, 14, 0, 0),
  (63, 0, 7, 0, 7, 0, 0),
  (64, 0, 162, 64, 98, 0, 0),
  (65, 0, 1, 0, 1, 0, 0),
  (66, 0, 1, 0, 1, 0, 0),
  (67, 0, 2, 0, 2, 0, 0),
  (69, 0, 2, 0, 2, 0, 0),
  (84, 0, 1, 0, 1, 0, 0),
  (110, 0, 1, 0, 1, 0, 0),
  (116, 0, 21, 6, 15, 0, 0),
  (117, 0, 2, 0, 2, 0, 0),
  (119, 0, 1, 0, 1, 0, 0),
  (120, 0, 2, 0, 2, 0, 0),
  (121, 0, 1, 0, 1, 0, 0),
  (122, 0, 10, 0, 10, 0, 0),
  (123, 0, 1, 0, 1, 0, 0),
  (124, 0, 143, 0, 132, 0, 11),
  (126, 0, 27, 0, 27, 0, 0),
  (127, 0, 9, 0, 0, 0, 9),
  (128, 0, 1500, 1234, 266, 0, 0),
  (128, 1500, 3000, 1286, 214, 0, 0),
  (128, 3000, 4500, 1020, 480, 0, 0),
  (128, 4500, 6000, 228, 1272, 0, 0),
  (128, 6000, 7500, 0, 1500, 0, 0),
  (128, 7500, 9000, 397, 1103, 0, 0),
  (128, 9000, 10500, 1276, 224, 0, 0),
  (128, 10500, 12000, 1144, 356, 0, 0),
  (128, 12000, 13500, 1234, 266, 0, 0),
  (128, 13500, 15000, 1185, 315, 0, 0),
  (128, 15000, 16500, 1236, 264, 0, 0),
  (128, 16500, 18000, 1094, 406, 0, 0),
  (128, 18000, 19500, 1122, 378, 0, 0),
  (128, 19500, 21000, 1064, 436, 0, 0),
  (128, 21000, 22500, 1174, 326, 0, 0),
  (128, 22500, 24000, 1195, 305, 0, 0),
  (128, 24000, 25500, 1267, 233, 0, 0),
  (128, 25500, 27000, 1150, 350, 0, 0),
  (128, 27000, 28500, 1091, 409, 0, 0),
  (128, 28500, 30000, 1242, 258, 0, 0),
  (128, 30000, 31500, 1154, 346, 0, 0),
  (128, 31500, 32864, 1124, 240, 0, 0),
  (129, 0, 1449, 924, 525, 0, 0),
  (130, 0, 630, 0, 630, 0, 0),
  (131, 0, 196, 196, 0, 0, 0),
  (132, 0, 147, 0, 145, 1, 1),
  (133, 0, 49, 0, 48, 0, 1),
  (142, 0, 297, 189, 108, 0, 0),
  (143, 0, 77, 0, 66, 0, 11),
  (146, 0, 81, 0, 81, 0, 0),
  (147, 0, 63, 0, 54, 0, 9),
  (148, 0, 1500, 504, 996, 0, 0),
  (148, 1500, 3000, 1223, 272, 5, 0),
  (148, 3000, 4500, 1233, 244, 23, 0),
  (148, 4500, 4777, 251, 21, 5, 0),
  (149, 0, 756, 420, 280, 56, 0),
  (150, 0, 224, 0, 224, 0, 0),
  (167, 0, 72, 0, 72, 0, 0),
  (169, 0, 18, 0, 18, 0, 0),
  (170, 0, 9, 0, 9, 0, 0),
  (171, 0, 19, 0, 19, 0, 0),
  (172, 0, 6, 0, 6, 0, 0),
  (173, 0, 1, 0, 1, 0, 0),
  (183, 0, 1, 0, 1, 0, 0)]

/-- The chunks of each class are consecutive from `0` to its number of cells (`F34_cover`). -/
def coverOK (ncells : List Nat) : Bool :=
  (List.range 191).all fun c =>
    let rs := chunkTable.filter (·.1 == c)
    let n := ncells.getD c 0
    (rs.foldl (fun (pos : Option Nat) r => pos.bind fun p => if r.2.1 == p then some r.2.2.1 else none) (some 0)) == some n

theorem F34_chunks_cover : coverOK [17, 0, 0, 44247, 177, 0, 0, 0, 1, 0, 10, 0, 1, 1, 865, 42, 28, 0, 0, 0, 13, 0, 2, 239, 72, 88, 0, 0, 3, 1866, 273, 49, 0, 0, 1, 1, 0, 0, 0, 0, 394, 0, 20, 0, 154, 0, 0, 497, 0, 0, 0, 0, 0, 3, 0, 24, 37, 2, 2, 0, 0, 0, 14, 7, 162, 1, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 21, 2, 0, 1, 2, 1, 10, 1, 143, 0, 27, 9, 32864, 1449, 630, 196, 147, 49, 0, 0, 0, 0, 0, 0, 0, 0, 297, 77, 0, 0, 81, 63, 4777, 756, 224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 18, 9, 19, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] = true := by decide +kernel

/-- Totals: single-term cells, first-pass core cells, second-pass core cells, open cells. -/
theorem F34_totals :
    (chunkTable.map (·.2.2.2.1)).sum = 52432 ∧ (chunkTable.map (·.2.2.2.2.1)).sum = 37808 ∧
    (chunkTable.map (·.2.2.2.2.2.1)).sum = 990 ∧ (chunkTable.map (·.2.2.2.2.2.2)).sum = 43 := by decide +kernel

end L6.F34.Checks
