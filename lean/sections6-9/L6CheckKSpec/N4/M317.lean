import L6KSpec.Boxes
import L6KSpec.Load

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Boxes 20288–20315 of Lemma 6.19(c), sorted by the real part of the first centre. -/

namespace L6CheckKSpec.N4.M317

open Lean6.Special.D88.Boxes L6KSpec

load_box_chunks x "data/ksp/N4_M317.bin" 21763

theorem ok0 : (boxesOf 270 11 8 x0).all n4BoxOKB = true := by decide +kernel
theorem ok1 : (boxesOf 270 11 8 x1).all n4BoxOKB = true := by decide +kernel
theorem ok2 : (boxesOf 270 11 8 x2).all n4BoxOKB = true := by decide +kernel
theorem ok3 : (boxesOf 270 11 4 x3).all n4BoxOKB = true := by decide +kernel

/-- The boxes of this module. -/
noncomputable def boxes : List Box := boxesOf 270 11 8 x0 ++ boxesOf 270 11 8 x1 ++ boxesOf 270 11 8 x2 ++ boxesOf 270 11 4 x3

theorem all_ok : boxes.all n4BoxOKB = true := by
  simp only [boxes, List.all_append, ok0, ok1, ok2, ok3, Bool.and_self]

end L6CheckKSpec.N4.M317
