import L6KSpec.Boxes
import L6KSpec.Load

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Boxes 4224–4287 of Lemma 6.19(d), sorted by the real part of the first centre. -/

namespace L6CheckKSpec.KC.M66

open Lean6.Special.D88.Boxes L6KSpec

load_box_chunks x "data/ksp/KC_M66.bin" 54648

theorem ok0 : (boxesOf 273 12 8 x0).all kcBoxOKB = true := by decide +kernel
theorem ok1 : (boxesOf 273 12 8 x1).all kcBoxOKB = true := by decide +kernel
theorem ok2 : (boxesOf 273 12 8 x2).all kcBoxOKB = true := by decide +kernel
theorem ok3 : (boxesOf 273 12 8 x3).all kcBoxOKB = true := by decide +kernel
theorem ok4 : (boxesOf 273 12 8 x4).all kcBoxOKB = true := by decide +kernel
theorem ok5 : (boxesOf 273 12 8 x5).all kcBoxOKB = true := by decide +kernel
theorem ok6 : (boxesOf 273 12 8 x6).all kcBoxOKB = true := by decide +kernel
theorem ok7 : (boxesOf 273 12 8 x7).all kcBoxOKB = true := by decide +kernel

/-- The boxes of this module. -/
noncomputable def boxes : List Box := boxesOf 273 12 8 x0 ++ boxesOf 273 12 8 x1 ++ boxesOf 273 12 8 x2 ++ boxesOf 273 12 8 x3 ++ boxesOf 273 12 8 x4 ++ boxesOf 273 12 8 x5 ++ boxesOf 273 12 8 x6 ++ boxesOf 273 12 8 x7

theorem all_ok : boxes.all kcBoxOKB = true := by
  simp only [boxes, List.all_append, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, Bool.and_self]

end L6CheckKSpec.KC.M66
