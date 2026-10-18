import L6KSpec.Boxes
import L6KSpec.Load

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Boxes 4736–4787 of Lemma 6.19(d), sorted by the real part of the first centre. -/

namespace L6CheckKSpec.KC.M74

open Lean6.Special.D88.Boxes L6KSpec

load_box_chunks x "data/ksp/KC_M74.bin" 44403

theorem ok0 : (boxesOf 273 12 8 x0).all kcBoxOKB = true := by decide +kernel
theorem ok1 : (boxesOf 273 12 8 x1).all kcBoxOKB = true := by decide +kernel
theorem ok2 : (boxesOf 273 12 8 x2).all kcBoxOKB = true := by decide +kernel
theorem ok3 : (boxesOf 273 12 8 x3).all kcBoxOKB = true := by decide +kernel
theorem ok4 : (boxesOf 273 12 8 x4).all kcBoxOKB = true := by decide +kernel
theorem ok5 : (boxesOf 273 12 8 x5).all kcBoxOKB = true := by decide +kernel
theorem ok6 : (boxesOf 273 12 4 x6).all kcBoxOKB = true := by decide +kernel

/-- The boxes of this module. -/
noncomputable def boxes : List Box := boxesOf 273 12 8 x0 ++ boxesOf 273 12 8 x1 ++ boxesOf 273 12 8 x2 ++ boxesOf 273 12 8 x3 ++ boxesOf 273 12 8 x4 ++ boxesOf 273 12 8 x5 ++ boxesOf 273 12 4 x6

theorem all_ok : boxes.all kcBoxOKB = true := by
  simp only [boxes, List.all_append, ok0, ok1, ok2, ok3, ok4, ok5, ok6, Bool.and_self]

end L6CheckKSpec.KC.M74
