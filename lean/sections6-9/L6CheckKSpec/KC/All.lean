import L6KSpec.Boxes
import L6CheckKSpec.KC.M0
import L6CheckKSpec.KC.M1
import L6CheckKSpec.KC.M2
import L6CheckKSpec.KC.M3
import L6CheckKSpec.KC.M4
import L6CheckKSpec.KC.M5
import L6CheckKSpec.KC.M6
import L6CheckKSpec.KC.M7
import L6CheckKSpec.KC.M8
import L6CheckKSpec.KC.M9
import L6CheckKSpec.KC.M10
import L6CheckKSpec.KC.M11
import L6CheckKSpec.KC.M12
import L6CheckKSpec.KC.M13
import L6CheckKSpec.KC.M14
import L6CheckKSpec.KC.M15
import L6CheckKSpec.KC.M16
import L6CheckKSpec.KC.M17
import L6CheckKSpec.KC.M18
import L6CheckKSpec.KC.M19
import L6CheckKSpec.KC.M20
import L6CheckKSpec.KC.M21
import L6CheckKSpec.KC.M22
import L6CheckKSpec.KC.M23
import L6CheckKSpec.KC.M24
import L6CheckKSpec.KC.M25
import L6CheckKSpec.KC.M26
import L6CheckKSpec.KC.M27
import L6CheckKSpec.KC.M28
import L6CheckKSpec.KC.M29
import L6CheckKSpec.KC.M30
import L6CheckKSpec.KC.M31
import L6CheckKSpec.KC.M32
import L6CheckKSpec.KC.M33
import L6CheckKSpec.KC.M34
import L6CheckKSpec.KC.M35
import L6CheckKSpec.KC.M36
import L6CheckKSpec.KC.M37
import L6CheckKSpec.KC.M38
import L6CheckKSpec.KC.M39
import L6CheckKSpec.KC.M40
import L6CheckKSpec.KC.M41
import L6CheckKSpec.KC.M42
import L6CheckKSpec.KC.M43
import L6CheckKSpec.KC.M44
import L6CheckKSpec.KC.M45
import L6CheckKSpec.KC.M46
import L6CheckKSpec.KC.M47
import L6CheckKSpec.KC.M48
import L6CheckKSpec.KC.M49
import L6CheckKSpec.KC.M50
import L6CheckKSpec.KC.M51
import L6CheckKSpec.KC.M52
import L6CheckKSpec.KC.M53
import L6CheckKSpec.KC.M54
import L6CheckKSpec.KC.M55
import L6CheckKSpec.KC.M56
import L6CheckKSpec.KC.M57
import L6CheckKSpec.KC.M58
import L6CheckKSpec.KC.M59
import L6CheckKSpec.KC.M60
import L6CheckKSpec.KC.M61
import L6CheckKSpec.KC.M62
import L6CheckKSpec.KC.M63
import L6CheckKSpec.KC.M64
import L6CheckKSpec.KC.M65
import L6CheckKSpec.KC.M66
import L6CheckKSpec.KC.M67
import L6CheckKSpec.KC.M68
import L6CheckKSpec.KC.M69
import L6CheckKSpec.KC.M70
import L6CheckKSpec.KC.M71
import L6CheckKSpec.KC.M72
import L6CheckKSpec.KC.M73
import L6CheckKSpec.KC.M74

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! All boxes of Lemma 6.19(d): the tests and the sweep. -/

namespace L6CheckKSpec.KC

open Lean6.Special.D88.Boxes L6KSpec

/-- All boxes, sorted by the real part of the first centre. -/
noncomputable def allBoxes : List Box := L6CheckKSpec.KC.M0.boxes ++ (L6CheckKSpec.KC.M1.boxes ++ (L6CheckKSpec.KC.M2.boxes ++ (L6CheckKSpec.KC.M3.boxes ++ (L6CheckKSpec.KC.M4.boxes ++ (L6CheckKSpec.KC.M5.boxes ++ (L6CheckKSpec.KC.M6.boxes ++ (L6CheckKSpec.KC.M7.boxes ++ (L6CheckKSpec.KC.M8.boxes ++ (L6CheckKSpec.KC.M9.boxes ++ (L6CheckKSpec.KC.M10.boxes ++ (L6CheckKSpec.KC.M11.boxes ++ (L6CheckKSpec.KC.M12.boxes ++ (L6CheckKSpec.KC.M13.boxes ++ (L6CheckKSpec.KC.M14.boxes ++ (L6CheckKSpec.KC.M15.boxes ++ (L6CheckKSpec.KC.M16.boxes ++ (L6CheckKSpec.KC.M17.boxes ++ (L6CheckKSpec.KC.M18.boxes ++ (L6CheckKSpec.KC.M19.boxes ++ (L6CheckKSpec.KC.M20.boxes ++ (L6CheckKSpec.KC.M21.boxes ++ (L6CheckKSpec.KC.M22.boxes ++ (L6CheckKSpec.KC.M23.boxes ++ (L6CheckKSpec.KC.M24.boxes ++ (L6CheckKSpec.KC.M25.boxes ++ (L6CheckKSpec.KC.M26.boxes ++ (L6CheckKSpec.KC.M27.boxes ++ (L6CheckKSpec.KC.M28.boxes ++ (L6CheckKSpec.KC.M29.boxes ++ (L6CheckKSpec.KC.M30.boxes ++ (L6CheckKSpec.KC.M31.boxes ++ (L6CheckKSpec.KC.M32.boxes ++ (L6CheckKSpec.KC.M33.boxes ++ (L6CheckKSpec.KC.M34.boxes ++ (L6CheckKSpec.KC.M35.boxes ++ (L6CheckKSpec.KC.M36.boxes ++ (L6CheckKSpec.KC.M37.boxes ++ (L6CheckKSpec.KC.M38.boxes ++ (L6CheckKSpec.KC.M39.boxes ++ (L6CheckKSpec.KC.M40.boxes ++ (L6CheckKSpec.KC.M41.boxes ++ (L6CheckKSpec.KC.M42.boxes ++ (L6CheckKSpec.KC.M43.boxes ++ (L6CheckKSpec.KC.M44.boxes ++ (L6CheckKSpec.KC.M45.boxes ++ (L6CheckKSpec.KC.M46.boxes ++ (L6CheckKSpec.KC.M47.boxes ++ (L6CheckKSpec.KC.M48.boxes ++ (L6CheckKSpec.KC.M49.boxes ++ (L6CheckKSpec.KC.M50.boxes ++ (L6CheckKSpec.KC.M51.boxes ++ (L6CheckKSpec.KC.M52.boxes ++ (L6CheckKSpec.KC.M53.boxes ++ (L6CheckKSpec.KC.M54.boxes ++ (L6CheckKSpec.KC.M55.boxes ++ (L6CheckKSpec.KC.M56.boxes ++ (L6CheckKSpec.KC.M57.boxes ++ (L6CheckKSpec.KC.M58.boxes ++ (L6CheckKSpec.KC.M59.boxes ++ (L6CheckKSpec.KC.M60.boxes ++ (L6CheckKSpec.KC.M61.boxes ++ (L6CheckKSpec.KC.M62.boxes ++ (L6CheckKSpec.KC.M63.boxes ++ (L6CheckKSpec.KC.M64.boxes ++ (L6CheckKSpec.KC.M65.boxes ++ (L6CheckKSpec.KC.M66.boxes ++ (L6CheckKSpec.KC.M67.boxes ++ (L6CheckKSpec.KC.M68.boxes ++ (L6CheckKSpec.KC.M69.boxes ++ (L6CheckKSpec.KC.M70.boxes ++ (L6CheckKSpec.KC.M71.boxes ++ (L6CheckKSpec.KC.M72.boxes ++ (L6CheckKSpec.KC.M73.boxes ++ (L6CheckKSpec.KC.M74.boxes))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem all_ok : allBoxes.all kcBoxOKB = true := by
  simp only [allBoxes, List.all_append, L6CheckKSpec.KC.M0.all_ok, L6CheckKSpec.KC.M1.all_ok, L6CheckKSpec.KC.M2.all_ok, L6CheckKSpec.KC.M3.all_ok, L6CheckKSpec.KC.M4.all_ok, L6CheckKSpec.KC.M5.all_ok, L6CheckKSpec.KC.M6.all_ok, L6CheckKSpec.KC.M7.all_ok, L6CheckKSpec.KC.M8.all_ok, L6CheckKSpec.KC.M9.all_ok, L6CheckKSpec.KC.M10.all_ok, L6CheckKSpec.KC.M11.all_ok, L6CheckKSpec.KC.M12.all_ok, L6CheckKSpec.KC.M13.all_ok, L6CheckKSpec.KC.M14.all_ok, L6CheckKSpec.KC.M15.all_ok, L6CheckKSpec.KC.M16.all_ok, L6CheckKSpec.KC.M17.all_ok, L6CheckKSpec.KC.M18.all_ok, L6CheckKSpec.KC.M19.all_ok, L6CheckKSpec.KC.M20.all_ok, L6CheckKSpec.KC.M21.all_ok, L6CheckKSpec.KC.M22.all_ok, L6CheckKSpec.KC.M23.all_ok, L6CheckKSpec.KC.M24.all_ok, L6CheckKSpec.KC.M25.all_ok, L6CheckKSpec.KC.M26.all_ok, L6CheckKSpec.KC.M27.all_ok, L6CheckKSpec.KC.M28.all_ok, L6CheckKSpec.KC.M29.all_ok, L6CheckKSpec.KC.M30.all_ok, L6CheckKSpec.KC.M31.all_ok, L6CheckKSpec.KC.M32.all_ok, L6CheckKSpec.KC.M33.all_ok, L6CheckKSpec.KC.M34.all_ok, L6CheckKSpec.KC.M35.all_ok, L6CheckKSpec.KC.M36.all_ok, L6CheckKSpec.KC.M37.all_ok, L6CheckKSpec.KC.M38.all_ok, L6CheckKSpec.KC.M39.all_ok, L6CheckKSpec.KC.M40.all_ok, L6CheckKSpec.KC.M41.all_ok, L6CheckKSpec.KC.M42.all_ok, L6CheckKSpec.KC.M43.all_ok, L6CheckKSpec.KC.M44.all_ok, L6CheckKSpec.KC.M45.all_ok, L6CheckKSpec.KC.M46.all_ok, L6CheckKSpec.KC.M47.all_ok, L6CheckKSpec.KC.M48.all_ok, L6CheckKSpec.KC.M49.all_ok, L6CheckKSpec.KC.M50.all_ok, L6CheckKSpec.KC.M51.all_ok, L6CheckKSpec.KC.M52.all_ok, L6CheckKSpec.KC.M53.all_ok, L6CheckKSpec.KC.M54.all_ok, L6CheckKSpec.KC.M55.all_ok, L6CheckKSpec.KC.M56.all_ok, L6CheckKSpec.KC.M57.all_ok, L6CheckKSpec.KC.M58.all_ok, L6CheckKSpec.KC.M59.all_ok, L6CheckKSpec.KC.M60.all_ok, L6CheckKSpec.KC.M61.all_ok, L6CheckKSpec.KC.M62.all_ok, L6CheckKSpec.KC.M63.all_ok, L6CheckKSpec.KC.M64.all_ok, L6CheckKSpec.KC.M65.all_ok, L6CheckKSpec.KC.M66.all_ok, L6CheckKSpec.KC.M67.all_ok, L6CheckKSpec.KC.M68.all_ok, L6CheckKSpec.KC.M69.all_ok, L6CheckKSpec.KC.M70.all_ok, L6CheckKSpec.KC.M71.all_ok, L6CheckKSpec.KC.M72.all_ok, L6CheckKSpec.KC.M73.all_ok, L6CheckKSpec.KC.M74.all_ok, Bool.and_self]

theorem length_eq : allBoxes.length = 4788 := by decide +kernel
theorem sweep : sweepOK 574817955317602359319015 allBoxes = true := by decide +kernel

end L6CheckKSpec.KC
