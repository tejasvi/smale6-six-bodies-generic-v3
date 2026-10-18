import L6CheckKSpec.KC.All
import L6SoundKSpec.Counts
import L6CheckKSpec.KC.Cnt0
import L6CheckKSpec.KC.Cnt1
import L6CheckKSpec.KC.Cnt2
import L6CheckKSpec.KC.Cnt3
import L6CheckKSpec.KC.Cnt4
import L6CheckKSpec.KC.Cnt5
import L6CheckKSpec.KC.Cnt6
import L6CheckKSpec.KC.Cnt7
import L6CheckKSpec.KC.Cnt8
import L6CheckKSpec.KC.Cnt9
import L6CheckKSpec.KC.Cnt10
import L6CheckKSpec.KC.Cnt11
import L6CheckKSpec.KC.Cnt12
import L6CheckKSpec.KC.Cnt13
import L6CheckKSpec.KC.Cnt14
import L6CheckKSpec.KC.Cnt15
import L6CheckKSpec.KC.Cnt16
import L6CheckKSpec.KC.Cnt17
import L6CheckKSpec.KC.Cnt18
import L6CheckKSpec.KC.Cnt19
import L6CheckKSpec.KC.Cnt20
import L6CheckKSpec.KC.Cnt21
import L6CheckKSpec.KC.Cnt22
import L6CheckKSpec.KC.Cnt23
import L6CheckKSpec.KC.Cnt24
import L6CheckKSpec.KC.Cnt25
import L6CheckKSpec.KC.Cnt26
import L6CheckKSpec.KC.Cnt27
import L6CheckKSpec.KC.Cnt28
import L6CheckKSpec.KC.Cnt29
import L6CheckKSpec.KC.Cnt30
import L6CheckKSpec.KC.Cnt31
import L6CheckKSpec.KC.Cnt32
import L6CheckKSpec.KC.Cnt33
import L6CheckKSpec.KC.Cnt34
import L6CheckKSpec.KC.Cnt35
import L6CheckKSpec.KC.Cnt36
import L6CheckKSpec.KC.Cnt37
import L6CheckKSpec.KC.Cnt38
import L6CheckKSpec.KC.Cnt39
import L6CheckKSpec.KC.Cnt40
import L6CheckKSpec.KC.Cnt41
import L6CheckKSpec.KC.Cnt42
import L6CheckKSpec.KC.Cnt43
import L6CheckKSpec.KC.Cnt44
import L6CheckKSpec.KC.Cnt45
import L6CheckKSpec.KC.Cnt46
import L6CheckKSpec.KC.Cnt47
import L6CheckKSpec.KC.Cnt48
import L6CheckKSpec.KC.Cnt49
import L6CheckKSpec.KC.Cnt50
import L6CheckKSpec.KC.Cnt51
import L6CheckKSpec.KC.Cnt52
import L6CheckKSpec.KC.Cnt53
import L6CheckKSpec.KC.Cnt54
import L6CheckKSpec.KC.Cnt55
import L6CheckKSpec.KC.Cnt56
import L6CheckKSpec.KC.Cnt57
import L6CheckKSpec.KC.Cnt58
import L6CheckKSpec.KC.Cnt59
import L6CheckKSpec.KC.Cnt60
import L6CheckKSpec.KC.Cnt61
import L6CheckKSpec.KC.Cnt62
import L6CheckKSpec.KC.Cnt63
import L6CheckKSpec.KC.Cnt64
import L6CheckKSpec.KC.Cnt65
import L6CheckKSpec.KC.Cnt66
import L6CheckKSpec.KC.Cnt67
import L6CheckKSpec.KC.Cnt68
import L6CheckKSpec.KC.Cnt69
import L6CheckKSpec.KC.Cnt70
import L6CheckKSpec.KC.Cnt71
import L6CheckKSpec.KC.Cnt72
import L6CheckKSpec.KC.Cnt73
import L6CheckKSpec.KC.Cnt74

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! The counts of all KC boxes. -/

namespace L6CheckKSpec.KC

open L6KSpec

theorem counts_ok : kcCountsB allBoxes = some (1092, 3696, 36) := by
  rw [show allBoxes = L6CheckKSpec.KC.M0.boxes ++ (L6CheckKSpec.KC.M1.boxes ++ (L6CheckKSpec.KC.M2.boxes ++ (L6CheckKSpec.KC.M3.boxes ++ (L6CheckKSpec.KC.M4.boxes ++ (L6CheckKSpec.KC.M5.boxes ++ (L6CheckKSpec.KC.M6.boxes ++ (L6CheckKSpec.KC.M7.boxes ++ (L6CheckKSpec.KC.M8.boxes ++ (L6CheckKSpec.KC.M9.boxes ++ (L6CheckKSpec.KC.M10.boxes ++ (L6CheckKSpec.KC.M11.boxes ++ (L6CheckKSpec.KC.M12.boxes ++ (L6CheckKSpec.KC.M13.boxes ++ (L6CheckKSpec.KC.M14.boxes ++ (L6CheckKSpec.KC.M15.boxes ++ (L6CheckKSpec.KC.M16.boxes ++ (L6CheckKSpec.KC.M17.boxes ++ (L6CheckKSpec.KC.M18.boxes ++ (L6CheckKSpec.KC.M19.boxes ++ (L6CheckKSpec.KC.M20.boxes ++ (L6CheckKSpec.KC.M21.boxes ++ (L6CheckKSpec.KC.M22.boxes ++ (L6CheckKSpec.KC.M23.boxes ++ (L6CheckKSpec.KC.M24.boxes ++ (L6CheckKSpec.KC.M25.boxes ++ (L6CheckKSpec.KC.M26.boxes ++ (L6CheckKSpec.KC.M27.boxes ++ (L6CheckKSpec.KC.M28.boxes ++ (L6CheckKSpec.KC.M29.boxes ++ (L6CheckKSpec.KC.M30.boxes ++ (L6CheckKSpec.KC.M31.boxes ++ (L6CheckKSpec.KC.M32.boxes ++ (L6CheckKSpec.KC.M33.boxes ++ (L6CheckKSpec.KC.M34.boxes ++ (L6CheckKSpec.KC.M35.boxes ++ (L6CheckKSpec.KC.M36.boxes ++ (L6CheckKSpec.KC.M37.boxes ++ (L6CheckKSpec.KC.M38.boxes ++ (L6CheckKSpec.KC.M39.boxes ++ (L6CheckKSpec.KC.M40.boxes ++ (L6CheckKSpec.KC.M41.boxes ++ (L6CheckKSpec.KC.M42.boxes ++ (L6CheckKSpec.KC.M43.boxes ++ (L6CheckKSpec.KC.M44.boxes ++ (L6CheckKSpec.KC.M45.boxes ++ (L6CheckKSpec.KC.M46.boxes ++ (L6CheckKSpec.KC.M47.boxes ++ (L6CheckKSpec.KC.M48.boxes ++ (L6CheckKSpec.KC.M49.boxes ++ (L6CheckKSpec.KC.M50.boxes ++ (L6CheckKSpec.KC.M51.boxes ++ (L6CheckKSpec.KC.M52.boxes ++ (L6CheckKSpec.KC.M53.boxes ++ (L6CheckKSpec.KC.M54.boxes ++ (L6CheckKSpec.KC.M55.boxes ++ (L6CheckKSpec.KC.M56.boxes ++ (L6CheckKSpec.KC.M57.boxes ++ (L6CheckKSpec.KC.M58.boxes ++ (L6CheckKSpec.KC.M59.boxes ++ (L6CheckKSpec.KC.M60.boxes ++ (L6CheckKSpec.KC.M61.boxes ++ (L6CheckKSpec.KC.M62.boxes ++ (L6CheckKSpec.KC.M63.boxes ++ (L6CheckKSpec.KC.M64.boxes ++ (L6CheckKSpec.KC.M65.boxes ++ (L6CheckKSpec.KC.M66.boxes ++ (L6CheckKSpec.KC.M67.boxes ++ (L6CheckKSpec.KC.M68.boxes ++ (L6CheckKSpec.KC.M69.boxes ++ (L6CheckKSpec.KC.M70.boxes ++ (L6CheckKSpec.KC.M71.boxes ++ (L6CheckKSpec.KC.M72.boxes ++ (L6CheckKSpec.KC.M73.boxes ++ (L6CheckKSpec.KC.M74.boxes)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) from rfl]
  rw [kcCountsB_append, L6CheckKSpec.KC.Cnt0.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt1.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt2.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt3.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt4.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt5.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt6.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt7.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt8.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt9.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt10.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt11.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt12.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt13.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt14.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt15.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt16.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt17.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt18.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt19.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt20.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt21.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt22.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt23.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt24.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt25.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt26.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt27.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt28.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt29.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt30.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt31.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt32.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt33.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt34.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt35.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt36.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt37.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt38.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt39.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt40.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt41.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt42.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt43.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt44.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt45.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt46.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt47.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt48.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt49.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt50.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt51.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt52.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt53.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt54.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt55.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt56.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt57.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt58.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt59.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt60.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt61.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt62.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt63.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt64.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt65.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt66.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt67.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt68.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt69.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt70.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt71.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt72.cnt, kcCountsB_append, L6CheckKSpec.KC.Cnt73.cnt, L6CheckKSpec.KC.Cnt74.cnt]
  rfl

end L6CheckKSpec.KC
