import L6K.F2S.Keep
import L6Sound.Common.Farkas

/-!
# The decisions from data are sound

`keepK_sound`: a program discarded by `keepK T` has no solution of its strict form. This is `KeepSound (keepK T)` of
`L6Sound.F2S.Complete`, proved as `keepLP_sound` is (Lemma 4.6, `Farkas.check_sound_strict_all`).
-/

namespace L6K.F2S

open L6

theorem keepK_sound (T : CTree) :
    ∀ rows nv, keepK T rows nv = false → ∀ h : ℕ → ℚ, ¬ ∀ r ∈ rows, r.StrictHolds nv h := by
  intro rows nv hk h hrows
  unfold keepK at hk
  obtain ⟨cert, -, hc⟩ := List.any_eq_true.mp (by simpa using hk)
  exact Farkas.check_sound_strict_all hc h hrows

end L6K.F2S
