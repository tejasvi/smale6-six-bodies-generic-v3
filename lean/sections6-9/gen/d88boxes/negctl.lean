import Lean6.Special.Comp.D88.Boxes.N4.D000
import Lean6.Special.Comp.D88.Boxes.KC.D000

/-! Negative controls of the box checkers on the first chunk of each file
(run: `lake env lean gen/d88boxes/negctl.lean`; expected output 64, 0, 0, 64, 0, 0). -/

open Lean6.Special.D88.Boxes

/-- Prefix the real part of the first center with the digit `1` (a change far larger than the radius). -/
def perturb (s : String) : String :=
  match s.splitOn "|" with
  | r :: c0 :: rest => String.intercalate "|" (r :: ("1" ++ c0) :: rest)
  | _ => s

/-- Replace the radius by `1e-90` (smaller than the residual at the center). -/
def tinyR (s : String) : String :=
  match s.splitOn "|" with
  | _ :: rest => String.intercalate "|" ("1e-90" :: rest)
  | _ => s

#eval (N4.D000.data.map n4BoxOK).count true
#eval (N4.D000.data.map fun s => n4BoxOK (perturb s)).count true
#eval (N4.D000.data.map fun s => n4BoxOK (tinyR s)).count true
#eval (KC.D000.data.map kcBoxOK).count true
#eval (KC.D000.data.map fun s => kcBoxOK (perturb s)).count true
#eval (KC.D000.data.map fun s => kcBoxOK (tinyR s)).count true
