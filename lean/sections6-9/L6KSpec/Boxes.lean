import Lean6.Special.Comp.D88.Boxes.Check

/-!
# The boxes of Lemma 6.19(c), (d) for the kernel

For `decide +kernel`. The decimal box strings of version 1 do not reduce in the kernel; here a box is a value of
`Box` (radius `rho / 2^P`, centres at scale `2^P`, exactly what `parseBox` returns), decoded from a packed literal:
`1 + 2n` records of `W` bits per box (the radius, then the real and imaginary parts of the `n` centres, each integer
by its zigzag code). The tests of a box are those of `n4BoxOK` and `kcBoxOK` after parsing. Disjointness is checked by
a sweep over the boxes sorted by the real part of their first centre (`sweepOK`): a box is compared with the
following boxes whose key is within its radius plus the largest radius; beyond them, the first coordinate separates.
-/

namespace L6KSpec

open Lean6.Special.D88.Boxes

noncomputable section

/-- Records of `RB` bits, `c` of them, low record first, put in front of `acc`. Binary splitting keeps the
copies of big numbers small. The first argument is fuel for the depth. -/
def decode (RB : Nat) : Nat → Nat → Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat → List Nat)
    (fun c n acc =>
      Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ acc => acc)
        (fun _ ih n acc => (n % 2 ^ RB) :: ih (n / 2 ^ RB) acc) c n acc)
    (fun _ ih c n acc =>
      let h := c / 2
      Bool.rec
        (ih h (n % 2 ^ (h * RB)) (ih (c - h) (n / 2 ^ (h * RB)) acc))
        (Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ acc => acc)
          (fun _ ih n acc => (n % 2 ^ RB) :: ih (n / 2 ^ RB) acc) c n acc)
        (Nat.ble c 8))

end

/-- The integer of a zigzag code: `2c ↦ c`, `2c + 1 ↦ -(c + 1)`. -/
def unzz (z : Nat) : Int := Nat.rec (motive := fun _ => Int) (Int.ofNat (z / 2)) (fun _ _ => Int.negSucc (z / 2)) (z % 2)

/-- The pairs of a list of records (real, imaginary), as integers. -/
def pairsOf : List Nat → List (Int × Int)
  | a :: b :: rest => (unzz a, unzz b) :: pairsOf rest
  | _ => []

/-- Boxes of `1 + 2n` records each. -/
def boxesOfRecs (n : Nat) : Nat → List Nat → List Box
  | 0, _ => []
  | k + 1, l => ⟨l.headD 0, pairsOf ((l.drop 1).take (2 * n))⟩ :: boxesOfRecs n k (l.drop (1 + 2 * n))

/-- **The boxes of a literal**: `cnt` boxes with `n` centres, records of `W` bits packed in `x`. -/
noncomputable def boxesOf (W n cnt x : Nat) : List Box := boxesOfRecs n cnt (decode W 40 (cnt * (1 + 2 * n)) x [])

/-- The tests of a box of Lemma 6.19(c) (those of `n4BoxOK` after parsing). -/
def n4BoxOKB (b : Box) : Bool := n4RadiusOK b && krawBox s11T b && n4Extra b

/-- The tests of a box of Lemma 6.19(d) (those of `kcBoxOK` after parsing). -/
def kcBoxOKB (b : Box) : Bool := kcRadiusOK b && krawBox kc12T b && kcExtra b

/-- The key of a box: the real part of its first centre. -/
def boxKey (b : Box) : Int := (b.c 0).1

/-- The boxes after `b` whose key exceeds that of `b` by at most `b.rho + R` are separated from `b`. -/
def sweepFrom (R : Nat) (b : Box) : List Box → Bool
  | [] => true
  | b' :: rest => decide (boxKey b' - boxKey b > (b.rho + R : Nat)) || (sepBoxes b b' && sweepFrom R b rest)

/-- **The sweep**: the keys increase (weakly), every radius is at most `R`, and each box is separated from the
following boxes within reach. -/
def sweepOK (R : Nat) : List Box → Bool
  | [] => true
  | b :: rest => decide (b.rho ≤ R) && (rest.head?.all fun b' => decide (boxKey b ≤ boxKey b')) &&
      sweepFrom R b rest && sweepOK R rest

end L6KSpec
