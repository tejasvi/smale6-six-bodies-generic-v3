import Lean6.Special.Comp.D98.UPoly

/-!
# Root disks of `S_μ` and bounds of `ρ` on them (no Mathlib)

Exact rational arithmetic on Gaussian rationals `(x, y) = x + y i`. For a factor `f ∈ ℤ[t]` of `S_μ` of degree `d`
and a list of `d` disks `D(c, r)`, `r = 2^-m`, `facOK` checks: `|f(c)|² < lc(f)² r^{2d}` for every centre (so each
disk contains a root of `f`), the centres are more than `2r` apart (so the disks are disjoint and contain all the
roots), and on each disk `diskOK`: bounds `λ_k ≤ |ℓ_k(c)| ≤ υ_k` (`ℓ₁ = μ₂ + μ₃t`, `ℓ₂ = ℓ₁ − M`, `ℓ₃ = ℓ₁ − Mt`),
`L_k = λ_k − |∂ℓ_k| r > 0`, `U_k = υ_k + |∂ℓ_k| r`, rational `x₁, x₂ ≥ 0` with `x₁² μ₃² L₁ ≥ μ₁² U₃`,
`x₂² μ₃² L₂ ≥ μ₂² U₃` (so `A₁ ≤ x₁ A₃`, `A₂ ≤ x₂ A₃` on the disk) and `θ (1 + x₁ + x₂) ≤ 1` (so `ρ ≥ θ`).
-/

namespace Lean6.Special.Comp.D98

open UP

/-- Gaussian rationals. -/
abbrev GQ := Rat × Rat

def gmul (x y : GQ) : GQ := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

def gnorm2 (x : GQ) : Rat := x.1 * x.1 + x.2 * x.2

/-- `f(c)` by Horner (constant term first). -/
def hornerQ : UP → GQ → GQ
  | [], _ => (0, 0)
  | a :: rest, c =>
    let v := gmul c (hornerQ rest c)
    ((a : Rat) + v.1, v.2)

/-- The scale `2^256` of the centres and of the bounds. -/
def KS : Rat := (2 : Rat) ^ 256

/-- One disk: the centre `(a + b i)/2^256`; `λ_k = l_k/2^256`, `υ_k = u_k/2^256`; `x_k = X_k/2^256`. -/
structure Disk where
  a : Int
  b : Int
  l1 : Nat
  l2 : Nat
  l3 : Nat
  u1 : Nat
  u2 : Nat
  u3 : Nat
  x1 : Nat
  x2 : Nat

/-- The disks of one factor, with the radius `2^-m`. -/
structure FacDisks where
  m : Nat
  disks : List Disk

def Disk.c (D : Disk) : GQ := ((D.a : Rat) / KS, (D.b : Rat) / KS)

/-- `ℓ_k(c)` for `ℓ_k = p + q t`. -/
def ellAt (p q : Int) (c : GQ) : GQ := ((p : Rat) + (q : Rat) * c.1, (q : Rat) * c.2)

/-- The bounds of one `ℓ_k = p + q t` on the disk: `λ² ≤ |ℓ(c)|² ≤ υ²` and `L = λ − |q| r > 0`. -/
def ellOK (p q : Int) (c : GQ) (r : Rat) (l u : Nat) : Bool :=
  let n2 := gnorm2 (ellAt p q c)
  let lam : Rat := (l : Rat) / KS
  let ups : Rat := (u : Rat) / KS
  decide (lam * lam ≤ n2) && decide (n2 ≤ ups * ups) && decide (0 < lam - (q.natAbs : Rat) * r)

/-- The checks on one disk for the masses `(m₁, m₂, m₃)` and the bound `θ`. -/
def diskOK (m1 m2 m3 : Int) (θ : Rat) (r : Rat) (D : Disk) : Bool :=
  let M := m1 + m2 + m3
  let c := D.c
  let L1 : Rat := (D.l1 : Rat) / KS - (m3.natAbs : Rat) * r
  let L2 : Rat := (D.l2 : Rat) / KS - (m3.natAbs : Rat) * r
  let U3 : Rat := (D.u3 : Rat) / KS + ((m3 - M).natAbs : Rat) * r
  let x1 : Rat := (D.x1 : Rat) / KS
  let x2 : Rat := (D.x2 : Rat) / KS
  ellOK m2 m3 c r D.l1 D.u1 && ellOK (m2 - M) m3 c r D.l2 D.u2 && ellOK m2 (m3 - M) c r D.l3 D.u3 &&
    decide ((m1 : Rat) * m1 * U3 ≤ x1 * x1 * ((m3 : Rat) * m3) * L1) &&
    decide ((m2 : Rat) * m2 * U3 ≤ x2 * x2 * ((m3 : Rat) * m3) * L2) &&
    decide (θ * (1 + x1 + x2) ≤ 1)

/-- `p` holds for every pair `(x, y)` with `x` before `y`. -/
def pairwiseB {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => xs.all (p x) && pairwiseB p xs

/-- The checks for one factor `f` of degree `d ≥ 1`. -/
def facOK (m1 m2 m3 : Int) (θ : Rat) (f : UP) (F : FacDisks) : Bool :=
  let d := f.length - 1
  let lc := f.getLast?.getD 0
  let r : Rat := 1 / (2 : Rat) ^ F.m
  decide (lc ≠ 0) && decide (1 ≤ d) && F.disks.length == d &&
    F.disks.all (fun D => decide (gnorm2 (hornerQ f D.c) < (lc : Rat) * lc * r ^ (2 * d))) &&
    pairwiseB (fun D E => decide (4 * r * r < gnorm2 (D.c.1 - E.c.1, D.c.2 - E.c.2))) F.disks &&
    F.disks.all (diskOK m1 m2 m3 θ r)

/-- The eight factors of `S_μ`, in the order of `SUP`. -/
def factorsUP (m1 m2 m3 : Int) : List UP :=
  [lagUP, N01UP, N10UP, N11UP, comp (QUP m1 m2 m3 1 1 1) tm1UP, comp (QUP m1 m2 m3 1 1 (-1)) tm1UP,
    comp (QUP m1 m2 m3 1 (-1) (-1)) tm1UP, comp (QUP m1 m2 m3 1 (-1) 1) tm1UP]

/-- All factors. -/
def rootsOK (m1 m2 m3 : Int) (θ : Rat) (Fs : List FacDisks) : Bool :=
  Fs.length == 8 && ((factorsUP m1 m2 m3).zip Fs).all fun fF => facOK m1 m2 m3 θ fF.1 fF.2

/-- An upper bound of `ρ` on one disk: rational `y₁, y₂ ≥ 0` with `y₁² μ₃² U₁ ≤ μ₁² L₃`, `y₂² μ₃² U₂ ≤ μ₂² L₃`
(so `A₁ ≥ y₁ A₃`, `A₂ ≥ y₂ A₃`) and `1 ≤ θ' (1 + y₁ + y₂)` (so `ρ ≤ θ'`). -/
def upperOK (m1 m2 m3 : Int) (θ' : Rat) (r : Rat) (D : Disk) (Y1 Y2 : Nat) : Bool :=
  let M := m1 + m2 + m3
  let U1 : Rat := (D.u1 : Rat) / KS + (m3.natAbs : Rat) * r
  let U2 : Rat := (D.u2 : Rat) / KS + (m3.natAbs : Rat) * r
  let L3 : Rat := (D.l3 : Rat) / KS - ((m3 - M).natAbs : Rat) * r
  let y1 : Rat := (Y1 : Rat) / KS
  let y2 : Rat := (Y2 : Rat) / KS
  decide (y1 * y1 * ((m3 : Rat) * m3) * U1 ≤ (m1 : Rat) * m1 * L3) &&
    decide (y2 * y2 * ((m3 : Rat) * m3) * U2 ≤ (m2 : Rat) * m2 * L3) && decide (1 ≤ θ' * (1 + y1 + y2))

end Lean6.Special.Comp.D98
