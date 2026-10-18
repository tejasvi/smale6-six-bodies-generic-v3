/-!
# Dense univariate integer polynomials and the polynomials of Sec. 6.4 (no Mathlib)

`UP` is the list of coefficients of `t⁰, t¹, …` of a polynomial in `ℤ[t]`. The operations are the schoolbook ones;
`Lean6.Special.D98.UPolySem` proves that they are the operations of `ℤ[X]` (`toPoly`). This module also builds, from
integer masses `μ = (m₁, m₂, m₃)`, the polynomial `S_μ` of Sec. 6.4 (`SUP`) and the polynomial `Φ₃(t; μ)` of
Sec. 6.6 (`Phi3UP`), and states the checkers of the certificates of Lemma 6.9 (`sqfOK`) and Theorem 6.15
(`bezOK`).
-/

namespace Lean6.Special.Comp.D98

/-- A dense polynomial in `ℤ[t]`: the coefficients of `t⁰, t¹, …`. -/
abbrev UP := List Int

namespace UP

/-- Sum. -/
def add : UP → UP → UP
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

/-- Negation. -/
def neg (p : UP) : UP := p.map (- ·)

/-- Difference. -/
def sub (p q : UP) : UP := add p (neg q)

/-- `c · p`. -/
def scale (c : Int) (p : UP) : UP := p.map (c * ·)

/-- Product (no trailing zeros are created when a factor is empty). -/
def mul : UP → UP → UP
  | [], _ => []
  | _ :: _, [] => []
  | a :: p, b :: q => add (scale a (b :: q)) (0 :: mul p (b :: q))

/-- Power. -/
def pow (p : UP) : Nat → UP
  | 0 => [1]
  | n + 1 => mul (pow p n) p

/-- The formal derivative. -/
def deriv : UP → UP
  | [] => []
  | _ :: p => add p (0 :: deriv p)

/-- Composition `p(q)` (Horner). -/
def comp (p q : UP) : UP := p.foldr (fun a acc => add [a] (mul q acc)) []

/-- All coefficients are zero. -/
def isZero (p : UP) : Bool := p.all (· == 0)

/-- The identity test. -/
def eqv (p q : UP) : Bool := isZero (sub p q)

/-- `p` has degree exactly `d` and leading coefficient `lc ≠ 0`: `d + 1` coefficients, the last one `lc`. -/
def degLead (p : UP) (d : Nat) (lc : Int) : Bool := p.length == d + 1 && p.getLast? == some lc && lc != 0

end UP

open UP

/-! ## The polynomials of Sec. 6.4 -/

/-- `t² − t + 1`. -/
def lagUP : UP := [1, -1, 1]
/-- `N₀₁ = t⁴ − 5t³ + 9t² − 5t + 1`. -/
def N01UP : UP := [1, -5, 9, -5, 1]
/-- `N₁₀ = t⁴ + t³ − 2t + 1`. -/
def N10UP : UP := [1, -2, 0, 1, 1]
/-- `N₁₁ = t⁴ − 2t³ + t + 1`. -/
def N11UP : UP := [1, 1, 0, -2, 1]

/-- The quintic `Q_σ(x)` for the masses `(m₁, m₂, m₃)` and the signs `(a, b, c) = (σ₁₂, σ₁₃, σ₂₃)`, expanded:
`(m₁+m₂)a x³(1+x)² + m₁a x²(1+x)² + m₃b x³ − m₁b x² − m₃c x(1+x)² − (m₂+m₃)c (1+x)²`. -/
def QUP (m1 m2 m3 a b c : Int) : UP :=
  [-(m2 + m3) * c, -(2 * m2 + 3 * m3) * c, m1 * (a - b) - (m2 + 3 * m3) * c, (3 * m1 + m2) * a + m3 * (b - c),
    (3 * m1 + 2 * m2) * a, (m1 + m2) * a]

/-- `t − 1`. -/
def tm1UP : UP := [-1, 1]

/-- `S_μ(t) = (t² − t + 1) N₀₁ N₁₀ N₁₁ ∏_σ Q_σ(t − 1)` over the four classes
`σ ∈ {(1,1,1), (1,1,−1), (1,−1,−1), (1,−1,1)}`. -/
def SUP (m1 m2 m3 : Int) : UP :=
  mul (mul (mul (mul lagUP N01UP) N10UP) N11UP)
    (mul (mul (mul (comp (QUP m1 m2 m3 1 1 1) tm1UP) (comp (QUP m1 m2 m3 1 1 (-1)) tm1UP))
      (comp (QUP m1 m2 m3 1 (-1) (-1)) tm1UP)) (comp (QUP m1 m2 m3 1 (-1) 1) tm1UP))

/-- `Φ₃(t; μ) = Y₁² + Y₂² + Y₃² − 2(Y₁Y₂ + Y₂Y₃ + Y₃Y₁)` with `Y_l = μ_l² Λ_l(t)`, `Λ₁ = ℓ₂ℓ₃`, `Λ₂ = ℓ₁ℓ₃`,
`Λ₃ = ℓ₁ℓ₂`, `ℓ₁ = μ₂ + μ₃t`, `ℓ₂ = ℓ₁ − M`, `ℓ₃ = ℓ₁ − Mt`, `M = μ₁ + μ₂ + μ₃`. -/
def Phi3UP (m1 m2 m3 : Int) : UP :=
  let M := m1 + m2 + m3
  let l1 : UP := [m2, m3]
  let l2 : UP := [m2 - M, m3]
  let l3 : UP := [m2, m3 - M]
  let Y1 := scale (m1 * m1) (mul l2 l3)
  let Y2 := scale (m2 * m2) (mul l1 l3)
  let Y3 := scale (m3 * m3) (mul l1 l2)
  sub (add (add (mul Y1 Y1) (mul Y2 Y2)) (mul Y3 Y3))
    (scale 2 (add (add (mul Y1 Y2) (mul Y2 Y3)) (mul Y3 Y1)))

/-! ## Checkers -/

/-- A certificate that `g` and `S` have the square-free part `g₀`: `a₁ g = g₀ q₁`, `a₂ g₀^kg = g q₂`,
`a₃ S = g₀ q₃`, `a₄ g₀^ks = S q₄` with nonzero integers `aᵢ`, and `u g₀ + v g₀' = c ≠ 0`. -/
structure SqfCert where
  kg : Nat
  ks : Nat
  a1 : Int
  q1 : UP
  a2 : Int
  q2 : UP
  a3 : Int
  q3 : UP
  a4 : Int
  q4 : UP
  u : UP
  v : UP
  c : Int

/-- The checker of a `SqfCert`. -/
def sqfOK (S g g0 : UP) (C : SqfCert) : Bool :=
  C.a1 != 0 && C.a2 != 0 && C.a3 != 0 && C.a4 != 0 && C.c != 0 &&
    eqv (scale C.a1 g) (mul g0 C.q1) && eqv (scale C.a2 (pow g0 C.kg)) (mul g C.q2) &&
    eqv (scale C.a3 S) (mul g0 C.q3) && eqv (scale C.a4 (pow g0 C.ks)) (mul S C.q4) &&
    eqv (add (mul C.u g0) (mul C.v (deriv g0))) [C.c]

/-- The checker of a Bezout identity `U f + V g = c` with `c ≠ 0`. -/
def bezOK (f g U V : UP) (c : Int) : Bool :=
  c != 0 && eqv (add (mul U f) (mul V g)) [c]

end Lean6.Special.Comp.D98
