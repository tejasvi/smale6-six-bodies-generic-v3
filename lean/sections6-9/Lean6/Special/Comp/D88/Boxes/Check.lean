import Lean6.Special.Comp.Ball.KrawCheck
import Lean6.Special.Comp.D88.Boxes.Sys

/-!
# The checkers of Lemma 6.19(c), (d) and of the last paragraph of Sec. 6.7 (no Mathlib)

A box is given by a string `"r|re,im|re,im|…"`: the radius field `r` and the midpoint `mid` of a line of the certificate
files of diagrams 88 and 94, verbatim. `parseBox` turns it into a radius `rho` and integer centers at scale `2^P`
(`P = 256`): `rho = ⌈r 2^P⌉` and each center the nearest integer to `2^P` times the decimal. The checked set is the
polydisc of the complex radius `rho/2^P` around the centers.

* `krawBox`: the Krawczyk test `krawOK` of the five-body development on the system and the polydisc.
* Moduli (`modBounds`): for a disc with integer center `(a, b)` and radius `R` at scale `T`, bounds `L ≤ T‖z‖ ≤ U`
  from `m = ⌊√(a² + b²)⌋` (checked: `m² ≤ a² + b² < (m+1)²`).
* Inverse square roots (`invSqrtBounds`): `λ/2^Q ≤ ‖z‖^{-1/2} ≤ υ/2^Q` from `λ² U ≤ 4^Q T ≤ υ² L` (checked).
* `n4Extra` (Lemma 6.19(c)): `X₃ − X₄ ≠ 0` on the polydisc and the T-test with margin `0.1756`.
* `kcExtra` (Lemma 6.19(d)): `X₃ ≠ 0` and the 32 sums, in exact rational arithmetic: square roots of the discs of
  `X₂`, `X₃` by `sqrtCover` (`w² ∈ D(c, r)` gives `±w ∈ D(s₀, δ/‖s₀‖)`), reciprocals, and discs of the sums.
* `kcClass`: the decisions of Sec. 6.7 (the T-test over the bodies 1, 2, 3; the relative margin `10⁻⁴`; the bounds
  on `Y₄` and `Y_l/Y₄` where the margin is below `10⁻⁴`).

Floating point is not used. Every square root comes with its checked square inequalities, so the soundness proofs
(`D88/Boxes/*.lean`) do not depend on how `isqrt` computes.
-/

namespace Lean6.Special.D88.Boxes

open Lean6.Special.Ball Lean6.Special.Kraw

/-- The fixed-point precision of the balls. -/
def P : Nat := 256

/-- The resolution `2^-Q` of the square-root bounds. -/
def Q : Nat := 128

/-! ## Parsing -/

/-- The value of a decimal digit. -/
def digitVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat) else none

/-- The value of a list of decimal digits, after the accumulator `acc`. -/
def parseDigits : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc =>
    match digitVal c with
    | some d => parseDigits cs (10 * acc + d)
    | none => none

/-- An integer `[-+]d…d`. -/
def parseIntC : List Char → Option Int
  | '-' :: r => (parseDigits r 0).map fun n => -(n : Int)
  | '+' :: r => (parseDigits r 0).map fun n => (n : Int)
  | r => (parseDigits r 0).map fun n => (n : Int)

/-- A decimal `[-]d…d[.d…d][e[-+]d…d]` as `(negative, N, E)`: the value `±N·10^E`. -/
def parseDec (s : String) : Option (Bool × Nat × Int) :=
  let cs := s.toList
  let ncs : Bool × List Char := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  let ms := ncs.2.span (fun c => c != 'e' && c != 'E')
  let ipf := ms.1.span (· != '.')
  let fp := ipf.2.drop 1
  let ex : Option Int := match ms.2 with
    | [] => some 0
    | _ :: e => parseIntC e
  match parseDigits (ipf.1 ++ fp) 0, ex with
  | some n, some e => some (ncs.1, n, e - (fp.length : Int))
  | _, _ => none

/-- The integer nearest to `±N·10^E·2^P` (ties away from zero). -/
def toFix (d : Bool × Nat × Int) : Int :=
  let v : Nat :=
    if 0 ≤ d.2.2 then d.2.1 * 10 ^ d.2.2.toNat * 2 ^ P
    else (2 * d.2.1 * 2 ^ P + 10 ^ (-d.2.2).toNat) / (2 * 10 ^ (-d.2.2).toNat)
  if d.1 then -(v : Int) else (v : Int)

/-- `⌈N·10^E·2^P⌉` (the sign is ignored). -/
def toFixCeil (d : Bool × Nat × Int) : Nat :=
  if 0 ≤ d.2.2 then d.2.1 * 10 ^ d.2.2.toNat * 2 ^ P
  else (d.2.1 * 2 ^ P + 10 ^ (-d.2.2).toNat - 1) / 10 ^ (-d.2.2).toNat

/-- A box: the radius `rho/2^P` and the centers (integer pairs at scale `2^P`). -/
structure Box where
  rho : Nat
  cs : List (Int × Int)
deriving Repr

/-- One coordinate `"re,im"`. -/
def parseCoord (s : String) : Option (Int × Int) :=
  match s.splitOn "," with
  | [a, b] =>
    match parseDec a, parseDec b with
    | some x, some y => some (toFix x, toFix y)
    | _, _ => none
  | _ => none

/-- A box string `"r|re,im|re,im|…"`. -/
def parseBox (s : String) : Option Box :=
  match s.splitOn "|" with
  | rs :: coords =>
    match parseDec rs, coords.mapM parseCoord with
    | some r, some cs => some ⟨toFixCeil r, cs⟩
    | _, _ => none
  | [] => none

/-- The `j`-th center (`(0, 0)` beyond the list). -/
def Box.c (b : Box) (j : Nat) : Int × Int := b.cs.getD j (0, 0)

/-! ## Balls of the centers and the Krawczyk test -/

/-- The biased natural of an integer (truncated at `0`). -/
def biased (x : Int) : Nat := (x + (bias P : Int)).toNat

/-- The exact ball of a center. -/
def mkCenter (x : Int × Int) : CB :=
  ⟨biased x.1, biased x.2, 0, x.1.natAbs + x.2.natAbs, x.1.natAbs + x.2.natAbs⟩

/-- The centers are small enough to be represented exactly. -/
def centersSmall (b : Box) : Bool := b.cs.all fun x => x.1.natAbs < bias P && x.2.natAbs < bias P

/-- The coefficient table `[1]`. -/
def tab1 : List CB := [one P]

/-- The Krawczyk test of the system `F` on the polydisc of the box. -/
def krawBox (F : List TPoly) (b : Box) : Bool :=
  centersSmall b && krawOK P tab1 F (b.cs.map mkCenter) b.rho

/-! ## Integer discs: moduli and inverse square roots -/

/-- `⌊√n⌋` by Newton's method from above, with fuel (only a proposal: every use checks its square inequalities). -/
def isqrtAux : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | fuel + 1, n, x =>
    let y := (x + n / x) / 2
    if y < x then isqrtAux fuel n y else x

/-- `⌊√n⌋` (a proposal). -/
def isqrt (n : Nat) : Nat := if n = 0 then 0 else isqrtAux (2 * Nat.log2 n + 8) n (2 ^ (Nat.log2 n / 2 + 1))

/-- A complex disc `{z : ‖z − (a + b i)/T‖ ≤ R/T}`. -/
structure IDisc where
  a : Int
  b : Int
  R : Nat
  T : Nat
deriving Repr

/-- Bounds `(L, U)` with `L ≤ T‖z‖ ≤ U` on the disc, if the square-root check passes. -/
def modBounds (d : IDisc) : Option (Nat × Nat) :=
  let n := d.a.natAbs * d.a.natAbs + d.b.natAbs * d.b.natAbs
  let m := isqrt n
  if m * m ≤ n && n < (m + 1) * (m + 1) then some (m - d.R, m + 1 + d.R) else none

/-- Bounds `(λ, υ)` with `λ/2^Q ≤ ‖z‖^{-1/2} ≤ υ/2^Q` from `L ≤ T‖z‖ ≤ U` (checked; `L > 0`). -/
def invSqrtBounds (L U T : Nat) : Option (Nat × Nat) :=
  let K := 4 ^ Q * T
  let lam := isqrt (K / U)
  let ups := isqrt (K / L) + 1
  if 0 < L && 0 < U && lam * lam * U ≤ K && K ≤ ups * ups * L then some (lam, ups) else none

/-- The inverse square-root bounds of a disc. -/
def discInvSqrt (d : IDisc) : Option (Nat × Nat) :=
  match modBounds d with
  | some (L, U) => invSqrtBounds L U d.T
  | none => none

/-- The disc excludes `0`: one of `|a|`, `|b|` exceeds `R`. -/
def discNonzero (d : IDisc) : Bool := d.R < d.a.natAbs || d.R < d.b.natAbs

/-- `2^P`. -/
def S : Nat := 2 ^ P

/-! ## Lemma 6.19(c): the polydisc of S11 -/

/-- The disc of `X₁ = v₀ + 1` (S11). -/
def n4D1 (b : Box) : IDisc := ⟨(b.c 0).1 + S, (b.c 0).2, b.rho, S⟩
/-- The disc of `X₂ = v₀`. -/
def n4D2 (b : Box) : IDisc := ⟨(b.c 0).1, (b.c 0).2, b.rho, S⟩
/-- The disc of `X₃ = v₁`. -/
def n4D3 (b : Box) : IDisc := ⟨(b.c 1).1, (b.c 1).2, b.rho, S⟩
/-- The disc of `X₄ = −(3v₀ + 3v₁ + 1)/30` (scale `30·2^P`). -/
def n4D4 (b : Box) : IDisc := ⟨-(3 * (b.c 0).1 + 3 * (b.c 1).1 + S), -(3 * (b.c 0).2 + 3 * (b.c 1).2), 6 * b.rho, 30 * S⟩
/-- The disc of `X₃ − X₄ = (3v₀ + 33v₁ + 1)/30`. -/
def n4X34Disc (b : Box) : IDisc :=
  ⟨3 * (b.c 0).1 + 33 * (b.c 1).1 + S, 3 * (b.c 0).2 + 33 * (b.c 1).2, 36 * b.rho, 30 * S⟩

/-- The T-test with margin `0.1756` and masses `(1, 2, 3, 30)` at some body:
`8244 m_k λ_k ≥ 11756 Σ_{l≠k} m_l υ_l`. -/
def tTestN4 (l1 u1 l2 u2 l3 u3 l4 u4 : Nat) : Bool :=
  11756 * (2 * u2 + 3 * u3 + 30 * u4) ≤ 8244 * l1 ||
  11756 * (u1 + 3 * u3 + 30 * u4) ≤ 8244 * (2 * l2) ||
  11756 * (u1 + 2 * u2 + 30 * u4) ≤ 8244 * (3 * l3) ||
  11756 * (u1 + 2 * u2 + 3 * u3) ≤ 8244 * (30 * l4)

/-- The extra tests of a box of Lemma 6.19(c). -/
def n4Extra (b : Box) : Bool :=
  b.cs.length == 11 && discNonzero (n4X34Disc b) &&
    match discInvSqrt (n4D1 b), discInvSqrt (n4D2 b), discInvSqrt (n4D3 b), discInvSqrt (n4D4 b) with
    | some (l1, u1), some (l2, u2), some (l3, u3), some (l4, u4) => tTestN4 l1 u1 l2 u2 l3 u3 l4 u4
    | _, _, _, _ => false

/-- The radius is positive and below `6·10^-47`. -/
def n4RadiusOK (b : Box) : Bool := 0 < b.rho && b.rho * 10 ^ 47 < 6 * S

/-- **A box of Lemma 6.19(c).** -/
def n4BoxOK (s : String) : Bool :=
  match parseBox s with
  | some b => n4RadiusOK b && krawBox s11T b && n4Extra b
  | none => false

/-- All boxes of a chunk. -/
def n4ChunkOK (l : List String) : Bool := l.all n4BoxOK

/-! ## Exact complex rationals -/

/-- A complex rational `(re, im)`. -/
abbrev CQ := Rat × Rat

/-- Sum. -/
def cadd (z w : CQ) : CQ := (z.1 + w.1, z.2 + w.2)
/-- Product. -/
def cmul (z w : CQ) : CQ := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)
/-- Real multiple. -/
def csmul (c : Rat) (z : CQ) : CQ := (c * z.1, c * z.2)
/-- `‖z‖²`. -/
def cnormSq (z : CQ) : Rat := z.1 * z.1 + z.2 * z.2
/-- Absolute value of a rational. -/
def qabs (x : Rat) : Rat := if x < 0 then -x else x
/-- An upper bound of the modulus: `|re| + |im|`. -/
def cabsUp (z : CQ) : Rat := qabs z.1 + qabs z.2

/-- A rational lower bound of `√x` (a proposal; its uses check `lo² ≤ x`). -/
def sqrtLo (x : Rat) : Rat :=
  if x ≤ 0 then 0 else ((isqrt (x * (4 ^ Q : Nat)).floor.toNat : Nat) : Rat) / ((2 ^ Q : Nat) : Rat)

/-- A rational upper bound of `√x` (a proposal; its uses check `x ≤ hi²`). -/
def sqrtHi (x : Rat) : Rat :=
  if x ≤ 0 then 0 else ((isqrt (x * (4 ^ Q : Nat)).ceil.toNat + 1 : Nat) : Rat) / ((2 ^ Q : Nat) : Rat)

/-- A disc `{z : ‖z − c‖ ≤ r}` with a rational center and radius. -/
structure QDisc where
  c : CQ
  r : Rat
deriving Repr

/-- The disc of a sum. -/
def qadd (d e : QDisc) : QDisc := ⟨cadd d.c e.c, d.r + e.r⟩
/-- The disc of a product. -/
def qmul (d e : QDisc) : QDisc := ⟨cmul d.c e.c, cabsUp d.c * e.r + cabsUp e.c * d.r + d.r * e.r⟩
/-- The disc of a real multiple. -/
def qsmul (s : Rat) (d : QDisc) : QDisc := ⟨csmul s d.c, qabs s * d.r⟩

/-- An approximate square root `p + q i` of the Gaussian integer `a + b i` (a proposal). -/
def gsqrt (a b : Int) : Int × Int :=
  let M := isqrt (a.natAbs * a.natAbs + b.natAbs * b.natAbs)
  let p := isqrt ((M + a).toNat / 2)
  let q := isqrt ((M - a).toNat / 2)
  (p, if b < 0 then -(q : Int) else q)

/-- `2^(P/2)`. -/
def H : Nat := 2 ^ (P / 2)

/-- The disc of `μ/w` for the square roots `w` (up to sign) of the points of the disc `D((a + b i)/S, R/S)`:
with `s₀ = (p + q i)/H`, `δ = (|p² − q² − a| + |2pq − b| + R)/S ≥ ‖s₀² − X‖`, `L = max(|p|, |q|)/H ≤ ‖s₀‖` and
`e = δ/L`, the center `μ/s₀` and the radius `μ e/(L (L − e))` (`none` unless `T = S`, `L > 0`, `e < L`). -/
def betaDisc (mu : Nat) (d : IDisc) : Option QDisc :=
  let pq := gsqrt d.a d.b
  let p := pq.1
  let q := pq.2
  let s0 : CQ := ((p : Rat) / (H : Rat), (q : Rat) / (H : Rat))
  let dInt : Nat := (p * p - q * q - d.a).natAbs + (2 * p * q - d.b).natAbs
  let delta : Rat := ((dInt : Rat) + (d.R : Rat)) / (S : Rat)
  let L : Rat := ((max p.natAbs q.natAbs : Nat) : Rat) / (H : Rat)
  if d.T = S && 0 < L && delta / L < L then
    some ⟨((mu : Rat) * s0.1 / cnormSq s0, -((mu : Rat) * s0.2) / cnormSq s0),
      (mu : Rat) * (delta / L) / (L * (L - delta / L))⟩
  else none

/-- `ρ₀ = ⌊2√2·2^Q⌋/2^Q`, an approximation of `ρ = (m₆/m₅)^{3/2} = 2√2` at `(m₅, m₆) = (1, 2)`. -/
def rho0 : Rat := ((isqrt (8 * 4 ^ Q) : Nat) : Rat) / ((2 ^ Q : Nat) : Rat)

/-- `2^-Q`. -/
def eta : Rat := 1 / ((2 ^ Q : Nat) : Rat)

/-- `ρ₀ ≤ 2√2 ≤ ρ₀ + 2^-Q`: `ρ₀ ≥ 0`, `ρ₀² ≤ 8 ≤ (ρ₀ + 2^-Q)²`. -/
def rho0OK : Bool := 0 ≤ rho0 && rho0 * rho0 ≤ 8 && 8 ≤ (rho0 + eta) * (rho0 + eta)

/-- The disc of `1 + i s ρ`. -/
def factorDisc (s : Int) : QDisc := ⟨(1, (s : Rat) * rho0), eta⟩

/-- The disc of the sum `β₁(1 + i s₁ρ) + ε₂ β₂(1 + i s₂ρ) + ε₃ β₃(1 + i s₃ρ)`. -/
def sumDisc3 (B1 B2 B3 : QDisc) (e2 e3 s1 s2 s3 : Int) : QDisc :=
  qadd (qadd (qmul B1 (factorDisc s1)) (qsmul (e2 : Rat) (qmul B2 (factorDisc s2))))
    (qsmul (e3 : Rat) (qmul B3 (factorDisc s3)))

/-- The 32 sign patterns `(ε₂, ε₃, s₁, s₂, s₃)` (with `ε₁ = 1`). -/
def patterns : List (Int × Int × Int × Int × Int) :=
  [1, -1].flatMap fun e2 => [1, -1].flatMap fun e3 => [1, -1].flatMap fun s1 => [1, -1].flatMap fun s2 =>
    [1, -1].map fun s3 => (e2, e3, s1, s2, s3)

/-- The checked lower bound `lo ≤ ‖z‖` (`lo ≥ 0`, `lo² ≤ ‖z‖²`). -/
def normLo (z : CQ) : Option Rat :=
  let lo := sqrtLo (cnormSq z)
  if 0 ≤ lo && lo * lo ≤ cnormSq z then some lo else none

/-- The checked upper bound `‖z‖ ≤ hi` (`hi ≥ 0`, `‖z‖² ≤ hi²`). -/
def normHi (z : CQ) : Option Rat :=
  let hi := sqrtHi (cnormSq z)
  if 0 ≤ hi && cnormSq z ≤ hi * hi then some hi else none

/-- An upper bound of `‖β‖` on a disc: `hi(‖c‖) + r`. -/
def discUp (d : QDisc) : Option Rat := (normHi d.c).map (· + d.r)

/-- A lower bound of `‖β‖` on a disc: `lo(‖c‖) − r`. -/
def discLo (d : QDisc) : Option Rat := (normLo d.c).map (· - d.r)

/-- The discs of `X₂ = v₀` and `X₃ = v₁` (KC12; `X₁ = 1`). -/
def kcD2 (b : Box) : IDisc := ⟨(b.c 0).1, (b.c 0).2, b.rho, S⟩
/-- The disc of `X₃`. -/
def kcD3 (b : Box) : IDisc := ⟨(b.c 1).1, (b.c 1).2, b.rho, S⟩
/-- The disc of `X₁ = 1`. -/
def kcD1 : IDisc := ⟨S, 0, 0, S⟩

/-- The sum test at one pattern: the lower bound of `‖Σ‖` is at least `1.47·10⁻⁶ · 3 · ub`. -/
def sumTestAt (B1 B2 B3 : QDisc) (ub : Rat) (pt : Int × Int × Int × Int × Int) : Bool :=
  let D := sumDisc3 B1 B2 B3 pt.1 pt.2.1 pt.2.2.1 pt.2.2.2.1 pt.2.2.2.2
  match normLo D.c with
  | some lo => (147 / 100000000 : Rat) * 3 * ub ≤ lo - D.r
  | none => false

/-- The extra tests of a box of Lemma 6.19(d). -/
def kcExtra (b : Box) : Bool :=
  b.cs.length == 12 && rho0OK && discNonzero (kcD3 b) &&
    match betaDisc 1 kcD1, betaDisc 2 (kcD2 b), betaDisc 3 (kcD3 b) with
    | some B1, some B2, some B3 =>
      match discUp B1, discUp B2, discUp B3 with
      | some u1, some u2, some u3 => patterns.all (sumTestAt B1 B2 B3 (u1 + u2 + u3))
      | _, _, _ => false
    | _, _, _ => false

/-- The radius is positive and below `5·10^-54`. -/
def kcRadiusOK (b : Box) : Bool := 0 < b.rho && b.rho * 10 ^ 54 < 5 * S

/-- **A box of Lemma 6.19(d).** -/
def kcBoxOK (s : String) : Bool :=
  match parseBox s with
  | some b => kcRadiusOK b && krawBox kc12T b && kcExtra b
  | none => false

/-- All boxes of a chunk. -/
def kcChunkOK (l : List String) : Bool := l.all kcBoxOK

/-! ## Sec. 6.7, last paragraph: certified decisions on the KC boxes -/

/-- The T-test over the bodies 1, 2, 3 (masses 1, 2, 3) passes on the box: some `k` has
`m_k λ_k > Σ_{l≠k} m_l υ_l`. -/
def t123Pass (l1 u1 l2 u2 l3 u3 : Nat) : Bool :=
  2 * u2 + 3 * u3 < l1 || u1 + 3 * u3 < 2 * l2 || u1 + 2 * u2 < 3 * l3

/-- It fails on the box: every `k` has `m_k υ_k < Σ_{l≠k} m_l λ_l`. -/
def t123Fail (l1 u1 l2 u2 l3 u3 : Nat) : Bool :=
  u1 < 2 * l2 + 3 * l3 && 2 * u2 < l1 + 3 * l3 && 3 * u3 < l1 + 2 * l2

/-- The decision of the T-test over the bodies 1, 2, 3 (`none`: undecided). -/
def t123Decide (b : Box) : Option Bool :=
  match discInvSqrt kcD1, discInvSqrt (kcD2 b), discInvSqrt (kcD3 b) with
  | some (l1, u1), some (l2, u2), some (l3, u3) =>
    if t123Pass l1 u1 l2 u2 l3 u3 then some true
    else if t123Fail l1 u1 l2 u2 l3 u3 then some false
    else none
  | _, _, _ => none

/-- At one pattern the relative margin is certainly below `10⁻⁴`: `hi(‖Σ‖) < 10⁻⁴ · 3 · lb`. -/
def smallAt (B1 B2 B3 : QDisc) (lb : Rat) (pt : Int × Int × Int × Int × Int) : Bool :=
  let D := sumDisc3 B1 B2 B3 pt.1 pt.2.1 pt.2.2.1 pt.2.2.2.1 pt.2.2.2.2
  match normHi D.c with
  | some hi => hi + D.r < (1 / 10000 : Rat) * 3 * lb
  | none => false

/-- At one pattern the relative margin is certainly at least `10⁻⁴`. -/
def bigAt (B1 B2 B3 : QDisc) (ub : Rat) (pt : Int × Int × Int × Int × Int) : Bool :=
  let D := sumDisc3 B1 B2 B3 pt.1 pt.2.1 pt.2.2.1 pt.2.2.2.1 pt.2.2.2.2
  match normLo D.c with
  | some lo => (1 / 10000 : Rat) * 3 * ub ≤ lo - D.r
  | none => false

/-- The decision of the relative margin (`some true`: below `10⁻⁴` at some pattern; `some false`: at least `10⁻⁴` at
all; `none`: undecided). -/
def smallDecide (b : Box) : Option Bool :=
  match betaDisc 1 kcD1, betaDisc 2 (kcD2 b), betaDisc 3 (kcD3 b) with
  | some B1, some B2, some B3 =>
    match discLo B1, discLo B2, discLo B3, discUp B1, discUp B2, discUp B3 with
    | some l1, some l2, some l3, some u1, some u2, some u3 =>
      if patterns.any (smallAt B1 B2 B3 (l1 + l2 + l3)) then some true
      else if patterns.all (bigAt B1 B2 B3 (u1 + u2 + u3)) then some false
      else none
    | _, _, _, _, _, _ => none
  | _, _, _ => none

/-- The disc of the coordinate `j` of the box. -/
def coordDisc (b : Box) (j : Nat) : IDisc := ⟨(b.c j).1, (b.c j).2, b.rho, S⟩

/-- On the box `‖Y₄‖ > 5·10³` and `‖Y_l‖ < 3·10⁻⁵ ‖Y₄‖` for `l = 1, 2, 3` (`Y_l` = coordinate `l + 1`). -/
def yBounds (b : Box) : Bool :=
  match modBounds (coordDisc b 5), modBounds (coordDisc b 2), modBounds (coordDisc b 3), modBounds (coordDisc b 4) with
  | some (L4, _), some (_, U1), some (_, U2), some (_, U3) =>
    5000 * S < L4 && U1 * 100000 < 3 * L4 && U2 * 100000 < 3 * L4 && U3 * 100000 < 3 * L4
  | _, _, _, _ => false

/-- The classification of a KC box: `(T-test over 1, 2, 3 passes, margin below 10⁻⁴)`; `none` if a decision fails or
if the margin is below `10⁻⁴` without the Y-bounds. -/
def kcClass (s : String) : Option (Bool × Bool) :=
  match parseBox s with
  | some b =>
    match t123Decide b, smallDecide b with
    | some t, some sm => if sm && !yBounds b then none else some (t, sm)
    | _, _ => none
  | none => none

/-- The counts `(#fail, #pass, #small)` over a list of boxes (`none` if some box is undecided). -/
def kcCounts : List String → Option (Nat × Nat × Nat)
  | [] => some (0, 0, 0)
  | s :: rest =>
    match kcClass s, kcCounts rest with
    | some (t, sm), some (f, p, k) => some (f + (if t then 0 else 1), p + (if t then 1 else 0), k + (if sm then 1 else 0))
    | _, _ => none

/-! ## Disjointness -/

/-- Two polydiscs are separated in some coordinate: the real or imaginary parts of the centers differ by more than
the sum of the radii. -/
def sepBoxes (b b' : Box) : Bool :=
  (b.cs.zip b'.cs).any fun (x, y) => b.rho + b'.rho < (x.1 - y.1).natAbs || b.rho + b'.rho < (x.2 - y.2).natAbs

/-- Pairwise separation of a list of boxes. -/
def pairwiseSep : List Box → Bool
  | [] => true
  | b :: rest => rest.all (sepBoxes b) && pairwiseSep rest

/-- All box strings parse, and the boxes are pairwise separated. -/
def allSep (l : List String) : Bool :=
  match l.mapM parseBox with
  | some bs => pairwiseSep bs
  | none => false

end Lean6.Special.D88.Boxes
