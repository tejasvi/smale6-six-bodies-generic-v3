/-!
# Linear systems with a common slack, and the certificate check of Lemma 4.6

A *row* is `lo ≤ a · h + c · s ≤ hi`, where `h` is the vector of heights (`a` has one integer coefficient per
height), `s` is the common slack, and either bound may be absent. All data are integers: the exponent forms of the
programs have coefficients in `½ℤ`, and every row is multiplied by `2`.

A *certificate* for a system is a list of pairs `(i, y)`: a row index and an integer multiplier (Lemma 4.6 with the
multipliers scaled to integers, which changes none of its conditions). `Farkas.check` tests the hypotheses of
Lemma 4.6; `L6Sound.Common.Farkas` proves that a system with an accepted certificate has no solution with `s > 0`,
and no solution of its strict form (`Row.strictHolds`).
-/

namespace L6

/-- A row `lo ≤ a · h + c · s ≤ hi` (integer data). -/
structure Row where
  a : Array Int
  c : Int
  lo : Option Int
  hi : Option Int
  deriving Repr, Inhabited, BEq

namespace Row

/-- The row stays valid when `s` decreases: `c > 0` only without a lower bound, `c < 0` only without an upper one. -/
def monotone (r : Row) : Bool :=
  (decide (r.c ≤ 0) || r.lo.isNone) && (decide (0 ≤ r.c) || r.hi.isNone)

/-- The bound used with a multiplier of sign `y`: the upper bound for `y > 0`, the lower bound for `y < 0`. -/
def bound? (r : Row) (y : Int) : Option Int :=
  if 0 < y then r.hi else if y < 0 then r.lo else some 0

end Row

namespace Farkas

/-- `acc + y · a`, coordinatewise on the first `n` coordinates (missing entries read as `0`). -/
def axpy (n : Nat) (acc : Array Int) (y : Int) (a : Array Int) : Array Int :=
  (List.range n).foldl (fun v j => v.set! j (v[j]! + y * a[j]!)) acc

/-- The combination of a certificate: `Σ y a`, `g = Σ y c`, `β = Σ y b`; `none` if a multiplier has no bound on its
side or a used row is not monotone. -/
def combine (n : Nat) (rows : Array Row) (cert : List (Nat × Int)) : Option (Array Int × Int × Int) :=
  cert.foldl (fun acc (i, y) =>
    match acc with
    | none => none
    | some (v, g, b) =>
      match rows[i]? with
      | none => none
      | some r =>
        if y = 0 then some (v, g, b)
        else if !r.monotone then none
        else match r.bound? y with
          | none => none
          | some bd => some (axpy n v y r.a, g + y * r.c, b + y * bd)) (some (Array.replicate n 0, 0, 0))

/-- The hypotheses of Lemma 4.6 for the integer multipliers `cert` on the system `rows` with `n` heights:
`Σ y a = 0`, `β + g⁻ ≤ 0`, and `g + g⁻ > 0` or `β + g⁻ < 0`, where `g⁻ = max 0 (−g)`. -/
def check (n : Nat) (rows : Array Row) (cert : List (Nat × Int)) : Bool :=
  match combine n rows cert with
  | none => false
  | some (v, g, b) =>
    let gm := if g < 0 then -g else 0
    v.all (· == 0) && decide (b + gm ≤ 0) && (decide (0 < g + gm) || decide (b + gm < 0))

end Farkas

end L6
