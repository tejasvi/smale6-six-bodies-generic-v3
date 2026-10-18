/-!
# Sparse multivariate polynomials (no Mathlib)

A polynomial is a list of terms `(c, m)`: a coefficient `c` and a monomial `m`, the list of exponents of the
variables `0, 1, 2, …` (missing trailing exponents are `0`). Lists need not be normalized: the meaning of a list is
the sum of its terms, so addition is concatenation and multiplication is the list of all products of terms. The
operations on coefficients are a record `Coeff α`, with instances for `ℤ` (`intC`), `ℚ` (`ratC`), `ℤ/p` (`modC p`, on
`Nat`) and `ℤ[j]` with `j² = −1 − j` (`zjC`, on pairs of integers).

`normalize` sorts the terms by monomial, adds the coefficients of equal monomials and drops zero coefficients;
`isZero p` asks that `normalize p` be empty. `Lean6.Special.Poly.Sem` proves that every operation here commutes with
evaluation in any commutative ring, so `isZero p = true` means that `p` is the zero polynomial function over every
commutative ring with a compatible coefficient map. All functions on long lists are tail-recursive (the certificates
have millions of terms).
-/

namespace Lean6.Special.Comp

/-- The operations on a coefficient type. -/
structure Coeff (α : Type) where
  zero : α
  one : α
  add : α → α → α
  mul : α → α → α
  neg : α → α
  isZero : α → Bool

/-- A monomial: the exponents of the variables `0, 1, 2, …`. -/
abbrev Mono := List Nat

namespace Mono

/-- The product of two monomials (exponents added). -/
def mul : Mono → Mono → Mono
  | [], k => k
  | a :: m, [] => a :: m
  | a :: m, b :: k => (a + b) :: mul m k

/-- Drop trailing zero exponents. -/
def trim : Mono → Mono
  | [] => []
  | a :: m =>
    let t := trim m
    if a == 0 && t.isEmpty then [] else a :: t

/-- Lexicographic order (used only to bring equal monomials together). -/
def le : Mono → Mono → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: m, b :: k => if a < b then true else if a == b then le m k else false

/-- The monomial of the variable `i`. -/
def var (i : Nat) : Mono := List.replicate i 0 ++ [1]

/-- The total degree. -/
def deg (m : Mono) : Nat := m.foldl (· + ·) 0

end Mono

/-- A polynomial: a list of terms `(coefficient, monomial)`, meaning their sum. -/
abbrev Poly (α : Type) := List (α × Mono)

namespace Poly

variable {α : Type} (C : Coeff α)

/-- The constant `c`. -/
def const (c : α) : Poly α := [(c, [])]

/-- The variable `i`. -/
def var (i : Nat) : Poly α := [(C.one, Mono.var i)]

/-- Sum (concatenation). -/
def add (p q : Poly α) : Poly α := p ++ q

/-- Negation. -/
def neg (p : Poly α) : Poly α := p.map fun t => (C.neg t.1, t.2)

/-- Difference. -/
def sub (p q : Poly α) : Poly α := p ++ neg C q

/-- `c · x^m · p`. -/
def mulTerm (c : α) (m : Mono) (p : Poly α) : Poly α := p.map fun t => (C.mul c t.1, Mono.mul m t.2)

/-- Product: all products of terms. -/
def mul (p q : Poly α) : Poly α := p.flatMap fun t => mulTerm C t.1 t.2 q

/-- Sum of a list of polynomials. -/
def sum (ps : List (Poly α)) : Poly α := ps.flatten

/-- Merge adjacent terms with equal monomials (`cur` is the current term, `acc` the reversed output). -/
def combineAux : Poly α → α × Mono → Poly α → Poly α
  | [], cur, acc => cur :: acc
  | t :: rest, cur, acc =>
    if t.2 == cur.2 then combineAux rest (C.add cur.1 t.1, cur.2) acc else combineAux rest t (cur :: acc)

/-- Merge adjacent terms with equal monomials (the output is reversed). -/
def combine : Poly α → Poly α
  | [] => []
  | t :: rest => combineAux C rest t []

/-- The normal form: monomials trimmed, sorted, equal monomials merged, zero coefficients dropped. -/
def normalize (p : Poly α) : Poly α :=
  ((combine C ((p.map fun t => (t.1, Mono.trim t.2)).mergeSort fun t u => Mono.le t.2 u.2)).filter
    fun t => !C.isZero t.1)

/-- The zero test. -/
def isZero (p : Poly α) : Bool := (normalize C p).isEmpty

/-- The identity test `p = q`. -/
def eqv (p q : Poly α) : Bool := isZero C (sub C p q)

/-- Power, normalizing after each product. -/
def pow (p : Poly α) : Nat → Poly α
  | 0 => const C.one
  | n + 1 => normalize C (mul C (pow p n) p)

/-- `∏ σ_i ^ e_i` for a monomial `e` (variables from index `i`). -/
def substMono (σ : Nat → Poly α) : Mono → Nat → Poly α
  | [], _ => const C.one
  | e :: m, i => normalize C (mul C (pow C (σ i) e) (substMono σ m (i + 1)))

/-- Substitution of the polynomials `σ i` for the variables `i`. -/
def subst (σ : Nat → Poly α) (p : Poly α) : Poly α :=
  normalize C (p.flatMap fun t => mul C (const t.1) (substMono C σ t.2 0))

/-- Map the coefficients. -/
def mapC {β : Type} (f : α → β) (p : Poly α) : Poly β := p.map fun t => (f t.1, t.2)

end Poly

/-! ## Coefficient types -/

/-- Integer coefficients. -/
def intC : Coeff Int where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  isZero := (· == 0)

/-- Rational coefficients. -/
def ratC : Coeff Rat where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  isZero := (· == 0)

/-- Coefficients in `ℤ/p`, as natural numbers (not necessarily reduced). -/
def modC (p : Nat) : Coeff Nat where
  zero := 0
  one := 1 % p
  add a b := (a + b) % p
  mul a b := (a * b) % p
  neg a := (p - a % p) % p
  isZero a := a % p == 0

/-- `ℤ[j]` with `j² + j + 1 = 0`: the pair `(a, b)` is `a + b j`. -/
def zjC : Coeff (Int × Int) where
  zero := (0, 0)
  one := (1, 0)
  add x y := (x.1 + y.1, x.2 + y.2)
  mul x y := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)
  neg x := (-x.1, -x.2)
  isZero x := x.1 == 0 && x.2 == 0

/-- The image of `a + b j` in `ℤ/p` for a root `r` of `t² + t + 1` modulo `p`. -/
def zjToMod (p r : Nat) (x : Int × Int) : Nat := ((x.1 + x.2 * r) % (p : Int)).toNat

end Lean6.Special.Comp
