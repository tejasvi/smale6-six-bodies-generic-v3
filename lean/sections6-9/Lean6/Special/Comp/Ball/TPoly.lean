import Lean6.Special.Comp.Ball.Defs

/-!
# Polynomials with a coefficient table: the format shared by the `D14a` checkers (no Mathlib)

A term `⟨c, k, mono⟩` stands for `c · κ_k · ∏ x_v^e` (`mono` a list of pairs `(v, e)`), where `κ` is a table of
coefficients (for the rows of `d14a(0)`: `1`, the masses and the products `M · m_l`; for `K14`: `1` and the four masses)
and `x` the variables, both indexed by naturals. A polynomial is a list of terms. The denotation and the soundness of
the ball evaluation are in `TPolySem.lean`.

* `tPow`, `tMono`, `tTerm`, `tEval`: the value of a polynomial at a point of balls `xs`, with coefficient balls `tab`.
-/

namespace Lean6.Special.Kraw

open Lean6.Special.Ball

/-- A term `c · κ_k · ∏ x_v^e`. -/
structure TTerm where
  c : Int
  k : Nat
  mono : List (Nat × Nat)
deriving Repr, DecidableEq

/-- A polynomial: a list of terms. -/
abbrev TPoly := List TTerm

section eval

variable (P : Nat)

/-- `x^e` in balls, by repeated products (`x^0 = 1`). -/
def tPow (x : CB) : Nat → CB
  | 0 => one P
  | Nat.succ e => mul P (tPow x e) x

/-- The monomial `∏ x_v^e` in balls (variables beyond the list are the zero ball). -/
def tMono (xs : List CB) : List (Nat × Nat) → CB
  | [] => one P
  | ve :: rest => mul P (tPow P (xs.getD ve.1 (zero P)) ve.2) (tMono xs rest)

/-- A term in balls (coefficients beyond the table are the zero ball). -/
def tTerm (tab xs : List CB) (t : TTerm) : CB :=
  mul P (mul P (ofInt P t.c) (tab.getD t.k (zero P))) (tMono P xs t.mono)

/-- A polynomial in balls. -/
def tEval (tab xs : List CB) : TPoly → CB
  | [] => zero P
  | t :: rest => add P (tTerm P tab xs t) (tEval tab xs rest)

end eval

end Lean6.Special.Kraw
