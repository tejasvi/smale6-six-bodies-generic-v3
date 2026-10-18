import Lean6.Special.Comp.Poly

/-!
# The monomial order of Lemma 6.19(b) (no Mathlib)

`grevGtStd m k`: the monomial `m` is larger than `k` in the standard graded reverse lexicographic order with the
first variable largest (the order `DRL` of msolve with the variables in the order of the input file): larger total
degree first; at equal degree, at the last position where the exponents differ, the monomial with the smaller
exponent is larger. Monomials are exponent lists of the same length. `Lean6.Special.D88.Count` proves that this is the
order `degRevLex` of Mathlib's `MonomialOrder` framework (`grevGtStd_iff`).
-/

namespace Lean6.Special.Comp.Count

open Lean6.Special.Comp

/-- The total degree. -/
def mdegS (m : Mono) : Nat := m.sum

/-- The comparison at the last position where two exponent lists differ: `some (m_i < k_i)`, or `none` if the lists
agree (lists of the same length). -/
def lastCmp : Mono → Mono → Option Bool
  | a :: m, b :: k =>
    match lastCmp m k with
    | some r => some r
    | none => if a == b then none else some (decide (a < b))
  | _, _ => none

/-- **The graded reverse lexicographic order**: `m > k`. -/
def grevGtStd (m k : Mono) : Bool :=
  if mdegS m == mdegS k then lastCmp m k == some true else decide (mdegS k < mdegS m)

end Lean6.Special.Comp.Count
