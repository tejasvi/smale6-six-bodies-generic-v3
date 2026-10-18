import L6F2.Search

/-!
# Every prune of the search has an accepted certificate

The search of `L6F2.Search` discards a linear program only through `decideLP` (`feasible`), which returns "discard"
only when `Farkas.check` accepts the certificate proposed by `LP.decide` for the rows of that program. With Lemma 4.6
(`Farkas.check` sound), every discarded pair of trees and every discarded choice of argmin sets has no solution with
`s > 0`, that is, the corresponding cell (or partial cell with the relaxation of `ℓ(x) ≤ 0`) is empty.
-/

namespace L6.F2

/-- `decideLP` discards only with an accepted certificate. -/
theorem decideLP_discard {rows : Array Row} {nv : Nat} (h : (decideLP rows nv).1 = false) :
    Farkas.check nv rows (LP.decide rows nv).cert = true := by
  unfold decideLP at h
  cases hk : (LP.decide rows nv).kept <;> cases hc : Farkas.check nv rows (LP.decide rows nv).cert <;>
    simp_all

/-- The same for one step of the search (`feasible`, which also updates the counters). -/
theorem feasible_discard {st : St} {rows : Array Row} {nv : Nat} (h : (feasible st rows nv).1 = false) :
    Farkas.check nv rows (LP.decide rows nv).cert = true := by
  unfold feasible at h
  exact decideLP_discard (by simpa using h)

end L6.F2
