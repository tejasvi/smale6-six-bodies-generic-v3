/-!
# Primality of the two primes of Lemma 7.9 by trial division (no Mathlib)

`trialPrime n`: `n ≥ 2` and no `d` with `2 ≤ d` and `d² ≤ n` divides `n` (`Lean6.Special.K4.C4.Final` proves that this
implies `Nat.Prime n`).
-/

namespace Lean6.Special.Comp.C4

/-- Trial division from `d` on, with fuel. -/
def trialGo (n : Nat) : Nat → Nat → Bool
  | _, 0 => false
  | d, fuel + 1 => if n < d * d then true else if n % d == 0 then false else trialGo n (d + 1) fuel

/-- Trial division up to `√n`. -/
def trialPrime (n : Nat) : Bool := 2 ≤ n && trialGo n 2 n

theorem trialPrime_32003 : trialPrime 32003 = true := by native_decide

theorem trialPrime_1073741789 : trialPrime 1073741789 = true := by native_decide

end Lean6.Special.Comp.C4
