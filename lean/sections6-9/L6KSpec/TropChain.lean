import L6KSpec.TropNorm

/-!
# A chain of polynomial identities modulo a prime, checked by the kernel

The certificate of a traced Buchberger run: a table `T` of polynomials (term lists `(key, c)` with natural coefficients,
sorted by key), the inputs first, then the elements of the run, and for each element `k` its derivation as an
identity over the inputs and the earlier elements,
  `T[k] = Σ c · X^m · T[r]`   (cofactor terms `(r, m, c)`, `r < k`),
taken modulo `p`. `chainStepOK` checks one identity: after merging (fuel `F`, `R` rounds of pairwise merges, the
merges of `L6KSpec.C4`), `(p − 1) · T[k] + Σ c · X^m · T[r]` has all its coefficients divisible by `p`, and the keys of
the monomials `X^m` are guarded (no carry between bytes). `chainOrder` checks that the steps are the elements
`n, n + 1, …` in order, each over earlier entries only. `L6SoundKSpec.TropChain` turns the checks into the vanishing of
every element where the inputs vanish (`chain_vanish`).

`sortN` (merge sort of a term list by key, with the recursors) and `toN` (a polynomial over `ℤ/p` of `Comp.Poly` as a
term list, the keys of `packKey`) connect the inputs of the table with a system of polynomials.
-/

namespace L6KSpec.Trop

open L6KSpec.C4

noncomputable section

/-- A step of a chain: the element `k`, the fuel and the rounds of its merge, its cofactor terms `(r, m, c)`. -/
abbrev ChainStep := Nat × Nat × Nat × List (Nat × Nat × Nat)

/-- **The check of one identity of a chain modulo `p`.** -/
def chainStepOK (p G : Nat) (T : List NTerms) (s : ChainStep) : Bool :=
  s.2.2.2.all (fun t => Nat.beq (Nat.land t.2.1 G) 0) &&
    zeroMod p (mergeAll s.2.1 s.2.2.1
      (shift 0 (p - 1) (nth [] T s.1) :: s.2.2.2.map fun t => shift t.2.1 t.2.2 (nth [] T t.1)))

/-- The steps are the elements `n, n + 1, …` in order, each with cofactor terms on earlier entries only. -/
def chainOrder : List ChainStep → Nat → Bool :=
  List.rec (fun _ => true) fun s _ ih n => Nat.beq s.1 n && s.2.2.2.all (fun t => Nat.blt t.1 n) && ih (n + 1)

/-- Merge of two term lists by key (fuel: at least the total length); equal keys are kept apart. -/
def mergeN : Nat → NTerms → NTerms → NTerms :=
  Nat.rec (motive := fun _ => NTerms → NTerms → NTerms)
    (fun a b => a ++ b)
    (fun _ ih a b =>
      List.rec (motive := fun _ => NTerms) b
        (fun x a' _ =>
          List.rec (motive := fun _ => NTerms) a
            (fun y b' _ => Bool.rec (y :: ih a b') (x :: ih a' b) (Nat.ble x.1 y.1)) b)
        a)

/-- Merge sort of a term list by key, with fuel `d` for the depth. -/
def sortN : Nat → NTerms → NTerms :=
  Nat.rec (motive := fun _ => NTerms → NTerms)
    (fun l => l)
    (fun _ ih l =>
      List.rec (motive := fun _ => NTerms) []
        (fun x t _ =>
          List.rec (motive := fun _ => NTerms) [x]
            (fun _ _ _ => mergeN l.length (ih (l.take (l.length / 2))) (ih (l.drop (l.length / 2)))) t)
        l)

/-- A polynomial over `ℤ/p` (`Comp.Poly Nat`) as a term list, the keys of `packKey`. -/
def toN (f : Lean6.Special.Comp.Poly Nat) : NTerms := f.map fun t => (packKey t.2, t.1)

end

end L6KSpec.Trop
