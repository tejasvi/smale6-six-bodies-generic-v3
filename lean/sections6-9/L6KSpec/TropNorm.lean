import Lean6.Special.Comp.D88.Trop.Check
import L6KSpec.C4Check

/-!
# The normal form of `Comp.Poly` for the kernel, and the leaf check of Lemma 6.19(a)

`Lean6.Special.Comp.Poly.normalize` sorts the terms with `List.mergeSort`, which the kernel does not unfold.
`normalizeK` is the same normal form with a merge sort written with the recursors (`msortM`, by the order `leK` on
monomials); `L6SoundKSpec.TropNorm` proves that it has the value of its input (`eval_normalizeK`), so `isZeroK` is a
sound zero test.

`leafOKK p s cofs cofR` is the test of a leaf `.leaf cofs cofR` of `Lean6.Special.Comp.D88.Trop.chk` for the system
`s` of the initial forms at the leaf, with `isZeroK` in place of `Poly.isZero`, and the condition that the monomials of
`s` have at most seventeen entries; `L6SoundKSpec.TropLeaf` proves that it gives the torus emptiness of `s`.

`packN` writes a polynomial over `ℤ/p` in the packed form of the cofactor checks of `L6KSpec.C4Check` (one byte per
exponent), for the systems whose certificates are checked there.
-/

namespace L6KSpec.Trop

open Lean6.Special.Comp Lean6.Special.Comp.D88.Trop

-- the functions written with the recursors are for the kernel; the compiler does not take recursors
noncomputable section

/-- The lexicographic order of monomials (as `Mono.le`), with the recursors. -/
def leK : Mono → Mono → Bool :=
  List.rec (motive := fun _ => Mono → Bool) (fun _ => true)
    (fun a _ ih k =>
      List.rec (motive := fun _ => Bool) false
        (fun b k' _ => Bool.rec (Bool.rec false (ih k') (Nat.beq a b)) true (Nat.blt a b)) k)

/-- Merge of two term lists by monomial (fuel: at least the total length). -/
def mergeM {α : Type} : Nat → Poly α → Poly α → Poly α :=
  Nat.rec (motive := fun _ => Poly α → Poly α → Poly α)
    (fun a b => a ++ b)
    (fun _ ih a b =>
      List.rec (motive := fun _ => Poly α) b
        (fun x a' _ =>
          List.rec (motive := fun _ => Poly α) a
            (fun y b' _ => Bool.rec (y :: ih a b') (x :: ih a' b) (leK x.2 y.2)) b)
        a)

/-- Merge sort of a term list by monomial, with fuel `d` for the depth. -/
def msortM {α : Type} : Nat → Poly α → Poly α :=
  Nat.rec (motive := fun _ => Poly α → Poly α)
    (fun l => l)
    (fun _ ih l =>
      List.rec (motive := fun _ => Poly α) []
        (fun x t _ =>
          List.rec (motive := fun _ => Poly α) [x]
            (fun _ _ _ => mergeM l.length (ih (l.take (l.length / 2))) (ih (l.drop (l.length / 2)))) t)
        l)

/-- `Poly.normalize` with `msortM` in place of `List.mergeSort`. -/
def normalizeK {α : Type} (C : Coeff α) (p : Poly α) : Poly α :=
  (Poly.combine C (msortM 40 (p.map fun t => (t.1, Mono.trim t.2)))).filter fun t => !C.isZero t.1

/-- The zero test with `normalizeK`. -/
def isZeroK {α : Type} (C : Coeff α) (p : Poly α) : Bool := (normalizeK C p).isEmpty

/-- The test of a leaf of the covering for the system `s` of its initial forms: the identity
`Σ c · s[pos] + cofR · (1 − x₁₇ x₀ ⋯ x₁₆) = 1` modulo `p`, and monomials of `s` with at most seventeen entries. -/
def leafOKK (p : Nat) (s : List (Poly Nat)) (cofs : List (Nat × Poly Nat)) (cofR : Poly Nat) : Bool :=
  s.all (fun f => f.all fun t => decide (t.2.length ≤ 17)) &&
    isZeroK (modC p)
      (Poly.sub (modC p)
        (Poly.add (Poly.sum (cofs.map fun c => Poly.mul (modC p) c.2 (s.getD c.1 []))) (Poly.mul (modC p) cofR (rabin p)))
        (Poly.const 1))

/-- The key of a monomial: one byte per exponent. -/
def packKey : Mono → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun e _ ih => e + 256 * ih)

/-- A polynomial over `ℤ/p` in the packed form of `L6KSpec.C4Check`. -/
def packN (f : Poly Nat) : L6KSpec.C4.KPoly := f.map fun t => (packKey t.2, (t.1 : Int))

/-- The monomials of the system have at most `nv` entries, each below `256`. -/
def sysSmall (nv : Nat) (s : List (Poly Nat)) : Bool :=
  s.all fun f => f.all fun t => decide (t.2.length ≤ nv) && t.2.all fun e => decide (e < 256)

end

end L6KSpec.Trop
