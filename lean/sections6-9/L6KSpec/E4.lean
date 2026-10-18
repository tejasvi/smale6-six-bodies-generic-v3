import Lean6.Special.Comp.K4.E4.Mac

/-!
# The Macaulay checks of §7.2, for the kernel

`macCheckK n D p s fs sel B` is lean6_special's `macCheck` (`Comp.K4.E4.Mac`) arranged for evaluation in the kernel:

* the rows `x^α f` are not normalized (`rowsRaw`; `Poly.normalize` sorts with `List.mergeSort`, which the kernel does
  not unfold), and the coefficient vector of a row on the monomials of degree `D` sums the coefficients of its terms
  with each trimmed monomial (`coeffVecK`); the check asks that the trimmed monomials be distinct and that every term
  of a selected row have one of them (`covered`);
* the selection `sel` of `m` rows and the inverse `B` of the selected block modulo `p` are given (computed outside,
  untrusted); only the selected rows are expanded;
* `A B ≡ 1 (mod p)` is checked on rows packed into natural numbers (`verifyPacked`).

`L6SoundKSpec.E4` proves that a passing check gives the conclusion of `macCheck_sound`.
-/

namespace L6KSpec.E4

open Lean6.Special.Comp Lean6.Special.Comp.E4

/-- The rows `x^α f` of degree `D`, for each form `f` of degree `df` and each `α` of degree `D − df`, not normalized
(the order of `macRows`). -/
def rowsRaw (n D : Nat) (fs : List (Poly ZJ × Nat)) : List (Poly ZJ) :=
  fs.flatMap fun f => (monos n (D - f.2)).map fun α => Poly.mulTerm zjC zjC.one α f.1

/-- The sum of the coefficients of the terms with monomial `k` (`zjC.add`). -/
def coefSum (k : Mono) : Poly ZJ → ZJ
  | [] => (0, 0)
  | t :: rest => if t.2 == k then zjC.add t.1 (coefSum k rest) else coefSum k rest

/-- The coefficient vector of `p` on the trimmed monomials `msT`. -/
def coeffVecK (msT : List Mono) (p : Poly ZJ) : List ZJ :=
  let pt := p.map fun t => (t.1, Mono.trim t.2)
  msT.map fun k => coefSum k pt

/-- Every term of `p` has one of the monomials `msT` (after trimming). -/
def covered (msT : List Mono) (p : Poly ZJ) : Bool := p.all fun t => msT.contains (Mono.trim t.2)

/-- No two elements of the list are equal. -/
def nodupB : List Mono → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

/-! ## The product test on packed rows

A row `b` of `B` is packed into the natural number `Σ_j (b_j mod p) 2^(72 j)` (`packRow`). For a row `a` of residues
`a_l < p`, `Σ_l a_l · pack(b_l)` (`dotPacked`) holds the integer entries of `a B` in its slots of 72 bits: each is
below `m p² < 2^72` when `m ≤ 128` and `p < 2^31`, so no slot overflows (`slotsUnit` reads them back). -/

/-- `Σ_j (b_j mod p) 2^(72 j)`. -/
def packRow (p : Nat) : List Nat → Nat
  | [] => 0
  | b :: bs => b % p + (packRow p bs <<< 72)

/-- `Σ_l a_l · P_l`. -/
def dotPacked : List Nat → List Nat → Nat
  | a :: as, P :: Ps => a * P + dotPacked as Ps
  | _, _ => 0

/-- The slots `j, j + 1, …` (`k` of them) of `x`, read from the lowest, are `≡ [j = i] (mod p)`. -/
def slotsUnit (p i : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | k + 1, j, x => (x % 2 ^ 72) % p == (if j == i then 1 else 0) && slotsUnit p i k (j + 1) (x >>> 72)

/-- **The trusted test, packed**: the `m` rows `A` (residues `< p`, `m` each) times the `m × m` matrix `B` is the
identity modulo `p`, for `m ≤ 128` and `p < 2^31`. -/
def verifyPacked (p m : Nat) (A B : List (List Nat)) : Bool :=
  let Bp := B.map (packRow p)
  m ≤ 128 && p < 2 ^ 31 && A.length == m && B.length == m && B.all (·.length == m) &&
    A.all (fun a => a.length == m && a.all (· < p)) &&
    (A.zipIdx.all fun ai => slotsUnit p ai.2 m 0 (dotPacked ai.1 Bp))

/-- **The check** for forms `fs` (each with its degree) in `n` variables, in degree `D`, modulo `p` with `s² ≡ −3`,
given the selected rows `sel` and the inverse `B` of the selected block. -/
def macCheckK (n D p s : Nat) (fs : List (Poly ZJ × Nat)) (sel : List Nat) (B : List (List Nat)) : Bool :=
  let ms := monos n D
  let msT := ms.map Mono.trim
  let rows := rowsRaw n D fs
  let srows := sel.map fun r => rows.getD r []
  let Asub := srows.map fun row => (coeffVecK msT row).map (toModS p s)
  nodupB msT && srows.all (covered msT) && sel.length == ms.length && verifyPacked p ms.length Asub B &&
    (List.range n).all fun k => ms.contains (purePow n k D)

/-! ## The forms `G_σ` without normalization -/

/-- `Gform` (`Comp.K4.E4.Mac`) before its final `Poly.normalize`: `Gform μ w k = Poly.normalize zjC (GformK μ w k)`. -/
def GformK (μ : List Int) (w : List Int) (k : Nat) : Poly ZJ :=
  ((List.range 4).filter (· != k)).flatMap fun l =>
    Poly.mul zjC [((sigmaOf w k l * μ.getD l 0, 0), [])]
      (((List.range 4).filter fun j => j != k && j != l).foldr (fun j acc => Poly.mul zjC (dsq k j) acc)
        [(zjC.one, [])])

/-- The four quartic forms `G_σ`, not normalized. -/
def formsGK (μ : List Int) (w : List Int) : List (Poly ZJ × Nat) := (List.range 4).map fun k => (GformK μ w k, 4)

end L6KSpec.E4
