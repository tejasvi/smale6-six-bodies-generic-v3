import Lean6.Special.Comp.K4.E4.Run

/-!
# The Macaulay matrices of `F_ε` and `G_σ` for symbolic masses (no Mathlib)

The forms `F_ε` and `G_σ` are linear in the masses. `coeffMat n D fs` is the coefficient matrix of the Macaulay rows
of `fs` in degree `D`, as in `macCheck`. For one pattern, `exportF` (degree 7, `F_ε`) and `exportG` (degree 8, `G_σ`)
check

* for the four unit mass vectors `unitL k`: there are `245` (resp. `60`) rows, and each row equals the sum of its
  listed terms on the monomials `monos n D` (as in `macCheck`);
* for each mass vector `μ` of the list: the coefficient matrix at `μ` has `245` (resp. `60`) rows and is `Σ_k μ_k`
  times the coefficient matrices at the unit masses, entry by entry on `245 × 120` (resp. `60 × 45`);
* for `G_σ`: every entry of the unit-mass matrices has `j`-part `0`.

`Lean6.Special.K4.E4.Export` uses these checks to define the Macaulay matrices for every `μ ∈ ℂ⁴` and to export the
determinants certified by the runs `allF_*`, `allG_*` of `Run`.
-/

namespace Lean6.Special.Comp.E4

open Lean6.Special.Comp

/-- The unit mass vectors. -/
def unitL : Nat → List Int
  | 0 => [1, 0, 0, 0]
  | 1 => [0, 1, 0, 0]
  | 2 => [0, 0, 1, 0]
  | _ => [0, 0, 0, 1]

/-- The coefficient matrix of the Macaulay rows in degree `D` (the matrix `A` of `macCheck`). -/
def coeffMat (n D : Nat) (fs : List (Poly ZJ × Nat)) : List (List ZJ) :=
  (macRows n D fs).map (coeffVec (monos n D))

/-- The entry `(r, l)` of a coefficient matrix (`0` outside). -/
def ent (A : List (List ZJ)) (r l : Nat) : ZJ := (A.getD r []).getD l (0, 0)

/-- The matrix as an array of arrays (constant-time access in the checks). -/
def toArr (A : List (List ZJ)) : Array (Array ZJ) := (A.map List.toArray).toArray

/-- The entry `(r, l)` of an array matrix. -/
def entA (A : Array (Array ZJ)) (r l : Nat) : ZJ := (A.getD r #[]).getD l (0, 0)

/-- `μ₀ a₀ + μ₁ a₁ + μ₂ a₂ + μ₃ a₃` in `ℤ[j]`. -/
def lin4 (μ : List Int) (a0 a1 a2 a3 : ZJ) : ZJ :=
  zjC.add (zjC.add (zjC.add (zjC.mul (μ.getD 0 0, 0) a0) (zjC.mul (μ.getD 1 0, 0) a1))
    (zjC.mul (μ.getD 2 0, 0) a2)) (zjC.mul (μ.getD 3 0, 0) a3)

/-- There are `R` Macaulay rows of `fs` in degree `D`, and each is the sum of its listed terms. -/
def rowsOK (n D R : Nat) (fs : List (Poly ZJ × Nat)) : Bool :=
  let rows := macRows n D fs
  rows.length == R &&
    (rows.zip (rows.map (coeffVec (monos n D)))).all fun ra => Poly.eqv zjC ra.1 (expand (monos n D) ra.2)

/-- On the index ranges `R × C`, the matrix `A` is `Σ_k μ_k A_k`. -/
def linOK (R C : Nat) (μ : List Int) (A A0 A1 A2 A3 : Array (Array ZJ)) : Bool :=
  (List.range R).all fun r => (List.range C).all fun l =>
    entA A r l == lin4 μ (entA A0 r l) (entA A1 r l) (entA A2 r l) (entA A3 r l)

/-- On the index ranges `R × C`, every entry of `A` has `j`-part `0`. -/
def realOK (R C : Nat) (A : Array (Array ZJ)) : Bool :=
  (List.range R).all fun r => (List.range C).all fun l => (entA A r l).2 == 0

/-- The export check of one pattern `v` of `F_ε` (degree 7), at the mass vectors `μs`. -/
def exportF (μs : List (List Int)) (v : List Nat) : Bool :=
  rowsOK 4 7 245 (formsF (unitL 0) v) && rowsOK 4 7 245 (formsF (unitL 1) v) &&
    rowsOK 4 7 245 (formsF (unitL 2) v) && rowsOK 4 7 245 (formsF (unitL 3) v) &&
    μs.all fun μ => (coeffMat 4 7 (formsF μ v)).length == 245 && linOK 245 120 μ (toArr (coeffMat 4 7 (formsF μ v)))
      (toArr (coeffMat 4 7 (formsF (unitL 0) v))) (toArr (coeffMat 4 7 (formsF (unitL 1) v)))
      (toArr (coeffMat 4 7 (formsF (unitL 2) v))) (toArr (coeffMat 4 7 (formsF (unitL 3) v)))

/-- The export check of one sign pattern `w` of `G_σ` (degree 8), at the mass vectors `μs`. -/
def exportG (μs : List (List Int)) (w : List Int) : Bool :=
  rowsOK 3 8 60 (formsG (unitL 0) w) && rowsOK 3 8 60 (formsG (unitL 1) w) &&
    rowsOK 3 8 60 (formsG (unitL 2) w) && rowsOK 3 8 60 (formsG (unitL 3) w) &&
    realOK 60 45 (toArr (coeffMat 3 8 (formsG (unitL 0) w))) &&
    realOK 60 45 (toArr (coeffMat 3 8 (formsG (unitL 1) w))) &&
    realOK 60 45 (toArr (coeffMat 3 8 (formsG (unitL 2) w))) &&
    realOK 60 45 (toArr (coeffMat 3 8 (formsG (unitL 3) w))) &&
    μs.all fun μ => (coeffMat 3 8 (formsG μ w)).length == 60 && linOK 60 45 μ (toArr (coeffMat 3 8 (formsG μ w)))
      (toArr (coeffMat 3 8 (formsG (unitL 0) w))) (toArr (coeffMat 3 8 (formsG (unitL 1) w)))
      (toArr (coeffMat 3 8 (formsG (unitL 2) w))) (toArr (coeffMat 3 8 (formsG (unitL 3) w)))

/-- The facts about the monomials used by the export. -/
def monosOK : Bool :=
  (monos 4 7).length == 120 && (monos 4 4).length == 35 && (monos 3 8).length == 45 && (monos 3 4).length == 15 &&
    (monos 4 7).all (·.length == 4) && (monos 4 4).all (·.length == 4) &&
    (monos 3 8).all (·.length == 3) && (monos 3 4).all (·.length == 3) &&
    ((List.range 4).all fun k => (monos 4 7).contains (purePow 4 k 7)) &&
    ((List.range 3).all fun k => (monos 3 8).contains (purePow 3 k 8))

end Lean6.Special.Comp.E4
