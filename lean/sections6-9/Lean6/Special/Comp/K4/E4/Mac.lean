import Lean6.Special.Comp.Poly

/-!
# Macaulay matrices of forms over `ℤ[j]` modulo `p` (no Mathlib)

For forms `f_1, …, f_N` in the variables `0, …, n − 1` with coefficients in `ℤ[j]` (`j² + j + 1 = 0`) and a degree `D`,
`macCheck n D p s fs` builds the rows `x^α f_i` of degree `D` (`macRows`), the matrix `A` of their coefficients on the
monomials of degree `D` (`monos n D`, `m` of them), checks that each row is the sum of its listed terms, maps `A` to
`ℤ/p` by `a + b j ↦ 2a − b + b s` (the image of `2(a + b j)` when `s² ≡ −3`, that is `s = 2j + 1`), selects `m`
rows and inverts the selected square block modulo `p` (both untrusted), and checks exactly that the block times the
proposed inverse is the identity modulo `p`. It also checks that the pure powers `x_k^D` are among the monomials.
`Lean6.Special.K4.E4.Sound` proves that then the forms have no common zero over `ℂ` other than `0`.
-/

namespace Lean6.Special.Comp.E4

open Lean6.Special.Comp

/-- Elements `a + b j` of `ℤ[j]`. -/
abbrev ZJ := Int × Int

/-- All exponent vectors of length `n` with sum `d`. -/
def monos : Nat → Nat → List Mono
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, d => (List.range (d + 1)).flatMap fun a => (monos n (d - a)).map (a :: ·)

/-- The exponent vector of `x_k ^ D` among `n` variables. -/
def purePow (n k D : Nat) : Mono := (List.range n).map fun i => if i == k then D else 0

/-- The rows `x^α f` of degree `D`, for each form `f` of degree `df` and each `α` of degree `D − df`. -/
def macRows (n D : Nat) (fs : List (Poly ZJ × Nat)) : List (Poly ZJ) :=
  fs.flatMap fun f => (monos n (D - f.2)).map fun α => Poly.normalize zjC (Poly.mulTerm zjC zjC.one α f.1)

/-- The coefficient of the monomial `μ` in a polynomial whose monomials are trimmed. -/
def coeffOf (p : Poly ZJ) (μ : Mono) : ZJ :=
  match p.find? (fun t => t.2 == Mono.trim μ) with
  | some t => t.1
  | none => (0, 0)

/-- The coefficient vector on the monomials `ms`. -/
def coeffVec (ms : List Mono) (p : Poly ZJ) : List ZJ := ms.map (coeffOf p)

/-- The polynomial with coefficients `a` on the monomials `ms`. -/
def expand (ms : List Mono) (a : List ZJ) : Poly ZJ := a.zip ms

/-- `2(a + b j) ↦ 2a − b + b s` in `ℤ/p`. -/
def toModS (p s : Nat) (x : ZJ) : Nat := ((2 * x.1 - x.2 + x.2 * (s : Int)) % (p : Int)).toNat

/-- `a ^ e mod p` (square and multiply). -/
def powMod (a e p : Nat) : Nat := Id.run do
  let mut r := 1 % p
  let mut b := a % p
  let mut k := e
  for _ in [0:64] do
    if k == 0 then break
    if k % 2 == 1 then r := (r * b) % p
    b := (b * b) % p
    k := k / 2
  return r

/-- Untrusted: indices of `m` rows of `rows` (entries mod `p`) that are independent modulo `p` (greedy echelon). -/
def selectRows (p m : Nat) (rows : Array (Array Nat)) : Array Nat := Id.run do
  let mut basis : Array (Nat × Array Nat) := #[]
  let mut sel : Array Nat := #[]
  for r in [0:rows.size] do
    if sel.size == m then break
    let mut v := rows[r]!
    for pb in basis do
      let c := v[pb.1]!
      if c != 0 then
        let b := pb.2
        v := (Array.range m).map fun j => (v[j]! + (p - c) * b[j]!) % p
    match (List.range m).find? (fun j => v[j]! != 0) with
    | none => pure ()
    | some pc =>
      let inv := powMod v[pc]! (p - 2) p
      basis := basis.push (pc, v.map fun x => (x * inv) % p)
      sel := sel.push r
  return sel

/-- Untrusted: an inverse modulo the prime `p` of the `m × m` matrix `A` (Gauss–Jordan; garbage if singular). Every
access is bounded (`getD`), so short or missing rows of a singular input cost nothing. -/
def inverseMod (p m : Nat) (A : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut M : Array (Array Nat) :=
    (Array.range m).map fun i => ((Array.range m).map fun j => (A.getD i #[]).getD j 0) ++
      (Array.range m).map fun j => if i == j then 1 else 0
  for col in [0:m] do
    let mut piv := m
    for r in [col:m] do
      if piv == m && ((M.getD r #[]).getD col 0) % p != 0 then piv := r
    if piv < m then
      let rp := M.getD piv #[]
      M := (M.set! piv (M.getD col #[])).set! col rp
      let inv := powMod ((M.getD col #[]).getD col 0) (p - 2) p
      let rowc := (M.getD col #[]).map fun x => (x * inv) % p
      M := M.set! col rowc
      for r in [0:m] do
        if r != col then
          let c := (M.getD r #[]).getD col 0
          if c % p != 0 then
            let rr := M.getD r #[]
            M := M.set! r ((Array.range (2 * m)).map fun j => (rr.getD j 0 + (p - c % p) * rowc.getD j 0) % p)
  return M.map fun row => row.extract m (2 * m)

/-- The entry `(A B)_{ij}` before reduction. -/
def dotIJ (m : Nat) (A B : Array (Array Nat)) (i j : Nat) : Nat :=
  ((List.range m).map fun l => (A.getD i #[]).getD l 0 * (B.getD l #[]).getD j 0).sum

/-- **The trusted test**: `A B ≡ 1 (mod p)` for `m × m` matrices. -/
def verifyInv (p m : Nat) (A B : Array (Array Nat)) : Bool :=
  (List.range m).all fun i => (List.range m).all fun j =>
    dotIJ m A B i j % p == if i == j then 1 else 0

/-- The matrix of the rows modulo `p`. -/
def modMat (p s : Nat) (A : List (List ZJ)) : Array (Array Nat) := (A.map fun a => (a.map (toModS p s)).toArray).toArray

/-- **The check** for forms `fs` (each with its degree) in `n` variables, in degree `D`, modulo `p`, with `s² ≡ −3`. -/
def macCheck (n D p s : Nat) (fs : List (Poly ZJ × Nat)) : Bool :=
  let ms := monos n D
  let m := ms.length
  let rows := macRows n D fs
  let A := rows.map (coeffVec ms)
  let Ap := modMat p s A
  let sel := selectRows p m Ap
  let Asub := sel.map fun r => Ap.getD r #[]
  let B := inverseMod p m Asub
  ((rows.zip A).all fun ra => Poly.eqv zjC ra.1 (expand ms ra.2)) && sel.size == m && verifyInv p m Asub B &&
    (List.range n).all fun k => ms.contains (purePow n k D)

/-! ## The forms of Lemma 7.6 -/

/-- `j ^ e` in `ℤ[j]`. -/
def jpow (e : Nat) : ZJ := if e % 3 == 0 then (1, 0) else if e % 3 == 1 then (0, 1) else (-1, -1)

/-- The index of the pair `{k, l}` (`k ≠ l`, bodies `0, …, 3`) in the order `01, 02, 03, 12, 13, 23`. -/
def pairIdx (k l : Nat) : Nat :=
  let a := min k l
  let b := max k l
  if a == 0 then b - 1 else if a == 1 then b + 1 else 5

/-- The exponent vector of `x_k ^ e`. -/
def powMono (k e : Nat) : Mono := List.replicate k 0 ++ [e]

/-- `A_k = Σ_{l ≠ k} ε_{kl} μ_l q_l` with `ε_{kl} = j^{v(kl)}`. -/
def Apoly (μ : List Int) (v : List Nat) (k : Nat) : Poly ZJ :=
  ((List.range 4).filter (· != k)).map fun l => (zjC.mul (jpow (v.getD (pairIdx k l) 0)) (μ.getD l 0, 0), Mono.var l)

/-- The seven cubic forms `F_ε`: `q_j² A_k − q_k² A_j` (`j < k`) and `Σ μ_k q_k³`, each of degree `3`. -/
def formsF (μ : List Int) (v : List Nat) : List (Poly ZJ × Nat) :=
  ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)].map fun jk =>
    (Poly.sub zjC (Poly.mulTerm zjC zjC.one (powMono jk.1 2) (Apoly μ v jk.2))
      (Poly.mulTerm zjC zjC.one (powMono jk.2 2) (Apoly μ v jk.1)), 3)) ++
  [((List.range 4).map fun k => ((μ.getD k 0, 0), powMono k 3), 3)]

/-- `ξ_k` with `ξ_0 = 0` and `ξ_k` the variable `k − 1` for `k = 1, 2, 3`. -/
def xiP (k : Nat) : Poly ZJ := if k == 0 then [] else Poly.var zjC (k - 1)

/-- `(ξ_k − ξ_j)²`. -/
def dsq (k j : Nat) : Poly ZJ := Poly.mul zjC (Poly.sub zjC (xiP k) (xiP j)) (Poly.sub zjC (xiP k) (xiP j))

/-- `σ_{kl}` from the signs `w` of the pairs `k < l`. -/
def sigmaOf (w : List Int) (k l : Nat) : Int := if k < l then w.getD (pairIdx k l) 1 else -w.getD (pairIdx k l) 1

/-- The form of body `k`: `Σ_{l ≠ k} σ_{kl} μ_l ∏_{j ≠ k, l} (ξ_k − ξ_j)²`. -/
def Gform (μ : List Int) (w : List Int) (k : Nat) : Poly ZJ :=
  Poly.normalize zjC <| ((List.range 4).filter (· != k)).flatMap fun l =>
    Poly.mul zjC [((sigmaOf w k l * μ.getD l 0, 0), [])]
      (((List.range 4).filter fun j => j != k && j != l).foldr (fun j acc => Poly.mul zjC (dsq k j) acc)
        [(zjC.one, [])])

/-- The four quartic forms `G_σ` in `(ξ_1, ξ_2, ξ_3)` (Lean's variables `0, 1, 2`), `ξ_0 = 0`. -/
def formsG (μ : List Int) (w : List Int) : List (Poly ZJ × Nat) := (List.range 4).map fun k => (Gform μ w k, 4)

/-- All `3^6` patterns `v ∈ {0, 1, 2}^6`. -/
def patsF : List (List Nat) :=
  (List.range 729).map fun c => (List.range 6).map fun i => c / 3 ^ i % 3

/-- All `2^6` sign patterns `w ∈ {1, −1}^6`. -/
def patsG : List (List Int) :=
  (List.range 64).map fun c => (List.range 6).map fun i => if c / 2 ^ i % 2 == 0 then 1 else -1

/-- The check of Lemma 7.7 / §7.2 at masses `μ` for all `ε` (degree 7) . -/
def allF (μ : List Int) (p s : Nat) : Bool := patsF.all fun v => macCheck 4 7 p s (formsF μ v)

/-- The check for all `σ` (degree 8). -/
def allG (μ : List Int) (p s : Nat) : Bool := patsG.all fun w => macCheck 3 8 p s (formsG μ w)

end Lean6.Special.Comp.E4
