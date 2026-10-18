import Lean6.Special.Comp.Poly

/-!
# Lemma 6.19(a): the checkers (no Mathlib)

* `checkMem`: the identities that put each polynomial of `G` into the ideal of the system (part (i)).
* `checkUnits`: the coefficients of `G`, polynomials in the masses, are nonzero at `μ₀` modulo `p` (part (ii)).
* `chk`: the certified covering of `w`-space by polyhedral cells (parts (iii), (iv)); see `Node`.

`G` is a list of `GPoly`: each term is a monomial in the seventeen torus coordinates `ξ` and its coefficient, a
polynomial in the masses `μ₁, …, μ₄` (variables `0, …, 3` of the coefficient). `flat g` is the same polynomial in
twenty-one variables (`ξ` first, then `μ`), and `gbar p μ₀ g` its reduction: the coefficients evaluated at `μ₀` and
reduced modulo `p`, with the monomials in the same order.
-/

namespace Lean6.Special.Comp.D88.Trop

open Lean6.Special.Comp

/-- A polynomial in `ξ` with coefficients in `ℤ[μ]`. -/
abbrev GPoly := List (Mono × Poly Int)

/-- Shift the variables of a monomial by `k`. -/
def shiftMono (k : Nat) (m : Mono) : Mono := List.replicate k 0 ++ m

/-- Pad a monomial with zeros to length `k` (it must have length at most `k`). -/
def padMono (k : Nat) (m : Mono) : Mono := m ++ List.replicate (k - m.length) 0

/-- `g` in the twenty-one variables `ξ₀, …, ξ₁₆, μ₁, …, μ₄`. -/
def flat (g : GPoly) : Poly Int :=
  g.flatMap fun t => t.2.map fun c => (c.1, padMono 17 t.1 ++ c.2)

/-- The value of a polynomial over `ℤ` in the masses at an integer point. -/
def evalZ (μ : List Int) (c : Poly Int) : Int :=
  c.foldl (fun acc t => acc + t.1 * ((μ.zip t.2).foldl (fun a me => a * me.1 ^ me.2) 1)) 0

/-- The reduction of `g` at the masses `μ₀` modulo `p`. -/
def gbar (p : Nat) (μ₀ : List Int) (g : GPoly) : Poly Nat :=
  g.map fun t => ((evalZ μ₀ t.2 % (p : Int)).toNat, t.1)

/-- **(ii)**: every coefficient is nonzero at `μ₀` modulo `p`, the monomials are distinct and have at most seventeen
entries, and every coefficient polynomial has at most four variables. -/
def checkUnits (p : Nat) (μ₀ : List Int) (G : List GPoly) : Bool :=
  G.all fun g =>
    g.all (fun t => evalZ μ₀ t.2 % (p : Int) != 0 && t.1.length ≤ 17 && t.2.all (fun c => c.2.length ≤ 4)) &&
    (g.map (fun t => Mono.trim t.1)).Nodup

/-! ## (i): membership in the ideal -/

/-- **(i)** for one polynomial: `g(ξ(v)) = Σ_j c_j F_j + c₀ (μ_u · i_u − 1)`, as an identity of polynomials over `ℤ`.
`σ` gives the substitution of the twenty-one variables of `flat g` (`ξ(v)` and the masses), `F` the system, `rel` the
polynomial `μ_u · i_u − 1`. -/
def memOK (σ : Nat → Poly Int) (F : List (Poly Int)) (rel : Poly Int) (g : GPoly) (cof : List (Poly Int))
    (c0 : Poly Int) : Bool :=
  Poly.isZero intC
    (Poly.sub intC (Poly.subst intC σ (flat g))
      (Poly.add (Poly.sum ((cof.zip F).map fun cf => Poly.mul intC cf.1 cf.2)) (Poly.mul intC c0 rel)))

/-- **(i)**: all polynomials of `G`, with their cofactors (`cofs[i]` = the twelve `c_j`, `c0s[i]` = `c₀`). -/
def checkMem (σ : Nat → Poly Int) (F : List (Poly Int)) (rel : Poly Int) (G : List GPoly)
    (cofs : List (List (Poly Int))) (c0s : List (Poly Int)) : Bool :=
  G.length == cofs.length && G.length == c0s.length && cofs.all (fun c => c.length == F.length) &&
    ((G.zip (cofs.zip c0s)).all fun t => memOK σ F rel t.1 t.2.1 t.2.2)

/-! ## Integer vectors -/

/-- Entrywise sum (shorter lists are padded with zeros). -/
def vadd : List Int → List Int → List Int
  | [], b => b
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: vadd as bs

/-- `c · v`. -/
def vsmul (c : Int) (v : List Int) : List Int := v.map (c * ·)

/-- `Σ c · rows[k]` over the sparse list of pairs `(k, c)` (an index out of range is a zero row). -/
def linS (rows : List (List Int)) (cs : List (Nat × Int)) : List Int :=
  cs.foldl (fun acc kc => vadd acc (vsmul kc.2 (rows.getD kc.1 []))) []

/-- The zero test of a vector. -/
def isZeroV (v : List Int) : Bool := v.all (· == 0)

/-- An exponent vector as integers. -/
def toZ (m : Mono) : List Int := m.map Int.ofNat

/-- `e_i − e_j` for the exponents of the terms `i`, `j` of `g`. -/
def diffE (g : Poly Nat) (i j : Nat) : List Int :=
  vadd (toZ (g.getD i (0, [])).2) (vsmul (-1) (toZ (g.getD j (0, [])).2))

/-- A sparse coefficient list with entries `≥ 0` and an entry `> 0` at an index below `n`. -/
def posOK (n : Nat) (cs : List (Nat × Int)) : Bool :=
  cs.all (fun kc => decide (0 ≤ kc.2)) && cs.any (fun kc => decide (0 < kc.2) && decide (kc.1 < n))

/-- The empty-cell certificate: `Σ u_k E_k + Σ y_k S_k = 0`, `y ≥ 0`, some `y_k > 0`. -/
def emptyOK (E S : List (List Int)) (u y : List (Nat × Int)) : Bool :=
  posOK S.length y && isZeroV (vadd (linS E u) (linS S y))

/-- `k h = Σ u E` with `k > 0`: `h` vanishes on the cell. -/
def eqOK (E : List (List Int)) (h : List Int) (c : Int × List (Nat × Int)) : Bool :=
  decide (0 < c.1) && isZeroV (vadd (vsmul c.1 h) (vsmul (-1) (linS E c.2)))

/-- `z h = Σ y S + Σ u E` with `z > 0`, `y ≥ 0`, some `y > 0`: `h` is positive on the cell. -/
def strictOK (E S : List (List Int)) (h : List Int) (c : Int × List (Nat × Int) × List (Nat × Int)) : Bool :=
  decide (0 < c.1) && posOK S.length c.2.1 &&
    isZeroV (vadd (vsmul c.1 h) (vsmul (-1) (vadd (linS S c.2.1) (linS E c.2.2))))

/-! ## The covering -/

/-- The certified covering. A cell is `{w : E w = 0, S w > 0}`; `faces` lists the established argmin faces
`(g, F)` (most recent first). -/
inductive Node where
  /-- the cell is empty -/
  | empty (u y : List (Nat × Int))
  /-- split along `h = e_i − e_j` (terms of polynomial `g`): `h > 0`, `h < 0`, `h = 0` -/
  | split (g i j : Nat) (gt lt eq : Node)
  /-- on the cell the argmin face of polynomial `g` is `F`: certificates for the other members of `F` (equal weight)
  and for the terms outside `F`, in increasing order (larger weight) -/
  | face (g : Nat) (F : List Nat) (eqc : List (Int × List (Nat × Int)))
      (strict : List (Int × List (Nat × Int) × List (Nat × Int))) (child : Node)
  /-- the most recent face has one term -/
  | mono
  /-- the initial forms of the faces have no common zero in the torus: `Σ c (in of face pos) + cR (1 − y ∏ x) = 1` -/
  | leaf (cofs : List (Nat × Poly Nat)) (cofR : Poly Nat)
  /-- the cell is `{0}`: certificates `k e_i = Σ u E` for `i < 17` -/
  | nonneg (certs : List (Int × List (Nat × Int)))
  /-- the initial forms of the faces are the system `hyps[k]`, whose torus emptiness is a hypothesis -/
  | hyp (k : Nat)
  deriving Inhabited

/-- The initial form of `g` on a face `F`: the terms with indices in `F`. -/
def inF (g : Poly Nat) (F : List Nat) : Poly Nat := F.map fun i => g.getD i (0, [])

/-- `1 − x₁₇ · x₀ ⋯ x₁₆` over `ℤ/p`. -/
def rabin (p : Nat) : Poly Nat := [((modC p).one, []), ((modC p).neg (modC p).one, List.replicate 18 1)]

/-- The unit vector `e_i` of length 17. -/
def unitV (i : Nat) : List Int := (List.range 17).map fun k => if k = i then 1 else 0

/-- **The checker of the covering.** `hyps` lists the systems whose torus emptiness is assumed (leaves `hyp`). -/
def chk (p : Nat) (Gb : List (Poly Nat)) (hyps : List (List (Poly Nat))) (E S : List (List Int))
    (faces : List (Nat × List Nat)) : Node → Bool
  | .empty u y => emptyOK E S u y
  | .split g i j gt lt eq =>
    let gg := Gb.getD g []
    let h := diffE gg i j
    decide (g < Gb.length) && decide (i < gg.length) && decide (j < gg.length) &&
      chk p Gb hyps E (S ++ [h]) faces gt && chk p Gb hyps E (S ++ [vsmul (-1) h]) faces lt &&
      chk p Gb hyps (E ++ [h]) S faces eq
  | .face g F eqc strict child =>
    let gg := Gb.getD g []
    match F with
    | [] => false
    | a0 :: rest =>
      let others := (List.range gg.length).filter fun i => !(F.contains i)
      decide (g < Gb.length) && F.all (fun i => decide (i < gg.length)) && F.Nodup &&
        rest.length == eqc.length && ((rest.zip eqc).all fun t => eqOK E (diffE gg t.1 a0) t.2) &&
        others.length == strict.length &&
        ((others.zip strict).all fun t => strictOK E S (diffE gg t.1 a0) t.2) &&
        chk p Gb hyps E S ((g, F) :: faces) child
  | .mono =>
    match faces with
    | (_, [_]) :: _ => true
    | _ => false
  | .leaf cofs cofR =>
    let ins := faces.map fun f => inF (Gb.getD f.1 []) f.2
    Poly.isZero (modC p)
      (Poly.sub (modC p)
        (Poly.add (Poly.sum (cofs.map fun c => Poly.mul (modC p) c.2 (ins.getD c.1 []))) (Poly.mul (modC p) cofR (rabin p)))
        (Poly.const 1))
  | .nonneg certs =>
    certs.length == 17 && (((List.range 17).zip certs).all fun t => eqOK E (unitV t.1) t.2)
  | .hyp k => decide (k < hyps.length) && (faces.map fun f => inF (Gb.getD f.1 []) f.2) == hyps.getD k []

/-- The data conditions on `Gb` used by the soundness proof: monomials with at most seventeen entries, coefficients
reduced modulo `p` and nonzero. -/
def gbOK (p : Nat) (Gb : List (Poly Nat)) : Bool :=
  Gb.all fun g => g.all fun t => decide (t.2.length ≤ 17) && decide (t.1 < p) && decide (t.1 ≠ 0)

end Lean6.Special.Comp.D88.Trop
