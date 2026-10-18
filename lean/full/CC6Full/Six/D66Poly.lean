import CC6Full.Six.D66
import CC6Full.Algebra.MacaulayBi
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.Tactic.NormNum.Prime

/-!
# Diagram 66: the polynomial of Theorem 7.13 (`thm:d66`)

Theorem 7.13 of the paper: if a singular place has diagram `66` with `z`-cluster `K`, centre `o ∈ K` and
`w`-triangle `{a, b, o}`, then `(m_{K∖{o}}, m_o)` lies in the set `B_C` of Proposition 7.11 (`prop:C4`). In the
labelling of Table 1, `K = {3, 4, 5, 6}`, `o = 6` and the masses are `μ = (m_3, m_4, m_5, m_6)`. Here `B_C` is
replaced by the zero set of one nonzero polynomial with integer coefficients, and the computation of Lemma 7.9
(`lem:C4cert`) at the mass point `μ₀ = (3, 5, 7, 11)` over `𝔽_32003` is taken as a hypothesis (`C4Cert`).

* `C4P.eqsAt`, `C4P.eqs`: the eleven equations of §7.3 in the unknowns `s, t, P₁₂, …, P₃₄, c`, obtained from
  `C₄(μ)` by eliminating `η` and writing `ξ = (μ₃ s, μ₃ t, −μ₁ s − μ₂ t, 0)`: four equations
  `Σ_{l≠k} μ_l P_kl³ (ξ_k − ξ_l)`, three equations `Σ_{l≠k} μ_l P_kl Π_{j≠k,l} (ξ_k − ξ_j) − c Π_{l≠k} (ξ_k − ξ_l)`
  and four triangle equations `a_ln a_nk + a_kl a_nk + a_kl a_ln` with `a_kl = P_kl² (ξ_k − ξ_l)`. `C4P.eqsAt` is
  written over any commutative ring; `C4P.eqs` is the polynomial version, in the variables `s, t` (`Sum.inl 0`,
  `Sum.inl 1`) and `P₁₂, P₁₃, P₁₄, P₂₃, P₂₄, P₃₄, c` (`Sum.inr 0, …, Sum.inr 6`) with coefficients in
  `ℤ[μ₁, …, μ₄]` (the variable `X l` is the mass `μ_{l+1}`).
* `C4P.wf`, `C4P.eqs_hom`: the equations are bihomogeneous of bidegrees `(1, 3)`, `(2, 1)` and `(2, 4)` for the
  grading `c4Shift` of §7.3: `deg s = deg t = (1, 0)`, `deg P_kl = (0, 1)`, `deg c = (−1, 1)`.
* `C4Cert`: Lemma 7.9 over `𝔽_32003`: at `μ₀`, on each of the `14` affine charts `chart i j` (`s = 1` or `t = 1`,
  and one of `P₁₂, …, P₃₄, c` equal to `1`) the equations generate the unit ideal. `C4Cert_iff` writes the
  equations on the charts out.
* `C4P.exists_zero_of_isC4`: a solution of `C₄(μ)` (`IsC4`) with `μ₃ ≠ 0` gives a point of `Z(μ)`, that is, a
  common zero `(s, t; P, c)` of the equations with `(s, t) ≠ 0` and `(P, c) ≠ 0` (§7.3).
* `d66_poly`: **Theorem 7.13**, the polynomial: `P ≠ 0` in `ℤ[m₁, …, m₆]` and `P(m) = 0` for all positive masses
  that have a germ with diagram `66`.

## The proof

`biMacaulay_transfer_poly` (Lemma 7.10 and Proposition 7.11 in the form used by the formalization: the chart
identities are homogenized, all monomials of some bidegree `(N, N)` lie in the ideal at `μ₀`, and a maximal minor
`h` of the Macaulay matrix in bidegree `(N, N)` does not vanish at `μ₀`) turns `C4Cert` into a polynomial
`h ∈ ℤ[μ₁, …, μ₄]`, `h ≠ 0`, such that the equations at `μ ∈ ℂ⁴` have no common zero on `X` when `h(μ) ≠ 0`. At a
germ with diagram `66`, Lemmas 7.4 and 7.5 (`Germ.d66_exists_C4`) give a solution of `C₄(m_3, m_4, m_5, m_6)`, and
`m_5 ≠ 0`, so it gives a point of `Z(m_3, m_4, m_5, m_6)` and `h(m_3, m_4, m_5, m_6) = 0`. The polynomial of the
theorem is `h` with the masses `μ₁, …, μ₄` renamed to the bodies `3, 4, 5, 6` (`K4.emb`).
-/

namespace CC6Full.Six

open MvPolynomial Finset

noncomputable section

namespace C4P

/-! ## The equations of §7.3 over a commutative ring -/

section Generic

variable {R : Type*} [CommRing R]

/-- The positions `ξ = (μ₃ s, μ₃ t, −(μ₁ s + μ₂ t), 0)` of §7.3: the solutions of `ξ₄ = 0` and
`Σ_{k≤3} μ_k ξ_k = 0` when `μ₃ ≠ 0` (the bodies `1, 2, 3, 4` of `C₄` are `0, 1, 2, 3` in Lean). -/
def xi (μ : Fin 4 → R) (s t : R) : Fin 4 → R := ![μ 2 * s, μ 2 * t, -(μ 0 * s + μ 1 * t), 0]

/-- The index of `P_kl` among the coordinates `(P₁₂, P₁₃, P₁₄, P₂₃, P₂₄, P₃₄, c)` of the second factor of `X`
(the values `0, …, 5`; the diagonal entries are not used). -/
def pairIdx : Fin 4 → Fin 4 → Fin 7 :=
  ![![0, 0, 1, 2], ![0, 0, 3, 4], ![1, 3, 0, 5], ![2, 4, 5, 0]]

/-- The symmetric matrix `(P_kl)` read off the coordinates `y = (P₁₂, …, P₃₄, c)`. -/
def Pm (y : Fin 7 → R) (k l : Fin 4) : R := y (pairIdx k l)

/-- The equation of the first line of §7.3 for the body `k`: `Σ_{l≠k} μ_l P_kl³ (ξ_k − ξ_l)`, that is `Φ^ξ_k`
(`force μ P ξ k`), (ii) of Lemma 7.5. -/
def eqI (μ ξ : Fin 4 → R) (P : Fin 4 → Fin 4 → R) (k : Fin 4) : R :=
  ∑ l ∈ univ.erase k, μ l * P k l ^ 3 * (ξ k - ξ l)

/-- The equation of the second line of §7.3 for the body `k`:
`Σ_{l≠k} μ_l P_kl Π_{j≠k,l} (ξ_k − ξ_j) − c Π_{l≠k} (ξ_k − ξ_l)`, which is (iii) of Lemma 7.5 multiplied by
`Π_{l≠k} (ξ_k − ξ_l)` after the elimination of `η`. -/
def eqII (μ ξ : Fin 4 → R) (P : Fin 4 → Fin 4 → R) (c : R) (k : Fin 4) : R :=
  ∑ l ∈ univ.erase k, μ l * P k l * ∏ j ∈ (univ.erase k).erase l, (ξ k - ξ j) -
    c * ∏ l ∈ univ.erase k, (ξ k - ξ l)

/-- `a_kl = P_kl² (ξ_k − ξ_l)` (§7.3). -/
def aa (ξ : Fin 4 → R) (P : Fin 4 → Fin 4 → R) (k l : Fin 4) : R := P k l ^ 2 * (ξ k - ξ l)

/-- The equation of the third line of §7.3 for the triangle `{k, l, n}`: `a_ln a_nk + a_kl a_nk + a_kl a_ln`, the
relation `η_kl + η_ln + η_nk = 0` multiplied by `a_kl a_ln a_nk`. -/
def eqIII (ξ : Fin 4 → R) (P : Fin 4 → Fin 4 → R) (k l n : Fin 4) : R :=
  aa ξ P l n * aa ξ P n k + aa ξ P k l * aa ξ P n k + aa ξ P k l * aa ξ P l n

/-- **The eleven equations of §7.3** at the masses `μ` and the point `(s, t; y)`, where
`y = (P₁₂, P₁₃, P₁₄, P₂₃, P₂₄, P₃₄, c)` and `ξ = xi μ s t`: the first line for the bodies `1, 2, 3, 4`, the second
line for the bodies `1, 2, 3`, and the third line for the triangles `123, 124, 134, 234`. -/
def eqsAt (μ : Fin 4 → R) (s t : R) (y : Fin 7 → R) : Fin 11 → R :=
  ![eqI μ (xi μ s t) (Pm y) 0, eqI μ (xi μ s t) (Pm y) 1, eqI μ (xi μ s t) (Pm y) 2,
    eqI μ (xi μ s t) (Pm y) 3,
    eqII μ (xi μ s t) (Pm y) (y 6) 0, eqII μ (xi μ s t) (Pm y) (y 6) 1, eqII μ (xi μ s t) (Pm y) (y 6) 2,
    eqIII (xi μ s t) (Pm y) 0 1 2, eqIII (xi μ s t) (Pm y) 0 1 3, eqIII (xi μ s t) (Pm y) 0 2 3,
    eqIII (xi μ s t) (Pm y) 1 2 3]

/-! ### Naturality: ring maps send the equations to the equations at the images -/

variable {S : Type*} [CommRing S] (φ : R →+* S)

/-- The positions `ξ` are natural in the ring. -/
theorem map_xi {μ : Fin 4 → R} {s t : R} {μ' : Fin 4 → S} {s' t' : S} (hμ : ∀ l, φ (μ l) = μ' l)
    (hs : φ s = s') (ht : φ t = t') (k : Fin 4) : φ (xi μ s t k) = xi μ' s' t' k := by
  fin_cases k <;> simp [xi, hμ, hs, ht]

/-- The equations of the first line are natural in the ring. -/
theorem map_eqI {μ ξ : Fin 4 → R} {P : Fin 4 → Fin 4 → R} {μ' ξ' : Fin 4 → S} {P' : Fin 4 → Fin 4 → S}
    (hμ : ∀ l, φ (μ l) = μ' l) (hξ : ∀ l, φ (ξ l) = ξ' l) (hP : ∀ k l, φ (P k l) = P' k l) (k : Fin 4) :
    φ (eqI μ ξ P k) = eqI μ' ξ' P' k := by
  simp only [eqI, map_sum, map_mul, map_pow, map_sub, hμ, hξ, hP]

/-- The equations of the second line are natural in the ring. -/
theorem map_eqII {μ ξ : Fin 4 → R} {P : Fin 4 → Fin 4 → R} {c : R} {μ' ξ' : Fin 4 → S}
    {P' : Fin 4 → Fin 4 → S} {c' : S} (hμ : ∀ l, φ (μ l) = μ' l) (hξ : ∀ l, φ (ξ l) = ξ' l)
    (hP : ∀ k l, φ (P k l) = P' k l) (hc : φ c = c') (k : Fin 4) :
    φ (eqII μ ξ P c k) = eqII μ' ξ' P' c' k := by
  simp only [eqII, map_sum, map_mul, map_prod, map_sub, hμ, hξ, hP, hc]

/-- The triangle equations are natural in the ring. -/
theorem map_eqIII {ξ : Fin 4 → R} {P : Fin 4 → Fin 4 → R} {ξ' : Fin 4 → S} {P' : Fin 4 → Fin 4 → S}
    (hξ : ∀ l, φ (ξ l) = ξ' l) (hP : ∀ k l, φ (P k l) = P' k l) (k l n : Fin 4) :
    φ (eqIII ξ P k l n) = eqIII ξ' P' k l n := by
  simp only [eqIII, aa, map_add, map_mul, map_pow, map_sub, hξ, hP]

/-- The equations are natural in the ring: a ring map `φ` sends the equations at `(μ, s, t, y)` to the equations
at `(φ μ, φ s, φ t, φ y)`. -/
theorem map_eqsAt {μ : Fin 4 → R} {s t : R} {y : Fin 7 → R} {μ' : Fin 4 → S} {s' t' : S} {y' : Fin 7 → S}
    (hμ : ∀ l, φ (μ l) = μ' l) (hs : φ s = s') (ht : φ t = t') (hy : ∀ j, φ (y j) = y' j) (i : Fin 11) :
    φ (eqsAt μ s t y i) = eqsAt μ' s' t' y' i := by
  have hξ := map_xi φ hμ hs ht
  have hP : ∀ k l, φ (Pm y k l) = Pm y' k l := fun k l => hy _
  fin_cases i
  · exact map_eqI φ hμ hξ hP 0
  · exact map_eqI φ hμ hξ hP 1
  · exact map_eqI φ hμ hξ hP 2
  · exact map_eqI φ hμ hξ hP 3
  · exact map_eqII φ hμ hξ hP (hy 6) 0
  · exact map_eqII φ hμ hξ hP (hy 6) 1
  · exact map_eqII φ hμ hξ hP (hy 6) 2
  · exact map_eqIII φ hξ hP 0 1 2
  · exact map_eqIII φ hξ hP 0 1 3
  · exact map_eqIII φ hξ hP 0 2 3
  · exact map_eqIII φ hξ hP 1 2 3

end Generic

/-! ## The equations with coefficients in `ℤ[μ₁, …, μ₄]` -/

/-- **The eleven equations of §7.3** as polynomials in `s, t` (`X (Sum.inl 0)`, `X (Sum.inl 1)`) and
`P₁₂, P₁₃, P₁₄, P₂₃, P₂₄, P₃₄, c` (`X (Sum.inr 0)`, …, `X (Sum.inr 6)`), with coefficients in `ℤ[μ₁, …, μ₄]`: the
masses are the coefficients `μ_{l+1} = C (X l)`. -/
def eqs : Fin 11 → MvPolynomial (Fin 2 ⊕ Fin 7) (MvPolynomial (Fin 4) ℤ) :=
  eqsAt (fun l => C (X l)) (X (Sum.inl 0)) (X (Sum.inl 1)) fun j => X (Sum.inr j)

/-- Specialized at the masses `μ` (through `ψ : ℤ →+* K`) and evaluated at the point `(x; y)`, the polynomials
`eqs` are the equations `eqsAt μ (x 0) (x 1) y` (`s = x 0`, `t = x 1`). -/
theorem eval_map_eqs {K : Type*} [CommRing K] (ψ : ℤ →+* K) (μ : Fin 4 → K) (x : Fin 2 → K) (y : Fin 7 → K)
    (i : Fin 11) : eval (Sum.elim x y) (map (eval₂Hom ψ μ) (eqs i)) = eqsAt μ (x 0) (x 1) y i :=
  map_eqsAt ((eval (Sum.elim x y)).comp (map (eval₂Hom ψ μ))) (μ := fun l => C (X l)) (s := X (Sum.inl 0))
    (t := X (Sum.inl 1)) (y := fun j => X (Sum.inr j)) (μ' := μ) (s' := x 0) (t' := x 1) (y' := y)
    (fun l => by simp) (by simp) (by simp) (fun j => by simp) i

/-! ## Bidegrees -/

/-- The bidegrees of the eleven equations for the grading `c4Shift` (`deg s = deg t = (1, 0)`,
`deg P_kl = (0, 1)`, `deg c = (−1, 1)`): `(1, 3)`, `(2, 1)` and `(2, 4)` (§7.3). -/
def wf : Fin 11 → ℤ × ℤ :=
  ![(1, 3), (1, 3), (1, 3), (1, 3), (2, 1), (2, 1), (2, 1), (2, 4), (2, 4), (2, 4), (2, 4)]

/-- Change of the stated weight along an equality. -/
theorem hom_of_eq {σ A : Type*} [CommSemiring A] {w : σ → ℤ × ℤ} {p : MvPolynomial σ A} {a b : ℤ × ℤ}
    (h : p.IsWeightedHomogeneous w a) (e : a = b) : p.IsWeightedHomogeneous w b :=
  e ▸ h

section Hom

variable {μ ξ : Fin 4 → MvPolynomial (Fin 2 ⊕ Fin 7) (MvPolynomial (Fin 4) ℤ)}
  {P : Fin 4 → Fin 4 → MvPolynomial (Fin 2 ⊕ Fin 7) (MvPolynomial (Fin 4) ℤ)}

/-- The equations of the first line have bidegree `(1, 3)`. -/
theorem hom_eqI (hμ : ∀ l, (μ l).IsWeightedHomogeneous (biWeight c4Shift) 0)
    (hξ : ∀ k, (ξ k).IsWeightedHomogeneous (biWeight c4Shift) (1, 0))
    (hP : ∀ k l, (P k l).IsWeightedHomogeneous (biWeight c4Shift) (0, 1)) (k : Fin 4) :
    (eqI μ ξ P k).IsWeightedHomogeneous (biWeight c4Shift) (1, 3) :=
  IsWeightedHomogeneous.sum _ _ _ fun l _ =>
    hom_of_eq (((hμ l).mul ((hP k l).pow 3)).mul ((hξ k).sub (hξ l))) (by decide)

/-- The equations of the second line have bidegree `(2, 1)`. -/
theorem hom_eqII (hμ : ∀ l, (μ l).IsWeightedHomogeneous (biWeight c4Shift) 0)
    (hξ : ∀ k, (ξ k).IsWeightedHomogeneous (biWeight c4Shift) (1, 0))
    (hP : ∀ k l, (P k l).IsWeightedHomogeneous (biWeight c4Shift) (0, 1))
    {c : MvPolynomial (Fin 2 ⊕ Fin 7) (MvPolynomial (Fin 4) ℤ)}
    (hc : c.IsWeightedHomogeneous (biWeight c4Shift) (-1, 1)) (k : Fin 4) :
    (eqII μ ξ P c k).IsWeightedHomogeneous (biWeight c4Shift) (2, 1) := by
  have hd : ∀ j, (ξ k - ξ j).IsWeightedHomogeneous (biWeight c4Shift) (1, 0) := fun j => (hξ k).sub (hξ j)
  refine (IsWeightedHomogeneous.sum _ _ _ fun l hl => ?_).sub ?_
  · have hp := IsWeightedHomogeneous.prod ((univ.erase k).erase l) (fun j => ξ k - ξ j)
      (fun _ => ((1 : ℤ), (0 : ℤ))) fun j _ => hd j
    simp only [sum_const, card_erase_of_mem hl, card_erase_of_mem (mem_univ k), card_univ,
      Fintype.card_fin] at hp
    exact hom_of_eq (((hμ l).mul (hP k l)).mul hp) (by decide)
  · have hp := IsWeightedHomogeneous.prod (univ.erase k) (fun l => ξ k - ξ l)
      (fun _ => ((1 : ℤ), (0 : ℤ))) fun l _ => hd l
    simp only [sum_const, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin] at hp
    exact hom_of_eq (hc.mul hp) (by decide)

/-- `a_kl` has bidegree `(1, 2)`. -/
theorem hom_aa (hξ : ∀ k, (ξ k).IsWeightedHomogeneous (biWeight c4Shift) (1, 0))
    (hP : ∀ k l, (P k l).IsWeightedHomogeneous (biWeight c4Shift) (0, 1)) (k l : Fin 4) :
    (aa ξ P k l).IsWeightedHomogeneous (biWeight c4Shift) (1, 2) :=
  hom_of_eq (((hP k l).pow 2).mul ((hξ k).sub (hξ l))) (by decide)

/-- The triangle equations have bidegree `(2, 4)`. -/
theorem hom_eqIII (hξ : ∀ k, (ξ k).IsWeightedHomogeneous (biWeight c4Shift) (1, 0))
    (hP : ∀ k l, (P k l).IsWeightedHomogeneous (biWeight c4Shift) (0, 1)) (k l n : Fin 4) :
    (eqIII ξ P k l n).IsWeightedHomogeneous (biWeight c4Shift) (2, 4) := by
  have h : ∀ a b a' b' : Fin 4,
      (aa ξ P a b * aa ξ P a' b').IsWeightedHomogeneous (biWeight c4Shift) (2, 4) := fun a b a' b' =>
    hom_of_eq ((hom_aa hξ hP a b).mul (hom_aa hξ hP a' b')) (by decide)
  exact ((h l n n k).add (h k l n k)).add (h k l l n)

end Hom

/-- The masses are constants: bidegree `(0, 0)`. -/
theorem hom_mu (l : Fin 4) :
    (C (X l) : MvPolynomial (Fin 2 ⊕ Fin 7) (MvPolynomial (Fin 4) ℤ)).IsWeightedHomogeneous
      (biWeight c4Shift) 0 :=
  isWeightedHomogeneous_C _ _

/-- `P_kl` is never the coordinate `c`. -/
theorem pairIdx_ne_six (k l : Fin 4) : pairIdx k l ≠ 6 := by
  revert k l
  decide

/-- `deg P_kl = (0, 1)`. -/
theorem hom_P (k l : Fin 4) : IsWeightedHomogeneous (biWeight c4Shift)
    (Pm (fun j => (X (Sum.inr j) : MvPolynomial (Fin 2 ⊕ Fin 7) (MvPolynomial (Fin 4) ℤ))) k l) (0, 1) :=
  hom_of_eq (isWeightedHomogeneous_X _ _ (Sum.inr (pairIdx k l))) (biWeight_c4Shift_P (pairIdx_ne_six k l))

/-- `deg c = (−1, 1)`. -/
theorem hom_c :
    (X (Sum.inr 6) : MvPolynomial (Fin 2 ⊕ Fin 7) (MvPolynomial (Fin 4) ℤ)).IsWeightedHomogeneous
      (biWeight c4Shift) (-1, 1) :=
  hom_of_eq (isWeightedHomogeneous_X _ _ _) biWeight_c4Shift_c

/-- `deg ξ_k = (1, 0)`: the positions are linear in `s, t`. -/
theorem hom_xi (k : Fin 4) :
    (xi (fun l => (C (X l) : MvPolynomial (Fin 2 ⊕ Fin 7) (MvPolynomial (Fin 4) ℤ))) (X (Sum.inl 0))
      (X (Sum.inl 1)) k).IsWeightedHomogeneous (biWeight c4Shift) (1, 0) := by
  have hs : (X (Sum.inl 0) : MvPolynomial (Fin 2 ⊕ Fin 7) (MvPolynomial (Fin 4) ℤ)).IsWeightedHomogeneous
      (biWeight c4Shift) (1, 0) := isWeightedHomogeneous_X _ _ _
  have ht : (X (Sum.inl 1) : MvPolynomial (Fin 2 ⊕ Fin 7) (MvPolynomial (Fin 4) ℤ)).IsWeightedHomogeneous
      (biWeight c4Shift) (1, 0) := isWeightedHomogeneous_X _ _ _
  fin_cases k
  · exact hs.C_mul _
  · exact ht.C_mul _
  · exact ((hs.C_mul _).add (ht.C_mul _)).neg
  · exact isWeightedHomogeneous_zero _ _ _

/-- **The bidegrees** (§7.3): the equations `eqs` are bihomogeneous of bidegrees `wf` for the grading `c4Shift`,
`(1, 3)` for the first line, `(2, 1)` for the second and `(2, 4)` for the third. -/
theorem eqs_hom (i : Fin 11) : (eqs i).IsWeightedHomogeneous (biWeight c4Shift) (wf i) := by
  have hI := hom_eqI hom_mu hom_xi hom_P
  have hII := hom_eqII hom_mu hom_xi hom_P hom_c
  have hIII := hom_eqIII hom_xi hom_P
  fin_cases i
  · exact hI 0
  · exact hI 1
  · exact hI 2
  · exact hI 3
  · exact hII 0
  · exact hII 1
  · exact hII 2
  · exact hIII 0 1 2
  · exact hIII 0 1 3
  · exact hIII 0 2 3
  · exact hIII 1 2 3

/-! ## The certificate fact -/

/-- The mass point `μ₀ = (3, 5, 7, 11)` of Lemma 7.9 (`lem:C4cert`), in `𝔽_32003`. -/
def μ₀ : Fin 4 → ZMod 32003 := ![3, 5, 7, 11]

/-- `32003` is prime, so `ZMod 32003` is the field `𝔽_32003`. -/
theorem fact_prime_32003 : Fact (Nat.Prime 32003) :=
  ⟨by norm_num⟩

end C4P

/-- **The certificate fact of Lemma 7.9** (`lem:C4cert`), over `𝔽_32003`: at `μ₀ = (3, 5, 7, 11)`, on each of the
`14` affine charts `{s = 1 or t = 1} × {one of P₁₂, …, P₃₄, c equal to 1}` of `X` (`chart i j`, which substitutes
`1` for the variables `Sum.inl i` and `Sum.inr j`), the eleven equations of §7.3 (`C4P.eqs`, specialized at `μ₀`
by `eval₂Hom (Int.castRingHom (ZMod 32003)) C4P.μ₀`) generate the unit ideal of the polynomial ring over
`ZMod 32003`. This is the hypothesis `hcharts` of `biMacaulay_transfer_poly`. -/
def C4Cert : Prop :=
  ∀ (i : Fin 2) (j : Fin 7), (1 : MvPolynomial (Fin 2 ⊕ Fin 7) (ZMod 32003)) ∈
    Ideal.span (Set.range fun k => chart i j (map (eval₂Hom (Int.castRingHom (ZMod 32003)) C4P.μ₀) (C4P.eqs k)))

namespace C4P

/-- The coordinates on the chart `(i, j)`: `1` for `Sum.inl i` and `Sum.inr j`, the variable otherwise. -/
def chartPt (i : Fin 2) (j : Fin 7) : Fin 2 ⊕ Fin 7 → MvPolynomial (Fin 2 ⊕ Fin 7) (ZMod 32003) :=
  Sum.elim (fun i' => if i' = i then 1 else X (Sum.inl i')) fun j' => if j' = j then 1 else X (Sum.inr j')

/-- On the chart `(i, j)`, the specialized polynomials `eqs` are the equations `eqsAt` at the masses `μ₀` and the
point `chartPt i j`. -/
theorem chart_map_eqs (i : Fin 2) (j : Fin 7) (k : Fin 11) :
    chart i j (map (eval₂Hom (Int.castRingHom (ZMod 32003)) μ₀) (eqs k)) =
      eqsAt (fun l => C (μ₀ l)) (chartPt i j (Sum.inl 0)) (chartPt i j (Sum.inl 1))
        (fun j' => chartPt i j (Sum.inr j')) k :=
  map_eqsAt ((chart i j).toRingHom.comp (map (eval₂Hom (Int.castRingHom (ZMod 32003)) μ₀)))
    (μ := fun l => C (X l)) (s := X (Sum.inl 0)) (t := X (Sum.inl 1)) (y := fun j => X (Sum.inr j))
    (μ' := fun l => C (μ₀ l)) (s' := chartPt i j (Sum.inl 0)) (t' := chartPt i j (Sum.inl 1))
    (y' := fun j' => chartPt i j (Sum.inr j'))
    (fun l => by simp [chart]) (by simp [chart, chartPt]) (by simp [chart, chartPt])
    (fun j' => by simp [chart, chartPt]) k

end C4P

/-- `C4Cert` written out: at `μ₀ = (3, 5, 7, 11)`, for each of the `14` charts, the eleven equations of §7.3 with
`1` substituted for `s` or `t` and for one of `P₁₂, …, P₃₄, c` generate the unit ideal over `𝔽_32003`. This is the
statement of Lemma 7.9 (`lem:C4cert`) for the first prime. -/
theorem C4Cert_iff : C4Cert ↔ ∀ (i : Fin 2) (j : Fin 7), (1 : MvPolynomial (Fin 2 ⊕ Fin 7) (ZMod 32003)) ∈
    Ideal.span (Set.range fun k => C4P.eqsAt (fun l => C (C4P.μ₀ l)) (C4P.chartPt i j (Sum.inl 0))
      (C4P.chartPt i j (Sum.inl 1)) (fun j' => C4P.chartPt i j (Sum.inr j')) k) := by
  simp only [C4Cert, C4P.chart_map_eqs]

namespace C4P

/-! ## From a solution of `C₄(μ)` to a point of `Z(μ)` -/

section Passage

variable {R : Type*} [CommRing R]

/-- The equation of the first line for the body `k` only uses the `P_kl` with `l ≠ k`. -/
theorem eqI_congr {μ ξ : Fin 4 → R} {P P' : Fin 4 → Fin 4 → R} (k : Fin 4)
    (h : ∀ l, k ≠ l → P k l = P' k l) : eqI μ ξ P k = eqI μ ξ P' k :=
  sum_congr rfl fun l hl => by rw [h l (ne_of_mem_erase hl).symm]

/-- The equation of the second line for the body `k` only uses the `P_kl` with `l ≠ k`. -/
theorem eqII_congr {μ ξ : Fin 4 → R} {P P' : Fin 4 → Fin 4 → R} (c : R) (k : Fin 4)
    (h : ∀ l, k ≠ l → P k l = P' k l) : eqII μ ξ P c k = eqII μ ξ P' c k := by
  unfold eqII
  rw [sum_congr rfl fun l hl => by rw [h l (ne_of_mem_erase hl).symm]]

/-- The triangle equation for `{k, l, n}` only uses `P_kl`, `P_ln`, `P_nk`. -/
theorem eqIII_congr {ξ : Fin 4 → R} {P P' : Fin 4 → Fin 4 → R} {k l n : Fin 4} (h1 : P k l = P' k l)
    (h2 : P l n = P' l n) (h3 : P n k = P' n k) : eqIII ξ P k l n = eqIII ξ P' k l n := by
  simp only [eqIII, aa, h1, h2, h3]

end Passage

/-- The second line from (iii) of Lemma 7.5: if `P_kl² (ξ_k − ξ_l)(η_k − η_l) = 1` and `Φ^η_k = c`, then
`Σ_{l≠k} μ_l P_kl Π_{j≠k,l} (ξ_k − ξ_j) = c Π_{l≠k} (ξ_k − ξ_l)`: each term `μ_l P_kl³ (η_k − η_l)` of `Φ^η_k`,
multiplied by `Π_{j≠k} (ξ_k − ξ_j)`, is `μ_l P_kl Π_{j≠k,l} (ξ_k − ξ_j)`. -/
theorem eqII_eq_zero {μ ξ η : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ} {c : ℂ} (hd : DistEqs P ξ η) (k : Fin 4)
    (hf : force μ P η k = c) : eqII μ ξ P c k = 0 := by
  unfold eqII
  rw [sub_eq_zero, ← hf, force, sum_mul]
  refine sum_congr rfl fun l hl => ?_
  have hkl : k ≠ l := (ne_of_mem_erase hl).symm
  have hprod : (ξ k - ξ l) * ∏ j ∈ (univ.erase k).erase l, (ξ k - ξ j) = ∏ j ∈ univ.erase k, (ξ k - ξ j) :=
    mul_prod_erase (univ.erase k) (fun j => ξ k - ξ j) hl
  linear_combination (-(μ l * P k l * ∏ j ∈ (univ.erase k).erase l, (ξ k - ξ j))) * hd k l hkl +
    (μ l * P k l ^ 3 * (η k - η l)) * hprod

/-- The third line from the distance equations: `1/a_kl + 1/a_ln + 1/a_nk = η_kl + η_ln + η_nk = 0`. -/
theorem eqIII_eq_zero {ξ η : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ} (hd : DistEqs P ξ η) {k l n : Fin 4}
    (hkl : k ≠ l) (hln : l ≠ n) (hnk : n ≠ k) : eqIII ξ P k l n = 0 := by
  have h1 := hd k l hkl
  have h2 := hd l n hln
  have h3 := hd n k hnk
  unfold eqIII aa
  linear_combination (-(P l n ^ 2 * (ξ l - ξ n) * (P n k ^ 2 * (ξ n - ξ k)))) * h1 -
    (P k l ^ 2 * (ξ k - ξ l) * (P n k ^ 2 * (ξ n - ξ k))) * h2 -
    (P k l ^ 2 * (ξ k - ξ l) * (P l n ^ 2 * (ξ l - ξ n))) * h3

/-- The coordinates `y = (P₁₂, P₁₃, P₁₄, P₂₃, P₂₄, P₃₄, c)` of a symmetric matrix `P` and a force `c`. -/
def yOf (P : Fin 4 → Fin 4 → ℂ) (c : ℂ) : Fin 7 → ℂ := ![P 0 1, P 0 2, P 0 3, P 1 2, P 1 3, P 2 3, c]

/-- Off the diagonal, the matrix read off `yOf P c` is the symmetric matrix `P`. -/
theorem Pm_yOf {P : Fin 4 → Fin 4 → ℂ} (hP : IsSymm P) (c : ℂ) {k l : Fin 4} (hkl : k ≠ l) :
    Pm (yOf P c) k l = P k l := by
  fin_cases k <;> fin_cases l <;> first | exact absurd rfl hkl | rfl | exact hP _ _

/-- A solution of `C₄(μ)` with `μ₃ ≠ 0` solves the eleven equations of §7.3 at `s = ξ₁/μ₃`, `t = ξ₂/μ₃` and
`y = (P₁₂, …, P₃₄, c)`: then `ξ = (μ₃ s, μ₃ t, −μ₁ s − μ₂ t, 0)` by `ξ₄ = 0` and `Σ_{k≤3} μ_k ξ_k = 0`; the first
line is (ii) of Lemma 7.5, the second line follows from (iii) and the distance equations (i), and the third from
(i). -/
theorem eqsAt_eq_zero_of_isC4 {μ ξ η : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ} {c : ℂ} (h : IsC4 μ ξ η P c)
    (hμ : μ 2 ≠ 0) (i : Fin 11) : eqsAt μ (ξ 0 / μ 2) (ξ 1 / μ 2) (yOf P c) i = 0 := by
  obtain ⟨hsym, hdist, hfξ, hfη, hξ3, hsum⟩ := h
  have hsum' : μ 0 * ξ 0 + μ 1 * ξ 1 + μ 2 * ξ 2 = 0 := by
    rw [Finset.sum_erase _ (by rw [hξ3, mul_zero]), Fin.sum_univ_four, hξ3, mul_zero, add_zero] at hsum
    exact hsum
  have hinv : μ 2 * (μ 2)⁻¹ = 1 := mul_inv_cancel₀ hμ
  have hxi : xi μ (ξ 0 / μ 2) (ξ 1 / μ 2) = ξ := by
    funext k
    fin_cases k
    · show μ 2 * (ξ 0 / μ 2) = ξ 0
      rw [div_eq_mul_inv]
      linear_combination ξ 0 * hinv
    · show μ 2 * (ξ 1 / μ 2) = ξ 1
      rw [div_eq_mul_inv]
      linear_combination ξ 1 * hinv
    · show -(μ 0 * (ξ 0 / μ 2) + μ 1 * (ξ 1 / μ 2)) = ξ 2
      rw [div_eq_mul_inv, div_eq_mul_inv]
      linear_combination (-(μ 2)⁻¹) * hsum' + ξ 2 * hinv
    · show (0 : ℂ) = ξ 3
      exact hξ3.symm
  have hPm : ∀ k l, k ≠ l → Pm (yOf P c) k l = P k l := fun k l hkl => Pm_yOf hsym c hkl
  have hI : ∀ k, eqI μ ξ (Pm (yOf P c)) k = 0 := fun k => by
    rw [eqI_congr k fun l hkl => hPm k l hkl]
    exact hfξ k
  have hII : ∀ k, k ≠ 3 → eqII μ ξ (Pm (yOf P c)) c k = 0 := fun k hk => by
    rw [eqII_congr c k fun l hkl => hPm k l hkl]
    exact eqII_eq_zero hdist k (hfη k hk)
  have hIII : ∀ k l n : Fin 4, k ≠ l → l ≠ n → n ≠ k → eqIII ξ (Pm (yOf P c)) k l n = 0 :=
    fun k l n hkl hln hnk => by
      rw [eqIII_congr (hPm k l hkl) (hPm l n hln) (hPm n k hnk)]
      exact eqIII_eq_zero hdist hkl hln hnk
  unfold eqsAt
  rw [hxi]
  fin_cases i
  · exact hI 0
  · exact hI 1
  · exact hI 2
  · exact hI 3
  · exact hII 0 (by decide)
  · exact hII 1 (by decide)
  · exact hII 2 (by decide)
  · exact hIII 0 1 2 (by decide) (by decide) (by decide)
  · exact hIII 0 1 3 (by decide) (by decide) (by decide)
  · exact hIII 0 2 3 (by decide) (by decide) (by decide)
  · exact hIII 1 2 3 (by decide) (by decide) (by decide)

/-- **A solution of `C₄(μ)` with `μ₃ ≠ 0` gives a point of `Z(μ)`** (§7.3, the sentence before Lemma 7.9, and the
last step of the proof of Proposition 7.11): there is a common zero `(x; y) = (s, t; P₁₂, …, P₃₄, c)` of the
equations at `μ` with `(s, t) ≠ 0` (`s = ξ₁/μ₃ ≠ 0` since `ξ₁ ≠ ξ₄ = 0`) and `(P, c) ≠ 0` (`P₁₂ ≠ 0`). -/
theorem exists_zero_of_isC4 {μ ξ η : Fin 4 → ℂ} {P : Fin 4 → Fin 4 → ℂ} {c : ℂ} (h : IsC4 μ ξ η P c)
    (hμ : μ 2 ≠ 0) : ∃ (x : Fin 2 → ℂ) (y : Fin 7 → ℂ), x ≠ 0 ∧ y ≠ 0 ∧
      ∀ k, eval (Sum.elim x y) (map (eval₂Hom (Int.castRingHom ℂ) μ) (eqs k)) = 0 := by
  refine ⟨![ξ 0 / μ 2, ξ 1 / μ 2], yOf P c, fun hx => ?_, fun hy => ?_, fun k => ?_⟩
  · have h0 : ξ 0 / μ 2 = 0 := congrFun hx 0
    have hd := h.2.1 0 3 (by decide)
    rw [h.2.2.2.2.1, (div_eq_zero_iff.mp h0).resolve_right hμ] at hd
    simp at hd
  · have h0 : P 0 1 = 0 := congrFun hy 0
    have hd := h.2.1 0 1 (by decide)
    rw [h0] at hd
    simp at hd
  · rw [eval_map_eqs]
    exact eqsAt_eq_zero_of_isC4 h hμ k

/-! ## Theorem 7.13 -/

/-- The renumbering `K4.emb` of the bodies of `K = {3, 4, 5, 6}` is injective. -/
theorem emb_injective : Function.Injective K4.emb := fun a b h => by
  by_contra hab
  exact K4.emb_ne hab h

/-- A polynomial with integer coefficients that vanishes at the complex point `m` (real) vanishes at `m`. -/
theorem aeval_eq_zero_of_ofReal {ι : Type*} {m : ι → ℝ} {P : MvPolynomial ι ℤ}
    (h : aeval (fun k => (m k : ℂ)) P = 0) : aeval m P = 0 := by
  have h' := aeval_algebraMap_apply ℂ m P
  rw [Complex.coe_algebraMap] at h'
  exact Complex.ofReal_eq_zero.mp (h'.symm.trans h)

end C4P

/-- **Theorem 7.13** (`thm:d66`), the polynomial, given the certificate fact `C4Cert` of Lemma 7.9 at
`μ₀ = (3, 5, 7, 11)` over `𝔽_32003`: there is a nonzero `P ∈ ℤ[m₁, …, m₆]` with `P(m) = 0` for all positive masses
`m` that have a germ (a singular place) with diagram `66` in the labelling of Table 1. `P` is the polynomial `h(μ)`
of Proposition 7.11 (`prop:C4`), given by `biMacaulay_transfer_poly` (Lemma 7.10), in the masses
`μ = (m₃, m₄, m₅, m₆)` of the `z`-cluster `K = {3, 4, 5, 6}` with the centre `6` last (bodies `2, …, 5` in Lean):
by Lemmas 7.4 and 7.5 (`Germ.d66_exists_C4`), `C₄(μ)` has a solution, and `μ₃ = m₅ ≠ 0`, so the equations of §7.3
have a common zero on `X` (`C4P.exists_zero_of_isC4`) and `h(μ) = 0`. -/
theorem d66_poly (hC : C4Cert) : ∃ P : MvPolynomial (Fin 6) ℤ, P ≠ 0 ∧
    ∀ m : Fin 6 → ℝ, (∀ i, 0 < m i) → ∀ G : Germ 6 m, G.HasDiagram Diagram.d66 →
      MvPolynomial.aeval m P = 0 := by
  have := C4P.fact_prime_32003
  obtain ⟨h, h0, -, hT⟩ := biMacaulay_transfer_poly (Int.castRingHom (ZMod 32003)) C4P.μ₀ C4P.eqs c4Shift
    C4P.wf C4P.eqs_hom hC
  refine ⟨rename K4.emb h, fun h1 => h0 ?_, fun m hm G hD => ?_⟩
  · exact rename_injective _ C4P.emb_injective (h1.trans (map_zero _).symm)
  · rw [aeval_rename]
    refine C4P.aeval_eq_zero_of_ofReal (m := m ∘ K4.emb) ?_
    by_contra hne
    obtain ⟨ξ, η, P, c, hC4⟩ := G.d66_exists_C4 hD
    obtain ⟨x, y, hx, hy, hxy⟩ := C4P.exists_zero_of_isC4 hC4 (K4.mass_ne_zero hm (K4.emb 2))
    have hne' : eval₂ (Int.castRingHom ℂ) (K4.muK m) h ≠ 0 := by
      rwa [aeval_def, algebraMap_int_eq] at hne
    rcases hT (Int.castRingHom ℂ) (K4.muK m) hne' x y hxy with h' | h'
    · exact hx h'
    · exact hy h'

end

end CC6Full.Six
