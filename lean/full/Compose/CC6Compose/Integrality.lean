import CC6Full.Six.D88
import CC6Full.Six.D94
import CC6Full.Algebra.GoodRedTorus
import Lean6.Special.D88.Trop.Gamma

/-!
# Bridge: the integrality of Lemma 6.18 for `S12` and `KC₁₂` from the certificate project

`D88Int` and `D94Int` (the hypotheses of `d88_poly` and `d94_poly`) from `CC6Full.goodred_torus_opt` at
`O = Opt 65521 μ0Z`, with the facts of Lemma 6.19 (a) proved in the certificate project (`Lean6.Special.D88.Trop`): the
membership identities `n4_G_mem`, `kc_G_mem`, the coefficient check `n4_units_ok`, `kc_units_ok` and the torus
statements `n4_torus_gamma`, `kc_torus_gamma`.

The certificate project writes polynomials as lists of terms (`Poly`, `Mono`, `GPoly`), with the unknowns, the masses
and the inverse `i_u` of one mass as numbered variables (`Comp.D88.Trop.Sys`). The translation:

* **The equations.** At a point `x` of a commutative ring at which the equations `D88.rows12` of `S12P` vanish and
  `x₁₄ x₁₅ = 1` (`μ₄ i_u = 1`), the twelve equations `n4F` vanish (`n4F_eval_zero`): they are the rows of `S12P` up to
  multiples of `μ₄ i_u − 1`, with the factor `i_u²` for the distance equations of the pairs `k4`. The equations `kcF`
  are those of `D94.KC12P`, the equation of the centre with the opposite sign (`kcF_eval_zero`).
* **The coordinates.** `ξ88`, `ξ94`: the seventeen torus coordinates `n4σ`, `kcσ` evaluated in `O[v]` at the unknowns,
  the masses and `1/μ₄` (resp. `1/μ₃`), units of `O`. Modulo the ideal they are units by the distance equations
  (`n4σ_isUnit`, `kcσ_isUnit`), and the unknowns are polynomials in them (`q88`, `q94`: one `X`- or `Y`-equation and
  differences).
* **The family `G`.** `toMv g`: a polynomial of `GN4` (resp. `GKC`) over `O`, the coefficient of a `ξ`-monomial being
  its coefficient polynomial evaluated at the masses (`coefO`). By the coefficient check `checkUnits` the coefficients
  are units of `O` (their residues are the values `evalZ` at `μ₀` modulo `p`, `resPt_coefO`) and the exponents are
  distinct (`mono17_injective`), so the coefficients of `toMv g` are those of `g`. Its value at `ξ` is the value of
  `flat g` (`aeval_toMv`), which lies in the ideal by `n4_G_mem`, `kc_G_mem` at the point `x88`, `x94` of `O[v]/I`.
* **The initial forms.** `initFormOpt` of `toMv g` at `w : Fin 17 → Γ`, evaluated at `y` in a field of characteristic
  `p`, is `initialFormG` of the reduction `gbar g` at `w` and `y` extended by `0` and `1` (`eval_initFormOpt_toMv`):
  the weights `tropWeight` and `wtG` agree, so do the minimal terms and the reduced coefficients. So `TropCertTorusOpt`
  follows from `TorusEmptyG` (`tropCert_of_torus`).
-/

namespace CC6Compose.Integ

open Lean6.Special Lean6.Special.Comp

noncomputable section

/-! ## Sparse polynomials of the certificate project -/

section Sparse

variable {R : Type*} [CommRing R]

theorem mono_eval_map {S : Type*} [CommRing S] (f : R →+* S) (x : ℕ → R) :
    ∀ (m : Mono) (i : ℕ), f (Mono.eval x m i) = Mono.eval (fun k => f (x k)) m i
  | [], _ => by simp [Mono.eval]
  | e :: m, i => by simp only [Mono.eval, map_mul, map_pow, mono_eval_map f x m (i + 1)]

/-- Ring homomorphisms commute with the evaluation of integer polynomials. -/
theorem poly_eval_map {S : Type*} [CommRing S] (f : R →+* S) (x : ℕ → R) (q : Poly ℤ) :
    f (Poly.eval (intHom R) x q) = Poly.eval (intHom S) (fun k => f (x k)) q := by
  induction q with
  | nil => simp
  | cons t q ih =>
    rw [Poly.eval_cons, Poly.eval_cons, map_add, map_mul, ih, mono_eval_map]
    simp [intHom]

theorem mono_eval_eq_prod (y : ℕ → R) :
    ∀ (m : Mono) (n s : ℕ), m.length ≤ n → Mono.eval y m s = ∏ k ∈ Finset.range n, y (s + k) ^ m.getD k 0
  | [], n, s, _ => by simp [Mono.eval]
  | _ :: _, 0, _, h => by simp at h
  | e :: m, n + 1, s, h => by
    rw [Finset.prod_range_succ', Mono.eval, mono_eval_eq_prod y m n (s + 1) (by simp at h; omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [mul_comm (y s ^ e)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show s + 1 + k = s + (k + 1) by omega]

theorem mono_eval_shift (y : ℕ → R) :
    ∀ (m : Mono) (s i : ℕ), Mono.eval y m (s + i) = Mono.eval (fun k => y (s + k)) m i
  | [], _, _ => rfl
  | e :: m, s, i => by
    simp only [Mono.eval]
    rw [← mono_eval_shift y m s (i + 1)]
    rfl

theorem mono_eval_append (y : ℕ → R) :
    ∀ (m m' : Mono) (i : ℕ), Mono.eval y (m ++ m') i = Mono.eval y m i * Mono.eval y m' (i + m.length)
  | [], m', i => by simp [Mono.eval]
  | e :: m, m', i => by
    simp only [List.cons_append, Mono.eval, mono_eval_append y m m' (i + 1), List.length_cons]
    rw [show i + 1 + m.length = i + (m.length + 1) by omega, mul_assoc]

theorem mono_eval_replicate_zero (y : ℕ → R) : ∀ (n i : ℕ), Mono.eval y (List.replicate n 0) i = 1
  | 0, _ => rfl
  | n + 1, i => by
    simp only [List.replicate_succ, Mono.eval, pow_zero, one_mul, mono_eval_replicate_zero y n (i + 1)]

theorem mono_eval_pad (y : ℕ → R) (m m' : Mono) (hm : m.length ≤ 17) :
    Mono.eval y (Comp.D88.Trop.padMono 17 m ++ m') 0 =
      Mono.eval y m 0 * Mono.eval (fun k => y (17 + k)) m' 0 := by
  have hl : (Comp.D88.Trop.padMono 17 m).length = 17 := by
    simp only [Comp.D88.Trop.padMono, List.length_append, List.length_replicate]
    omega
  rw [mono_eval_append, hl, Comp.D88.Trop.padMono, mono_eval_append, mono_eval_replicate_zero, mul_one,
    show (0 + 17 : ℕ) = 17 + 0 from rfl, mono_eval_shift]

theorem eval_map_pad (y : ℕ → R) (m : Mono) (hm : m.length ≤ 17) (c : Poly ℤ) :
    Poly.eval (intHom R) y (c.map fun u => (u.1, Comp.D88.Trop.padMono 17 m ++ u.2)) =
      Mono.eval y m 0 * Poly.eval (intHom R) (fun k => y (17 + k)) c := by
  induction c with
  | nil => simp
  | cons u c ih =>
    simp only [List.map_cons, Poly.eval_cons, ih, mono_eval_pad y m u.2 hm]
    ring

/-- The evaluation of `flat g`: the `ξ`-monomials at the first seventeen coordinates, the coefficients (polynomials in
the masses) at the coordinates from `17` on. -/
theorem eval_flat (y : ℕ → R) (g : Comp.D88.Trop.GPoly) (hg : ∀ t ∈ g, t.1.length ≤ 17) :
    Poly.eval (intHom R) y (Comp.D88.Trop.flat g) =
      (g.map fun t => Mono.eval y t.1 0 * Poly.eval (intHom R) (fun k => y (17 + k)) t.2).sum := by
  unfold Comp.D88.Trop.flat
  induction g with
  | nil => simp
  | cons t g ih =>
    rw [List.flatMap_cons, Poly.eval_append, ih (fun u hu => hg u (List.mem_cons_of_mem _ hu)),
      eval_map_pad y t.1 (hg t (List.mem_cons_self ..)) t.2, List.map_cons, List.sum_cons]

/-- The evaluation only reads the coordinates below the lengths of the monomials. -/
theorem poly_eval_congr {α : Type} {C : Coeff α} (h : C.Hom R) {x y : ℕ → R} {n : ℕ}
    (hxy : ∀ k < n, x k = y k) : ∀ (q : Poly α), (∀ t ∈ q, t.2.length ≤ n) → Poly.eval h x q = Poly.eval h y q
  | [], _ => rfl
  | t :: q, hq => by
    rw [Poly.eval_cons, Poly.eval_cons, poly_eval_congr h hxy q fun u hu => hq u (List.mem_cons_of_mem _ hu),
      D88.Trop.mono_eval_congr t.2 0 fun k _ hk => hxy k (by have := hq t (List.mem_cons_self ..); omega)]

theorem foldl_add_eq {β : Type*} (G : β → ℤ) :
    ∀ (l : List β) (a : ℤ), l.foldl (fun acc t => acc + G t) a = a + (l.map G).sum
  | [], a => by simp
  | t :: l, a => by rw [List.foldl_cons, foldl_add_eq G l, List.map_cons, List.sum_cons, add_assoc]

theorem foldl_zip_pow : ∀ (μ : List ℤ) (m : Mono) (b : ℤ), m.length ≤ μ.length →
    (μ.zip m).foldl (fun a me => a * me.1 ^ me.2) b = b * Mono.eval (fun k => μ.getD k 0) m 0
  | _, [], b, _ => by simp [Mono.eval]
  | [], _ :: _, _, h => by simp at h
  | a :: μ, e :: m, b, h => by
    simp only [List.zip_cons_cons, List.foldl_cons]
    rw [foldl_zip_pow μ m _ (by simp at h; omega), Mono.eval, show (0 + 1 : ℕ) = 1 + 0 from rfl, mono_eval_shift]
    have hμ : (fun k => (a :: μ).getD (1 + k) 0) = fun k => μ.getD k 0 := by
      funext k
      rw [Nat.add_comm, List.getD_cons_succ]
    rw [hμ, List.getD_cons_zero, mul_assoc]

/-- `evalZ` (the value of a polynomial in the masses at an integer point, as computed by the checker) is the
evaluation at the point, for monomials with at most as many entries as the point. -/
theorem evalZ_eq (μ : List ℤ) (c : Poly ℤ) (hc : ∀ t ∈ c, t.2.length ≤ μ.length) :
    Comp.D88.Trop.evalZ μ c = Poly.eval (intHom ℤ) (fun k => μ.getD k 0) c := by
  rw [Comp.D88.Trop.evalZ, foldl_add_eq, zero_add, Poly.eval]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [foldl_zip_pow μ t.2 1 (hc t ht), one_mul]
  simp [intHom]

theorem dotG_toZ {Γ : Type*} [AddCommGroup Γ] (w : ℕ → Γ) :
    ∀ (m : Mono) (n s : ℕ), m.length ≤ n →
      D88.Trop.dotG w (Comp.D88.Trop.toZ m) s = ∑ k ∈ Finset.range n, m.getD k 0 • w (s + k)
  | [], n, s, _ => by simp [Comp.D88.Trop.toZ, D88.Trop.dotG]
  | _ :: _, 0, _, h => by simp at h
  | e :: m, n + 1, s, h => by
    have ih := dotG_toZ w m n (s + 1) (by simp at h; omega)
    simp only [Comp.D88.Trop.toZ] at ih ⊢
    rw [List.map_cons, D88.Trop.dotG, ih, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero, Int.ofNat_eq_natCast, natCast_zsmul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show s + 1 + k = s + (k + 1) by omega]

theorem sum_map_filter_range {M : Type*} [AddCommMonoid M] (P : ℕ → Prop) [DecidablePred P] (f : ℕ → M) (n : ℕ) :
    (((List.range n).filter fun i => decide (P i)).map f).sum = ∑ i ∈ Finset.range n, if P i then f i else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    congr 1
    by_cases hP : P n <;> simp [hP]

/-- The initial form of the certificate project, evaluated, as a sum over the terms with a minimality condition. -/
theorem eval_initialFormG_map {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] {C : Coeff ℕ} (h : C.Hom R)
    (x : ℕ → R) (w : ℕ → Γ) {β : Type*} (g : List β) (F : β → ℕ × Mono) :
    Poly.eval h x (D88.Trop.initialFormG w (g.map F)) =
      ∑ i : Fin g.length, if (∀ j : Fin g.length, D88.Trop.wtG w (F g[i.1]).2 ≤ D88.Trop.wtG w (F g[j.1]).2)
        then h.f (F g[i.1]).1 * Mono.eval x (F g[i.1]).2 0 else 0 := by
  have hterm : ∀ j (hj : j < g.length), D88.Trop.term (g.map F) j = F g[j] := fun j hj => by
    rw [D88.Trop.term, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  rw [D88.Trop.initialFormG, Poly.eval, List.map_map]
  simp only [List.length_map]
  rw [sum_map_filter_range, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcond : (∀ j < g.length, D88.Trop.wtG w (D88.Trop.term (g.map F) i).2 ≤
      D88.Trop.wtG w (D88.Trop.term (g.map F) j).2) ↔
      ∀ j : Fin g.length, D88.Trop.wtG w (F g[i.1]).2 ≤ D88.Trop.wtG w (F g[j.1]).2 := by
    rw [hterm i i.2]
    constructor
    · intro hh j
      rw [← hterm j j.2]
      exact hh j j.2
    · intro hh j hj
      rw [hterm j hj]
      exact hh ⟨j, hj⟩
  refine if_congr hcond ?_ rfl
  simp only [Function.comp_apply, hterm i i.2]

end Sparse

/-! ## Sums of monomials with distinct exponents -/

section SumMono

open MvPolynomial

/-- The exponent vector of a monomial of the certificate project with at most seventeen entries. -/
def mono17 (m : Mono) : Fin 17 →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => m.getD i 0

theorem mono17_apply (m : Mono) (i : Fin 17) : mono17 m i = m.getD i 0 := rfl

theorem trim_eq_nil_of (m : Mono) (h : ∀ k, m.getD k 0 = 0) : Mono.trim m = [] := by
  induction m with
  | nil => rfl
  | cons a m ih =>
    have ha : a = 0 := by simpa using h 0
    have ht : Mono.trim m = [] := ih fun k => by simpa using h (k + 1)
    simp [Mono.trim, ha, ht]

theorem trim_congr : ∀ (m m' : Mono), (∀ k, m.getD k 0 = m'.getD k 0) → Mono.trim m = Mono.trim m'
  | [], m', h => by
    rw [trim_eq_nil_of m' (fun k => by simpa using (h k).symm)]
    rfl
  | a :: m, [], h => by
    rw [trim_eq_nil_of (a :: m) (fun k => by simpa using h k)]
    rfl
  | a :: m, b :: m', h => by
    have hab : a = b := by simpa using h 0
    have ht := trim_congr m m' fun k => by simpa using h (k + 1)
    simp only [Mono.trim, hab, ht]

theorem trim_eq_of_mono17_eq {m m' : Mono} (hm : m.length ≤ 17) (hm' : m'.length ≤ 17)
    (h : mono17 m = mono17 m') : Mono.trim m = Mono.trim m' := by
  refine trim_congr m m' fun k => ?_
  by_cases hk : k < 17
  · exact DFunLike.congr_fun h ⟨k, hk⟩
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem mono17_prod {S : Type*} [CommRing S] (y : Fin 17 → S) (x : ℕ → S) (hxy : ∀ i : Fin 17, x i = y i)
    (m : Mono) (hm : m.length ≤ 17) : (mono17 m).prod (fun i e => y i ^ e) = Mono.eval x m 0 := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), mono_eval_eq_prod x m 17 0 hm, Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mono17_apply, zero_add, hxy]

variable {S : Type*} [CommSemiring S] {n N : ℕ} (α : Fin n → (Fin N →₀ ℕ)) (a : Fin n → S)

theorem coeff_sumMono (hα : Function.Injective α) (i : Fin n) :
    (∑ j, monomial (α j) (a j)).coeff (α i) = a i := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial, hα.eq_iff]
  simp

theorem coeff_sumMono_of_ne (β : Fin N →₀ ℕ) (hβ : ∀ i, α i ≠ β) :
    (∑ j, monomial (α j) (a j)).coeff β = 0 := by
  classical
  rw [coeff_sum]
  simp [coeff_monomial, hβ]

theorem support_sumMono (hα : Function.Injective α) (ha : ∀ i, a i ≠ 0) :
    (∑ j, monomial (α j) (a j)).support = Finset.univ.image α := by
  ext β
  rw [mem_support_iff, Finset.mem_image]
  constructor
  · intro h
    by_contra hne
    simp only [Finset.mem_univ, true_and, not_exists] at hne
    exact h (coeff_sumMono_of_ne α a β hne)
  · rintro ⟨i, -, rfl⟩
    rw [coeff_sumMono α a hα]
    exact ha i

theorem initPattern_sumMono {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] (w : Fin N → Γ)
    (hα : Function.Injective α) (ha : ∀ i, a i ≠ 0) :
    CC6Full.initPattern w (∑ j, monomial (α j) (a j)) =
      (Finset.univ.filter fun i => ∀ j, CC6Full.tropWeight w (α i) ≤ CC6Full.tropWeight w (α j)).image α := by
  ext β
  rw [CC6Full.mem_initPattern, support_sumMono α a hα ha]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact ⟨i, fun j => h _ ⟨j, rfl⟩, rfl⟩
  · rintro ⟨i, h, rfl⟩
    exact ⟨⟨i, rfl⟩, fun β ⟨j, hj⟩ => hj ▸ h j⟩

theorem initFormOpt_sumMono {p : ℕ} [Fact p.Prime] {r : ℕ} {μ₀ : Fin r → ℤ} {Γ : Type*} [AddCommMonoid Γ]
    [LinearOrder Γ] (w : Fin N → Γ) (a : Fin n → CC6Full.Opt p μ₀) (hα : Function.Injective α)
    (ha : ∀ i, a i ≠ 0) :
    CC6Full.initFormOpt p μ₀ w (∑ j, monomial (α j) (a j)) =
      ∑ i ∈ Finset.univ.filter (fun i => ∀ j, CC6Full.tropWeight w (α i) ≤ CC6Full.tropWeight w (α j)),
        monomial (α i) (CC6Full.resPt p μ₀ (a i)) := by
  rw [CC6Full.initFormOpt, initPattern_sumMono α a w hα ha, Finset.sum_image fun i _ j _ h => hα h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_sumMono α a hα]

theorem eval_map_sum_monomial {T : Type*} [CommSemiring T] (φ : S →+* T) (y : Fin N → T) {ι : Type*}
    (s : Finset ι) (β : ι → (Fin N →₀ ℕ)) (b : ι → S) :
    eval y (map φ (∑ i ∈ s, monomial (β i) (b i))) = ∑ i ∈ s, φ (b i) * (β i).prod (fun k e => y k ^ e) := by
  simp [map_sum, map_monomial, eval_monomial]

end SumMono

/-! ## The local ring `O`, the coefficients and the polynomials of `G` over `O` -/

section Opt

open CC6Full MvPolynomial

local notation "𝒪" => Opt 65521 CC6Full.Six.μ0Z

/-- An element of `O` with nonzero residue is a unit. -/
theorem isUnit_of_resPt_ne_zero {x : 𝒪} (h : resPt 65521 Six.μ0Z x ≠ 0) : IsUnit x := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← ker_resPt, RingHom.mem_ker]
  exact h

/-- The masses `μ₁, …, μ₄` in `O` (and `0` from the index `4` on). -/
def μO (k : ℕ) : 𝒪 := algebraMap (MvPolynomial (Fin 4) ℤ) 𝒪 (if h : k < 4 then X ⟨k, h⟩ else 0)

theorem μO_fin (k : Fin 4) : μO k = algebraMap (MvPolynomial (Fin 4) ℤ) 𝒪 (X k) := by
  rw [μO, dite_eq_left k.2]

theorem resPt_μO {k : ℕ} (hk : k < 4) :
    resPt 65521 Six.μ0Z (μO k) = (([1, 2, 3, 30] : List ℤ).getD k 0 : ZMod 65521) := by
  rw [μO, dite_eq_left hk, resPt_algebraMap, eval_X]
  interval_cases k <;> rfl

theorem isUnit_μO {k : ℕ} (hk : k < 4) : IsUnit (μO k) := by
  refine isUnit_of_resPt_ne_zero ?_
  rw [resPt_μO hk, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  interval_cases k <;> decide

/-- The inverse of `μ₄` in `O`. -/
def iu4 : 𝒪 := Ring.inverse (μO 3)

theorem μO_mul_iu4 : μO 3 * iu4 = 1 := Ring.mul_inverse_cancel _ (isUnit_μO (by norm_num))

/-- The inverse of `μ₃` in `O`. -/
def iu3 : 𝒪 := Ring.inverse (μO 2)

theorem μO_mul_iu3 : μO 2 * iu3 = 1 := Ring.mul_inverse_cancel _ (isUnit_μO (by norm_num))

/-- The coefficient in `O` of a term of a polynomial of `G`: the polynomial in the masses at `μ`. -/
def coefO (c : Poly ℤ) : 𝒪 := Poly.eval (intHom 𝒪) μO c

theorem resPt_coefO (c : Poly ℤ) (hc : ∀ t ∈ c, t.2.length ≤ 4) :
    resPt 65521 Six.μ0Z (coefO c) = ((Comp.D88.Trop.evalZ [1, 2, 3, 30] c : ℤ) : ZMod 65521) := by
  rw [coefO, poly_eval_map, evalZ_eq [1, 2, 3, 30] c hc, ← eq_intCast (Int.castRingHom (ZMod 65521)),
    poly_eval_map]
  exact poly_eval_congr _ (fun k hk => by rw [resPt_μO hk]; rfl) c hc

theorem isUnit_coefO (c : Poly ℤ) (hc : ∀ t ∈ c, t.2.length ≤ 4)
    (h : ¬ (65521 : ℤ) ∣ Comp.D88.Trop.evalZ [1, 2, 3, 30] c) : IsUnit (coefO c) := by
  refine isUnit_of_resPt_ne_zero ?_
  rw [resPt_coefO c hc, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact_mod_cast h

/-- The conditions of the coefficient check `checkUnits` on a polynomial of `G`: the coefficients are nonzero at
`μ₀` modulo `p`, the `ξ`-monomials have at most seventeen entries and are distinct after trimming, and the monomials of
the coefficients have at most four entries. -/
def UnitsOK (g : Comp.D88.Trop.GPoly) : Prop :=
  (∀ t ∈ g, ¬ (65521 : ℤ) ∣ Comp.D88.Trop.evalZ [1, 2, 3, 30] t.2 ∧ t.1.length ≤ 17 ∧
    ∀ c ∈ t.2, c.2.length ≤ 4) ∧ (g.map fun t => Mono.trim t.1).Nodup

theorem unitsOK_of_check {G : List Comp.D88.Trop.GPoly}
    (h : Comp.D88.Trop.checkUnits 65521 [1, 2, 3, 30] G = true) : ∀ g ∈ G, UnitsOK g := by
  intro g hg
  simp only [Comp.D88.Trop.checkUnits, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  obtain ⟨hall, hnd⟩ := h g hg
  refine ⟨fun t ht => ?_, by simpa using hnd⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hall t ht
  exact ⟨fun hd => h1 (Int.emod_eq_zero_of_dvd hd), h2, h3⟩

/-- A polynomial of `G` as a polynomial in the seventeen coordinates over `O`. -/
def toMv (g : Comp.D88.Trop.GPoly) : MvPolynomial (Fin 17) 𝒪 :=
  ∑ i : Fin g.length, monomial (mono17 g[i.1].1) (coefO g[i.1].2)

theorem mono17_injective {g : Comp.D88.Trop.GPoly} (hg : UnitsOK g) :
    Function.Injective fun i : Fin g.length => mono17 g[i.1].1 := by
  intro i j hij
  have h := trim_eq_of_mono17_eq (hg.1 _ (List.getElem_mem _)).2.1 (hg.1 _ (List.getElem_mem _)).2.1 hij
  have h2 : (g.map fun t => Mono.trim t.1)[i.1]'(by simp) = (g.map fun t => Mono.trim t.1)[j.1]'(by simp) := by
    simpa using h
  exact Fin.ext ((List.Nodup.getElem_inj_iff hg.2).mp h2)

theorem isUnit_coefO_of {g : Comp.D88.Trop.GPoly} (hg : UnitsOK g) (i : Fin g.length) :
    IsUnit (coefO g[i.1].2) :=
  isUnit_coefO _ (hg.1 _ (List.getElem_mem _)).2.2 (hg.1 _ (List.getElem_mem _)).1

theorem coeff_toMv {g : Comp.D88.Trop.GPoly} (hg : UnitsOK g) (i : Fin g.length) :
    (toMv g).coeff (mono17 g[i.1].1) = coefO g[i.1].2 :=
  coeff_sumMono (fun i : Fin g.length => mono17 g[i.1].1) (fun i => coefO g[i.1].2) (mono17_injective hg) i

theorem support_toMv {g : Comp.D88.Trop.GPoly} (hg : UnitsOK g) :
    (toMv g).support = Finset.univ.image fun i : Fin g.length => mono17 g[i.1].1 :=
  support_sumMono (fun i : Fin g.length => mono17 g[i.1].1) (fun i => coefO g[i.1].2) (mono17_injective hg)
    fun i => (isUnit_coefO_of hg i).ne_zero

/-- **The coefficients of `G` over `O` are units** (from `checkUnits`). -/
theorem toMv_isUnit {g : Comp.D88.Trop.GPoly} (hg : UnitsOK g) :
    ∀ α ∈ (toMv g).support, IsUnit ((toMv g).coeff α) := by
  intro β hβ
  rw [support_toMv hg, Finset.mem_image] at hβ
  obtain ⟨i, -, rfl⟩ := hβ
  rw [coeff_toMv hg]
  exact isUnit_coefO_of hg i

theorem initFormOpt_toMv {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] (w : Fin 17 → Γ)
    {g : Comp.D88.Trop.GPoly} (hg : UnitsOK g) :
    initFormOpt 65521 Six.μ0Z w (toMv g) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin g.length =>
          ∀ j : Fin g.length, tropWeight w (mono17 g[i.1].1) ≤ tropWeight w (mono17 g[j.1].1)),
        monomial (mono17 g[i.1].1) (resPt 65521 Six.μ0Z (coefO g[i.1].2)) :=
  initFormOpt_sumMono (fun i : Fin g.length => mono17 g[i.1].1) w (fun i => coefO g[i.1].2)
    (mono17_injective hg) fun i => (isUnit_coefO_of hg i).ne_zero

theorem tropWeight_mono17 {Γ : Type*} [AddCommGroup Γ] (w : Fin 17 → Γ) (m : Mono) (hm : m.length ≤ 17) :
    tropWeight w (mono17 m) = D88.Trop.wtG (fun k => if h : k < 17 then w ⟨k, h⟩ else 0) m := by
  rw [tropWeight, D88.Trop.wtG, dotG_toZ _ m 17 0 hm, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mono17_apply, zero_add, dite_eq_left i.2]

theorem castHom_resPt_coefO {K : Type} [Field K] [CharP K 65521] (c : Poly ℤ) (hc : ∀ t ∈ c, t.2.length ≤ 4) :
    ZMod.castHom (dvd_refl 65521) K (resPt 65521 Six.μ0Z (coefO c)) =
      (D88.Trop.modHomK 65521 K).f ((Comp.D88.Trop.evalZ [1, 2, 3, 30] c % ((65521 : ℕ) : ℤ)).toNat) := by
  have key : ((Comp.D88.Trop.evalZ [1, 2, 3, 30] c % ((65521 : ℕ) : ℤ) : ℤ) : K) =
      (Comp.D88.Trop.evalZ [1, 2, 3, 30] c : K) := by
    rw [← map_intCast (ZMod.castHom (dvd_refl 65521) K), ZMod.intCast_mod, map_intCast]
  rw [resPt_coefO c hc, map_intCast]
  show _ = (((Comp.D88.Trop.evalZ [1, 2, 3, 30] c % ((65521 : ℕ) : ℤ)).toNat : ℕ) : K)
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num)), key]

/-- The initial form `initFormOpt` of a polynomial of `G` over `O`, evaluated in a field `K` of characteristic `p`, is
the initial form `initialFormG` of the certificate project of its reduction `gbar`, at the weights and the point
extended by `0` and `1` beyond the seventeen coordinates. -/
theorem eval_initFormOpt_toMv {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] (w : Fin 17 → Γ)
    {K : Type} [Field K] [CharP K 65521] (y : Fin 17 → K) {g : Comp.D88.Trop.GPoly} (hg : UnitsOK g) :
    eval y (map (ZMod.castHom (dvd_refl 65521) K) (initFormOpt 65521 Six.μ0Z w (toMv g))) =
      Poly.eval (D88.Trop.modHomK 65521 K) (fun k => if h : k < 17 then y ⟨k, h⟩ else 1)
        (D88.Trop.initialFormG (fun k => if h : k < 17 then w ⟨k, h⟩ else 0)
          (Comp.D88.Trop.gbar 65521 [1, 2, 3, 30] g)) := by
  rw [initFormOpt_toMv w hg, eval_map_sum_monomial, Finset.sum_filter, Comp.D88.Trop.gbar,
    eval_initialFormG_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hl : ∀ j : Fin g.length, g[j.1].1.length ≤ 17 := fun j => (hg.1 _ (List.getElem_mem _)).2.1
  have hw : ∀ j : Fin g.length, tropWeight w (mono17 g[j.1].1) =
      D88.Trop.wtG (fun k => if h : k < 17 then w ⟨k, h⟩ else 0) g[j.1].1 := fun j => tropWeight_mono17 w _ (hl j)
  refine if_congr ?_ ?_ rfl
  · constructor
    · intro h j
      have h1 := h j
      rw [hw, hw] at h1
      exact h1
    · intro h j
      rw [hw, hw]
      exact h j
  · rw [castHom_resPt_coefO _ (hg.1 _ (List.getElem_mem _)).2.2,
      mono17_prod y (fun k => if h : k < 17 then y ⟨k, h⟩ else 1) (fun k => dite_eq_left k.2) _ (hl i)]

/-- The finite set `G` over `O` of a list of polynomials of the certificate project. -/
def Gset (G : List Comp.D88.Trop.GPoly) : Finset (MvPolynomial (Fin 17) 𝒪) := by
  classical exact (G.map toMv).toFinset

theorem mem_Gset {G : List Comp.D88.Trop.GPoly} {f : MvPolynomial (Fin 17) 𝒪} :
    f ∈ Gset G ↔ ∃ g ∈ G, toMv g = f := by
  classical
  simp only [Gset, List.mem_toFinset, List.mem_map]

/-- **The torus certificate** `TropCertTorusOpt` for `G` over `O`, from the torus statements of the certificate project
for the reductions `gbar` (over every linearly ordered abelian group, every field of characteristic `p`). -/
theorem tropCert_of_torus (G : List Comp.D88.Trop.GPoly) (hG : ∀ g ∈ G, UnitsOK g)
    (htor : ∀ (Γ : Type) [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] (w : ℕ → Γ),
      (∃ i < 17, w i < 0) → D88.Trop.TorusEmptyG 65521 (G.map (Comp.D88.Trop.gbar 65521 [1, 2, 3, 30])) w) :
    TropCertTorusOpt 65521 Six.μ0Z (Gset G) := by
  intro Γ _ _ _ w hw K _ _ y hy
  obtain ⟨i, hi⟩ := hw
  have hw' : ∃ k < 17, (fun k => if h : k < 17 then w ⟨k, h⟩ else 0) k < 0 := by
    refine ⟨i, i.2, ?_⟩
    show (if h : (i : ℕ) < 17 then w ⟨i, h⟩ else 0) < 0
    rw [dite_eq_left i.2]
    exact hi
  have hx : ∀ k < 17, (fun k => if h : k < 17 then y ⟨k, h⟩ else 1) k ≠ 0 := fun k hk => by
    show (if h : k < 17 then y ⟨k, h⟩ else 1) ≠ 0
    rw [dite_eq_left hk]
    exact hy _
  obtain ⟨gb, hgb, hne⟩ := htor Γ _ hw' K _ hx
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hgb
  refine ⟨toMv g, mem_Gset.mpr ⟨g, hg, rfl⟩, ?_⟩
  rw [eval_initFormOpt_toMv w y (hG g hg)]
  exact hne

end Opt

/-! ## The systems of the certificate project at a point of a commutative ring -/

section Eqns

open Comp.D88.Trop

variable {R : Type*} [CommRing R] (x : ℕ → R)

theorem eval_V (i : ℕ) : Poly.eval (intHom R) x (V i) = x i := Poly.eval_var _ _ _

theorem eval_K (c : ℤ) : Poly.eval (intHom R) x (K c) = c := by
  simp [K, Poly.eval_const, intHom]

theorem eval_pa (a b : Poly ℤ) :
    Poly.eval (intHom R) x (pa a b) = Poly.eval (intHom R) x a + Poly.eval (intHom R) x b := by
  rw [pa, Poly.eval_normalize, Poly.eval_add]

theorem eval_ps (a b : Poly ℤ) :
    Poly.eval (intHom R) x (ps a b) = Poly.eval (intHom R) x a - Poly.eval (intHom R) x b := by
  rw [ps, Poly.eval_normalize, Poly.eval_sub]

theorem eval_pm (a b : Poly ℤ) :
    Poly.eval (intHom R) x (pm a b) = Poly.eval (intHom R) x a * Poly.eval (intHom R) x b := by
  rw [pm, Poly.eval_normalize, Poly.eval_mul]

theorem eval_psum (l : List (Poly ℤ)) :
    Poly.eval (intHom R) x (psum l) = (l.map (Poly.eval (intHom R) x)).sum := by
  rw [psum, Poly.eval_normalize, Poly.eval_sum]

theorem eval_eqn (B : Bodies) (Z : ℕ → Poly ℤ) (k : ℕ) :
    Poly.eval (intHom R) x (B.eqn Z k) = Poly.eval (intHom R) x (Z k) -
      (([1, 2, 3, 4].filter (· ≠ k)).map fun l => x (B.mu0 + l - 1) * x (B.p0 + pairIdx k l) ^ 3 *
        (Poly.eval (intHom R) x (Z k) - Poly.eval (intHom R) x (Z l))).sum := by
  rw [Bodies.eqn, eval_ps, eval_psum, List.map_map]
  congr 2
  refine List.map_congr_left fun l _ => ?_
  simp only [Function.comp_apply, eval_pm, Poly.eval_pow, Bodies.mu, Bodies.P, eval_V, eval_ps]

theorem eval_D (B : Bodies) (k l : ℕ) :
    Poly.eval (intHom R) x (B.D k l) = x (B.p0 + pairIdx k l) ^ 2 *
      (Poly.eval (intHom R) x (B.X k) - Poly.eval (intHom R) x (B.X l)) *
      (Poly.eval (intHom R) x (B.Y k) - Poly.eval (intHom R) x (B.Y l)) - 1 := by
  simp only [Bodies.D, eval_ps, eval_pm, Poly.eval_pow, Bodies.P, eval_V, eval_K, Int.cast_one]

theorem filt1 : ([1, 2, 3, 4].filter (· ≠ 1)) = [2, 3, 4] := rfl
theorem filt2 : ([1, 2, 3, 4].filter (· ≠ 2)) = [1, 3, 4] := rfl
theorem filt3 : ([1, 2, 3, 4].filter (· ≠ 3)) = [1, 2, 4] := rfl
theorem filt4 : ([1, 2, 3, 4].filter (· ≠ 4)) = [1, 2, 3] := rfl

theorem pI12 : pairIdx 1 2 = 0 := rfl
theorem pI13 : pairIdx 1 3 = 1 := rfl
theorem pI14 : pairIdx 1 4 = 2 := rfl
theorem pI21 : pairIdx 2 1 = 0 := rfl
theorem pI23 : pairIdx 2 3 = 3 := rfl
theorem pI24 : pairIdx 2 4 = 4 := rfl
theorem pI31 : pairIdx 3 1 = 1 := rfl
theorem pI32 : pairIdx 3 2 = 3 := rfl
theorem pI34 : pairIdx 3 4 = 5 := rfl
theorem pI41 : pairIdx 4 1 = 2 := rfl
theorem pI42 : pairIdx 4 2 = 4 := rfl
theorem pI43 : pairIdx 4 3 = 5 := rfl

theorem cs2 : (Fin.castSucc (2 : Fin 3) : Fin 4) = 2 := rfl

/-! ### `N4` -/

theorem n4_p0 : n4Bodies.p0 = 5 := rfl
theorem n4_mu0 : n4Bodies.mu0 = 11 := rfl

theorem n4_X1 : Poly.eval (intHom R) x (n4Bodies.X 1) = x 0 + 1 := by
  show Poly.eval (intHom R) x (pa (V 0) (K 1)) = _
  rw [eval_pa, eval_V, eval_K, Int.cast_one]

theorem n4_X2 : Poly.eval (intHom R) x (n4Bodies.X 2) = x 0 := eval_V x 0
theorem n4_X3 : Poly.eval (intHom R) x (n4Bodies.X 3) = x 1 := eval_V x 1

theorem n4_X4 : Poly.eval (intHom R) x (n4Bodies.X 4) =
    -((x 11 * (x 0 + 1) + x 12 * x 0 + x 13 * x 1) * x 15) := by
  show Poly.eval (intHom R) x
    (pm (K (-1)) (pm (psum [pm (V 11) (pa (V 0) (K 1)), pm (V 12) (V 0), pm (V 13) (V 1)]) (V 15))) = _
  simp only [eval_pm, eval_psum, eval_pa, eval_V, eval_K, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  push_cast
  ring

theorem n4_Y1 : Poly.eval (intHom R) x (n4Bodies.Y 1) = x 2 := eval_V x 2
theorem n4_Y2 : Poly.eval (intHom R) x (n4Bodies.Y 2) = x 3 := eval_V x 3
theorem n4_Y3 : Poly.eval (intHom R) x (n4Bodies.Y 3) = x 4 := eval_V x 4

theorem n4_Y4 : Poly.eval (intHom R) x (n4Bodies.Y 4) = -((x 11 * x 2 + x 12 * x 3 + x 13 * x 4) * x 15) := by
  show Poly.eval (intHom R) x
    (pm (K (-1)) (pm (psum [pm (V 11) (V 2), pm (V 12) (V 3), pm (V 13) (V 4)]) (V 15))) = _
  simp only [eval_pm, eval_psum, eval_V, eval_K, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

/-- **The equations of `S12` of the certificate project vanish** at a point `x` where the equations `rows12` of
`S12P` vanish (with the unknowns `x₀, …, x₁₀`, the masses `x₁₁, …, x₁₄`) and `x₁₄ x₁₅ = 1`. -/
theorem n4F_eval_zero (hu : x 14 * x 15 = 1)
    (hrows : ∀ j, CC6Full.Six.D88.rows12 (fun k : Fin 4 => x (11 + k)) (fun j : Fin 11 => x j) j = 0) :
    ∀ F ∈ n4F, Poly.eval (intHom R) x F = 0 := by
  have hr : ∀ j : Fin 12, CC6Full.Six.D88.rows12 (fun k : Fin 4 => x (11 + k)) (fun j : Fin 11 => x j) j = 0 :=
    hrows
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have h4 := hr 4
  have h5 := hr 5
  have h6 := hr 6
  have h7 := hr 7
  have h8 := hr 8
  have h9 := hr 9
  have h10 := hr 10
  have h11 := hr 11
  simp [CC6Full.Six.D88.rows12, CC6Full.Six.D88.rowX, CC6Full.Six.D88.rowY, CC6Full.Six.D88.rowD,
    CC6Full.Six.D88.rowD4, CC6Full.Six.D88.gX, CC6Full.Six.D88.gY, CC6Full.Six.D88.gmX, CC6Full.Six.D88.gmY,
    CC6Full.Six.D88.gp, Fin.sum_univ_four, cs2] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  intro F hF
  simp only [n4F, pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Bodies.Xeq, Bodies.Yeq, eval_eqn, eval_D, filt1, filt2, filt3, n4_p0, n4_mu0, pI12, pI13, pI14,
      pI21, pI23, pI24, pI31, pI32, pI34, n4_X1, n4_X2, n4_X3, n4_X4, n4_Y1, n4_Y2, n4_Y3, n4_Y4, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
  · linear_combination h0 - x 7 ^ 3 * (x 11 * (x 0 + 1) + x 12 * x 0 + x 13 * x 1) * hu
  · linear_combination h1 - x 9 ^ 3 * (x 11 * (x 0 + 1) + x 12 * x 0 + x 13 * x 1) * hu
  · linear_combination h2 - x 10 ^ 3 * (x 11 * (x 0 + 1) + x 12 * x 0 + x 13 * x 1) * hu
  · linear_combination h3 - x 7 ^ 3 * (x 11 * x 2 + x 12 * x 3 + x 13 * x 4) * hu
  · linear_combination h4 - x 9 ^ 3 * (x 11 * x 2 + x 12 * x 3 + x 13 * x 4) * hu
  · linear_combination h5 - x 10 ^ 3 * (x 11 * x 2 + x 12 * x 3 + x 13 * x 4) * hu
  · linear_combination h6
  · linear_combination h7
  · linear_combination x 15 ^ 2 * h8 + (-(x 7 ^ 2 * ((x 0 + 1) * x 15 * (x 14 * x 2 + (x 11 * x 2 + x 12 * x 3 +
      x 13 * x 4)) + x 2 * x 15 * (x 14 * (x 0 + 1) + (x 11 * (x 0 + 1) + x 12 * x 0 + x 13 * x 1)) -
      (x 14 * x 15 - 1) * (x 0 + 1) * x 2)) + (x 15 * x 14 + 1)) * hu
  · linear_combination h9
  · linear_combination x 15 ^ 2 * h10 + (-(x 9 ^ 2 * (x 0 * x 15 * (x 14 * x 3 + (x 11 * x 2 + x 12 * x 3 +
      x 13 * x 4)) + x 3 * x 15 * (x 14 * x 0 + (x 11 * (x 0 + 1) + x 12 * x 0 + x 13 * x 1)) -
      (x 14 * x 15 - 1) * x 0 * x 3)) + (x 15 * x 14 + 1)) * hu
  · linear_combination x 15 ^ 2 * h11 + (-(x 10 ^ 2 * (x 1 * x 15 * (x 14 * x 4 + (x 11 * x 2 + x 12 * x 3 +
      x 13 * x 4)) + x 4 * x 15 * (x 14 * x 1 + (x 11 * (x 0 + 1) + x 12 * x 0 + x 13 * x 1)) -
      (x 14 * x 15 - 1) * x 1 * x 4)) + (x 15 * x 14 + 1)) * hu

/-! ### `KC` -/

theorem kc_p0 : kcBodies.p0 = 6 := rfl
theorem kc_mu0 : kcBodies.mu0 = 12 := rfl

theorem kc_X1 : Poly.eval (intHom R) x (kcBodies.X 1) = 1 := by
  show Poly.eval (intHom R) x (K 1) = _
  rw [eval_K, Int.cast_one]

theorem kc_X2 : Poly.eval (intHom R) x (kcBodies.X 2) = x 0 := eval_V x 0
theorem kc_X3 : Poly.eval (intHom R) x (kcBodies.X 3) = x 1 := eval_V x 1

theorem kc_X4 : Poly.eval (intHom R) x (kcBodies.X 4) = 0 := by
  show Poly.eval (intHom R) x (K 0) = _
  rw [eval_K, Int.cast_zero]

theorem kc_Y1 : Poly.eval (intHom R) x (kcBodies.Y 1) = x 2 := eval_V x 2
theorem kc_Y2 : Poly.eval (intHom R) x (kcBodies.Y 2) = x 3 := eval_V x 3
theorem kc_Y3 : Poly.eval (intHom R) x (kcBodies.Y 3) = x 4 := eval_V x 4
theorem kc_Y4 : Poly.eval (intHom R) x (kcBodies.Y 4) = x 5 := eval_V x 5

/-- **The equations of `KC12` of the certificate project vanish** at a point `x` where the equations `KC12` of
`KC12P` vanish (with the unknowns `x₀, …, x₁₁`, the masses `x₁₂, …, x₁₅`). -/
theorem kcF_eval_zero
    (hrows : ∀ j, CC6Full.Six.D94.KC12 (fun k : Fin 4 => x (12 + k)) (fun j : Fin 12 => x j) j = 0) :
    ∀ F ∈ kcF, Poly.eval (intHom R) x F = 0 := by
  have hr : ∀ j : Fin 12, CC6Full.Six.D94.KC12 (fun k : Fin 4 => x (12 + k)) (fun j : Fin 12 => x j) j = 0 :=
    hrows
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have h4 := hr 4
  have h5 := hr 5
  have h6 := hr 6
  have h7 := hr 7
  have h8 := hr 8
  have h9 := hr 9
  have h10 := hr 10
  have h11 := hr 11
  simp [CC6Full.Six.D94.KC12, CC6Full.Six.D94.Xeq, CC6Full.Six.D94.Xc, CC6Full.Six.D94.Yeq,
    CC6Full.Six.D94.dist, CC6Full.Six.D94.X, CC6Full.Six.D94.Y, CC6Full.Six.D94.p, Fin.sum_univ_four]
    at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  intro F hF
  simp only [kcF, pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Bodies.Xeq, Bodies.Yeq, eval_eqn, eval_D, filt1, filt2, filt3, filt4, kc_p0, kc_mu0, pI12, pI13,
      pI14, pI21, pI23, pI24, pI31, pI32, pI34, pI41, pI42, pI43, kc_X1, kc_X2, kc_X3, kc_X4, kc_Y1, kc_Y2, kc_Y3,
      kc_Y4, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  · linear_combination h0
  · linear_combination h1
  · linear_combination h2
  · linear_combination -h3
  · linear_combination h4
  · linear_combination h5
  · linear_combination h6
  · linear_combination h7
  · linear_combination h8
  · linear_combination h9
  · linear_combination h10
  · linear_combination h11

/-! ### Units and the unknowns in the coordinates -/

theorem isUnit_of_dist {P a b : R} (h : P ^ 2 * a * b - 1 = 0) : IsUnit P ∧ IsUnit a ∧ IsUnit b :=
  ⟨IsUnit.of_mul_eq_one (P * a * b) (by linear_combination h),
    IsUnit.of_mul_eq_one (P ^ 2 * b) (by linear_combination h),
    IsUnit.of_mul_eq_one (P ^ 2 * a) (by linear_combination h)⟩

theorem dist_units (B : Bodies) {Fs : List (Poly ℤ)} (h : ∀ F ∈ Fs, Poly.eval (intHom R) x F = 0) {k l : ℕ}
    (hkl : B.D k l ∈ Fs) : IsUnit (x (B.p0 + pairIdx k l)) ∧
      IsUnit (Poly.eval (intHom R) x (B.X k) - Poly.eval (intHom R) x (B.X l)) ∧
      IsUnit (Poly.eval (intHom R) x (B.Y k) - Poly.eval (intHom R) x (B.Y l)) :=
  isUnit_of_dist (by rw [← eval_D]; exact h _ hkl)

/-- The coordinates `ξ(x)` of `N4` are units where the equations vanish (by the distance equations). -/
theorem n4σ_isUnit (h : ∀ F ∈ n4F, Poly.eval (intHom R) x F = 0) (i : ℕ) (hi : i < 17) :
    IsUnit (Poly.eval (intHom R) x (n4σ i)) := by
  have m12 : n4Bodies.D 1 2 ∈ n4F := by simp [n4F, pairs]
  have m13 : n4Bodies.D 1 3 ∈ n4F := by simp [n4F, pairs]
  have m14 : n4Bodies.D 1 4 ∈ n4F := by simp [n4F, pairs]
  have m23 : n4Bodies.D 2 3 ∈ n4F := by simp [n4F, pairs]
  have m24 : n4Bodies.D 2 4 ∈ n4F := by simp [n4F, pairs]
  have m34 : n4Bodies.D 3 4 ∈ n4F := by simp [n4F, pairs]
  have u12 := dist_units x n4Bodies h m12
  have u13 := dist_units x n4Bodies h m13
  have u14 := dist_units x n4Bodies h m14
  have u23 := dist_units x n4Bodies h m23
  have u24 := dist_units x n4Bodies h m24
  have u34 := dist_units x n4Bodies h m34
  simp only [n4_p0, pI12, pI13, pI14, pI23, pI24, pI34] at u12 u13 u14 u23 u24 u34
  interval_cases i
  · rw [show n4σ 0 = ps (n4Bodies.X 1) (n4Bodies.X 3) from rfl, eval_ps]; exact u13.2.1
  · rw [show n4σ 1 = ps (n4Bodies.X 1) (n4Bodies.X 4) from rfl, eval_ps]; exact u14.2.1
  · rw [show n4σ 2 = ps (n4Bodies.X 2) (n4Bodies.X 3) from rfl, eval_ps]; exact u23.2.1
  · rw [show n4σ 3 = ps (n4Bodies.X 2) (n4Bodies.X 4) from rfl, eval_ps]; exact u24.2.1
  · rw [show n4σ 4 = ps (n4Bodies.X 3) (n4Bodies.X 4) from rfl, eval_ps]; exact u34.2.1
  · rw [show n4σ 5 = ps (n4Bodies.Y 1) (n4Bodies.Y 2) from rfl, eval_ps]; exact u12.2.2
  · rw [show n4σ 6 = ps (n4Bodies.Y 1) (n4Bodies.Y 3) from rfl, eval_ps]; exact u13.2.2
  · rw [show n4σ 7 = ps (n4Bodies.Y 1) (n4Bodies.Y 4) from rfl, eval_ps]; exact u14.2.2
  · rw [show n4σ 8 = ps (n4Bodies.Y 2) (n4Bodies.Y 3) from rfl, eval_ps]; exact u23.2.2
  · rw [show n4σ 9 = ps (n4Bodies.Y 2) (n4Bodies.Y 4) from rfl, eval_ps]; exact u24.2.2
  · rw [show n4σ 10 = ps (n4Bodies.Y 3) (n4Bodies.Y 4) from rfl, eval_ps]; exact u34.2.2
  · rw [show n4σ 11 = V 5 from rfl, eval_V]; exact u12.1
  · rw [show n4σ 12 = V 6 from rfl, eval_V]; exact u13.1
  · rw [show n4σ 13 = V 7 from rfl, eval_V]; exact u14.1
  · rw [show n4σ 14 = V 8 from rfl, eval_V]; exact u23.1
  · rw [show n4σ 15 = V 9 from rfl, eval_V]; exact u24.1
  · rw [show n4σ 16 = V 10 from rfl, eval_V]; exact u34.1

/-- The coordinates `ξ(x)` of `KC` are units where the equations vanish. -/
theorem kcσ_isUnit (h : ∀ F ∈ kcF, Poly.eval (intHom R) x F = 0) (i : ℕ) (hi : i < 17) :
    IsUnit (Poly.eval (intHom R) x (kcσ i)) := by
  have m12 : kcBodies.D 1 2 ∈ kcF := by simp [kcF, pairs]
  have m13 : kcBodies.D 1 3 ∈ kcF := by simp [kcF, pairs]
  have m14 : kcBodies.D 1 4 ∈ kcF := by simp [kcF, pairs]
  have m23 : kcBodies.D 2 3 ∈ kcF := by simp [kcF, pairs]
  have m24 : kcBodies.D 2 4 ∈ kcF := by simp [kcF, pairs]
  have m34 : kcBodies.D 3 4 ∈ kcF := by simp [kcF, pairs]
  have u12 := dist_units x kcBodies h m12
  have u13 := dist_units x kcBodies h m13
  have u14 := dist_units x kcBodies h m14
  have u23 := dist_units x kcBodies h m23
  have u24 := dist_units x kcBodies h m24
  have u34 := dist_units x kcBodies h m34
  simp only [kc_p0, pI12, pI13, pI14, pI23, pI24, pI34, kc_X2, kc_X3, kc_X4, sub_zero] at u12 u13 u14 u23 u24 u34
  interval_cases i
  · rw [show kcσ 0 = V 0 from rfl, eval_V]; exact u24.2.1
  · rw [show kcσ 1 = V 1 from rfl, eval_V]; exact u34.2.1
  · rw [show kcσ 2 = ps (kcBodies.X 1) (kcBodies.X 2) from rfl, eval_ps, kc_X2]; exact u12.2.1
  · rw [show kcσ 3 = ps (kcBodies.X 1) (kcBodies.X 3) from rfl, eval_ps, kc_X3]; exact u13.2.1
  · rw [show kcσ 4 = ps (kcBodies.X 2) (kcBodies.X 3) from rfl, eval_ps, kc_X2, kc_X3]; exact u23.2.1
  · rw [show kcσ 5 = ps (kcBodies.Y 1) (kcBodies.Y 4) from rfl, eval_ps]; exact u14.2.2
  · rw [show kcσ 6 = ps (kcBodies.Y 2) (kcBodies.Y 4) from rfl, eval_ps]; exact u24.2.2
  · rw [show kcσ 7 = ps (kcBodies.Y 3) (kcBodies.Y 4) from rfl, eval_ps]; exact u34.2.2
  · rw [show kcσ 8 = ps (kcBodies.Y 1) (kcBodies.Y 2) from rfl, eval_ps]; exact u12.2.2
  · rw [show kcσ 9 = ps (kcBodies.Y 1) (kcBodies.Y 3) from rfl, eval_ps]; exact u13.2.2
  · rw [show kcσ 10 = ps (kcBodies.Y 2) (kcBodies.Y 3) from rfl, eval_ps]; exact u23.2.2
  · rw [show kcσ 11 = V 6 from rfl, eval_V]; exact u12.1
  · rw [show kcσ 12 = V 7 from rfl, eval_V]; exact u13.1
  · rw [show kcσ 13 = V 8 from rfl, eval_V]; exact u14.1
  · rw [show kcσ 14 = V 9 from rfl, eval_V]; exact u23.1
  · rw [show kcσ 15 = V 10 from rfl, eval_V]; exact u24.1
  · rw [show kcσ 16 = V 11 from rfl, eval_V]; exact u34.1

/-- The coordinates of `N4` used for the unknowns, and the masses. -/
theorem n4σ_vals :
    Poly.eval (intHom R) x (n4σ 2) = x 0 - x 1 ∧ Poly.eval (intHom R) x (n4σ 3) = x 0 + (x 11 * (x 0 + 1) +
      x 12 * x 0 + x 13 * x 1) * x 15 ∧
    Poly.eval (intHom R) x (n4σ 5) = x 2 - x 3 ∧ Poly.eval (intHom R) x (n4σ 6) = x 2 - x 4 ∧
    Poly.eval (intHom R) x (n4σ 7) = x 2 + (x 11 * x 2 + x 12 * x 3 + x 13 * x 4) * x 15 ∧
    Poly.eval (intHom R) x (n4σ 11) = x 5 ∧ Poly.eval (intHom R) x (n4σ 12) = x 6 ∧
    Poly.eval (intHom R) x (n4σ 13) = x 7 ∧ Poly.eval (intHom R) x (n4σ 14) = x 8 ∧
    Poly.eval (intHom R) x (n4σ 15) = x 9 ∧ Poly.eval (intHom R) x (n4σ 16) = x 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, eval_V x 5, eval_V x 6, eval_V x 7, eval_V x 8, eval_V x 9, eval_V x 10⟩
  · rw [show n4σ 2 = ps (n4Bodies.X 2) (n4Bodies.X 3) from rfl, eval_ps, n4_X2, n4_X3]
  · rw [show n4σ 3 = ps (n4Bodies.X 2) (n4Bodies.X 4) from rfl, eval_ps, n4_X2, n4_X4, sub_neg_eq_add]
  · rw [show n4σ 5 = ps (n4Bodies.Y 1) (n4Bodies.Y 2) from rfl, eval_ps, n4_Y1, n4_Y2]
  · rw [show n4σ 6 = ps (n4Bodies.Y 1) (n4Bodies.Y 3) from rfl, eval_ps, n4_Y1, n4_Y3]
  · rw [show n4σ 7 = ps (n4Bodies.Y 1) (n4Bodies.Y 4) from rfl, eval_ps, n4_Y1, n4_Y4, sub_neg_eq_add]

theorem n4σ_mass {k : ℕ} (hk : k < 4) : Poly.eval (intHom R) x (n4σ (17 + k)) = x (11 + k) := by
  interval_cases k <;> exact eval_V x _

/-- The unknowns `X₂` and `Y₁` of `N4` from the `X`-equation of body `2` and the `Y`-equation of body `1`. -/
theorem n4_hX (h : ∀ F ∈ n4F, Poly.eval (intHom R) x F = 0) :
    x 0 = -(x 11 * x 5 ^ 3) + x 13 * x 8 ^ 3 * (x 0 - x 1) +
      x 14 * x 9 ^ 3 * (x 0 + (x 11 * (x 0 + 1) + x 12 * x 0 + x 13 * x 1) * x 15) ∧
    x 2 = x 12 * x 5 ^ 3 * (x 2 - x 3) + x 13 * x 6 ^ 3 * (x 2 - x 4) +
      x 14 * x 7 ^ 3 * (x 2 + (x 11 * x 2 + x 12 * x 3 + x 13 * x 4) * x 15) := by
  have e1 := h (n4Bodies.Xeq 2) (by simp [n4F])
  have e2 := h (n4Bodies.Yeq 1) (by simp [n4F])
  simp only [Bodies.Xeq, Bodies.Yeq, eval_eqn, filt1, filt2, n4_p0, n4_mu0, pI12, pI13, pI14, pI21, pI23, pI24,
    n4_X1, n4_X2, n4_X3, n4_X4, n4_Y1, n4_Y2, n4_Y3, n4_Y4, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at e1 e2
  exact ⟨by linear_combination e1, by linear_combination e2⟩

/-- The coordinates of `KC` used for the unknowns, and the masses. -/
theorem kcσ_vals :
    Poly.eval (intHom R) x (kcσ 0) = x 0 ∧ Poly.eval (intHom R) x (kcσ 1) = x 1 ∧
    Poly.eval (intHom R) x (kcσ 5) = x 2 - x 5 ∧ Poly.eval (intHom R) x (kcσ 8) = x 2 - x 3 ∧
    Poly.eval (intHom R) x (kcσ 9) = x 2 - x 4 ∧
    Poly.eval (intHom R) x (kcσ 11) = x 6 ∧ Poly.eval (intHom R) x (kcσ 12) = x 7 ∧
    Poly.eval (intHom R) x (kcσ 13) = x 8 ∧ Poly.eval (intHom R) x (kcσ 14) = x 9 ∧
    Poly.eval (intHom R) x (kcσ 15) = x 10 ∧ Poly.eval (intHom R) x (kcσ 16) = x 11 := by
  refine ⟨eval_V x 0, eval_V x 1, ?_, ?_, ?_, eval_V x 6, eval_V x 7, eval_V x 8, eval_V x 9, eval_V x 10,
    eval_V x 11⟩
  · rw [show kcσ 5 = ps (kcBodies.Y 1) (kcBodies.Y 4) from rfl, eval_ps, kc_Y1, kc_Y4]
  · rw [show kcσ 8 = ps (kcBodies.Y 1) (kcBodies.Y 2) from rfl, eval_ps, kc_Y1, kc_Y2]
  · rw [show kcσ 9 = ps (kcBodies.Y 1) (kcBodies.Y 3) from rfl, eval_ps, kc_Y1, kc_Y3]

theorem kcσ_mass {k : ℕ} (hk : k < 4) : Poly.eval (intHom R) x (kcσ (17 + k)) = x (12 + k) := by
  interval_cases k <;> exact eval_V x _

/-- The unknown `Y₁` of `KC` from the `Y`-equation of body `1`. -/
theorem kc_hX (h : ∀ F ∈ kcF, Poly.eval (intHom R) x F = 0) :
    x 2 = x 13 * x 6 ^ 3 * (x 2 - x 3) + x 14 * x 7 ^ 3 * (x 2 - x 4) + x 15 * x 8 ^ 3 * (x 2 - x 5) := by
  have e := h (kcBodies.Yeq 1) (by simp [kcF])
  simp only [Bodies.Yeq, eval_eqn, filt1, kc_p0, kc_mu0, pI12, pI13, pI14, kc_Y1, kc_Y2, kc_Y3, kc_Y4,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e
  linear_combination e

end Eqns

/-! ## `goodred_torus_opt` for `S12` and `KC₁₂` -/

section Inst

open CC6Full MvPolynomial

local notation "𝒪" => Opt 65521 CC6Full.Six.μ0Z

theorem mk_aeval {m N : ℕ} (I : Ideal (MvPolynomial (Fin m) 𝒪)) (ξ : Fin N → MvPolynomial (Fin m) 𝒪)
    (q : MvPolynomial (Fin N) 𝒪) :
    Ideal.Quotient.mk I (aeval ξ q) = aeval (fun i => Ideal.Quotient.mk I (ξ i)) q := by
  rw [← Ideal.Quotient.mkₐ_eq_mk 𝒪, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]

/-- A polynomial of `G` over `O` at `ξ` is `flat g` of the certificate project at the point whose first seventeen
coordinates are `ξ` and whose coordinates `17, …, 20` are the masses. -/
theorem aeval_toMv {R : Type*} [CommRing R] [Algebra 𝒪 R] (ξR : Fin 17 → R) (y : ℕ → R)
    (hy : ∀ i : Fin 17, y i = ξR i) (hμ : ∀ k < 4, y (17 + k) = algebraMap 𝒪 R (μO k))
    {g : Comp.D88.Trop.GPoly} (hg : UnitsOK g) :
    aeval ξR (toMv g) = Poly.eval (intHom R) y (Comp.D88.Trop.flat g) := by
  rw [eval_flat y g fun t ht => (hg.1 t ht).2.1, toMv, map_sum, ← Fin.sum_univ_fun_getElem]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [aeval_monomial, mono17_prod ξR y hy _ (hg.1 _ (List.getElem_mem _)).2.1,
    mul_comm (algebraMap 𝒪 R (coefO g[i.1].2)), coefO, poly_eval_map (algebraMap 𝒪 R)]
  congr 1
  exact poly_eval_congr _ (fun k hk => (hμ k hk).symm) _ (hg.1 _ (List.getElem_mem _)).2.2

/-! ### `S12` -/

/-- The ideal of `S12P` over `O` (the ideal of `D88Int`). -/
abbrev I88 : Ideal (MvPolynomial (Fin 11) 𝒪) :=
  Ideal.span (Set.range fun i => MvPolynomial.map (algebraMap (MvPolynomial (Fin 4) ℤ) 𝒪) (Six.D88.S12P i))

/-- The variables of `N4` of the certificate project in `O[v]`: the unknowns `v₀, …, v₁₀`, the masses, `1/μ₄`. -/
def xO88 (k : ℕ) : MvPolynomial (Fin 11) 𝒪 :=
  if h : k < 11 then X ⟨k, h⟩ else if k < 15 then C (μO (k - 11)) else if k = 15 then C iu4 else 0

/-- The seventeen torus coordinates `ξ(v)` of `N4` over `O`. -/
def ξ88 (i : Fin 17) : MvPolynomial (Fin 11) 𝒪 := Poly.eval (intHom _) xO88 (Comp.D88.Trop.n4σ i)

/-- The variables of `N4` in `O[v]/I`. -/
def x88 (k : ℕ) : MvPolynomial (Fin 11) 𝒪 ⧸ I88 := Ideal.Quotient.mk I88 (xO88 k)

theorem x88_lt (j : Fin 11) : x88 j = Ideal.Quotient.mk I88 (X j) := by
  rw [x88, xO88, dite_eq_left j.2]

theorem x88_mass {k : ℕ} (hk : k < 4) : x88 (11 + k) = algebraMap 𝒪 _ (μO k) := by
  rw [x88, xO88, dite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]
  rfl

theorem x88_hu : x88 14 * x88 15 = 1 := by
  have h14 : xO88 14 = C (μO 3) := by simp [xO88]
  have h15 : xO88 15 = C iu4 := by simp [xO88]
  rw [x88, x88, h14, h15, ← map_mul, ← C_mul, μO_mul_iu4, C_1, map_one]

theorem x88_rows (j : Fin 12) :
    Six.D88.rows12 (fun k : Fin 4 => x88 (11 + k)) (fun j : Fin 11 => x88 j) j = 0 := by
  set f : MvPolynomial (Fin 11) (MvPolynomial (Fin 4) ℤ) →+* MvPolynomial (Fin 11) 𝒪 ⧸ I88 :=
    (Ideal.Quotient.mk I88).comp (MvPolynomial.map (algebraMap (MvPolynomial (Fin 4) ℤ) 𝒪)) with hf
  have hμ : (fun k : Fin 4 => x88 (11 + k)) = fun k => f (C (X k)) := by
    funext k
    rw [x88_mass k.2, hf, RingHom.comp_apply, map_C, μO_fin]
    rfl
  have hv : (fun j : Fin 11 => x88 j) = fun j => f (X j) := by
    funext j
    rw [x88_lt, hf, RingHom.comp_apply, map_X]
  have e := Six.D88.map_rows12 f (fun k => C (X k)) X j
  rw [hμ, hv, ← e]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

theorem mk_ξ88 (i : Fin 17) :
    Ideal.Quotient.mk I88 (ξ88 i) = Poly.eval (intHom _) x88 (Comp.D88.Trop.n4σ i) := by
  rw [ξ88, poly_eval_map]
  rfl

theorem n4F_x88 : ∀ F ∈ Comp.D88.Trop.n4F, Poly.eval (intHom _) x88 F = 0 :=
  n4F_eval_zero x88 x88_hu x88_rows

/-- The coordinates `ξ` are units modulo the ideal of `S12`. -/
theorem hξ88 (i : Fin 17) : IsUnit (Ideal.Quotient.mk I88 (ξ88 i)) := by
  rw [mk_ξ88]
  exact n4σ_isUnit x88 n4F_x88 i i.2

/-- The unknowns of `S12` as polynomials in `ξ` over `O`, modulo the ideal: `X₂` and `Y₁` from the `X`-equation of
body `2` and the `Y`-equation of body `1`, the others by differences. -/
def q88 : Fin 11 → MvPolynomial (Fin 17) 𝒪 :=
  ![-(C (μO 0) * X 11 ^ 3) + C (μO 2) * X 14 ^ 3 * X 2 + C (μO 3) * X 15 ^ 3 * X 3,
    -(C (μO 0) * X 11 ^ 3) + C (μO 2) * X 14 ^ 3 * X 2 + C (μO 3) * X 15 ^ 3 * X 3 - X 2,
    C (μO 1) * X 11 ^ 3 * X 5 + C (μO 2) * X 12 ^ 3 * X 6 + C (μO 3) * X 13 ^ 3 * X 7,
    C (μO 1) * X 11 ^ 3 * X 5 + C (μO 2) * X 12 ^ 3 * X 6 + C (μO 3) * X 13 ^ 3 * X 7 - X 5,
    C (μO 1) * X 11 ^ 3 * X 5 + C (μO 2) * X 12 ^ 3 * X 6 + C (μO 3) * X 13 ^ 3 * X 7 - X 6,
    X 11, X 12, X 13, X 14, X 15, X 16]

theorem hX88 (j : Fin 11) : ∃ q : MvPolynomial (Fin 17) 𝒪, X j - aeval ξ88 q ∈ I88 := by
  refine ⟨q88 j, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, mk_aeval, ← x88_lt]
  simp only [mk_ξ88]
  obtain ⟨s2, s3, s5, s6, s7, s11, s12, s13, s14, s15, s16⟩ := n4σ_vals x88
  obtain ⟨e0, e2⟩ := n4_hX x88 n4F_x88
  have m0 : algebraMap 𝒪 _ (μO 0) = x88 11 := (x88_mass (k := 0) (by norm_num)).symm
  have m1 : algebraMap 𝒪 _ (μO 1) = x88 12 := (x88_mass (k := 1) (by norm_num)).symm
  have m2 : algebraMap 𝒪 _ (μO 2) = x88 13 := (x88_mass (k := 2) (by norm_num)).symm
  have m3 : algebraMap 𝒪 _ (μO 3) = x88 14 := (x88_mass (k := 3) (by norm_num)).symm
  fin_cases j <;> simp [q88, s2, s3, s5, s6, s7, s11, s12, s13, s14, s15, s16, m0, m1, m2, m3] <;>
    first | linear_combination e0 | linear_combination e2

theorem unitsN4_of (hu : type_of% @Lean6.Special.Comp.D88.Trop.n4_units_ok) :
    ∀ g ∈ Comp.D88.Trop.GN4, UnitsOK g :=
  unitsOK_of_check hu

theorem unitsN4 : ∀ g ∈ Comp.D88.Trop.GN4, UnitsOK g := unitsN4_of Comp.D88.Trop.n4_units_ok

theorem hG88_of (hu : type_of% @Lean6.Special.Comp.D88.Trop.n4_units_ok) :
    ∀ g ∈ Gset Comp.D88.Trop.GN4, ∀ α ∈ g.support, IsUnit (g.coeff α) := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := mem_Gset.mp hg
  exact toMv_isUnit (unitsN4_of hu g₀ hg₀)

/-- The polynomials of `G` at `ξ` lie in the ideal of `S12`: the membership identities `n4_G_mem` at the point `x88`
of `O[v]/I`, where the equations of the certificate project vanish. -/
theorem hGI88_of (hu : type_of% @Lean6.Special.Comp.D88.Trop.n4_units_ok)
    (hm : type_of% @Lean6.Special.D88.Trop.n4_G_mem.{0}) :
    ∀ g ∈ Gset Comp.D88.Trop.GN4, aeval ξ88 g ∈ I88 := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := mem_Gset.mp hg
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg₀
  rw [← Ideal.Quotient.eq_zero_iff_mem, mk_aeval,
    aeval_toMv _ (fun j => Poly.eval (intHom _) x88 (Comp.D88.Trop.n4σ j)) (fun i => (mk_ξ88 i).symm)
      (fun k hk => by rw [n4σ_mass x88 hk, x88_mass hk]) (unitsN4_of hu _ hg₀),
    hm i hi x88 x88_hu]
  refine List.sum_eq_zero fun a ha => ?_
  obtain ⟨cf, hcf, rfl⟩ := List.mem_map.mp ha
  rw [n4F_x88 cf.2 (List.of_mem_zip hcf).2, mul_zero]

theorem hcert88_of (hu : type_of% @Lean6.Special.Comp.D88.Trop.n4_units_ok)
    (ht : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0}) :
    TropCertTorusOpt 65521 Six.μ0Z (Gset Comp.D88.Trop.GN4) :=
  tropCert_of_torus _ (unitsN4_of hu) (by intro Γ _ _ _ w hw; exact ht w hw)

/-! ### `KC₁₂` -/

/-- The ideal of `KC12P` over `O` (the ideal of `D94Int`). -/
abbrev I94 : Ideal (MvPolynomial (Fin 12) 𝒪) :=
  Ideal.span (Set.range fun i => MvPolynomial.map (algebraMap (MvPolynomial (Fin 4) ℤ) 𝒪) (Six.D94.KC12P i))

/-- The variables of `KC` of the certificate project in `O[v]`: the unknowns `v₀, …, v₁₁`, the masses, `1/μ₃`. -/
def xO94 (k : ℕ) : MvPolynomial (Fin 12) 𝒪 :=
  if h : k < 12 then X ⟨k, h⟩ else if k < 16 then C (μO (k - 12)) else if k = 16 then C iu3 else 0

/-- The seventeen torus coordinates `ξ(v)` of `KC` over `O`. -/
def ξ94 (i : Fin 17) : MvPolynomial (Fin 12) 𝒪 := Poly.eval (intHom _) xO94 (Comp.D88.Trop.kcσ i)

/-- The variables of `KC` in `O[v]/I`. -/
def x94 (k : ℕ) : MvPolynomial (Fin 12) 𝒪 ⧸ I94 := Ideal.Quotient.mk I94 (xO94 k)

theorem x94_lt (j : Fin 12) : x94 j = Ideal.Quotient.mk I94 (X j) := by
  rw [x94, xO94, dite_eq_left j.2]

theorem x94_mass {k : ℕ} (hk : k < 4) : x94 (12 + k) = algebraMap 𝒪 _ (μO k) := by
  rw [x94, xO94, dite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]
  rfl

theorem x94_hu : x94 14 * x94 16 = 1 := by
  have h14 : xO94 14 = C (μO 2) := by simp [xO94]
  have h16 : xO94 16 = C iu3 := by simp [xO94]
  rw [x94, x94, h14, h16, ← map_mul, ← C_mul, μO_mul_iu3, C_1, map_one]

theorem x94_rows (j : Fin 12) :
    Six.D94.KC12 (fun k : Fin 4 => x94 (12 + k)) (fun j : Fin 12 => x94 j) j = 0 := by
  set f : MvPolynomial (Fin 12) (MvPolynomial (Fin 4) ℤ) →+* MvPolynomial (Fin 12) 𝒪 ⧸ I94 :=
    (Ideal.Quotient.mk I94).comp (MvPolynomial.map (algebraMap (MvPolynomial (Fin 4) ℤ) 𝒪)) with hf
  have hμ : (fun k : Fin 4 => x94 (12 + k)) = fun k => f (C (X k)) := by
    funext k
    rw [x94_mass k.2, hf, RingHom.comp_apply, map_C, μO_fin]
    rfl
  have hv : (fun j : Fin 12 => x94 j) = fun j => f (X j) := by
    funext j
    rw [x94_lt, hf, RingHom.comp_apply, map_X]
  have e := Six.D94.map_KC12 f (fun k => C (X k)) X j
  rw [hμ, hv, ← e]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

theorem mk_ξ94 (i : Fin 17) :
    Ideal.Quotient.mk I94 (ξ94 i) = Poly.eval (intHom _) x94 (Comp.D88.Trop.kcσ i) := by
  rw [ξ94, poly_eval_map]
  rfl

theorem kcF_x94 : ∀ F ∈ Comp.D88.Trop.kcF, Poly.eval (intHom _) x94 F = 0 :=
  kcF_eval_zero x94 x94_rows

/-- The coordinates `ξ` are units modulo the ideal of `KC₁₂`. -/
theorem hξ94 (i : Fin 17) : IsUnit (Ideal.Quotient.mk I94 (ξ94 i)) := by
  rw [mk_ξ94]
  exact kcσ_isUnit x94 kcF_x94 i i.2

/-- The unknowns of `KC₁₂` as polynomials in `ξ` over `O`, modulo the ideal: `Y₁` from the `Y`-equation of body `1`,
the others by differences or directly. -/
def q94 : Fin 12 → MvPolynomial (Fin 17) 𝒪 :=
  ![X 0, X 1,
    C (μO 1) * X 11 ^ 3 * X 8 + C (μO 2) * X 12 ^ 3 * X 9 + C (μO 3) * X 13 ^ 3 * X 5,
    C (μO 1) * X 11 ^ 3 * X 8 + C (μO 2) * X 12 ^ 3 * X 9 + C (μO 3) * X 13 ^ 3 * X 5 - X 8,
    C (μO 1) * X 11 ^ 3 * X 8 + C (μO 2) * X 12 ^ 3 * X 9 + C (μO 3) * X 13 ^ 3 * X 5 - X 9,
    C (μO 1) * X 11 ^ 3 * X 8 + C (μO 2) * X 12 ^ 3 * X 9 + C (μO 3) * X 13 ^ 3 * X 5 - X 5,
    X 11, X 12, X 13, X 14, X 15, X 16]

theorem hX94 (j : Fin 12) : ∃ q : MvPolynomial (Fin 17) 𝒪, X j - aeval ξ94 q ∈ I94 := by
  refine ⟨q94 j, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, mk_aeval, ← x94_lt]
  simp only [mk_ξ94]
  obtain ⟨s0, s1, s5, s8, s9, s11, s12, s13, s14, s15, s16⟩ := kcσ_vals x94
  have e2 := kc_hX x94 kcF_x94
  have m1 : algebraMap 𝒪 _ (μO 1) = x94 13 := (x94_mass (k := 1) (by norm_num)).symm
  have m2 : algebraMap 𝒪 _ (μO 2) = x94 14 := (x94_mass (k := 2) (by norm_num)).symm
  have m3 : algebraMap 𝒪 _ (μO 3) = x94 15 := (x94_mass (k := 3) (by norm_num)).symm
  fin_cases j <;> simp [q94, s0, s1, s5, s8, s9, s11, s12, s13, s14, s15, s16, m1, m2, m3] <;>
    linear_combination e2

theorem unitsKC_of (hu : type_of% @Lean6.Special.Comp.D88.Trop.kc_units_ok) :
    ∀ g ∈ Comp.D88.Trop.GKC, UnitsOK g :=
  unitsOK_of_check hu

theorem unitsKC : ∀ g ∈ Comp.D88.Trop.GKC, UnitsOK g := unitsKC_of Comp.D88.Trop.kc_units_ok

theorem hG94_of (hu : type_of% @Lean6.Special.Comp.D88.Trop.kc_units_ok) :
    ∀ g ∈ Gset Comp.D88.Trop.GKC, ∀ α ∈ g.support, IsUnit (g.coeff α) := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := mem_Gset.mp hg
  exact toMv_isUnit (unitsKC_of hu g₀ hg₀)

/-- The polynomials of `G` at `ξ` lie in the ideal of `KC₁₂`: the membership identities `kc_G_mem` at the point
`x94` of `O[v]/I`. -/
theorem hGI94_of (hu : type_of% @Lean6.Special.Comp.D88.Trop.kc_units_ok)
    (hm : type_of% @Lean6.Special.D88.Trop.kc_G_mem.{0}) :
    ∀ g ∈ Gset Comp.D88.Trop.GKC, aeval ξ94 g ∈ I94 := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := mem_Gset.mp hg
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg₀
  rw [← Ideal.Quotient.eq_zero_iff_mem, mk_aeval,
    aeval_toMv _ (fun j => Poly.eval (intHom _) x94 (Comp.D88.Trop.kcσ j)) (fun i => (mk_ξ94 i).symm)
      (fun k hk => by rw [kcσ_mass x94 hk, x94_mass hk]) (unitsKC_of hu _ hg₀),
    hm i hi x94 x94_hu]
  refine List.sum_eq_zero fun a ha => ?_
  obtain ⟨cf, hcf, rfl⟩ := List.mem_map.mp ha
  rw [kcF_x94 cf.2 (List.of_mem_zip hcf).2, mul_zero]

theorem hcert94_of (hu : type_of% @Lean6.Special.Comp.D88.Trop.kc_units_ok)
    (ht : type_of% @Lean6.Special.D88.Trop.kc_torus_gamma.{0}) :
    TropCertTorusOpt 65521 Six.μ0Z (Gset Comp.D88.Trop.GKC) :=
  tropCert_of_torus _ (unitsKC_of hu) (by intro Γ _ _ _ w hw; exact ht w hw)

end Inst

end

end CC6Compose.Integ

namespace CC6Compose

open CC6Compose.Integ

/-- **`D88Int`** (Lemma 6.18 with Lemma 6.19 (a) for `S12`): `goodred_torus_opt` with the coordinates `ξ` of the
certificate project, the set `G` of `GN4` over `O`, the coefficient check, the membership identities and the torus
statement. -/
theorem d88Int_of (hu : type_of% @Lean6.Special.Comp.D88.Trop.n4_units_ok)
    (hm : type_of% @Lean6.Special.D88.Trop.n4_G_mem.{0}) (ht : type_of% @Lean6.Special.D88.Trop.n4_torus_gamma.{0}) :
    CC6Full.Six.D88Int :=
  CC6Full.goodred_torus_opt 65521 CC6Full.Six.μ0Z I88 ξ88 hξ88 hX88 (Gset Lean6.Special.Comp.D88.Trop.GN4)
    (hG88_of hu) (hGI88_of hu hm) (hcert88_of hu ht)

theorem d88Int : CC6Full.Six.D88Int :=
  d88Int_of Lean6.Special.Comp.D88.Trop.n4_units_ok Lean6.Special.D88.Trop.n4_G_mem
    Lean6.Special.D88.Trop.n4_torus_gamma

/-- **`D94Int`** (Lemma 6.18 with Lemma 6.19 (a) for `KC₁₂`). -/
theorem d94Int_of (hu : type_of% @Lean6.Special.Comp.D88.Trop.kc_units_ok)
    (hm : type_of% @Lean6.Special.D88.Trop.kc_G_mem.{0}) (ht : type_of% @Lean6.Special.D88.Trop.kc_torus_gamma.{0}) :
    CC6Full.Six.D94Int :=
  CC6Full.goodred_torus_opt 65521 CC6Full.Six.μ0Z I94 ξ94 hξ94 hX94 (Gset Lean6.Special.Comp.D88.Trop.GKC)
    (hG94_of hu) (hGI94_of hu hm) (hcert94_of hu ht)

theorem d94Int : CC6Full.Six.D94Int :=
  d94Int_of Lean6.Special.Comp.D88.Trop.kc_units_ok Lean6.Special.D88.Trop.kc_G_mem
    Lean6.Special.D88.Trop.kc_torus_gamma

end CC6Compose
