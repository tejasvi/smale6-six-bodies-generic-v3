import CC6Full.Curve.ConstU
import CC6Full.Curve.Balancing
import CC6Full.Curve.CorU
import CC6Full.Germ.Basic

/-!
# Places give germs (Lemma 2.5, `lem:place`); a germ with `ℓ ≤ 0` (Part I)

Lemma 2.5 (`lem:place`):

> Let `P` be a singular place. Every component of `𝒵` and of `𝒲` has exponent at least `−2`, and each of the two
> vectors has a component of exponent `−2`. Let `t` be a local parameter at `P` and `ϑ² = t`. After the point of `C`
> near `P` is rotated by `s = ϑ^{2γ}`, every function `f` of the three kinds that does not vanish identically on `C`
> becomes `f = ϑ^{d e(f)} y_f(ϑ)` with `y_f ∈ ℂ{ϑ}`, `y_f(0) ≠ 0` and `d e(f) ∈ ℤ`.

Formal version. Let `ι : ℂ(C) → ℂ((t))` be an expansion at `P` (`Place.Expansion`, from `Expansion_exists`). In the
variable `τ = ϑ^d`, so that `t = τ^{2/d}` and `s = τ^{2γ/d}`:

* `Curve.tauEmb c : ℂ((t)) → HahnSeries ℚ ℂ`, `t ↦ τ^c`, multiplies orders by `c` (`Curve.orderTop_tauEmb`);
* `Curve.placeHom E hP = tauEmb (2/d) ∘ ι ∘ fn` (`Φ`): a ring hom `ℂ[Coord] → HahnSeries ℚ ℂ`, the identity on `ℂ`,
  killing the ideal of `C`, with `ord Φ(f) = (2/d) ν(f)`;
* `Place.rotS = τ^{2γ/d}`, `Place.rotSinv = τ^{−2γ/d}`; the series `s Φ(z_k)`, `s⁻¹ Φ(w_k)`, `Φ(p_kl)` have the
  orders `e(z_k) = (2/d)(ν(z_k) + γ)`, `e(w_k) = (2/d)(ν(w_k) − γ)`, `e(p_kl) = (2/d) ν(p_kl)`, and
  `(2/d)(ν(f) + γ) = −2 + (2/d)(ν(f) − ν(𝒵))` (`Place.exponent_z`), `(2/d)(ν(f) − γ) = −2 + (2/d)(ν(f) − ν(𝒲))`
  (`Place.exponent_w`). Since `ν(𝒵)`, `ν(𝒲)` are minima over the components, the components of `𝒵`, `𝒲` have
  exponents `≥ −2` with equality at a component of minimal order: the first statement of Lemma 2.5
  (`Curve.lowAt_z`, `Curve.lowAt_w`).

`germOfPlace hC hP E` is the germ (`Germ`, `CC6Full/Germ/Basic.lean`) of the singular place `P` of the nontrivial
curve `C`: the rows give the equations of the bodies and the distance equations (the rotation factors out of the
equations of the bodies and cancels in the distance equations), and `U = E` with `E ≠ 0` comes from Lemma 2.3 (b)
(`Curve.U_const`) and `U ∉ I(C)`. Its type is the type of `P` (`germOfPlace_x`), so `ℓ` of the germ is `ℓ(x(P))`
(`germOfPlace_ell`, and `germ_of_place` in existential form). Any masses.

`exists_germ`: if positive masses have infinitely many central configurations up to similarity, there is a germ with
`ℓ ≤ 0` (Corollary 2.4 `cor:curve`, Corollary 2.7 `cor:sum`, `Expansion_exists`, `germOfPlace`).
-/

namespace CC6Full

open Finset MvPolynomial

noncomputable section

namespace Curve

/-! ## `t ↦ τ^c` -/

section tau

/-- `k ↦ c k`, an order embedding `ℤ ↪o ℚ` for `c > 0`. -/
def scaleEmb (c : ℚ) (hc : 0 < c) : ℤ ↪o ℚ :=
  OrderEmbedding.ofStrictMono (fun k : ℤ => c * k) fun a b hab => by
    have : (a : ℚ) < b := by exact_mod_cast hab
    exact mul_lt_mul_of_pos_left this hc

theorem scaleEmb_apply (c : ℚ) (hc : 0 < c) (k : ℤ) : scaleEmb c hc k = c * k := rfl

/-- The ring hom `ℂ((t)) → HahnSeries ℚ ℂ`, `t ↦ τ^c`. -/
def tauEmb (c : ℚ) (hc : 0 < c) : LaurentSeries ℂ →+* Ser where
  toFun := HahnSeries.embDomain (scaleEmb c hc)
  map_one' := HahnSeries.embDomain_one _ (by rw [scaleEmb_apply, Int.cast_zero, mul_zero])
  map_mul' := HahnSeries.embDomain_mul _ (fun x y => by
    rw [scaleEmb_apply, scaleEmb_apply, scaleEmb_apply, Int.cast_add, mul_add])
  map_zero' := HahnSeries.embDomain_zero
  map_add' := HahnSeries.embDomain_add _

theorem tauEmb_apply (c : ℚ) (hc : 0 < c) (x : LaurentSeries ℂ) :
    tauEmb c hc x = HahnSeries.embDomain (scaleEmb c hc) x := rfl

theorem tauEmb_C (c : ℚ) (hc : 0 < c) (a : ℂ) : tauEmb c hc (HahnSeries.C a) = HahnSeries.C a := by
  rw [HahnSeries.C_apply, tauEmb_apply, HahnSeries.embDomain_single, scaleEmb_apply, Int.cast_zero, mul_zero,
    ← HahnSeries.C_apply]

/-- `t ↦ τ^c` multiplies orders by `c`. -/
theorem orderTop_tauEmb (c : ℚ) (hc : 0 < c) (x : LaurentSeries ℂ) :
    (tauEmb c hc x).orderTop = WithTop.map (scaleEmb c hc) x.orderTop := by
  rw [tauEmb_apply, HahnSeries.orderTop_embDomain]

end tau

end Curve

open Curve

/-! ## The rotation and the exponents at a singular place -/

section rotation

variable {N : ℕ} {C : ACurve (Coord N)} (P : Place C)

theorem Place.two_div_dd_pos (hP : P.Singular) : 0 < 2 / P.dd := div_pos two_pos (P.dd_pos hP)

/-- The rotation `s = τ^{2γ/d}` of Lemma 2.5 (`s = ϑ^{2γ}` with `ϑ = τ^{1/d}`). -/
def Place.rotS : Ser := HahnSeries.single (2 / P.dd * P.gamma) 1

/-- The inverse rotation `s⁻¹ = τ^{−2γ/d}`. -/
def Place.rotSinv : Ser := HahnSeries.single (-(2 / P.dd * P.gamma)) 1

theorem Place.rotS_mul_rotSinv : P.rotS * P.rotSinv = 1 := by
  rw [Place.rotS, Place.rotSinv, HahnSeries.single_mul_single, add_neg_cancel, mul_one,
    HahnSeries.single_zero_one]

theorem Place.orderTop_rotS_mul (x : Ser) :
    (P.rotS * x).orderTop = ((2 / P.dd * P.gamma : ℚ) : WithTop ℚ) + x.orderTop := by
  rw [HahnSeries.orderTop_mul, Place.rotS, HahnSeries.orderTop_single one_ne_zero]

theorem Place.orderTop_rotSinv_mul (x : Ser) :
    (P.rotSinv * x).orderTop = ((-(2 / P.dd * P.gamma) : ℚ) : WithTop ℚ) + x.orderTop := by
  rw [HahnSeries.orderTop_mul, Place.rotSinv, HahnSeries.orderTop_single one_ne_zero]

/-- At a singular place with `ν(𝒵) = zv`, `ν(𝒲) = wv`: `γ = −d − zv = d + wv`. -/
theorem Place.gamma_eq (hP : P.Singular) {zv wv : ℤ} (hz : P.vZ = zv) (hw : P.vW = wv) :
    P.gamma = -P.dd - zv ∧ P.gamma = P.dd + wv := by
  obtain ⟨zv', wv', hz', hw', -, hd, hg⟩ := P.exists_of_singular hP
  have h1 : zv' = zv := WithTop.coe_injective (hz'.symm.trans hz)
  have h2 : wv' = wv := WithTop.coe_injective (hw'.symm.trans hw)
  subst h1 h2
  rw [hd, hg]
  push_cast
  constructor <;> ring

/-- The exponent of a function of `z`-type: `(2/d)(ν(f) + γ) = −2 + (2/d)(ν(f) − ν(𝒵))`. -/
theorem Place.exponent_z (hP : P.Singular) {zv wv : ℤ} (hz : P.vZ = zv) (hw : P.vW = wv) (a : ℚ) :
    2 / P.dd * P.gamma + 2 / P.dd * a = -2 + 2 / P.dd * (a - zv) := by
  have hd := (P.dd_pos hP).ne'
  rw [(P.gamma_eq hP hz hw).1]
  field_simp
  ring

/-- The exponent of a function of `w`-type: `(2/d)(ν(f) − γ) = −2 + (2/d)(ν(f) − ν(𝒲))`. -/
theorem Place.exponent_w (hP : P.Singular) {zv wv : ℤ} (hz : P.vZ = zv) (hw : P.vW = wv) (a : ℚ) :
    -(2 / P.dd * P.gamma) + 2 / P.dd * a = -2 + 2 / P.dd * (a - wv) := by
  have hd := (P.dd_pos hP).ne'
  rw [(P.gamma_eq hP hz hw).2]
  field_simp
  ring

end rotation

namespace Curve

/-! ## The expansions at a singular place of a curve in `Y_m` -/

section germ

variable {n : ℕ} {m : Fin (n + 2) → ℝ} {C : Curve n m} {P : Place C.toACurve}

/-- `Φ(f) = ι(f)(τ^{2/d})`: the expansion of `f` at the singular place `P` in the variable `τ = t^{d/2}`. -/
def placeHom (E : P.Expansion) (hP : P.Singular) : Poly (n + 2) →+* Ser :=
  (tauEmb (2 / P.dd) (P.two_div_dd_pos hP)).comp (E.ι.comp C.fnHom)

theorem placeHom_apply (E : P.Expansion) (hP : P.Singular) (f : Poly (n + 2)) :
    placeHom E hP f = tauEmb (2 / P.dd) (P.two_div_dd_pos hP) (E.ι (C.fn f)) := rfl

theorem placeHom_C (E : P.Expansion) (hP : P.Singular) (a : ℂ) : placeHom E hP (MvPolynomial.C a) = cS a := by
  rw [placeHom_apply, E.map_const, tauEmb_C]

theorem placeHom_eq_zero (E : P.Expansion) (hP : P.Singular) {f : Poly (n + 2)} (hf : f ∈ C.ideal) :
    placeHom E hP f = 0 := by
  rw [placeHom_apply, ACurve.fn_eq_zero_iff.mpr hf, map_zero, map_zero]

/-- The order of `Φ(f)` is `(2/d) ν(f)`. -/
theorem orderTop_placeHom_of_eq (E : P.Expansion) (hP : P.Singular) {f : Poly (n + 2)} {a : ℤ} (hf : P.v f = a) :
    (placeHom E hP f).orderTop = ((2 / P.dd * a : ℚ) : WithTop ℚ) := by
  rw [placeHom_apply, orderTop_tauEmb, E.orderTop_eq]
  change WithTop.map _ (P.v f) = _
  rw [hf, WithTop.map_coe, scaleEmb_apply]

/-- The exponent `e(f) = (2/d)(ν(f) + γ)` of a function of `z`-type (Lemma 2.5): the order of `s Φ(f)`. -/
theorem orderTop_rotS_mul_placeHom (E : P.Expansion) (hP : P.Singular) {zv wv : ℤ} (hz : P.vZ = zv)
    (hw : P.vW = wv) {f : Poly (n + 2)} {a : ℤ} (hf : P.v f = a) :
    (P.rotS * placeHom E hP f).orderTop = ((-2 + 2 / P.dd * (a - zv) : ℚ) : WithTop ℚ) := by
  rw [P.orderTop_rotS_mul, orderTop_placeHom_of_eq E hP hf, ← WithTop.coe_add, P.exponent_z hP hz hw]

/-- The exponent `e(f) = (2/d)(ν(f) − γ)` of a function of `w`-type (Lemma 2.5): the order of `s⁻¹ Φ(f)`. -/
theorem orderTop_rotSinv_mul_placeHom (E : P.Expansion) (hP : P.Singular) {zv wv : ℤ} (hz : P.vZ = zv)
    (hw : P.vW = wv) {f : Poly (n + 2)} {a : ℤ} (hf : P.v f = a) :
    (P.rotSinv * placeHom E hP f).orderTop = ((-2 + 2 / P.dd * (a - wv) : ℚ) : WithTop ℚ) := by
  rw [P.orderTop_rotSinv_mul, orderTop_placeHom_of_eq E hP hf, ← WithTop.coe_add, P.exponent_w hP hz hw]

/-- A function of `z`-type with `ν(f) ≥ ν(𝒵)` has exponent `≥ −2`. -/
theorem neg_two_le_orderTop_z (E : P.Expansion) (hP : P.Singular) {f : Poly (n + 2)} (hf : P.vZ ≤ P.v f) :
    ((-2 : ℚ) : WithTop ℚ) ≤ (P.rotS * placeHom E hP f).orderTop := by
  obtain ⟨zv, wv, hz, hw, -, -, -⟩ := P.exists_of_singular hP
  rcases eq_or_ne (P.v f) ⊤ with htop | hne
  · rw [placeHom_eq_zero E hP ((P.v_eq_top_iff f).mp htop), mul_zero, HahnSeries.orderTop_zero]
    exact le_top
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [orderTop_rotS_mul_placeHom E hP hz hw ha.symm, WithTop.coe_le_coe]
    rw [hz, ← ha] at hf
    have h1 : (zv : ℚ) ≤ a := by exact_mod_cast hf
    have h2 : 0 ≤ 2 / P.dd * ((a : ℚ) - zv) := mul_nonneg (P.two_div_dd_pos hP).le (by linarith)
    linarith

/-- A function of `w`-type with `ν(f) ≥ ν(𝒲)` has exponent `≥ −2`. -/
theorem neg_two_le_orderTop_w (E : P.Expansion) (hP : P.Singular) {f : Poly (n + 2)} (hf : P.vW ≤ P.v f) :
    ((-2 : ℚ) : WithTop ℚ) ≤ (P.rotSinv * placeHom E hP f).orderTop := by
  obtain ⟨zv, wv, hz, hw, -, -, -⟩ := P.exists_of_singular hP
  rcases eq_or_ne (P.v f) ⊤ with htop | hne
  · rw [placeHom_eq_zero E hP ((P.v_eq_top_iff f).mp htop), mul_zero, HahnSeries.orderTop_zero]
    exact le_top
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [orderTop_rotSinv_mul_placeHom E hP hz hw ha.symm, WithTop.coe_le_coe]
    rw [hw, ← ha] at hf
    have h1 : (wv : ℚ) ≤ a := by exact_mod_cast hf
    have h2 : 0 ≤ 2 / P.dd * ((a : ℚ) - wv) := mul_nonneg (P.two_div_dd_pos hP).le (by linarith)
    linarith

/-- A function of `z`-type with `ν(f) = ν(𝒵)` has exponent `−2`. -/
theorem orderTop_z_eq_neg_two (E : P.Expansion) (hP : P.Singular) {f : Poly (n + 2)} (hf : P.v f = P.vZ) :
    (P.rotS * placeHom E hP f).orderTop = ((-2 : ℚ) : WithTop ℚ) := by
  obtain ⟨zv, wv, hz, hw, -, -, -⟩ := P.exists_of_singular hP
  rw [orderTop_rotS_mul_placeHom E hP hz hw (hf.trans hz), sub_self, mul_zero, add_zero]

/-- A function of `w`-type with `ν(f) = ν(𝒲)` has exponent `−2`. -/
theorem orderTop_w_eq_neg_two (E : P.Expansion) (hP : P.Singular) {f : Poly (n + 2)} (hf : P.v f = P.vW) :
    (P.rotSinv * placeHom E hP f).orderTop = ((-2 : ℚ) : WithTop ℚ) := by
  obtain ⟨zv, wv, hz, hw, -, -, -⟩ := P.exists_of_singular hP
  rw [orderTop_rotSinv_mul_placeHom E hP hz hw (hf.trans hw), sub_self, mul_zero, add_zero]

theorem pair_univ_nonempty : (univ : Finset (Pair (n + 2))).Nonempty :=
  ⟨⟨(0, 1), Fin.zero_lt_one⟩, Finset.mem_univ _⟩

/-- **Lemma 2.5** (`lem:place`), first statement, colour `z`: the components of `𝒵` have exponents `≥ −2`, and one
has exponent `−2`. -/
theorem lowAt_z (E : P.Expansion) (hP : P.Singular) :
    LowAt (fun k l => placeHom E hP (pP k l)) (fun k => P.rotS * placeHom E hP (zP k)) := by
  have hterm : ∀ k l, termZ (fun k l => placeHom E hP (pP k l)) (fun k => P.rotS * placeHom E hP (zP k)) k l =
      P.rotS * placeHom E hP (pP k l ^ 3 * (zP k - zP l)) := by
    intro k l
    simp only [termZ, map_mul, map_pow, map_sub]
    ring
  refine ⟨fun k => neg_two_le_orderTop_z E hP (P.vZ_le_z k), fun k l hkl => ?_, ?_⟩
  · rw [hterm]
    exact neg_two_le_orderTop_z E hP (P.vZ_le_termZ hkl)
  · rcases le_total (univ.inf fun k => P.v (zP k))
      (univ.inf fun e : Pair (n + 2) => P.v (X (pc e) ^ 3 * (zP e.1.1 - zP e.1.2))) with h | h
    · left
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf univ univ_nonempty (fun k => P.v (zP k))
      refine ⟨k, orderTop_z_eq_neg_two E hP ?_⟩
      rw [Place.vZ, inf_eq_left.mpr h, hk]
    · right
      obtain ⟨e, -, he⟩ := Finset.exists_mem_eq_inf univ pair_univ_nonempty
        (fun e : Pair (n + 2) => P.v (X (pc e) ^ 3 * (zP e.1.1 - zP e.1.2)))
      refine ⟨e.1.1, e.1.2, ne_of_lt e.2, ?_⟩
      rw [hterm]
      refine orderTop_z_eq_neg_two E hP ?_
      rw [pP_pair, Place.vZ, inf_eq_right.mpr h, he]

/-- **Lemma 2.5** (`lem:place`), first statement, colour `w`. -/
theorem lowAt_w (E : P.Expansion) (hP : P.Singular) :
    LowAt (fun k l => placeHom E hP (pP k l)) (fun k => P.rotSinv * placeHom E hP (wP k)) := by
  have hterm : ∀ k l, termZ (fun k l => placeHom E hP (pP k l)) (fun k => P.rotSinv * placeHom E hP (wP k)) k l =
      P.rotSinv * placeHom E hP (pP k l ^ 3 * (wP k - wP l)) := by
    intro k l
    simp only [termZ, map_mul, map_pow, map_sub]
    ring
  refine ⟨fun k => neg_two_le_orderTop_w E hP (P.vW_le_w k), fun k l hkl => ?_, ?_⟩
  · rw [hterm]
    exact neg_two_le_orderTop_w E hP (P.vW_le_termW hkl)
  · rcases le_total (univ.inf fun k => P.v (wP k))
      (univ.inf fun e : Pair (n + 2) => P.v (X (pc e) ^ 3 * (wP e.1.1 - wP e.1.2))) with h | h
    · left
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf univ univ_nonempty (fun k => P.v (wP k))
      refine ⟨k, orderTop_w_eq_neg_two E hP ?_⟩
      rw [Place.vW, inf_eq_left.mpr h, hk]
    · right
      obtain ⟨e, -, he⟩ := Finset.exists_mem_eq_inf univ pair_univ_nonempty
        (fun e : Pair (n + 2) => P.v (X (pc e) ^ 3 * (wP e.1.1 - wP e.1.2)))
      refine ⟨e.1.1, e.1.2, ne_of_lt e.2, ?_⟩
      rw [hterm]
      refine orderTop_w_eq_neg_two E hP ?_
      rw [pP_pair, Place.vW, inf_eq_right.mpr h, he]

/-- The equations of the bodies (2.2) in `z` for the rotated expansions. -/
theorem placeHom_body_z (E : P.Expansion) (hP : P.Singular) (k : Fin (n + 2)) :
    P.rotS * placeHom E hP (zP k) = ∑ l ∈ univ.erase k, cS (m l) *
      termZ (fun k l => placeHom E hP (pP k l)) (fun k => P.rotS * placeHom E hP (zP k)) k l := by
  have h := placeHom_eq_zero E hP (C.rows_mem (rowZ_mem_rows m k))
  simp only [rowZ, map_sub, map_sum, map_mul, map_pow, placeHom_C] at h
  rw [sub_eq_zero] at h
  conv_lhs => rw [h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [termZ]
  ring

/-- The equations of the bodies (2.2) in `w` for the rotated expansions. -/
theorem placeHom_body_w (E : P.Expansion) (hP : P.Singular) (k : Fin (n + 2)) :
    P.rotSinv * placeHom E hP (wP k) = ∑ l ∈ univ.erase k, cS (m l) *
      termZ (fun k l => placeHom E hP (pP k l)) (fun k => P.rotSinv * placeHom E hP (wP k)) k l := by
  have h := placeHom_eq_zero E hP (C.rows_mem (rowW_mem_rows m k))
  simp only [rowW, map_sub, map_sum, map_mul, map_pow, placeHom_C] at h
  rw [sub_eq_zero] at h
  conv_lhs => rw [h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [termZ]
  ring

/-- The distance equations for the rotated expansions: the rotation cancels. -/
theorem placeHom_dist (E : P.Expansion) (hP : P.Singular) {k l : Fin (n + 2)} (hkl : k ≠ l) :
    placeHom E hP (pP k l) ^ 2 * (P.rotS * placeHom E hP (zP k) - P.rotS * placeHom E hP (zP l)) *
      (P.rotSinv * placeHom E hP (wP k) - P.rotSinv * placeHom E hP (wP l)) = 1 := by
  have h := placeHom_eq_zero E hP (C.dist_mem hkl)
  simp only [map_sub, map_mul, map_pow, map_one] at h
  have hs := P.rotS_mul_rotSinv
  linear_combination h + placeHom E hP (pP k l) ^ 2 * (placeHom E hP (zP k) - placeHom E hP (zP l)) *
    (placeHom E hP (wP k) - placeHom E hP (wP l)) * hs

/-- `U = c` on `C` in the form of the germs: `Σ_{k ≠ l} m_k m_l Φ(p_kl) = 2c`. -/
theorem placeHom_pot (E : P.Expansion) (hP : P.Singular) {c : ℂ} (hc : Upoly m - MvPolynomial.C c ∈ C.ideal) :
    ∑ k, ∑ l ∈ univ.erase k, cS (m k * m l) * placeHom E hP (pP k l) = cS (2 * c) := by
  have h := placeHom_eq_zero E hP hc
  rw [map_sub, placeHom_C, sub_eq_zero] at h
  have hU : placeHom E hP (Upoly m) =
      ∑ e : Pair (n + 2), cS (m e.1.1 * m e.1.2) * placeHom E hP (pP e.1.1 e.1.2) := by
    simp only [Upoly, map_sum, map_mul, placeHom_C, pP_pair, Complex.ofReal_mul]
  rw [sum_sum_erase_eq_two_mul_sum_pair _ (fun k l => by rw [pP_comm k l, mul_comm (m k : ℂ)]), ← hU, h]
  simp only [cS, map_mul, map_ofNat]

end germ

end Curve

open Curve

/-! ## The germ of a singular place -/

section main

variable {n : ℕ} {m : Fin (n + 2) → ℝ}

/-- The value of `U` on `C` (Lemma 2.3 (b), `Curve.U_const`). -/
def Curve.valU (C : Curve n m) : ℂ := Classical.choose C.U_const

theorem Curve.valU_spec (C : Curve n m) : Upoly m - MvPolynomial.C C.valU ∈ C.ideal :=
  Classical.choose_spec C.U_const

/-- On a nontrivial curve the value of `U` is not zero. -/
theorem Curve.valU_ne_zero {C : Curve n m} (hC : C.Nontrivial) : C.valU ≠ 0 := by
  intro h0
  apply hC.1
  have := C.valU_spec
  rwa [h0, map_zero, sub_zero] at this

/-- **The germ of a singular place** (Lemma 2.5, `lem:place`): for a singular place `P` of a nontrivial curve
`C ⊆ Y_m` and an expansion `E` at `P`, the rotated expansions `z_k = s Φ(z_k)`, `w_k = s⁻¹ Φ(w_k)`, `p_kl = Φ(p_kl)`
in the variable `τ = t^{d/2}`, with `s = τ^{2γ/d}` and `E` the value of `U` on `C`. Any masses. -/
def germOfPlace {C : Curve n m} (hC : C.Nontrivial) {P : Place C.toACurve} (hP : P.Singular) (E : P.Expansion) :
    Germ (n + 2) m where
  z k := P.rotS * placeHom E hP (zP k)
  w k := P.rotSinv * placeHom E hP (wP k)
  p k l := placeHom E hP (pP k l)
  p_symm k l := by simp only [pP_comm k l]
  body_z := placeHom_body_z E hP
  body_w := placeHom_body_w E hP
  dist _ _ hkl := placeHom_dist E hP hkl
  E := C.valU
  E_ne := Curve.valU_ne_zero hC
  pot := placeHom_pot E hP C.valU_spec
  low_z := lowAt_z E hP
  low_w := lowAt_w E hP

/-- The type of the germ of `P` is the type of `P`: `x_kl = −(2/d) ν(p_kl)` (Lemma 2.5: `e(p_kl) = (2/d) ν(p_kl)`). -/
theorem germOfPlace_x {C : Curve n m} (hC : C.Nontrivial) {P : Place C.toACurve} (hP : P.Singular)
    (E : P.Expansion) {k l : Fin (n + 2)} (hkl : k ≠ l) :
    (germOfPlace hC hP E).x k l = -(2 / P.dd) * (ordZ P.ord (C.fn (pP k l)) : ℚ) := by
  have hp := C.fn_pP_ne_zero hkl
  have hord := orderTop_placeHom_of_eq E hP (P.v_eq_ordZ hp)
  have hne : placeHom E hP (pP k l) ≠ 0 := by
    intro h0
    rw [h0, HahnSeries.orderTop_zero] at hord
    exact WithTop.top_ne_coe hord
  have h1 : (placeHom E hP (pP k l)).order = 2 / P.dd * (ordZ P.ord (C.fn (pP k l)) : ℚ) :=
    WithTop.coe_injective ((HahnSeries.order_eq_orderTop_of_ne_zero hne).trans hord)
  change -(placeHom E hP (pP k l)).order = _
  rw [h1]
  ring

/-- `ℓ` of the germ of `P` is `ℓ(x(P))`. -/
theorem germOfPlace_ell {C : Curve n m} (hC : C.Nontrivial) {P : Place C.toACurve} (hP : P.Singular)
    (E : P.Expansion) : (germOfPlace hC hP E).ell = P.ell := by
  have hsymm : ∀ k l, (germOfPlace hC hP E).x k l = (germOfPlace hC hP E).x l k := fun k l => by
    simp only [Germ.x, (germOfPlace hC hP E).p_symm k l]
  rw [Germ.ell, sum_sum_erase_eq_two_mul_sum_pair _ hsymm, Place.ell]
  have h : ∀ e : Pair (n + 2), (germOfPlace hC hP E).x e.1.1 e.1.2 = P.type e := fun e => by
    rw [germOfPlace_x hC hP E (ne_of_lt e.2), pP_pair, Place.type]
  simp only [h]
  ring

/-- **Places give germs** (Lemma 2.5, `lem:place`): every singular place `P` of a nontrivial curve `C ⊆ Y_m` has a
germ whose `ℓ` is `ℓ(x(P))`. Any masses. -/
theorem germ_of_place {C : Curve n m} (hC : C.Nontrivial) {P : Place C.toACurve} (hP : P.Singular) :
    ∃ G : Germ (n + 2) m, G.ell = P.ell := by
  obtain ⟨E⟩ := Expansion_exists P
  exact ⟨germOfPlace hC hP E, germOfPlace_ell hC hP E⟩

/-- **Part I**: if positive masses `m` have infinitely many central configurations up to similarity, there is a germ
with `ℓ ≤ 0` (Corollary 2.4 `cor:curve`, Corollary 2.7 `cor:sum`, Lemma 2.5 `lem:place`). -/
theorem exists_germ {m : Fin (n + 2) → ℝ} (hm : ∀ i, 0 < m i) (h : ¬ FinitelyManyCC m) :
    ∃ G : Germ (n + 2) m, G.ell ≤ 0 := by
  obtain ⟨C, hC⟩ := exists_curve hm h
  obtain ⟨P, hP, hell⟩ := Curve.exists_singular_place_ell_nonpos hC
  obtain ⟨E⟩ := Expansion_exists P
  exact ⟨germOfPlace hC hP E, by rw [germOfPlace_ell]; exact hell⟩

end main

end

end CC6Full
