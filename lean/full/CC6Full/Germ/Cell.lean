import CC6Full.Germ.TreeExists
import CC6Full.Germ.Symm
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.Tower

/-!
# Identities as data, cells and initial systems

Paper §4.2 (`ss:celldef`: the base identities of Definition 4.4, Lemma 4.3 (c)) and §5.1 (`ss:initial`: initial
systems, Lemma 5.1 `lem:single`, Lemma 5.2 `lem:core`), for germs.

## Terms and identities

* `Term n`: a term `c · Π (z_p − z_q) · Π (w_p − w_q) · Π p_kl` of an identity of §2.3: the coefficient
  `c ∈ ℚ[m, E]` (`MvPolynomial (Fin n ⊕ Unit) ℚ`, where `Sum.inl k` is the mass `m_k` and `Sum.inr ()` is `E`) and the
  lists of its factors; a position `z_k` is the factor `z_k − z_O`. At a germ `G`: `Term.eval G = c_i g_i`,
  `Term.mono G = g_i`, `Term.expo G` the sum of the exponents of the factors and `Term.lead G` the product of their
  leading coefficients (`Term.orderTop_mono`, `Term.leadingCoeff_mono`).
* `Identity n := List (Term n)`, `Identity.eval G = Σ_i c_i g_i`, `Identity.Holds I`: `Σ_i c_i g_i = 0` at every germ
  for all masses.
* `Identity.initial`: Lemma 2.10 (`lem:initial`) for an identity that holds: at every germ the least exponent of the
  present terms (nonzero coefficient, finite exponent) is attained twice and their initial form vanishes.
* The base identities of Definition 4.4 (`Identity.base`): the equations of the bodies (`Identity.bodyZ`,
  `Identity.bodyW`), `U = E` (`Identity.potU`) and `Σ_{k<l} m_k m_l z_kl w_kl = M E` (`Identity.lagr`); they hold
  (`Identity.base_holds`), and Lemma 4.3 (c) (`Identity.base_minTwice`).
* `Identity.IsArgmin I G S`: `S` is the argmin set of `I` at `G` (Definition 4.4), with `Identity.argminAt`, the
  argmin set at `G`. `Term.expoT`: the exponent of a term as a linear form in the heights of the two trees; it is
  `Term.expo` at a germ realizing the trees (`Term.expo_eq_expoT`), so argmin sets can be certified on the heights
  (`Identity.isArgmin_of_expoT`).

## Cells (Definition 4.4)

* `Cell n`: a pair of trees without heights and the argmin sets of the base identities. `Germ.LiesIn G c`: for some
  heights the trees of `c` realize the exponents of `G` and the argmin sets of the base identities at `G` are those of
  `c` (the heights of `G` lie in the polyhedron `Π` of the cell, up to the conditions of Lemma 4.3 (a) on the
  diagram, which are not formalized here).
* `Germ.exists_cell`: by Lemmas 4.2 and 4.3 a germ with positive masses lies in a cell whose roots have at least three
  children and whose argmin sets have at least two terms.

## Initial systems (§5.1)

* `CVar n`: the variables `m_k`, `E`, `X_{v,c}`, `Y_{v,c}` (a node and a child, as sets of points) and `P_kl`
  (`k < l`); `CPoly n` the polynomials over `ℚ` in them.
* `TreeShape.zlc p q`, `TreeShape.wlc p q`: `lc(z_p − z_q)`, `lc(w_p − w_q)` written through the trees by Lemma 4.2,
  `X̂_{v,c(p)} − X̂_{v,c(q)}` for `v = lca(p, q)`, with `X̂_{v,c₀} = 0` (`CPoly.xhat`); `Term.poly`; the initial form
  `Identity.initForm I S = Σ_{i∈S} c_i lc(g_i)`; the distance polynomials `distPoly k l = P_kl² lc(z_kl) lc(w_kl) − 1`.
* `Germ.leadPt`: the leading coefficients of a germ as a point; `Germ.eval_initForm`: the initial form of a holding
  identity vanishes there when `S` is its argmin set at the germ; `Germ.eval_distPoly`.
* Lemma 5.1: `Identity.single`, `Identity.single_of_expoT`. Lemma 5.2 (a): `core` (explicit cofactors, unit ideal),
  `core_span` (ideal membership), `Germ.LiesIn.core` (for a germ in a cell), `core_theta` (saturation by the product
  `theta` of the node coordinates, their differences, the `P_kl` and `E`, which does not vanish at the leading
  coefficients, `Germ.eval_theta_ne_zero`). Lemma 5.2 (b): `core_b`, `core_b_theta`, through `Germ.scale`.
-/

namespace CC6Full

open Finset

/-! ## Lists -/

section lists

theorem list_sum_map_filter {α M : Type*} [AddCommMonoid M] (L : List α) (p : α → Bool) (f : α → M) :
    ((L.filter p).map f).sum = (L.map fun x => if p x then f x else 0).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => by_cases h : p a <;> simp [h, ih]

theorem list_sum_flatMap {α β M : Type*} [AddCommMonoid M] (L : List α) (g : α → List β) (f : β → M) :
    ((L.flatMap g).map f).sum = (L.map fun a => ((g a).map f).sum).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem sum_map_filter_finRange {n : ℕ} {M : Type*} [AddCommMonoid M] (p : Fin n → Bool) (f : Fin n → M) :
    (((List.finRange n).filter p).map f).sum = ∑ l ∈ univ.filter (fun l => p l = true), f l := by
  rw [list_sum_map_filter, Finset.sum_filter, Fin.sum_univ_def]

theorem Ser.orderTop_list_prod (L : List Ser) : L.prod.orderTop = (L.map HahnSeries.orderTop).sum := by
  induction L with
  | nil => simp [HahnSeries.orderTop_one]
  | cons a L ih => rw [List.prod_cons, HahnSeries.orderTop_mul, ih, List.map_cons, List.sum_cons]

theorem Ser.leadingCoeff_list_prod (L : List Ser) :
    L.prod.leadingCoeff = (L.map HahnSeries.leadingCoeff).prod := by
  induction L with
  | nil => simp [HahnSeries.leadingCoeff_one]
  | cons a L ih => rw [List.prod_cons, HahnSeries.leadingCoeff_mul, ih, List.map_cons, List.prod_cons]

/-- A linear combination `Σ g_i f_i` vanishes at a point where all `f_i` vanish. -/
theorem aeval_zipWith_sum_eq_zero {σ : Type*} (V : σ → ℂ) :
    ∀ (gs fs : List (MvPolynomial σ ℚ)), (∀ f ∈ fs, MvPolynomial.aeval V f = 0) →
      MvPolynomial.aeval V (List.zipWith (· * ·) gs fs).sum = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | g :: gs, f :: fs, h => by
    rw [List.zipWith_cons_cons, List.sum_cons, map_add, map_mul, h f List.mem_cons_self, mul_zero, zero_add]
    exact aeval_zipWith_sum_eq_zero V gs fs fun f' hf' => h f' (List.mem_cons_of_mem _ hf')

/-- A polynomial with rational coefficients vanishes at a real point if it vanishes at its image in `ℂ`. -/
theorem aeval_ofReal_eq_zero {n : ℕ} {x : Fin n → ℝ} {h : MvPolynomial (Fin n) ℚ}
    (h0 : MvPolynomial.aeval (fun k => (x k : ℂ)) h = 0) : MvPolynomial.aeval x h = 0 := by
  have e : (fun k => (x k : ℂ)) = algebraMap ℝ ℂ ∘ x := by
    funext k
    simp
  rw [e, MvPolynomial.aeval_algebraMap_apply] at h0
  exact (algebraMap ℝ ℂ).injective (h0.trans (map_zero _).symm)

end lists

/-! ## Terms and identities -/

/-- A term `c · Π (z_p − z_q) · Π (w_p − w_q) · Π p_kl` of an identity of §2.3 (Lemma 2.10): the coefficient `c`, a
polynomial with rational coefficients in the masses (`Sum.inl k`) and `E` (`Sum.inr ()`), and the lists of the
factors; a position `z_k` is the factor `z_k − z_O`, written `(some k, none)`. -/
structure Term (n : ℕ) where
  /-- the coefficient, a polynomial in the masses and `E` -/
  coeff : MvPolynomial (Fin n ⊕ Unit) ℚ
  /-- the factors `z_p − z_q` -/
  zs : List (Pt n × Pt n)
  /-- the factors `w_p − w_q` -/
  ws : List (Pt n × Pt n)
  /-- the factors `p_kl` -/
  ps : List (Fin n × Fin n)

/-- An identity `Σ_i c_i g_i = 0` of §2.3, as the list of its terms. -/
abbrev Identity (n : ℕ) := List (Term n)

noncomputable section

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ} (G : Germ n m)

/-- The value of a coefficient polynomial at the masses `m` and the energy `E` of `G`. -/
def cval (c : MvPolynomial (Fin n ⊕ Unit) ℚ) : ℂ :=
  MvPolynomial.aeval (Sum.elim (fun k => (m k : ℂ)) fun _ => G.E) c

end Germ

namespace Term

variable {n : ℕ} {m : Fin n → ℝ} (G : Germ n m) (t : Term n)

/-- The product `g_i` of the factors of the term at `G`. -/
def mono : Ser :=
  (t.zs.map fun pq => G.zpos pq.1 - G.zpos pq.2).prod * (t.ws.map fun pq => G.wpos pq.1 - G.wpos pq.2).prod *
    (t.ps.map fun kl => G.p kl.1 kl.2).prod

/-- The value `c_i g_i` of the term at `G`. -/
def eval : Ser := cS (G.cval t.coeff) * t.mono G

/-- The exponent of the term at `G` (§2.3): the sum of the exponents of its factors, `⊤` if a factor vanishes. -/
def expo : WithTop ℚ :=
  (t.zs.map fun pq => G.hz pq.1 pq.2).sum + (t.ws.map fun pq => G.hw pq.1 pq.2).sum +
    (t.ps.map fun kl => (G.p kl.1 kl.2).orderTop).sum

/-- The leading coefficient `lc(g_i)` of the term at `G`: the product of the leading coefficients of its factors. -/
def lead : ℂ :=
  (t.zs.map fun pq => (G.zpos pq.1 - G.zpos pq.2).leadingCoeff).prod *
    (t.ws.map fun pq => (G.wpos pq.1 - G.wpos pq.2).leadingCoeff).prod *
    (t.ps.map fun kl => (G.p kl.1 kl.2).leadingCoeff).prod

/-- The exponent of a product is the sum of the exponents of the factors. -/
theorem orderTop_mono : (t.mono G).orderTop = t.expo G := by
  simp only [mono, expo, HahnSeries.orderTop_mul, Ser.orderTop_list_prod, List.map_map]
  rfl

/-- The leading coefficient of a product is the product of the leading coefficients of the factors. -/
theorem leadingCoeff_mono : (t.mono G).leadingCoeff = t.lead G := by
  simp only [mono, lead, HahnSeries.leadingCoeff_mul, Ser.leadingCoeff_list_prod, List.map_map]
  rfl

theorem mono_ne_zero_iff : t.mono G ≠ 0 ↔ t.expo G ≠ ⊤ := by
  rw [← orderTop_mono, Ne, Ne, HahnSeries.orderTop_eq_top]

end Term

namespace Identity

variable {n : ℕ} {m : Fin n → ℝ}

/-- The value `Σ_i c_i g_i` of the identity at `G`. -/
def eval (I : Identity n) (G : Germ n m) : Ser := (I.map fun t => t.eval G).sum

/-- The identity holds at every germ, for all masses. -/
def Holds (I : Identity n) : Prop := ∀ (m : Fin n → ℝ) (G : Germ n m), I.eval G = 0

theorem eval_eq_sum (I : Identity n) (G : Germ n m) :
    I.eval G = ∑ i : Fin I.length, cS (G.cval I[i.1].coeff) * I[i.1].mono G := by
  rw [eval, ← Fin.sum_univ_fun_getElem]
  rfl

theorem sum_eq_zero {I : Identity n} (hI : I.Holds) (G : Germ n m) :
    ∑ i : Fin I.length, cS (G.cval I[i.1].coeff) * I[i.1].mono G = 0 :=
  (I.eval_eq_sum G).symm.trans (hI m G)

open Classical in
/-- The terms present at `G` (§2.3): nonzero coefficient and finite exponent. -/
def present (I : Identity n) (G : Germ n m) : Finset (Fin I.length) :=
  univ.filter fun i => G.cval I[i.1].coeff ≠ 0 ∧ I[i.1].expo G ≠ ⊤

theorem mem_present {I : Identity n} {G : Germ n m} {i : Fin I.length} :
    i ∈ I.present G ↔ G.cval I[i.1].coeff ≠ 0 ∧ I[i.1].expo G ≠ ⊤ := by
  simp [present]

/-- **Lemma 2.10** (`lem:initial`) for an identity that holds at every germ: if some term is present at `G`, the
least exponent `e₀` of the present terms is attained by two of them, and the initial form
`Σ_{e(g_i) = e₀} c_i lc(g_i)` vanishes. -/
theorem initial {I : Identity n} (hI : I.Holds) (G : Germ n m) (hne : (I.present G).Nonempty) :
    (∃ i ∈ I.present G, ∃ j ∈ I.present G, i ≠ j ∧
        I[i.1].expo G = (I.present G).inf' hne (fun i => I[i.1].expo G) ∧
        I[j.1].expo G = (I.present G).inf' hne (fun i => I[i.1].expo G)) ∧
      ∑ i ∈ I.present G with I[i.1].expo G = (I.present G).inf' hne (fun i => I[i.1].expo G),
        G.cval I[i.1].coeff * I[i.1].lead G = 0 := by
  have hsum : ∑ i ∈ I.present G, cS (G.cval I[i.1].coeff) * I[i.1].mono G = 0 := by
    rw [← sum_eq_zero hI G]
    refine Finset.sum_subset (subset_univ _) fun i _ hi => ?_
    rw [mem_present, not_and_or, not_not, not_not] at hi
    rcases hi with hc | he
    · rw [hc, cS_zero, zero_mul]
    · rw [← Term.orderTop_mono, HahnSeries.orderTop_eq_top] at he
      rw [he, mul_zero]
  obtain ⟨h1, h2⟩ := initial_orderTop hne (c := fun i : Fin I.length => G.cval I[i.1].coeff)
    (g := fun i : Fin I.length => I[i.1].mono G)
    (fun i hi => (mem_present.mp hi).1) (fun i hi => (Term.mono_ne_zero_iff _ _).mpr (mem_present.mp hi).2) hsum
  have hinf : (I.present G).inf' hne (fun i => (I[i.1].mono G).orderTop) =
      (I.present G).inf' hne (fun i => I[i.1].expo G) := by
    congr 1
    funext i
    exact Term.orderTop_mono _ _
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, j, hj, hij, hie, hje⟩ := h1
    refine ⟨i, hi, j, hj, hij, ?_, ?_⟩
    · rw [← Term.orderTop_mono, ← hinf]
      exact hie
    · rw [← Term.orderTop_mono, ← hinf]
      exact hje
  · rw [← h2]
    refine Finset.sum_congr ?_ fun i _ => ?_
    · ext i
      simp only [mem_filter]
      rw [Term.orderTop_mono, hinf]
    · rw [Term.leadingCoeff_mono]

/-- The conclusion of Lemma 4.3 (c) for `I` at `G`: the least exponent of the terms is finite and attained by two
terms. -/
def MinTwice (I : Identity n) (G : Germ n m) : Prop :=
  ∃ i j : Fin I.length, i ≠ j ∧ I[i.1].expo G ≠ ⊤ ∧ I[i.1].expo G = I[j.1].expo G ∧
    ∀ l : Fin I.length, I[i.1].expo G ≤ I[l.1].expo G

/-- Lemma 2.10 (`lem:initial`) for an identity whose coefficients do not vanish at `G` and which has a term of finite
exponent: the least exponent is attained twice. -/
theorem minTwice {I : Identity n} (hI : I.Holds) {G : Germ n m} (hc : ∀ t ∈ I, G.cval t.coeff ≠ 0)
    (hfin : ∃ t ∈ I, t.expo G ≠ ⊤) : I.MinTwice G := by
  have hpres : ∀ i : Fin I.length, i ∈ I.present G ↔ I[i.1].expo G ≠ ⊤ := fun i =>
    mem_present.trans ⟨fun h => h.2, fun h => ⟨hc _ (List.getElem_mem _), h⟩⟩
  obtain ⟨t, ht, htf⟩ := hfin
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
  have hne : (I.present G).Nonempty := ⟨⟨k, hk⟩, (hpres _).mpr htf⟩
  obtain ⟨⟨i, hi, j, hj, hij, hie, hje⟩, -⟩ := initial hI G hne
  refine ⟨i, j, hij, (hpres i).mp hi, hie.trans hje.symm, fun l => ?_⟩
  by_cases hl : l ∈ I.present G
  · rw [hie]
    exact Finset.inf'_le _ hl
  · rw [hpres, not_not] at hl
    rw [hl]
    exact le_top

/-- `S` (a set of positions in the list of terms) is the argmin set of `I` at `G` (Definition 4.4): the terms in `S`
have one finite exponent `e` and all other terms have larger exponents. -/
def IsArgmin (I : Identity n) (G : Germ n m) (S : Finset ℕ) : Prop :=
  ∃ e : ℚ, (∀ i : Fin I.length, i.1 ∈ S → I[i.1].expo G = e) ∧
    ∀ i : Fin I.length, i.1 ∉ S → (e : WithTop ℚ) < I[i.1].expo G

/-- **Lemma 5.1** (`lem:single`), at a germ: an identity that holds at every germ cannot have a single term of least
exponent whose coefficient does not vanish. -/
theorem single {I : Identity n} (hI : I.Holds) (G : Germ n m) {i₀ : Fin I.length}
    (hc : G.cval I[i₀.1].coeff ≠ 0) (hS : I.IsArgmin G {i₀.1}) : False := by
  obtain ⟨e, hin, hout⟩ := hS
  have he : I[i₀.1].expo G = e := hin i₀ (mem_singleton_self _)
  have hg : I[i₀.1].mono G ≠ 0 := by
    rw [Term.mono_ne_zero_iff, he]
    exact WithTop.coe_ne_top
  have hmin : ∀ j ∈ (univ : Finset (Fin I.length)), j ≠ i₀ →
      (I[i₀.1].mono G).orderTop < (I[j.1].mono G).orderTop := by
    intro j _ hj
    rw [Term.orderTop_mono, Term.orderTop_mono, he]
    exact hout j fun h => hj (Fin.ext (mem_singleton.mp h))
  exact initial_not_unique_min (s := (univ : Finset (Fin I.length)))
    (c := fun i : Fin I.length => G.cval I[i.1].coeff) (g := fun i : Fin I.length => I[i.1].mono G)
    (sum_eq_zero hI G) (mem_univ i₀) hc hg hmin

end Identity

/-! ## The base identities (Definition 4.4) -/

namespace Identity

variable {n : ℕ}

/-- The pairs `(k, l)` with `k < l`, in lexicographic order. -/
def pairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun k => ((List.finRange n).filter fun l => k < l).map fun l => (k, l)

theorem sum_pairs {M : Type*} [AddCommMonoid M] (f : Fin n × Fin n → M) :
    ((pairs n).map f).sum = ∑ k, ∑ l ∈ Ioi k, f (k, l) := by
  rw [pairs, list_sum_flatMap, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  rw [List.map_map, sum_map_filter_finRange]
  simp only [decide_eq_true_eq, Finset.filter_lt_eq_Ioi, Function.comp_apply]

/-- The mass `m_k` as a coefficient. -/
abbrev cm (k : Fin n) : MvPolynomial (Fin n ⊕ Unit) ℚ := MvPolynomial.X (Sum.inl k)

/-- The energy `E` as a coefficient. -/
abbrev cE : MvPolynomial (Fin n ⊕ Unit) ℚ := MvPolynomial.X (Sum.inr ())

/-- The equation of the body `k` in `z` (2.2): `z_k − Σ_{l ≠ k} m_l p_kl³ (z_k − z_l) = 0`. Its terms are `z_k`
(position `0`) and the `−m_l Z_kl` for `l ≠ k` in increasing order. -/
def bodyZ (k : Fin n) : Identity n :=
  ⟨1, [(some k, none)], [], []⟩ ::
    ((List.finRange n).filter fun l => l ≠ k).map fun l => ⟨-cm l, [(some k, some l)], [], [(k, l), (k, l), (k, l)]⟩

/-- The equation of the body `k` in `w` (2.2): `w_k − Σ_{l ≠ k} m_l p_kl³ (w_k − w_l) = 0`, with the terms in the
order of `bodyZ`. -/
def bodyW (k : Fin n) : Identity n :=
  ⟨1, [], [(some k, none)], []⟩ ::
    ((List.finRange n).filter fun l => l ≠ k).map fun l => ⟨-cm l, [], [(some k, some l)], [(k, l), (k, l), (k, l)]⟩

/-- `U = E`: `Σ_{k<l} m_k m_l p_kl − E = 0`, with the pairs in the order of `pairs n` and the constant last. -/
def potU (n : ℕ) : Identity n :=
  (pairs n).map (fun kl => ⟨cm kl.1 * cm kl.2, [], [], [kl]⟩) ++ [⟨-cE, [], [], []⟩]

/-- Lagrange's identity `Σ_{k<l} m_k m_l z_kl w_kl − M E = 0` (`M U` in the paper), with the pairs in the order of
`pairs n` and the constant last. -/
def lagr (n : ℕ) : Identity n :=
  (pairs n).map (fun kl => ⟨cm kl.1 * cm kl.2, [(some kl.1, some kl.2)], [(some kl.1, some kl.2)], []⟩) ++
    [⟨-((∑ k, cm k) * cE), [], [], []⟩]

/-- The base identities of Definition 4.4 (`def:cell`): the `2n` equations of the bodies, `U = E` and
`Σ_{k<l} m_k m_l z_kl w_kl = M E`. -/
def base (n : ℕ) : List (Identity n) :=
  (List.finRange n).map bodyZ ++ (List.finRange n).map bodyW ++ [potU n, lagr n]

variable {m : Fin n → ℝ}

theorem eval_cons (t : Term n) (I : Identity n) (G : Germ n m) : eval (t :: I) G = t.eval G + I.eval G := by
  simp [eval]

theorem eval_append (I J : Identity n) (G : Germ n m) : eval (I ++ J) G = I.eval G + J.eval G := by
  simp [eval]

theorem eval_map {α : Type*} (f : α → Term n) (L : List α) (G : Germ n m) :
    eval (L.map f) G = (L.map fun a => (f a).eval G).sum := by
  simp only [eval, List.map_map]
  rfl

theorem eval_mk (G : Germ n m) (c : MvPolynomial (Fin n ⊕ Unit) ℚ) (zs ws : List (Pt n × Pt n))
    (ps : List (Fin n × Fin n)) :
    Term.eval G ⟨c, zs, ws, ps⟩ = cS (G.cval c) * ((zs.map fun pq => G.zpos pq.1 - G.zpos pq.2).prod *
      (ws.map fun pq => G.wpos pq.1 - G.wpos pq.2).prod * (ps.map fun kl => G.p kl.1 kl.2).prod) := rfl

theorem cval_one (G : Germ n m) : G.cval 1 = 1 := map_one _

theorem cval_neg (G : Germ n m) (c : MvPolynomial (Fin n ⊕ Unit) ℚ) : G.cval (-c) = -G.cval c := map_neg _ _

theorem cval_mul (G : Germ n m) (c d : MvPolynomial (Fin n ⊕ Unit) ℚ) : G.cval (c * d) = G.cval c * G.cval d :=
  map_mul _ _ _

theorem cval_sum (G : Germ n m) (c : Fin n → MvPolynomial (Fin n ⊕ Unit) ℚ) :
    G.cval (∑ k, c k) = ∑ k, G.cval (c k) := map_sum _ _ _

theorem cval_cm (G : Germ n m) (k : Fin n) : G.cval (cm k) = (m k : ℂ) := by simp [Germ.cval]

theorem cval_cE (G : Germ n m) : G.cval cE = G.E := by simp [Germ.cval]

theorem bodyZ_holds (k : Fin n) : (bodyZ k).Holds := by
  intro m G
  have h1 : Term.eval G ⟨1, [(some k, none)], [], []⟩ = G.z k := by
    rw [eval_mk]
    simp only [cval_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.zpos_some,
      Germ.zpos_none, cS_one]
    ring
  have h2 : ∀ l, Term.eval G ⟨-cm l, [(some k, some l)], [], [(k, l), (k, l), (k, l)]⟩ =
      -(cS (m l) * termZ G.p G.z k l) := by
    intro l
    rw [eval_mk]
    simp only [cval_neg, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.zpos_some,
      termZ, cS_neg]
    ring
  rw [bodyZ, eval_cons, eval_map, sum_map_filter_finRange]
  simp only [h1, h2, decide_eq_true_eq, Finset.filter_ne']
  rw [Finset.sum_neg_distrib, ← G.body_z k, add_neg_cancel]

theorem bodyW_holds (k : Fin n) : (bodyW k).Holds := by
  intro m G
  have h1 : Term.eval G ⟨1, [], [(some k, none)], []⟩ = G.w k := by
    rw [eval_mk]
    simp only [cval_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.wpos_some,
      Germ.wpos_none, cS_one]
    ring
  have h2 : ∀ l, Term.eval G ⟨-cm l, [], [(some k, some l)], [(k, l), (k, l), (k, l)]⟩ =
      -(cS (m l) * termZ G.p G.w k l) := by
    intro l
    rw [eval_mk]
    simp only [cval_neg, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.wpos_some,
      termZ, cS_neg]
    ring
  rw [bodyW, eval_cons, eval_map, sum_map_filter_finRange]
  simp only [h1, h2, decide_eq_true_eq, Finset.filter_ne']
  rw [Finset.sum_neg_distrib, ← G.body_w k, add_neg_cancel]

theorem potU_holds : (potU n).Holds := by
  intro m G
  have h1 : ∀ k l : Fin n, Term.eval G ⟨cm k * cm l, [], [], [(k, l)]⟩ = cS (m k) * cS (m l) * G.p k l := by
    intro k l
    rw [eval_mk]
    simp only [cval_mul, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, cS_mul]
    ring
  have h3 : Term.eval G ⟨-cE, [], [], []⟩ = -cS G.E := by
    rw [eval_mk]
    simp only [cval_neg, cval_cE, List.map_nil, List.prod_nil, cS_neg]
    ring
  rw [potU, eval_append, eval_map, sum_pairs, eval_cons, h3]
  simp only [h1]
  rw [G.U_eq]
  simp [eval]

theorem lagr_holds : (lagr n).Holds := by
  intro m G
  have h1 : ∀ k l : Fin n, Term.eval G ⟨cm k * cm l, [(some k, some l)], [(some k, some l)], []⟩ =
      cS (m k) * cS (m l) * ((G.z k - G.z l) * (G.w k - G.w l)) := by
    intro k l
    rw [eval_mk]
    simp only [cval_mul, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, cS_mul,
      Germ.zpos_some, Germ.wpos_some]
    ring
  have h3 : Term.eval G ⟨-((∑ k, cm k) * cE), [], [], []⟩ = -(cS ((∑ k, m k : ℝ) : ℂ) * cS G.E) := by
    rw [eval_mk]
    simp only [cval_neg, cval_mul, cval_sum, cval_cm, cval_cE, List.map_nil, List.prod_nil, cS_neg, cS_mul,
      Complex.ofReal_sum]
    ring
  rw [lagr, eval_append, eval_map, sum_pairs, eval_cons, h3]
  simp only [h1]
  rw [G.lagrange]
  simp [eval]

/-- The base identities hold at every germ (§2.3). -/
theorem base_holds : ∀ I ∈ base n, I.Holds := by
  intro I hI
  simp only [base, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with (⟨k, -, rfl⟩ | ⟨k, -, rfl⟩) | rfl | rfl
  · exact bodyZ_holds k
  · exact bodyW_holds k
  · exact potU_holds
  · exact lagr_holds

/-- **Lemma 4.3 (c)** (`lem:constraints`): at positive masses, in each base identity the least exponent of the terms
is attained by at least two terms. -/
theorem base_minTwice (hm : ∀ k, 0 < m k) (hn : 2 ≤ n) (G : Germ n m) : ∀ I ∈ base n, I.MinTwice G := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hm0 : ∀ k, (m k : ℂ) ≠ 0 := fun k => Complex.ofReal_ne_zero.mpr (hm k).ne'
  have hM : (∑ k, (m k : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_sum, Complex.ofReal_ne_zero]
    obtain ⟨k⟩ : Nonempty (Fin n) := inferInstance
    exact (Finset.sum_pos (fun k _ => hm k) ⟨k, mem_univ _⟩).ne'
  -- a term of an equation of a body with a factor `z_k − z_l` or `w_k − w_l`, `l ≠ k`, has finite exponent
  have hbody : ∀ k l : Fin n, l ≠ k → ∀ zs ws : List (Pt n × Pt n), (zs = [(some k, some l)] ∧ ws = [] ∨
      zs = [] ∧ ws = [(some k, some l)]) →
      (Term.mk (-cm l) zs ws [(k, l), (k, l), (k, l)]).expo G ≠ ⊤ := by
    intro k l hlk zs ws hzw
    rw [← Term.mono_ne_zero_iff]
    have hp := G.p_ne_zero hlk.symm
    rcases hzw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [Term.mono, G.z_sub_ne_zero hlk.symm] using hp
    · simpa [Term.mono, G.w_sub_ne_zero hlk.symm] using hp
  have hconst : ∀ c : MvPolynomial (Fin n ⊕ Unit) ℚ, (Term.mk c [] [] []).expo G ≠ ⊤ := by
    intro c
    simp [Term.expo]
  intro I hI
  simp only [base, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with (⟨k, -, rfl⟩ | ⟨k, -, rfl⟩) | rfl | rfl
  · obtain ⟨l, hlk⟩ := exists_ne k
    refine minTwice (bodyZ_holds k) ?_ ⟨_, ?_, hbody k l hlk _ [] (Or.inl ⟨rfl, rfl⟩)⟩
    · intro t ht
      simp only [bodyZ, List.mem_cons, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at ht
      rcases ht with rfl | ⟨l', -, rfl⟩
      · simp only [cval_one]
        exact one_ne_zero
      · simp only [cval_neg, cval_cm]
        exact neg_ne_zero.mpr (hm0 l')
    · simp only [bodyZ, List.mem_cons, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
      exact Or.inr ⟨l, by simpa using hlk, rfl⟩
  · obtain ⟨l, hlk⟩ := exists_ne k
    refine minTwice (bodyW_holds k) ?_ ⟨_, ?_, hbody k l hlk [] _ (Or.inr ⟨rfl, rfl⟩)⟩
    · intro t ht
      simp only [bodyW, List.mem_cons, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at ht
      rcases ht with rfl | ⟨l', -, rfl⟩
      · simp only [cval_one]
        exact one_ne_zero
      · simp only [cval_neg, cval_cm]
        exact neg_ne_zero.mpr (hm0 l')
    · simp only [bodyW, List.mem_cons, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
      exact Or.inr ⟨l, by simpa using hlk, rfl⟩
  · refine minTwice potU_holds ?_ ⟨_, ?_, hconst (-cE)⟩
    · intro t ht
      simp only [potU, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with ⟨kl, -, rfl⟩ | rfl
      · simp only [cval_mul, cval_cm]
        exact mul_ne_zero (hm0 _) (hm0 _)
      · simp only [cval_neg, cval_cE]
        exact neg_ne_zero.mpr G.E_ne
    · simp [potU]
  · refine minTwice lagr_holds ?_ ⟨_, ?_, hconst (-((∑ k, cm k) * cE))⟩
    · intro t ht
      simp only [lagr, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with ⟨kl, -, rfl⟩ | rfl
      · simp only [cval_mul, cval_cm]
        exact mul_ne_zero (hm0 _) (hm0 _)
      · simp only [cval_neg, cval_mul, cval_sum, cval_cm, cval_cE]
        exact neg_ne_zero.mpr (mul_ne_zero hM G.E_ne)
    · simp [lagr]

end Identity

/-! ## Cells (Definition 4.4) -/

theorem list_forall₂_map_self {α β : Type*} {R : α → β → Prop} {f : α → β} :
    ∀ {L : List α}, (∀ x ∈ L, R x (f x)) → List.Forall₂ R L (L.map f)
  | [], _ => List.Forall₂.nil
  | a :: _, h => List.Forall₂.cons (h a List.mem_cons_self)
      (list_forall₂_map_self fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A cell of Definition 4.4 (`def:cell`), as data: a pair of trees without heights and an argmin set for each base
identity (positions in its list of terms, in the order of `Identity.base n`). Its polyhedron `Π` is described by
`Germ.LiesIn`: the heights realizing the exponents of a germ with these trees and argmin sets. -/
structure Cell (n : ℕ) where
  /-- the tree of `z` -/
  tz : TreeShape n
  /-- the tree of `w` -/
  tw : TreeShape n
  /-- the argmin sets of the base identities -/
  argmin : List (Finset ℕ)

namespace Identity

variable {n : ℕ} {m : Fin n → ℝ}

open Classical in
/-- The argmin set of `I` at `G`: the positions of the terms of least exponent. -/
def argminAt (I : Identity n) (G : Germ n m) : Finset ℕ :=
  ((univ : Finset (Fin I.length)).filter fun i => ∀ j : Fin I.length, I[i.1].expo G ≤ I[j.1].expo G).image Fin.val

theorem mem_argminAt {I : Identity n} {G : Germ n m} {i : Fin I.length} :
    i.1 ∈ I.argminAt G ↔ ∀ j : Fin I.length, I[i.1].expo G ≤ I[j.1].expo G := by
  simp only [argminAt, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i', hi', he⟩
    rw [show i = i' from Fin.ext he.symm]
    exact hi'
  · exact fun h => ⟨i, h, rfl⟩

/-- If the least exponent is finite and attained twice, `argminAt` is the argmin set. -/
theorem isArgmin_argminAt {I : Identity n} {G : Germ n m} (hI : I.MinTwice G) : I.IsArgmin G (I.argminAt G) := by
  obtain ⟨i, j, -, hfin, -, hle⟩ := hI
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp hfin
  refine ⟨e, fun l hl => ?_, fun l hl => ?_⟩
  · exact le_antisymm ((mem_argminAt.mp hl) i |>.trans he.symm.le) (he ▸ hle l)
  · rw [mem_argminAt] at hl
    push Not at hl
    obtain ⟨l', hl'⟩ := hl
    exact lt_of_le_of_lt (he ▸ hle l') hl'

theorem two_le_card_argminAt {I : Identity n} {G : Germ n m} (hI : I.MinTwice G) : 2 ≤ (I.argminAt G).card := by
  obtain ⟨i, j, hij, -, hije, hle⟩ := hI
  have hi : i.1 ∈ I.argminAt G := mem_argminAt.mpr hle
  have hj : j.1 ∈ I.argminAt G := mem_argminAt.mpr (hije ▸ hle)
  exact Finset.one_lt_card.mpr ⟨i.1, hi, j.1, hj, fun h => hij (Fin.ext h)⟩

end Identity

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ}

/-- The germ `G` lies in the cell `c` (§4.2): for some heights, the trees of `c` realize the exponents of `G`
(`e(z_p − z_q)` and `e(w_p − w_q)`), and the argmin sets of the base identities at `G` are those of `c`. -/
def LiesIn (G : Germ n m) (c : Cell n) : Prop :=
  ∃ htz htw : Finset (Pt n) → ℚ, c.tz.Realizes G.hz htz ∧ c.tw.Realizes G.hw htw ∧
    List.Forall₂ (fun I S => Identity.IsArgmin I G S) (Identity.base n) c.argmin

/-- §4.2, after Definition 4.4: by Lemmas 4.2 and 4.3, a germ with positive masses lies in a cell whose trees have
roots with at least three children and whose argmin sets have at least two terms each. -/
theorem exists_cell (hm : ∀ k, 0 < m k) (hn : 2 ≤ n) (G : Germ n m) :
    ∃ c : Cell n, G.LiesIn c ∧ 3 ≤ (c.tz.children univ).card ∧ 3 ≤ (c.tw.children univ).card ∧
      ∀ S ∈ c.argmin, 2 ≤ S.card := by
  obtain ⟨Tz, htz, hRz⟩ := G.exists_tree_z hn
  obtain ⟨Tw, htw, hRw⟩ := G.exists_tree_w hn
  refine ⟨⟨Tz, Tw, (Identity.base n).map fun I => I.argminAt G⟩,
    ⟨htz, htw, hRz, hRw, list_forall₂_map_self fun I hI =>
      Identity.isArgmin_argminAt (Identity.base_minTwice hm hn G I hI)⟩,
    G.three_children_z hm hRz, G.three_children_w hm hRw, fun S hS => ?_⟩
  obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hS
  exact Identity.two_le_card_argminAt (Identity.base_minTwice hm hn G I hI)

end Germ

/-! ## Exponents on the heights of the trees -/

namespace TreeShape

variable {n : ℕ}

/-- The exponent `e(pos_p − pos_q)` read off a tree with heights: the height of `lca(p, q)`, or `⊤` on a leaf. -/
def hgt (T : TreeShape n) (hts : Finset (Pt n) → ℚ) (p q : Pt n) : WithTop ℚ :=
  if T.SameLeaf p q then ⊤ else (hts (T.lca p q) : WithTop ℚ)

theorem Realizes.eq_hgt {T : TreeShape n} {h : Pt n → Pt n → WithTop ℚ} {hts : Finset (Pt n) → ℚ}
    (hR : T.Realizes h hts) (p q : Pt n) : h p q = T.hgt hts p q := by
  unfold hgt
  split_ifs with hs
  · exact hR.same p q hs
  · exact hR.diff p q hs

end TreeShape

namespace Term

variable {n : ℕ} {m : Fin n → ℝ}

/-- The exponent of a term as a linear form in the heights of the trees `Tz`, `Tw` (Definition 4.4): a factor
`z_p − z_q` or `w_p − w_q` has the height of the lowest common ancestor (`⊤` on a leaf), and
`e(p_kl) = −x_kl = −(ζ_kl + ω_kl)/2`. -/
def expoT (Tz Tw : TreeShape n) (htz htw : Finset (Pt n) → ℚ) (t : Term n) : WithTop ℚ :=
  (t.zs.map fun pq => Tz.hgt htz pq.1 pq.2).sum + (t.ws.map fun pq => Tw.hgt htw pq.1 pq.2).sum +
    (t.ps.map fun kl =>
      ((-(htz (Tz.lca (some kl.1) (some kl.2)) + htw (Tw.lca (some kl.1) (some kl.2))) / 2 : ℚ) : WithTop ℚ)).sum

/-- At a germ realizing the trees, the exponent of a term is the linear form `expoT` in the heights (for terms whose
factors `p_kl` have `k ≠ l`). -/
theorem expo_eq_expoT {G : Germ n m} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ}
    (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) (t : Term n) (ht : ∀ kl ∈ t.ps, kl.1 ≠ kl.2) :
    t.expo G = t.expoT Tz Tw htz htw := by
  unfold expo expoT
  congr 1
  · congr 1
    · congr 1
      exact List.map_congr_left fun pq _ => hRz.eq_hgt pq.1 pq.2
    · congr 1
      exact List.map_congr_left fun pq _ => hRw.eq_hgt pq.1 pq.2
  · congr 1
    refine List.map_congr_left fun kl hkl => ?_
    have hne := ht kl hkl
    have hz : G.hz (some kl.1) (some kl.2) = _ := hRz.diff (some kl.1) (some kl.2) (Tz.not_sameLeaf_some hne)
    have hw : G.hw (some kl.1) (some kl.2) = _ := hRw.diff (some kl.1) (some kl.2) (Tw.not_sameLeaf_some hne)
    rw [G.hz_some_some hne, WithTop.coe_inj] at hz
    rw [G.hw_some_some hne, WithTop.coe_inj] at hw
    rw [G.orderTop_p hne, G.x_eq hne, hz, hw, WithTop.coe_inj]
    ring

end Term

namespace Identity

variable {n : ℕ} {m : Fin n → ℝ}

/-- Argmin sets certified on the heights: if the linear forms `expoT` of the terms in `S` take one value `e` at the
heights of a germ and the others are larger, then `S` is the argmin set of `I` at the germ. -/
theorem isArgmin_of_expoT {G : Germ n m} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ}
    (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {I : Identity n}
    (hI : ∀ t ∈ I, ∀ kl ∈ t.ps, kl.1 ≠ kl.2) {S : Finset ℕ} {e : ℚ}
    (hin : ∀ i : Fin I.length, i.1 ∈ S → I[i.1].expoT Tz Tw htz htw = e)
    (hout : ∀ i : Fin I.length, i.1 ∉ S → (e : WithTop ℚ) < I[i.1].expoT Tz Tw htz htw) : I.IsArgmin G S :=
  ⟨e, fun i hi => (Term.expo_eq_expoT hRz hRw _ (hI _ (List.getElem_mem _))).trans (hin i hi),
    fun i hi => (Term.expo_eq_expoT hRz hRw _ (hI _ (List.getElem_mem _))) ▸ hout i hi⟩

/-- **Lemma 5.1** (`lem:single`), on the heights: if at the heights of a germ the linear form of one term with a
nonvanishing coefficient is smaller than those of all other terms, the identity does not hold. -/
theorem single_of_expoT {G : Germ n m} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ}
    (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {I : Identity n} (hI : I.Holds)
    (hps : ∀ t ∈ I, ∀ kl ∈ t.ps, kl.1 ≠ kl.2) {i₀ : Fin I.length} (hc : G.cval I[i₀.1].coeff ≠ 0) {e : ℚ}
    (he : I[i₀.1].expoT Tz Tw htz htw = e)
    (hlt : ∀ j : Fin I.length, j ≠ i₀ → (e : WithTop ℚ) < I[j.1].expoT Tz Tw htz htw) : False := by
  refine single hI G hc (isArgmin_of_expoT hRz hRw hps (e := e) (fun i hi => ?_) fun i hi => hlt i ?_)
  · rw [mem_singleton] at hi
    rw [show i = i₀ from Fin.ext hi]
    exact he
  · rw [mem_singleton] at hi
    exact fun h => hi (congrArg Fin.val h)

end Identity

/-! ## Initial systems (§5.1) -/

/-- The variables of the initial systems (§5.1): the masses, `E`, the node coordinates `X_{v,c}` of the tree of `z`
and `Y_{v,c}` of the tree of `w` (a node `v` and a child `c` of it, as sets of points), and the leading coefficients
`P_kl` of the `p_kl` (used with `k < l`). -/
inductive CVar (n : ℕ)
  | mass (k : Fin n)
  | E
  | X (v c : Finset (Pt n))
  | Y (v c : Finset (Pt n))
  | P (k l : Fin n)
  deriving DecidableEq

/-- The polynomials of the initial systems: rational coefficients in the variables `CVar n`. -/
abbrev CPoly (n : ℕ) := MvPolynomial (CVar n) ℚ

namespace CPoly

variable {n : ℕ}

/-- A coefficient polynomial in the masses and `E` as a polynomial of the initial system. -/
def ofCoeff (c : MvPolynomial (Fin n ⊕ Unit) ℚ) : CPoly n :=
  MvPolynomial.rename (Sum.elim CVar.mass fun _ => CVar.E) c

/-- `X̂_{v,c}`: `0` for the first child `c₀` of `v` (Lemma 4.2), the variable `X_{v,c}` otherwise. -/
def xhat (v c : Finset (Pt n)) : CPoly n := if IsFirst v c then 0 else MvPolynomial.X (CVar.X v c)

/-- `Ŷ_{v,c}`: `0` for the first child `c₀` of `v`, the variable `Y_{v,c}` otherwise. -/
def yhat (v c : Finset (Pt n)) : CPoly n := if IsFirst v c then 0 else MvPolynomial.X (CVar.Y v c)

/-- `P_kl`, as the variable of the pair `(min k l, max k l)`. -/
def pvar (k l : Fin n) : CPoly n := MvPolynomial.X (CVar.P (min k l) (max k l))

/-- The substitution `m_j = 1` (Lemma 5.2 (b)). -/
def setMassOne (j : Fin n) : CPoly n →ₐ[ℚ] CPoly n :=
  MvPolynomial.aeval fun v => if v = CVar.mass j then 1 else MvPolynomial.X v

end CPoly

namespace TreeShape

variable {n : ℕ} (T : TreeShape n)

/-- `lc(z_p − z_q)` written through the tree `T` of `z` (Lemma 4.2): `X̂_{v,c(p)} − X̂_{v,c(q)}` with `v = lca(p, q)`,
and `0` if `p` and `q` share a leaf. -/
def zlc (p q : Pt n) : CPoly n :=
  if T.SameLeaf p q then 0
  else CPoly.xhat (T.lca p q) (T.child (T.lca p q) p) - CPoly.xhat (T.lca p q) (T.child (T.lca p q) q)

/-- `lc(w_p − w_q)` written through the tree `T` of `w` (Lemma 4.2). -/
def wlc (p q : Pt n) : CPoly n :=
  if T.SameLeaf p q then 0
  else CPoly.yhat (T.lca p q) (T.child (T.lca p q) p) - CPoly.yhat (T.lca p q) (T.child (T.lca p q) q)

end TreeShape

namespace Term

variable {n : ℕ}

/-- The term `c_i lc(g_i)` of an initial form as a polynomial of the initial system (§5.1), through the trees `Tz`
of `z` and `Tw` of `w`. -/
def poly (Tz Tw : TreeShape n) (t : Term n) : CPoly n :=
  CPoly.ofCoeff t.coeff * ((t.zs.map fun pq => Tz.zlc pq.1 pq.2).prod *
    (t.ws.map fun pq => Tw.wlc pq.1 pq.2).prod * (t.ps.map fun kl => CPoly.pvar kl.1 kl.2).prod)

end Term

/-- The initial form `Σ_{i ∈ S} c_i lc(g_i)` of an identity with argmin set `S` (§5.1), a polynomial in the node
coordinates of the trees `Tz`, `Tw`, the `P_kl`, `E` and the masses. -/
def Identity.initForm {n : ℕ} (Tz Tw : TreeShape n) (I : Identity n) (S : Finset ℕ) : CPoly n :=
  ∑ i ∈ univ.filter (fun i : Fin I.length => i.1 ∈ S), I[i.1].poly Tz Tw

/-- The distance polynomial `P_kl² lc(z_kl) lc(w_kl) − 1` of the pair `kl` (§5.1). -/
def distPoly {n : ℕ} (Tz Tw : TreeShape n) (k l : Fin n) : CPoly n :=
  CPoly.pvar k l ^ 2 * Tz.zlc (some k) (some l) * Tw.wlc (some k) (some l) - 1

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ} (G : Germ n m)

/-- The leading coefficients of `G` as a point of the variables of the initial systems (§5.1), for heights `htz`,
`htw` of the trees of `z` and `w`: the masses, `E`, the node coordinates and the `lc(p_kl)`. -/
def leadPt (htz htw : Finset (Pt n) → ℚ) : CVar n → ℂ
  | .mass k => (m k : ℂ)
  | .E => G.E
  | .X v c => G.xcoord htz v c
  | .Y v c => G.ycoord htw v c
  | .P k l => (G.p k l).leadingCoeff

variable {G} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ}

theorem eval_ofCoeff (c : MvPolynomial (Fin n ⊕ Unit) ℚ) :
    MvPolynomial.aeval (G.leadPt htz htw) (CPoly.ofCoeff c) = G.cval c := by
  have e : (G.leadPt htz htw ∘ Sum.elim CVar.mass fun _ : Unit => CVar.E) =
      Sum.elim (fun k => (m k : ℂ)) fun _ : Unit => G.E := by
    funext x
    rcases x with k | u <;> rfl
  rw [CPoly.ofCoeff, MvPolynomial.aeval_rename, e]
  rfl

theorem eval_pvar (k l : Fin n) : MvPolynomial.aeval (G.leadPt htz htw) (CPoly.pvar k l) = (G.p k l).leadingCoeff := by
  rw [CPoly.pvar, MvPolynomial.aeval_X]
  rcases le_total k l with h | h
  · rw [min_eq_left h, max_eq_right h]
    rfl
  · rw [min_eq_right h, max_eq_left h]
    show (G.p l k).leadingCoeff = _
    rw [G.p_symm]

theorem eval_xhat (hR : Tz.Realizes G.hz htz) {v : Finset (Pt n)} (hv : v ∈ Tz.nodes) {p : Pt n} (hp : p ∈ v) :
    MvPolynomial.aeval (G.leadPt htz htw) (CPoly.xhat v (Tz.child v p)) = G.xcoord htz v (Tz.child v p) := by
  unfold CPoly.xhat
  split_ifs with hf
  · rw [map_zero]
    exact (TreeShape.Realizes.coord_first (pos := G.zpos) hR hv hp hf).symm
  · rw [MvPolynomial.aeval_X]
    rfl

theorem eval_yhat (hR : Tw.Realizes G.hw htw) {v : Finset (Pt n)} (hv : v ∈ Tw.nodes) {p : Pt n} (hp : p ∈ v) :
    MvPolynomial.aeval (G.leadPt htz htw) (CPoly.yhat v (Tw.child v p)) = G.ycoord htw v (Tw.child v p) := by
  unfold CPoly.yhat
  split_ifs with hf
  · rw [map_zero]
    exact (TreeShape.Realizes.coord_first (pos := G.wpos) hR hv hp hf).symm
  · rw [MvPolynomial.aeval_X]
    rfl

/-- Lemma 4.2 at the level of polynomials: `zlc p q` evaluates to `lc(z_p − z_q)` at the leading coefficients. -/
theorem eval_zlc (hR : Tz.Realizes G.hz htz) (p q : Pt n) :
    MvPolynomial.aeval (G.leadPt htz htw) (Tz.zlc p q) = (G.zpos p - G.zpos q).leadingCoeff := by
  unfold TreeShape.zlc
  split_ifs with hs
  · rw [map_zero]
    have h0 := hR.same p q hs
    rw [hz_eq_top_iff] at h0
    rw [h0, sub_self, HahnSeries.leadingCoeff_zero]
  · have hv := Tz.lca_mem hR.wf p q
    rw [map_sub, eval_xhat hR hv (Tz.mem_lca_left p q), eval_xhat hR hv (Tz.mem_lca_right p q)]
    exact (lc_z_eq hR hs).symm

/-- `wlc p q` evaluates to `lc(w_p − w_q)` at the leading coefficients. -/
theorem eval_wlc (hR : Tw.Realizes G.hw htw) (p q : Pt n) :
    MvPolynomial.aeval (G.leadPt htz htw) (Tw.wlc p q) = (G.wpos p - G.wpos q).leadingCoeff := by
  unfold TreeShape.wlc
  split_ifs with hs
  · rw [map_zero]
    have h0 := hR.same p q hs
    rw [hw_eq_top_iff] at h0
    rw [h0, sub_self, HahnSeries.leadingCoeff_zero]
  · have hv := Tw.lca_mem hR.wf p q
    rw [map_sub, eval_yhat hR hv (Tw.mem_lca_left p q), eval_yhat hR hv (Tw.mem_lca_right p q)]
    exact (lc_w_eq hR hs).symm

/-- The polynomial of a term evaluates to `c_i lc(g_i)` at the leading coefficients. -/
theorem eval_poly (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) (t : Term n) :
    MvPolynomial.aeval (G.leadPt htz htw) (t.poly Tz Tw) = G.cval t.coeff * t.lead G := by
  simp only [Term.poly, Term.lead, map_mul, map_list_prod, List.map_map, Function.comp_def, eval_ofCoeff,
    eval_zlc hRz, eval_wlc hRw, eval_pvar]

/-- §5.1: at the leading coefficients of a germ realizing the trees, the initial form of an identity that holds
vanishes when `S` is its argmin set at the germ (Lemma 2.10). -/
theorem eval_initForm (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {I : Identity n} (hI : I.Holds)
    {S : Finset ℕ} (hS : I.IsArgmin G S) : MvPolynomial.aeval (G.leadPt htz htw) (I.initForm Tz Tw S) = 0 := by
  obtain ⟨e, hin, hout⟩ := hS
  have h0 := initial_coeff (s := univ) (c := fun i : Fin I.length => G.cval I[i.1].coeff)
    (g := fun i => I[i.1].mono G) (Identity.sum_eq_zero hI G) e
  rw [Identity.initForm, map_sum, ← h0, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_poly hRz hRw]
  split_ifs with hi
  · rw [Ser.coeff_of_orderTop_eq ((Term.orderTop_mono _ _).trans (hin i hi)), Term.leadingCoeff_mono]
  · rw [Ser.coeff_eq_zero_of_lt (by rw [Term.orderTop_mono]; exact hout i hi), mul_zero]

/-- §5.1: the distance polynomials vanish at the leading coefficients (`p_kl² z_kl w_kl = 1`). -/
theorem eval_distPoly (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {k l : Fin n} (hkl : k ≠ l) :
    MvPolynomial.aeval (G.leadPt htz htw) (distPoly Tz Tw k l) = 0 := by
  rw [distPoly, map_sub, map_mul, map_mul, map_pow, eval_pvar, eval_zlc hRz, eval_wlc hRw, map_one, sub_eq_zero]
  have h := congrArg HahnSeries.leadingCoeff (G.dist k l hkl)
  rw [HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_mul, Ser.leadingCoeff_pow,
    HahnSeries.leadingCoeff_one] at h
  exact h

end Germ

/-! ## Cores (Lemma 5.2) -/

/-- A member of an initial system (§5.1): the initial form of an identity with an argmin set, or the distance
polynomial of a pair. -/
inductive CoreItem (n : ℕ)
  | init (I : Identity n) (S : Finset ℕ)
  | dist (k l : Fin n)

namespace CoreItem

variable {n : ℕ} {m : Fin n → ℝ}

/-- The polynomial of the item, through the trees `Tz`, `Tw`. -/
def poly (Tz Tw : TreeShape n) : CoreItem n → CPoly n
  | init I S => I.initForm Tz Tw S
  | dist k l => distPoly Tz Tw k l

/-- The item belongs to the initial system of `G`: the identity holds and `S` is its argmin set at `G`, or the pair
consists of two bodies. -/
def Valid (G : Germ n m) : CoreItem n → Prop
  | init I S => I.Holds ∧ I.IsArgmin G S
  | dist k l => k ≠ l

theorem eval_poly_eq_zero {G : Germ n m} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ}
    (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {it : CoreItem n} (hv : it.Valid G) :
    MvPolynomial.aeval (G.leadPt htz htw) (it.poly Tz Tw) = 0 := by
  cases it with
  | init I S => exact Germ.eval_initForm hRz hRw hv.1 hv.2
  | dist k l => exact Germ.eval_distPoly hRz hRw hv

end CoreItem

variable {n : ℕ} {m : Fin n → ℝ}

/-- **Lemma 5.2 (a)** (`lem:core`), with explicit cofactors: let `G` be a germ realizing the trees `Tz`, `Tw` with
some heights, and `f_i` members of its initial system (initial forms of identities that hold, with their argmin sets
at `G`, and distance polynomials). If `Σ_i g_i f_i = h(m)` for polynomials `g_i` and `h ∈ ℚ[m]`, then `h(m) = 0`. -/
theorem core {G : Germ n m} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ} (items : List (CoreItem n))
    (gs : List (CPoly n)) (h : MvPolynomial (Fin n) ℚ) (hvalid : ∀ it ∈ items, it.Valid G)
    (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw)
    (hsum : (List.zipWith (· * ·) gs (items.map (CoreItem.poly Tz Tw))).sum = MvPolynomial.rename CVar.mass h) :
    MvPolynomial.aeval m h = 0 := by
  have h0 : MvPolynomial.aeval (G.leadPt htz htw) (MvPolynomial.rename CVar.mass h) = 0 := by
    rw [← hsum]
    refine aeval_zipWith_sum_eq_zero _ _ _ fun f hf => ?_
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hf
    exact CoreItem.eval_poly_eq_zero hRz hRw (hvalid it hit)
  rw [MvPolynomial.aeval_rename] at h0
  exact aeval_ofReal_eq_zero (x := m) h0

/-- **Lemma 5.2 (a)** (`lem:core`), with ideal membership: if `h(m)` lies in the ideal generated by members of the
initial system of `G`, then `h(m) = 0`. -/
theorem core_span {G : Germ n m} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ} (F : Set (CPoly n))
    (hF : ∀ f ∈ F, ∃ it : CoreItem n, it.Valid G ∧ f = it.poly Tz Tw) (hRz : Tz.Realizes G.hz htz)
    (hRw : Tw.Realizes G.hw htw) (h : MvPolynomial (Fin n) ℚ)
    (hmem : MvPolynomial.rename CVar.mass h ∈ Ideal.span F) : MvPolynomial.aeval m h = 0 := by
  have hker : Ideal.span F ≤ RingHom.ker (MvPolynomial.aeval (R := ℚ) (G.leadPt htz htw)) := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨it, hit, rfl⟩ := hF f hf
    exact RingHom.mem_ker.mpr (CoreItem.eval_poly_eq_zero hRz hRw hit)
  have h0 := RingHom.mem_ker.mp (hker hmem)
  rw [MvPolynomial.aeval_rename] at h0
  exact aeval_ofReal_eq_zero (x := m) h0

/-- Lemma 5.2 (a) for a germ that lies in a cell: the members of the initial system are written through the trees
of the cell. -/
theorem Germ.LiesIn.core {G : Germ n m} {c : Cell n} (hG : G.LiesIn c) (items : List (CoreItem n))
    (gs : List (CPoly n)) (h : MvPolynomial (Fin n) ℚ) (hvalid : ∀ it ∈ items, it.Valid G)
    (hsum : (List.zipWith (· * ·) gs (items.map (CoreItem.poly c.tz c.tw))).sum = MvPolynomial.rename CVar.mass h) :
    MvPolynomial.aeval m h = 0 := by
  obtain ⟨htz, htw, hRz, hRw, -⟩ := hG
  exact CC6Full.core items gs h hvalid hRz hRw hsum

/-! ## Lemma 5.2 (b): one mass set to `1` -/

namespace Germ

variable (G : Germ n m) (t : ℝ) (ht : 0 < t)

theorem scale_zpos (p : Pt n) : (G.scale t ht).zpos p = cS (cubeRoot t) * G.zpos p := by
  cases p with
  | none => rw [zpos_none, zpos_none, mul_zero]
  | some k => rfl

theorem scale_wpos (p : Pt n) : (G.scale t ht).wpos p = cS (cubeRoot t) * G.wpos p := by
  cases p with
  | none => rw [wpos_none, wpos_none, mul_zero]
  | some k => rfl

/-- Scaling the masses does not change the exponents `e(z_p − z_q)` (Lemma 2.1 (b)). -/
theorem scale_hz : (G.scale t ht).hz = G.hz := by
  funext p q
  rw [hz_def, hz_def, scale_zpos, scale_zpos, ← mul_sub, Ser.orderTop_cS_mul (cubeRoot_ne_zero ht)]

/-- Scaling the masses does not change the exponents `e(w_p − w_q)`. -/
theorem scale_hw : (G.scale t ht).hw = G.hw := by
  funext p q
  rw [hw_def, hw_def, scale_wpos, scale_wpos, ← mul_sub, Ser.orderTop_cS_mul (cubeRoot_ne_zero ht)]

end Germ

theorem Term.expo_scale (G : Germ n m) {t : ℝ} (ht : 0 < t) (τ : Term n) : τ.expo (G.scale t ht) = τ.expo G := by
  simp only [Term.expo, Germ.scale_hz, Germ.scale_hw, Germ.scale_p,
    Ser.orderTop_cS_mul (inv_ne_zero (Germ.cubeRoot_ne_zero ht))]

theorem Identity.IsArgmin.scale {I : Identity n} {G : Germ n m} {S : Finset ℕ} (hS : I.IsArgmin G S) {t : ℝ}
    (ht : 0 < t) : I.IsArgmin (G.scale t ht) S := by
  obtain ⟨e, hin, hout⟩ := hS
  exact ⟨e, fun i hi => (Term.expo_scale G ht _).trans (hin i hi), fun i hi => (Term.expo_scale G ht _) ▸ hout i hi⟩

theorem CoreItem.Valid.scale {it : CoreItem n} {G : Germ n m} (hv : it.Valid G) {t : ℝ} (ht : 0 < t) :
    it.Valid (G.scale t ht) := by
  cases it with
  | init I S => exact ⟨hv.1, hv.2.scale ht⟩
  | dist k l => exact hv

theorem aeval_setMassOne {V : CVar n → ℂ} {j : Fin n} (hV : V (CVar.mass j) = 1) (f : CPoly n) :
    MvPolynomial.aeval V (CPoly.setMassOne j f) = MvPolynomial.aeval V f := by
  have hF : (fun v => MvPolynomial.aeval V (if v = CVar.mass j then (1 : CPoly n) else MvPolynomial.X v)) = V := by
    funext v
    split_ifs with hv
    · rw [hv, map_one, hV]
    · rw [MvPolynomial.aeval_X]
  simp only [CPoly.setMassOne, MvPolynomial.comp_aeval_apply]
  rw [hF]

/-- **Lemma 5.2 (b)** (`lem:core`): the same with the mass `m_j` set to `1` in the members of the initial system:
if `Σ_i g_i f_i|_{m_j = 1} = h(m)`, then `h(m / m_j) = 0`. Proof of the paper: the germ `G.scale (1 / m_j)` has the
masses `m / m_j` (Lemma 2.1 (b)), the same exponents, trees, heights and argmin sets, and part (a) applies to it. -/
theorem core_b {G : Germ n m} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ} (j : Fin n) (hj : 0 < m j)
    (items : List (CoreItem n)) (gs : List (CPoly n)) (h : MvPolynomial (Fin n) ℚ)
    (hvalid : ∀ it ∈ items, it.Valid G) (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw)
    (hsum : (List.zipWith (· * ·) gs (items.map fun it => CPoly.setMassOne j (it.poly Tz Tw))).sum =
      MvPolynomial.rename CVar.mass h) :
    MvPolynomial.aeval (fun k => m k / m j) h = 0 := by
  have ht : 0 < (m j)⁻¹ := inv_pos.mpr hj
  set G' := G.scale (m j)⁻¹ ht with hG'
  have hRz' : Tz.Realizes G'.hz htz := by rw [hG', Germ.scale_hz]; exact hRz
  have hRw' : Tw.Realizes G'.hw htw := by rw [hG', Germ.scale_hw]; exact hRw
  have hV : G'.leadPt htz htw (CVar.mass j) = 1 := by
    show ((((m j)⁻¹ • m) j : ℝ) : ℂ) = 1
    rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hj.ne', Complex.ofReal_one]
  have h0 : MvPolynomial.aeval (G'.leadPt htz htw) (MvPolynomial.rename CVar.mass h) = 0 := by
    rw [← hsum]
    refine aeval_zipWith_sum_eq_zero _ _ _ fun f hf => ?_
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hf
    rw [aeval_setMassOne hV]
    exact CoreItem.eval_poly_eq_zero hRz' hRw' ((hvalid it hit).scale ht)
  rw [MvPolynomial.aeval_rename] at h0
  have h1 : (G'.leadPt htz htw ∘ CVar.mass) = fun k => ((m k / m j : ℝ) : ℂ) := by
    funext k
    show ((((m j)⁻¹ • m) k : ℝ) : ℂ) = _
    rw [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  rw [h1] at h0
  exact aeval_ofReal_eq_zero h0

/-! ## The product `Θ` (§5.1) and Lemma 5.2 with saturation -/

namespace TreeShape

variable (T : TreeShape n)

/-- The product of the differences `X̂_{v,c} − X̂_{v,c'}` over the nodes `v` of the tree `T` of `z` and the ordered
pairs of distinct children `c ≠ c'` of `v` (§5.1). Since `X̂_{v,c₀} = 0`, it contains the coordinates `X_{v,c}`,
`c ≠ c₀`, up to sign. -/
def thetaX : CPoly n :=
  ∏ v ∈ T.nodes.toFinset, ∏ cc ∈ (T.children v).offDiag, (CPoly.xhat v cc.1 - CPoly.xhat v cc.2)

/-- The same product for the tree `T` of `w`, with the coordinates `Ŷ_{v,c}`. -/
def thetaY : CPoly n :=
  ∏ v ∈ T.nodes.toFinset, ∏ cc ∈ (T.children v).offDiag, (CPoly.yhat v cc.1 - CPoly.yhat v cc.2)

end TreeShape

/-- The product `Θ` of §5.1 for the trees `Tz`, `Tw`: the node coordinates `X_{v,c}`, `Y_{v,c}` (`c ≠ c₀`) and their
differences at each node, the `P_kl` (`k < l`) and `E`. -/
def theta (Tz Tw : TreeShape n) : CPoly n :=
  Tz.thetaX * Tw.thetaY * (∏ k : Fin n, ∏ l ∈ Ioi k, CPoly.pvar k l) * MvPolynomial.X CVar.E

namespace Germ

variable {G : Germ n m} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ}

/-- Lemma 4.2: the node coordinates of distinct children of a node differ. -/
theorem eval_xhat_sub_ne_zero (hR : Tz.Realizes G.hz htz) {v : Finset (Pt n)} (hv : v ∈ Tz.nodes)
    {c c' : Finset (Pt n)} (hc : c ∈ Tz.children v) (hc' : c' ∈ Tz.children v) (hne : c ≠ c') :
    MvPolynomial.aeval (G.leadPt htz htw) (CPoly.xhat v c - CPoly.xhat v c') ≠ 0 := by
  simp only [TreeShape.children, mem_image] at hc hc'
  obtain ⟨p, hp, rfl⟩ := hc
  obtain ⟨q, hq, rfl⟩ := hc'
  rw [map_sub, eval_xhat hR hv hp, eval_xhat hR hv hq, sub_ne_zero]
  exact TreeShape.Realizes.coord_ne (pos := G.zpos) hR hv hp hq fun hqp =>
    hne (Tz.child_eq_of_mem hR.wf hqp).symm

/-- Lemma 4.2: the node coordinates of distinct children of a node of the tree of `w` differ. -/
theorem eval_yhat_sub_ne_zero (hR : Tw.Realizes G.hw htw) {v : Finset (Pt n)} (hv : v ∈ Tw.nodes)
    {c c' : Finset (Pt n)} (hc : c ∈ Tw.children v) (hc' : c' ∈ Tw.children v) (hne : c ≠ c') :
    MvPolynomial.aeval (G.leadPt htz htw) (CPoly.yhat v c - CPoly.yhat v c') ≠ 0 := by
  simp only [TreeShape.children, mem_image] at hc hc'
  obtain ⟨p, hp, rfl⟩ := hc
  obtain ⟨q, hq, rfl⟩ := hc'
  rw [map_sub, eval_yhat hR hv hp, eval_yhat hR hv hq, sub_ne_zero]
  exact TreeShape.Realizes.coord_ne (pos := G.wpos) hR hv hp hq fun hqp =>
    hne (Tw.child_eq_of_mem hR.wf hqp).symm

/-- §5.1: `Θ` does not vanish at the leading coefficients of a germ realizing the trees. -/
theorem eval_theta_ne_zero (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) :
    MvPolynomial.aeval (G.leadPt htz htw) (theta Tz Tw) ≠ 0 := by
  have hX : MvPolynomial.aeval (G.leadPt htz htw) Tz.thetaX ≠ 0 := by
    rw [TreeShape.thetaX, map_prod, Finset.prod_ne_zero_iff]
    intro v hv
    rw [map_prod, Finset.prod_ne_zero_iff]
    intro cc hcc
    rw [mem_offDiag] at hcc
    exact eval_xhat_sub_ne_zero hRz (List.mem_toFinset.mp hv) hcc.1 hcc.2.1 hcc.2.2
  have hY : MvPolynomial.aeval (G.leadPt htz htw) Tw.thetaY ≠ 0 := by
    rw [TreeShape.thetaY, map_prod, Finset.prod_ne_zero_iff]
    intro v hv
    rw [map_prod, Finset.prod_ne_zero_iff]
    intro cc hcc
    rw [mem_offDiag] at hcc
    exact eval_yhat_sub_ne_zero hRw (List.mem_toFinset.mp hv) hcc.1 hcc.2.1 hcc.2.2
  have hP : MvPolynomial.aeval (G.leadPt htz htw) (∏ k : Fin n, ∏ l ∈ Ioi k, CPoly.pvar k l) ≠ 0 := by
    rw [map_prod, Finset.prod_ne_zero_iff]
    intro k _
    rw [map_prod, Finset.prod_ne_zero_iff]
    intro l hl
    rw [eval_pvar]
    exact HahnSeries.leadingCoeff_ne_zero.mpr (G.p_ne_zero (mem_Ioi.mp hl).ne)
  have hE : MvPolynomial.aeval (G.leadPt htz htw) (MvPolynomial.X CVar.E : CPoly n) ≠ 0 := by
    rw [MvPolynomial.aeval_X]
    exact G.E_ne
  rw [theta, map_mul, map_mul, map_mul]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hX hY) hP) hE

end Germ

/-- **Lemma 5.2 (a)** (`lem:core`) with saturation by `Θ`: if `Σ_i g_i f_i = h(m) Θ^N` for members `f_i` of the
initial system of `G`, then `h(m) = 0` (the leading coefficients are a common zero of the `f_i` at which `Θ` does not
vanish). -/
theorem core_theta {G : Germ n m} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ} (items : List (CoreItem n))
    (gs : List (CPoly n)) (h : MvPolynomial (Fin n) ℚ) (N : ℕ) (hvalid : ∀ it ∈ items, it.Valid G)
    (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw)
    (hsum : (List.zipWith (· * ·) gs (items.map (CoreItem.poly Tz Tw))).sum =
      MvPolynomial.rename CVar.mass h * theta Tz Tw ^ N) :
    MvPolynomial.aeval m h = 0 := by
  have h0 : MvPolynomial.aeval (G.leadPt htz htw) (MvPolynomial.rename CVar.mass h * theta Tz Tw ^ N) = 0 := by
    rw [← hsum]
    refine aeval_zipWith_sum_eq_zero _ _ _ fun f hf => ?_
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hf
    exact CoreItem.eval_poly_eq_zero hRz hRw (hvalid it hit)
  rw [map_mul, map_pow, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · rw [MvPolynomial.aeval_rename] at h0
    exact aeval_ofReal_eq_zero (x := m) h0
  · exact absurd h0 (pow_ne_zero N (Germ.eval_theta_ne_zero hRz hRw))

/-- **Lemma 5.2 (b)** (`lem:core`) with saturation by `Θ`: if `Σ_i g_i f_i|_{m_j = 1} = h(m) Θ^N`, then
`h(m / m_j) = 0`. -/
theorem core_b_theta {G : Germ n m} {Tz Tw : TreeShape n} {htz htw : Finset (Pt n) → ℚ} (j : Fin n) (hj : 0 < m j)
    (items : List (CoreItem n)) (gs : List (CPoly n)) (h : MvPolynomial (Fin n) ℚ) (N : ℕ)
    (hvalid : ∀ it ∈ items, it.Valid G) (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw)
    (hsum : (List.zipWith (· * ·) gs (items.map fun it => CPoly.setMassOne j (it.poly Tz Tw))).sum =
      MvPolynomial.rename CVar.mass h * theta Tz Tw ^ N) :
    MvPolynomial.aeval (fun k => m k / m j) h = 0 := by
  have ht : 0 < (m j)⁻¹ := inv_pos.mpr hj
  set G' := G.scale (m j)⁻¹ ht with hG'
  have hRz' : Tz.Realizes G'.hz htz := by rw [hG', Germ.scale_hz]; exact hRz
  have hRw' : Tw.Realizes G'.hw htw := by rw [hG', Germ.scale_hw]; exact hRw
  have hV : G'.leadPt htz htw (CVar.mass j) = 1 := by
    show ((((m j)⁻¹ • m) j : ℝ) : ℂ) = 1
    rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hj.ne', Complex.ofReal_one]
  have h0 : MvPolynomial.aeval (G'.leadPt htz htw) (MvPolynomial.rename CVar.mass h * theta Tz Tw ^ N) = 0 := by
    rw [← hsum]
    refine aeval_zipWith_sum_eq_zero _ _ _ fun f hf => ?_
    obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hf
    rw [aeval_setMassOne hV]
    exact CoreItem.eval_poly_eq_zero hRz' hRw' ((hvalid it hit).scale ht)
  rw [map_mul, map_pow, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · rw [MvPolynomial.aeval_rename] at h0
    have h1 : (G'.leadPt htz htw ∘ CVar.mass) = fun k => ((m k / m j : ℝ) : ℂ) := by
      funext k
      show ((((m j)⁻¹ • m) k : ℝ) : ℂ) = _
      rw [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [h1] at h0
    exact aeval_ofReal_eq_zero h0
  · exact absurd h0 (pow_ne_zero N (Germ.eval_theta_ne_zero hRz' hRw'))

end

end CC6Full
