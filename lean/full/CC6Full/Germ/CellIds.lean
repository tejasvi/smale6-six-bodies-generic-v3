import CC6Full.Germ.Cell
import CC6Full.Germ.Identities

/-!
# The identities of §5.1 as data

Besides the base identities, the initial systems of §5.1 (the list at the beginning of Section 5, `sec:exclusion`)
use the following identities of §2.3 (`ss:identities`): the subset sums, the torques `T_J`, the partial virials, the
differences, `U = Σ_k m_k z_k w_k` and `Σ_k m_k z_k w_k = E`. This file writes them as data `Identity n`
(`Cell.lean`) for every number of bodies `n`, every set of bodies `J : Finset (Fin n)` and all bodies `k`, `l`, and
proves that they hold at every germ (`Identity.Holds`) from the equalities of series of `Identities.lean`.

## The form of the identities

Each term is a coefficient in `ℚ[m, E]` times a product of the factors `z_k`, `w_k`, `z_kl`, `w_kl`, `p_kl` of §2.3.
As in `Identity.bodyZ`, the position `z_k` is the factor `(some k, none)`, that is `z_k − z_O` with `z_O = 0`, the
separation `z_kl = z_k − z_l` is the factor `(some k, some l)`, and `Z_kl = p_kl³ z_kl` is the factor `z_kl` with three
factors `p_kl`, written `(k, l)` with the bodies in the order of the formula (`G.p_symm` and `CPoly.pvar` make this
order irrelevant). An identity `A = B` of §2.3 is written `A − B = 0`, with the terms of `A` first and then those of
`B`, each sum in the order of the formula. A sum over `k ∈ J` runs over `Identity.bodiesIn J` (increasing `k`), a sum
over `k ∈ J`, `l ∈ Jᶜ` over `Identity.cross J` (the pairs `(k, l)` in lexicographic order), and a sum over `k < l`
in `J` over `Identity.pairsIn J` (lexicographic order).

* `Identity.subsetSumZ J`, `Identity.subsetSumW J` (subset sums):
  `Σ_{k∈J} m_k z_k − Σ_{k∈J, l∈Jᶜ} m_k m_l p_kl³ z_kl = 0`, and the same in `w`.
* `Identity.torque J` (torques): `T_J = Σ_{k∈J, l∈Jᶜ} (m_k m_l p_kl³ z_k w_l − m_k m_l p_kl³ z_l w_k) = 0`; the two
  terms of each pair are listed separately, `m_k m_l p_kl³ z_k w_l` first.
* `Identity.partialVirial J` (partial virials):
  `Σ_{k∈J} m_k z_k w_k − Σ_{k<l ∈ J} m_k m_l p_kl − ½ Σ_{k∈J, l∈Jᶜ} m_k m_l p_kl³ (w_k z_kl + z_k w_kl) = 0`.
  It is **not** multiplied by `2`: the terms of the last sum have the coefficient `−½ m_k m_l` (`C (1/2)`), and the
  two terms `w_k z_kl` and `z_k w_kl` of each pair are listed separately, in this order. The sum over the pairs inside
  `J` is over `k < l` (each pair once, coefficient `−m_k m_l`), not over the ordered pairs.
* `Identity.differenceZ k l`, `Identity.differenceW k l` (differences):
  `z_kl − Σ_{j≠k} m_j p_kj³ z_kj + Σ_{j≠l} m_j p_lj³ z_lj = 0` (the term `z_kl` with coefficient `1`, then the terms
  of the first sum, then those of the second, each in increasing `j`), and the same in `w`. They hold for all `k`, `l`.
* `Identity.potVirial n`: `U = Σ_k m_k z_k w_k`, written `Σ_{k<l} m_k m_l p_kl − Σ_k m_k z_k w_k = 0` with the pairs
  in the order of `Identity.pairs n` (as in `Identity.potU`).
* `Identity.virialE n`: `Σ_k m_k z_k w_k − E = 0`, the constant last (as in `Identity.potU`).

The terms with a factor that vanishes identically (a position `z_k` with `z_k = 0`) are kept: their exponent is `⊤`,
so they lie in no argmin set (`Identity.IsArgmin`), while §2.3 omits them.

## The list of §5.1

`Identity.secondary n j₀` is the set of the identities of the list of §5.1, with the paper's conditions: the subset
sums for `2 ≤ |J| ≤ 4`, the torques `T_J` for the sets `J ∋ j₀` with `|J| ≤ 5` (the paper's body `1` is `j₀`, which is
`0 : Fin 6` for six bodies), the partial virials for all nonempty `J ≠ {1, …, n}`, the differences of the pairs
`k < l`, `U = Σ_k m_k z_k w_k` and `Σ_k m_k z_k w_k = E`. They hold (`Identity.secondary_holds`), and their factors
`p_kl` have `k ≠ l` (`Identity.secondary_psNe`, the hypothesis of `Identity.isArgmin_of_expoT` and
`Identity.single_of_expoT`).
-/

namespace CC6Full

open Finset

noncomputable section

namespace Identity

variable {n : ℕ}

/-! ## Lists of bodies and pairs -/

/-- The bodies of `J`, in increasing order. -/
def bodiesIn (J : Finset (Fin n)) : List (Fin n) := (List.finRange n).filter fun k => k ∈ J

/-- The pairs `(k, l)` with `k ∈ J` and `l ∈ Jᶜ`, in lexicographic order. -/
def cross (J : Finset (Fin n)) : List (Fin n × Fin n) :=
  (bodiesIn J).flatMap fun k => (bodiesIn Jᶜ).map fun l => (k, l)

/-- The pairs `(k, l)` with `k < l` in `J`, in lexicographic order. -/
def pairsIn (J : Finset (Fin n)) : List (Fin n × Fin n) :=
  (bodiesIn J).flatMap fun k => ((bodiesIn J).filter fun l => k < l).map fun l => (k, l)

theorem mem_bodiesIn {J : Finset (Fin n)} {k : Fin n} : k ∈ bodiesIn J ↔ k ∈ J := by
  simp [bodiesIn]

theorem mem_cross {J : Finset (Fin n)} {kl : Fin n × Fin n} : kl ∈ cross J ↔ kl.1 ∈ J ∧ kl.2 ∉ J := by
  obtain ⟨k, l⟩ := kl
  simp only [cross, List.mem_flatMap, List.mem_map, mem_bodiesIn, Finset.mem_compl, Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk', l', hl', rfl, rfl⟩
    exact ⟨hk', hl'⟩
  · rintro ⟨hk, hl⟩
    exact ⟨k, hk, l, hl, rfl, rfl⟩

theorem mem_pairsIn {J : Finset (Fin n)} {kl : Fin n × Fin n} :
    kl ∈ pairsIn J ↔ kl.1 ∈ J ∧ kl.2 ∈ J ∧ kl.1 < kl.2 := by
  obtain ⟨k, l⟩ := kl
  simp only [pairsIn, List.mem_flatMap, List.mem_map, List.mem_filter, mem_bodiesIn, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk', l', ⟨hl', hkl⟩, rfl, rfl⟩
    exact ⟨hk', hl', hkl⟩
  · rintro ⟨hk, hl, hkl⟩
    exact ⟨k, hk, l, ⟨hl, hkl⟩, rfl, rfl⟩

theorem mem_pairs {kl : Fin n × Fin n} : kl ∈ pairs n ↔ kl.1 < kl.2 := by
  obtain ⟨k, l⟩ := kl
  simp only [pairs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨k', l', hkl, rfl, rfl⟩
    exact hkl
  · intro hkl
    exact ⟨k, l, hkl, rfl, rfl⟩

theorem sum_bodiesIn {M : Type*} [AddCommMonoid M] (J : Finset (Fin n)) (f : Fin n → M) :
    ((bodiesIn J).map f).sum = ∑ k ∈ J, f k := by
  rw [bodiesIn, sum_map_filter_finRange]
  refine Finset.sum_congr ?_ fun k _ => rfl
  ext k
  simp

theorem sum_cross {M : Type*} [AddCommMonoid M] (J : Finset (Fin n)) (f : Fin n × Fin n → M) :
    ((cross J).map f).sum = ∑ k ∈ J, ∑ l ∈ Jᶜ, f (k, l) := by
  rw [cross, list_sum_flatMap, sum_bodiesIn]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [List.map_map]
  exact sum_bodiesIn Jᶜ fun l => f (k, l)

theorem sum_pairsIn {M : Type*} [AddCommMonoid M] (J : Finset (Fin n)) (f : Fin n × Fin n → M) :
    ((pairsIn J).map f).sum = ∑ k ∈ J, ∑ l ∈ J with k < l, f (k, l) := by
  rw [pairsIn, list_sum_flatMap, sum_bodiesIn]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [List.map_map, bodiesIn, List.filter_filter, sum_map_filter_finRange]
  refine Finset.sum_congr ?_ fun l _ => rfl
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq]
  tauto

variable {m : Fin n → ℝ}

theorem eval_flatMap {α : Type*} (L : List α) (g : α → Identity n) (G : Germ n m) :
    eval (L.flatMap g) G = (L.map fun a => (g a).eval G).sum :=
  list_sum_flatMap L g fun t => t.eval G

theorem eval_pair (a b : Term n) (G : Germ n m) : eval [a, b] G = a.eval G + b.eval G := by
  simp [eval]

theorem cval_half (G : Germ n m) : G.cval (MvPolynomial.C (1 / 2 : ℚ)) = 1 / 2 := by
  simp [Germ.cval]

/-! ## The identities -/

/-- **Subset sums** in `z` (§2.3): `Σ_{k∈J} m_k z_k − Σ_{k∈J, l∈Jᶜ} m_k m_l p_kl³ z_kl = 0`. The terms `m_k z_k`
(`k ∈ J`, increasing), then the terms `−m_k m_l p_kl³ z_kl` (`(k, l) ∈ cross J`). -/
def subsetSumZ (J : Finset (Fin n)) : Identity n :=
  (bodiesIn J).map (fun k => ⟨cm k, [(some k, none)], [], []⟩) ++
    (cross J).map fun kl => ⟨-(cm kl.1 * cm kl.2), [(some kl.1, some kl.2)], [], [kl, kl, kl]⟩

/-- **Subset sums** in `w` (§2.3): `Σ_{k∈J} m_k w_k − Σ_{k∈J, l∈Jᶜ} m_k m_l p_kl³ w_kl = 0`, with the terms in the
order of `subsetSumZ`. -/
def subsetSumW (J : Finset (Fin n)) : Identity n :=
  (bodiesIn J).map (fun k => ⟨cm k, [], [(some k, none)], []⟩) ++
    (cross J).map fun kl => ⟨-(cm kl.1 * cm kl.2), [], [(some kl.1, some kl.2)], [kl, kl, kl]⟩

/-- **Torques** (§2.3): `T_J = Σ_{k∈J, l∈Jᶜ} (m_k m_l p_kl³ z_k w_l − m_k m_l p_kl³ z_l w_k) = 0`. For each pair
`(k, l) ∈ cross J` the two terms are listed separately: `m_k m_l p_kl³ z_k w_l`, then `−m_k m_l p_kl³ z_l w_k`. -/
def torque (J : Finset (Fin n)) : Identity n :=
  (cross J).flatMap fun kl =>
    [⟨cm kl.1 * cm kl.2, [(some kl.1, none)], [(some kl.2, none)], [kl, kl, kl]⟩,
      ⟨-(cm kl.1 * cm kl.2), [(some kl.2, none)], [(some kl.1, none)], [kl, kl, kl]⟩]

/-- **Partial virials** (§2.3), as in the paper, not multiplied by `2`:
`Σ_{k∈J} m_k z_k w_k − Σ_{k<l ∈ J} m_k m_l p_kl − ½ Σ_{k∈J, l∈Jᶜ} m_k m_l p_kl³ (w_k z_kl + z_k w_kl) = 0`.
The terms `m_k z_k w_k` (`k ∈ J`, increasing); the terms `−m_k m_l p_kl` of the pairs `k < l` inside `J`
(`pairsIn J`, each pair once); for each pair `(k, l) ∈ cross J` the two terms `−½ m_k m_l p_kl³ w_k z_kl` and
`−½ m_k m_l p_kl³ z_k w_kl`, in this order, with the coefficient `−½ m_k m_l` written `−(C (1/2) · m_k m_l)`. -/
def partialVirial (J : Finset (Fin n)) : Identity n :=
  (bodiesIn J).map (fun k => ⟨cm k, [(some k, none)], [(some k, none)], []⟩) ++
    (pairsIn J).map (fun kl => ⟨-(cm kl.1 * cm kl.2), [], [], [kl]⟩) ++
    (cross J).flatMap fun kl =>
      [⟨-(MvPolynomial.C (1 / 2 : ℚ) * (cm kl.1 * cm kl.2)), [(some kl.1, some kl.2)], [(some kl.1, none)],
          [kl, kl, kl]⟩,
        ⟨-(MvPolynomial.C (1 / 2 : ℚ) * (cm kl.1 * cm kl.2)), [(some kl.1, none)], [(some kl.1, some kl.2)],
          [kl, kl, kl]⟩]

/-- **Differences** in `z` (§2.3): `z_kl = Σ_{j≠k} m_j Z_kj − Σ_{j≠l} m_j Z_lj`, written
`z_kl − Σ_{j≠k} m_j p_kj³ z_kj + Σ_{j≠l} m_j p_lj³ z_lj = 0`: the term `z_kl` (coefficient `1`), then the terms
`−m_j p_kj³ z_kj` (`j ≠ k`, increasing), then the terms `m_j p_lj³ z_lj` (`j ≠ l`, increasing). -/
def differenceZ (k l : Fin n) : Identity n :=
  ⟨1, [(some k, some l)], [], []⟩ ::
    (((List.finRange n).filter fun j => j ≠ k).map
        (fun j => ⟨-cm j, [(some k, some j)], [], [(k, j), (k, j), (k, j)]⟩) ++
      ((List.finRange n).filter fun j => j ≠ l).map
        fun j => ⟨cm j, [(some l, some j)], [], [(l, j), (l, j), (l, j)]⟩)

/-- **Differences** in `w` (§2.3): `w_kl − Σ_{j≠k} m_j p_kj³ w_kj + Σ_{j≠l} m_j p_lj³ w_lj = 0`, with the terms in
the order of `differenceZ`. -/
def differenceW (k l : Fin n) : Identity n :=
  ⟨1, [], [(some k, some l)], []⟩ ::
    (((List.finRange n).filter fun j => j ≠ k).map
        (fun j => ⟨-cm j, [], [(some k, some j)], [(k, j), (k, j), (k, j)]⟩) ++
      ((List.finRange n).filter fun j => j ≠ l).map
        fun j => ⟨cm j, [], [(some l, some j)], [(l, j), (l, j), (l, j)]⟩)

/-- `U = Σ_k m_k z_k w_k` (§2.3, Lemma 2.3 (a)), written `Σ_{k<l} m_k m_l p_kl − Σ_k m_k z_k w_k = 0`: the terms
`m_k m_l p_kl` in the order of `pairs n` (as in `potU`), then the terms `−m_k z_k w_k` (increasing `k`). -/
def potVirial (n : ℕ) : Identity n :=
  (pairs n).map (fun kl => ⟨cm kl.1 * cm kl.2, [], [], [kl]⟩) ++
    (List.finRange n).map fun k => ⟨-cm k, [(some k, none)], [(some k, none)], []⟩

/-- `Σ_k m_k z_k w_k = E` (the partial virial of all bodies with `U = E`), written `Σ_k m_k z_k w_k − E = 0`: the
terms `m_k z_k w_k` (increasing `k`), then the constant `−E`. -/
def virialE (n : ℕ) : Identity n :=
  (List.finRange n).map (fun k => ⟨cm k, [(some k, none)], [(some k, none)], []⟩) ++ [⟨-cE, [], [], []⟩]

/-! ## The identities hold -/

theorem subsetSumZ_holds (J : Finset (Fin n)) : (subsetSumZ J).Holds := by
  intro m G
  have h1 : ∀ k, Term.eval G ⟨cm k, [(some k, none)], [], []⟩ = cS (m k) * G.z k := by
    intro k
    rw [eval_mk]
    simp only [cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.zpos_some,
      Germ.zpos_none]
    ring
  have h2 : ∀ kl : Fin n × Fin n,
      Term.eval G ⟨-(cm kl.1 * cm kl.2), [(some kl.1, some kl.2)], [], [kl, kl, kl]⟩ =
        -(cS (m kl.1) * cS (m kl.2) * termZ G.p G.z kl.1 kl.2) := by
    intro kl
    rw [eval_mk]
    simp only [cval_neg, cval_mul, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Germ.zpos_some, termZ, cS_neg, cS_mul]
    ring
  rw [subsetSumZ, eval_append, eval_map, eval_map]
  simp only [h1, h2, sum_bodiesIn, sum_cross]
  rw [G.subsetSum_z J]
  simp only [Finset.sum_neg_distrib, add_neg_cancel]

theorem subsetSumW_holds (J : Finset (Fin n)) : (subsetSumW J).Holds := by
  intro m G
  have h1 : ∀ k, Term.eval G ⟨cm k, [], [(some k, none)], []⟩ = cS (m k) * G.w k := by
    intro k
    rw [eval_mk]
    simp only [cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.wpos_some,
      Germ.wpos_none]
    ring
  have h2 : ∀ kl : Fin n × Fin n,
      Term.eval G ⟨-(cm kl.1 * cm kl.2), [], [(some kl.1, some kl.2)], [kl, kl, kl]⟩ =
        -(cS (m kl.1) * cS (m kl.2) * termZ G.p G.w kl.1 kl.2) := by
    intro kl
    rw [eval_mk]
    simp only [cval_neg, cval_mul, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Germ.wpos_some, termZ, cS_neg, cS_mul]
    ring
  rw [subsetSumW, eval_append, eval_map, eval_map]
  simp only [h1, h2, sum_bodiesIn, sum_cross]
  rw [G.subsetSum_w J]
  simp only [Finset.sum_neg_distrib, add_neg_cancel]

theorem torque_holds (J : Finset (Fin n)) : (torque J).Holds := by
  intro m G
  have h : ∀ kl : Fin n × Fin n,
      eval [⟨cm kl.1 * cm kl.2, [(some kl.1, none)], [(some kl.2, none)], [kl, kl, kl]⟩,
        ⟨-(cm kl.1 * cm kl.2), [(some kl.2, none)], [(some kl.1, none)], [kl, kl, kl]⟩] G =
        cS (m kl.1) * cS (m kl.2) * (G.p kl.1 kl.2 ^ 3 * (G.z kl.1 * G.w kl.2 - G.z kl.2 * G.w kl.1)) := by
    intro kl
    rw [eval_pair, eval_mk, eval_mk]
    simp only [cval_neg, cval_mul, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Germ.zpos_some, Germ.zpos_none, Germ.wpos_some, Germ.wpos_none, cS_neg, cS_mul]
    ring
  rw [torque, eval_flatMap]
  simp only [h, sum_cross]
  exact G.torque J

theorem partialVirial_holds (J : Finset (Fin n)) : (partialVirial J).Holds := by
  intro m G
  have h1 : ∀ k, Term.eval G ⟨cm k, [(some k, none)], [(some k, none)], []⟩ = cS (m k) * (G.z k * G.w k) := by
    intro k
    rw [eval_mk]
    simp only [cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.zpos_some,
      Germ.zpos_none, Germ.wpos_some, Germ.wpos_none]
    ring
  have h2 : ∀ kl : Fin n × Fin n, Term.eval G ⟨-(cm kl.1 * cm kl.2), [], [], [kl]⟩ =
      -(cS (m kl.1) * cS (m kl.2) * G.p kl.1 kl.2) := by
    intro kl
    rw [eval_mk]
    simp only [cval_neg, cval_mul, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      cS_neg, cS_mul]
    ring
  have h3 : ∀ kl : Fin n × Fin n,
      eval [⟨-(MvPolynomial.C (1 / 2 : ℚ) * (cm kl.1 * cm kl.2)), [(some kl.1, some kl.2)], [(some kl.1, none)],
          [kl, kl, kl]⟩,
        ⟨-(MvPolynomial.C (1 / 2 : ℚ) * (cm kl.1 * cm kl.2)), [(some kl.1, none)], [(some kl.1, some kl.2)],
          [kl, kl, kl]⟩] G =
        -(cS (1 / 2) * (cS (m kl.1) * cS (m kl.2) * (G.p kl.1 kl.2 ^ 3 *
          (G.w kl.1 * (G.z kl.1 - G.z kl.2) + G.z kl.1 * (G.w kl.1 - G.w kl.2))))) := by
    intro kl
    rw [eval_pair, eval_mk, eval_mk]
    simp only [cval_neg, cval_mul, cval_cm, cval_half, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, Germ.zpos_some, Germ.zpos_none, Germ.wpos_some, Germ.wpos_none, cS_neg, cS_mul]
    ring
  rw [partialVirial, eval_append, eval_append, eval_map, eval_map, eval_flatMap]
  simp only [h1, h2, h3, sum_bodiesIn, sum_pairsIn, sum_cross, Finset.sum_neg_distrib, ← Finset.mul_sum]
  linear_combination G.partialVirial J

theorem differenceZ_holds (k l : Fin n) : (differenceZ k l).Holds := by
  intro m G
  have h0 : Term.eval G ⟨1, [(some k, some l)], [], []⟩ = G.z k - G.z l := by
    rw [eval_mk]
    simp only [cval_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.zpos_some, cS_one]
    ring
  have h1 : ∀ j, Term.eval G ⟨-cm j, [(some k, some j)], [], [(k, j), (k, j), (k, j)]⟩ =
      -(cS (m j) * termZ G.p G.z k j) := by
    intro j
    rw [eval_mk]
    simp only [cval_neg, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.zpos_some,
      termZ, cS_neg]
    ring
  have h2 : ∀ j, Term.eval G ⟨cm j, [(some l, some j)], [], [(l, j), (l, j), (l, j)]⟩ =
      cS (m j) * termZ G.p G.z l j := by
    intro j
    rw [eval_mk]
    simp only [cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.zpos_some, termZ]
    ring
  rw [differenceZ, eval_cons, eval_append, eval_map, eval_map, sum_map_filter_finRange,
    sum_map_filter_finRange]
  simp only [h0, h1, h2, decide_eq_true_eq, Finset.filter_ne', Finset.sum_neg_distrib]
  linear_combination G.difference_z k l

theorem differenceW_holds (k l : Fin n) : (differenceW k l).Holds := by
  intro m G
  have h0 : Term.eval G ⟨1, [], [(some k, some l)], []⟩ = G.w k - G.w l := by
    rw [eval_mk]
    simp only [cval_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.wpos_some, cS_one]
    ring
  have h1 : ∀ j, Term.eval G ⟨-cm j, [], [(some k, some j)], [(k, j), (k, j), (k, j)]⟩ =
      -(cS (m j) * termZ G.p G.w k j) := by
    intro j
    rw [eval_mk]
    simp only [cval_neg, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.wpos_some,
      termZ, cS_neg]
    ring
  have h2 : ∀ j, Term.eval G ⟨cm j, [], [(some l, some j)], [(l, j), (l, j), (l, j)]⟩ =
      cS (m j) * termZ G.p G.w l j := by
    intro j
    rw [eval_mk]
    simp only [cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.wpos_some, termZ]
    ring
  rw [differenceW, eval_cons, eval_append, eval_map, eval_map, sum_map_filter_finRange,
    sum_map_filter_finRange]
  simp only [h0, h1, h2, decide_eq_true_eq, Finset.filter_ne', Finset.sum_neg_distrib]
  linear_combination G.difference_w k l

theorem potVirial_holds : (potVirial n).Holds := by
  intro m G
  have h1 : ∀ kl : Fin n × Fin n, Term.eval G ⟨cm kl.1 * cm kl.2, [], [], [kl]⟩ =
      cS (m kl.1) * cS (m kl.2) * G.p kl.1 kl.2 := by
    intro kl
    rw [eval_mk]
    simp only [cval_mul, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, cS_mul]
    ring
  have h2 : ∀ k, Term.eval G ⟨-cm k, [(some k, none)], [(some k, none)], []⟩ =
      -(cS (m k) * (G.z k * G.w k)) := by
    intro k
    rw [eval_mk]
    simp only [cval_neg, cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.zpos_some,
      Germ.zpos_none, Germ.wpos_some, Germ.wpos_none, cS_neg]
    ring
  rw [potVirial, eval_append, eval_map, eval_map]
  simp only [h1, h2, sum_pairs, ← Fin.sum_univ_def]
  rw [G.U_eq_virial, Finset.sum_neg_distrib, add_neg_cancel]

theorem virialE_holds : (virialE n).Holds := by
  intro m G
  have h1 : ∀ k, Term.eval G ⟨cm k, [(some k, none)], [(some k, none)], []⟩ = cS (m k) * (G.z k * G.w k) := by
    intro k
    rw [eval_mk]
    simp only [cval_cm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Germ.zpos_some,
      Germ.zpos_none, Germ.wpos_some, Germ.wpos_none]
    ring
  have h2 : Term.eval G ⟨-cE, [], [], []⟩ = -cS G.E := by
    rw [eval_mk]
    simp only [cval_neg, cval_cE, List.map_nil, List.prod_nil, cS_neg]
    ring
  rw [virialE, eval_append, eval_map, eval_cons, h2]
  simp only [h1, ← Fin.sum_univ_def]
  rw [G.virial]
  simp [eval]

/-! ## The list of §5.1 -/

/-- The identities of the list of §5.1 besides the base identities, for `n` bodies, with the body `j₀` in the role
of the paper's body `1` (`0 : Fin 6` for six bodies): the subset sums (in `z` and in `w`) for `2 ≤ |J| ≤ 4`, the
torques `T_J` for `j₀ ∈ J`, `|J| ≤ 5`, the partial virials for nonempty `J ≠ {1, …, n}`, the differences (in `z` and
in `w`) of the pairs `k < l`, `U = Σ_k m_k z_k w_k` and `Σ_k m_k z_k w_k = E`. -/
def secondary (n : ℕ) (j₀ : Fin n) : Set (Identity n) :=
  {I | (∃ J : Finset (Fin n), 2 ≤ J.card ∧ J.card ≤ 4 ∧ (I = subsetSumZ J ∨ I = subsetSumW J)) ∨
    (∃ J : Finset (Fin n), j₀ ∈ J ∧ J.card ≤ 5 ∧ I = torque J) ∨
    (∃ J : Finset (Fin n), J.Nonempty ∧ J ≠ univ ∧ I = partialVirial J) ∨
    (∃ k l : Fin n, k < l ∧ (I = differenceZ k l ∨ I = differenceW k l)) ∨
    I = potVirial n ∨ I = virialE n}

/-- The identities of the list of §5.1 hold at every germ (§2.3). -/
theorem secondary_holds {j₀ : Fin n} : ∀ I ∈ secondary n j₀, I.Holds := by
  rintro I (⟨J, -, -, rfl | rfl⟩ | ⟨J, -, -, rfl⟩ | ⟨J, -, -, rfl⟩ | ⟨k, l, -, rfl | rfl⟩ | rfl | rfl)
  · exact subsetSumZ_holds J
  · exact subsetSumW_holds J
  · exact torque_holds J
  · exact partialVirial_holds J
  · exact differenceZ_holds k l
  · exact differenceW_holds k l
  · exact potVirial_holds
  · exact virialE_holds

/-! ## The factors `p_kl` have `k ≠ l` -/

/-- The factors `p_kl` of the terms of `I` are of pairs of distinct bodies: the hypothesis of
`Identity.isArgmin_of_expoT` and `Identity.single_of_expoT`. -/
def PsNe (I : Identity n) : Prop := ∀ t ∈ I, ∀ kl ∈ t.ps, kl.1 ≠ kl.2

theorem ne_of_mem_cross {J : Finset (Fin n)} {kl : Fin n × Fin n} (h : kl ∈ cross J) : kl.1 ≠ kl.2 := by
  rw [mem_cross] at h
  intro he
  exact h.2 (he ▸ h.1)

theorem ne_of_mem_pairsIn {J : Finset (Fin n)} {kl : Fin n × Fin n} (h : kl ∈ pairsIn J) : kl.1 ≠ kl.2 :=
  (mem_pairsIn.mp h).2.2.ne

theorem ne_of_mem_pairs {kl : Fin n × Fin n} (h : kl ∈ pairs n) : kl.1 ≠ kl.2 :=
  (mem_pairs.mp h).ne

theorem subsetSumZ_psNe (J : Finset (Fin n)) : (subsetSumZ J).PsNe := by
  intro t ht kl hkl
  simp only [subsetSumZ, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨k, -, rfl⟩ | ⟨kl', hkl', rfl⟩
  · simp at hkl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hkl
    rw [hkl]
    exact ne_of_mem_cross hkl'

theorem subsetSumW_psNe (J : Finset (Fin n)) : (subsetSumW J).PsNe := by
  intro t ht kl hkl
  simp only [subsetSumW, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨k, -, rfl⟩ | ⟨kl', hkl', rfl⟩
  · simp at hkl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hkl
    rw [hkl]
    exact ne_of_mem_cross hkl'

theorem torque_psNe (J : Finset (Fin n)) : (torque J).PsNe := by
  intro t ht kl hkl
  simp only [torque, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ht
  obtain ⟨kl', hkl', rfl | rfl⟩ := ht
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hkl
    rw [hkl]
    exact ne_of_mem_cross hkl'

theorem partialVirial_psNe (J : Finset (Fin n)) : (partialVirial J).PsNe := by
  intro t ht kl hkl
  simp only [partialVirial, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at ht
  rcases ht with (⟨k, -, rfl⟩ | ⟨kl', hkl', rfl⟩) | ⟨kl', hkl', rfl | rfl⟩
  · simp at hkl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hkl
    rw [hkl]
    exact ne_of_mem_pairsIn hkl'
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hkl
    rw [hkl]
    exact ne_of_mem_cross hkl'

theorem differenceZ_psNe (k l : Fin n) : (differenceZ k l).PsNe := by
  intro t ht kl hkl
  simp only [differenceZ, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq] at ht
  rcases ht with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · simp at hkl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hkl
    rw [hkl]
    exact Ne.symm hj
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hkl
    rw [hkl]
    exact Ne.symm hj

theorem differenceW_psNe (k l : Fin n) : (differenceW k l).PsNe := by
  intro t ht kl hkl
  simp only [differenceW, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq] at ht
  rcases ht with rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · simp at hkl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hkl
    rw [hkl]
    exact Ne.symm hj
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hkl
    rw [hkl]
    exact Ne.symm hj

theorem potVirial_psNe : (potVirial n).PsNe := by
  intro t ht kl hkl
  simp only [potVirial, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨kl', hkl', rfl⟩ | ⟨k, -, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hkl
    rw [hkl]
    exact ne_of_mem_pairs hkl'
  · simp at hkl

theorem virialE_psNe : (virialE n).PsNe := by
  intro t ht kl hkl
  simp only [virialE, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ⟨k, -, rfl⟩ | rfl
  · simp at hkl
  · simp at hkl

/-- The factors `p_kl` of the identities of the list of §5.1 have `k ≠ l`. -/
theorem secondary_psNe {j₀ : Fin n} : ∀ I ∈ secondary n j₀, I.PsNe := by
  rintro I (⟨J, -, -, rfl | rfl⟩ | ⟨J, -, -, rfl⟩ | ⟨J, -, -, rfl⟩ | ⟨k, l, -, rfl | rfl⟩ | rfl | rfl)
  · exact subsetSumZ_psNe J
  · exact subsetSumW_psNe J
  · exact torque_psNe J
  · exact partialVirial_psNe J
  · exact differenceZ_psNe k l
  · exact differenceW_psNe k l
  · exact potVirial_psNe
  · exact virialE_psNe

end Identity

end

end CC6Full
