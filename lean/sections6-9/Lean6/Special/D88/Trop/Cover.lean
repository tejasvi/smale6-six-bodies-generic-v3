import Lean6.Special.Comp.D88.Trop.Check
import Lean6.Special.Poly.Sem
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Lemma 6.19(a), (iii)–(iv): soundness of the covering checker

`cover_sound`: if `chk p Gb hyps [] [] [] root = true` (and `gbOK p Gb = true`), and every system of `hyps` has no
common zero in the torus (`HypsOK`), then for every weight vector `w : ℕ → ℚ` with a negative entry among
`w 0, …, w 16`, the initial forms `initialForm w g` (`g ∈ Gb`) have no common zero in the torus `(K^*)^{17}` of any
field `K` of characteristic `p`. This is the hypothesis on the cones of the
prevariety in Lemma 6.18 (`lem:goodred`), for all `w` at once: a vector `w` outside the prevariety has a polynomial
whose initial form is a monomial, and the covering certifies those cells as well.
-/

namespace Lean6.Special.D88.Trop

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.D88.Trop

/-! ## Weights -/

/-- `⟨v, w⟩` for an integer vector `v` whose first entry belongs to the coordinate `i`. -/
def dotQ (w : ℕ → ℚ) : List Int → ℕ → ℚ
  | [], _ => 0
  | a :: v, i => (a : ℚ) * w i + dotQ w v (i + 1)

variable {w : ℕ → ℚ}

theorem dotQ_vadd : ∀ (a b : List Int) (i : ℕ), dotQ w (vadd a b) i = dotQ w a i + dotQ w b i
  | [], b, i => by simp [vadd, dotQ]
  | a :: as, [], i => by simp [vadd, dotQ]
  | a :: as, b :: bs, i => by
    simp only [vadd, dotQ, dotQ_vadd as bs (i + 1), Int.cast_add]
    ring

theorem dotQ_vsmul (c : Int) : ∀ (v : List Int) (i : ℕ), dotQ w (vsmul c v) i = c * dotQ w v i
  | [], i => by simp [vsmul, dotQ]
  | a :: v, i => by
    have := dotQ_vsmul c v (i + 1)
    simp only [vsmul, List.map_cons, dotQ] at this ⊢
    rw [this]
    push_cast
    ring

theorem dotQ_zero_of_isZeroV : ∀ {v : List Int} (i : ℕ), isZeroV v = true → dotQ w v i = 0
  | [], _, _ => rfl
  | a :: v, i, h => by
    simp only [isZeroV, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have := dotQ_zero_of_isZeroV (v := v) (i + 1) (by simpa [isZeroV] using h.2)
    simp [dotQ, h.1, this]

theorem dotQ_linS_aux (rows : List (List Int)) (i : ℕ) :
    ∀ (cs : List (Nat × Int)) (acc : List Int),
      dotQ w (cs.foldl (fun acc kc => vadd acc (vsmul kc.2 (rows.getD kc.1 []))) acc) i =
        dotQ w acc i + (cs.map fun kc => (kc.2 : ℚ) * dotQ w (rows.getD kc.1 []) i).sum
  | [], acc => by simp
  | kc :: cs, acc => by
    rw [List.foldl_cons, dotQ_linS_aux rows i cs, dotQ_vadd, dotQ_vsmul, List.map_cons, List.sum_cons]
    ring

theorem dotQ_linS (rows : List (List Int)) (cs : List (Nat × Int)) (i : ℕ) :
    dotQ w (linS rows cs) i = (cs.map fun kc => (kc.2 : ℚ) * dotQ w (rows.getD kc.1 []) i).sum := by
  rw [linS, dotQ_linS_aux, show dotQ w [] i = 0 from rfl, zero_add]

/-! ## Cells and certificates -/

/-- `w` lies in the cell `{E w = 0, S w > 0}`. -/
def InCell (E S : List (List Int)) (w : ℕ → ℚ) : Prop :=
  (∀ e ∈ E, dotQ w e 0 = 0) ∧ (∀ s ∈ S, 0 < dotQ w s 0)

theorem getD_mem_or_nil {rows : List (List Int)} (k : ℕ) : rows.getD k [] ∈ rows ∨ rows.getD k [] = [] := by
  by_cases hk : k < rows.length
  · left
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  · right
    rw [List.getD_eq_default _ _ (by omega)]

theorem dotQ_linS_E {E S : List (List Int)} (h : InCell E S w) (u : List (Nat × Int)) : dotQ w (linS E u) 0 = 0 := by
  rw [dotQ_linS]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨kc, -, rfl⟩ := List.mem_map.mp hx
  rcases getD_mem_or_nil (rows := E) kc.1 with hm | hm
  · rw [h.1 _ hm, mul_zero]
  · rw [hm]; simp [dotQ]

theorem dotQ_linS_S {E S : List (List Int)} (h : InCell E S w) {y : List (Nat × Int)}
    (hy : posOK S.length y = true) : 0 < dotQ w (linS S y) 0 := by
  simp only [posOK, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hy
  obtain ⟨hnn, kc0, hkc0, hpos, hlt⟩ := hy
  rw [dotQ_linS]
  have hterm : ∀ kc ∈ y, 0 ≤ (kc.2 : ℚ) * dotQ w (S.getD kc.1 []) 0 := by
    intro kc hkc
    have h1 : (0 : ℚ) ≤ kc.2 := by exact_mod_cast hnn kc hkc
    rcases getD_mem_or_nil (rows := S) kc.1 with hm | hm
    · exact mul_nonneg h1 (h.2 _ hm).le
    · rw [hm]; simp [dotQ]
  have hpos' : 0 < (kc0.2 : ℚ) * dotQ w (S.getD kc0.1 []) 0 := by
    have hm : S.getD kc0.1 [] ∈ S := by
      rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
    exact mul_pos (by exact_mod_cast hpos) (h.2 _ hm)
  obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem hkc0
  rw [hsplit, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  have s1 : 0 ≤ (l1.map fun kc => (kc.2 : ℚ) * dotQ w (S.getD kc.1 []) 0).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp hx
      exact hterm kc (by rw [hsplit]; exact List.mem_append_left _ hkc)
  have s2 : 0 ≤ (l2.map fun kc => (kc.2 : ℚ) * dotQ w (S.getD kc.1 []) 0).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨kc, hkc, rfl⟩ := List.mem_map.mp hx
      exact hterm kc (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hkc))
  linarith

theorem not_inCell_of_emptyOK {E S : List (List Int)} {u y : List (Nat × Int)} (h : emptyOK E S u y = true) :
    ¬ InCell E S w := by
  intro hc
  simp only [emptyOK, Bool.and_eq_true] at h
  have h0 := dotQ_zero_of_isZeroV (w := w) 0 h.2
  rw [dotQ_vadd, dotQ_linS_E hc] at h0
  have := dotQ_linS_S hc h.1
  linarith

theorem dotQ_eq_zero_of_eqOK {E S : List (List Int)} {h : List Int} {c : Int × List (Nat × Int)}
    (hc : InCell E S w) (hok : eqOK E h c = true) : dotQ w h 0 = 0 := by
  simp only [eqOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  have h0 := dotQ_zero_of_isZeroV (w := w) 0 hok.2
  rw [dotQ_vadd, dotQ_vsmul, dotQ_vsmul, dotQ_linS_E hc] at h0
  have hk : (0 : ℚ) < c.1 := by exact_mod_cast hok.1
  have : (c.1 : ℚ) * dotQ w h 0 = 0 := by simpa using h0
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact h1

theorem dotQ_pos_of_strictOK {E S : List (List Int)} {h : List Int}
    {c : Int × List (Nat × Int) × List (Nat × Int)} (hc : InCell E S w) (hok : strictOK E S h c = true) :
    0 < dotQ w h 0 := by
  simp only [strictOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hz, hy⟩, hzero⟩ := hok
  have h0 := dotQ_zero_of_isZeroV (w := w) 0 hzero
  rw [dotQ_vadd, dotQ_vsmul, dotQ_vsmul, dotQ_vadd, dotQ_linS_E hc] at h0
  have hS := dotQ_linS_S hc hy
  have hk : (0 : ℚ) < c.1 := by exact_mod_cast hz
  have : (c.1 : ℚ) * dotQ w h 0 = dotQ w (linS S c.2.1) 0 := by push_cast at h0; linarith
  by_contra hneg
  push Not at hneg
  have : (c.1 : ℚ) * dotQ w h 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le hneg
  linarith

/-! ## Weights of monomials and faces -/

/-- The weight `⟨e, w⟩` of a monomial. -/
def wt (w : ℕ → ℚ) (m : Mono) : ℚ := dotQ w (toZ m) 0

/-- The term `i` of `g` (or `(0, [])`). -/
def term (g : Poly ℕ) (i : ℕ) : ℕ × Mono := g.getD i (0, [])

theorem dotQ_diffE (g : Poly ℕ) (i j : ℕ) : dotQ w (diffE g i j) 0 = wt w (term g i).2 - wt w (term g j).2 := by
  rw [diffE, dotQ_vadd, dotQ_vsmul]
  simp [wt, term]
  ring

/-- **The initial form** of `g` at `w`: the terms of minimal weight (in their order in `g`). -/
def initialForm (w : ℕ → ℚ) (g : Poly ℕ) : Poly ℕ :=
  ((List.range g.length).filter fun i => decide (∀ j < g.length, wt w (term g i).2 ≤ wt w (term g j).2)).map
    (term g)

/-- `F` is the set of indices of the terms of minimal weight. -/
def FaceAt (g : Poly ℕ) (F : List ℕ) (w : ℕ → ℚ) : Prop :=
  F.Nodup ∧ (∀ i ∈ F, i < g.length) ∧
    ∀ i < g.length, (i ∈ F ↔ ∀ j < g.length, wt w (term g i).2 ≤ wt w (term g j).2)

theorem inF_eq_map (g : Poly ℕ) (F : List ℕ) : inF g F = F.map (term g) := rfl

theorem perm_initialForm {g : Poly ℕ} {F : List ℕ} (h : FaceAt g F w) :
    ((List.range g.length).filter fun i => decide (∀ j < g.length, wt w (term g i).2 ≤ wt w (term g j).2)).Perm F := by
  rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) h.1]
  intro i
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hi, hmin⟩
    exact (h.2.2 i hi).mpr hmin
  · intro hi
    exact ⟨h.2.1 i hi, (h.2.2 i (h.2.1 i hi)).mp hi⟩

theorem eval_initialForm {R : Type*} [CommRing R] {C : Coeff ℕ} (hC : C.Hom R) (x : ℕ → R) {g : Poly ℕ}
    {F : List ℕ} (h : FaceAt g F w) : Poly.eval hC x (initialForm w g) = Poly.eval hC x (inF g F) := by
  rw [initialForm, inF_eq_map]
  exact Poly.eval_perm hC x ((perm_initialForm h).map _)

/-! ## Coefficients in a field of characteristic `p` -/

/-- `ℤ/p` into a commutative ring of characteristic `p`. -/
def modHomK (p : ℕ) [NeZero p] (K : Type*) [CommRing K] [CharP K p] : (modC p).Hom K where
  f := fun a => (a : K)
  map_zero := by simp [modC]
  map_one := by
    show ((1 % p : ℕ) : K) = 1
    rw [← CharP.cast_eq_mod K p 1, Nat.cast_one]
  map_add := by
    intro a b
    show (((a + b) % p : ℕ) : K) = (a : K) + (b : K)
    rw [← CharP.cast_eq_mod K p, Nat.cast_add]
  map_mul := by
    intro a b
    show (((a * b) % p : ℕ) : K) = (a : K) * (b : K)
    rw [← CharP.cast_eq_mod K p, Nat.cast_mul]
  map_neg := by
    intro a
    show (((p - a % p) % p : ℕ) : K) = -(a : K)
    have hle : a % p ≤ p := (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))).le
    rw [← CharP.cast_eq_mod K p, Nat.cast_sub hle, CharP.cast_eq_zero, ← CharP.cast_eq_mod K p a, zero_sub]
  map_isZero := by
    intro a ha
    simp only [modC, beq_iff_eq] at ha
    show (a : K) = 0
    rw [CharP.cast_eq_mod K p a, ha, Nat.cast_zero]

/-- The torus statement: at no point of `(K^*)^{17}` do all the initial forms at `w` vanish. -/
def TorusEmpty (p : ℕ) [NeZero p] (Gb : List (Poly ℕ)) (w : ℕ → ℚ) : Prop :=
  ∀ (K : Type) [Field K] [CharP K p] (x : ℕ → K), (∀ i < 17, x i ≠ 0) →
    ∃ g ∈ Gb, Poly.eval (modHomK p K) x (initialForm w g) ≠ 0

/-- A system of polynomials over `ℤ/p` has no common zero in the torus `(K^*)^{17}` of any field of characteristic `p`. -/
def TorusEmptySys (p : ℕ) [NeZero p] (sys : List (Poly ℕ)) : Prop :=
  ∀ (K : Type) [Field K] [CharP K p] (x : ℕ → K), (∀ i < 17, x i ≠ 0) → ∃ f ∈ sys, Poly.eval (modHomK p K) x f ≠ 0

/-- Every system of the list has no common zero in the torus. -/
def HypsOK (p : ℕ) [NeZero p] (hyps : List (List (Poly ℕ))) : Prop := ∀ s ∈ hyps, TorusEmptySys p s

/-! ## Evaluation facts -/

theorem mono_eval_congr {R : Type*} [CommRing R] {x y : ℕ → R} :
    ∀ (m : Mono) (i : ℕ), (∀ k, i ≤ k → k < i + m.length → x k = y k) → Mono.eval x m i = Mono.eval y m i
  | [], _, _ => rfl
  | e :: m, i, h => by
    simp only [Mono.eval]
    rw [h i le_rfl (by simp), mono_eval_congr m (i + 1) fun k hk1 hk2 => h k (by omega) (by simp at hk2 ⊢; omega)]

theorem mono_eval_ne_zero {K : Type*} [Field K] {x : ℕ → K} :
    ∀ (m : Mono) (i : ℕ), (∀ k, i ≤ k → k < i + m.length → x k ≠ 0) → Mono.eval x m i ≠ 0
  | [], _, _ => one_ne_zero
  | e :: m, i, h => by
    simp only [Mono.eval]
    exact mul_ne_zero (pow_ne_zero _ (h i le_rfl (by simp)))
      (mono_eval_ne_zero m (i + 1) fun k hk1 hk2 => h k (by omega) (by simp at hk2 ⊢; omega))

theorem mono_eval_replicate_one {R : Type*} [CommRing R] (x : ℕ → R) :
    ∀ (n i : ℕ), Mono.eval x (List.replicate n 1) i = ∏ k ∈ Finset.range n, x (i + k)
  | 0, i => by simp [Mono.eval]
  | n + 1, i => by
    rw [List.replicate_succ, Mono.eval, mono_eval_replicate_one x n (i + 1), pow_one, Finset.prod_range_succ']
    simp only [add_zero]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    omega

/-- The evaluation of a polynomial only reads the variables below the lengths of its monomials. -/
theorem eval_congr17 {R : Type*} [CommRing R] {C : Coeff ℕ} (hC : C.Hom R) {x y : ℕ → R}
    (hxy : ∀ k < 17, x k = y k) : ∀ (q : Poly ℕ), (∀ t ∈ q, t.2.length ≤ 17) → Poly.eval hC x q = Poly.eval hC y q
  | [], _ => rfl
  | t :: q, h => by
    rw [Poly.eval_cons, Poly.eval_cons, eval_congr17 hC hxy q fun u hu => h u (List.mem_cons_of_mem _ hu),
      mono_eval_congr t.2 0 fun k _ hk => hxy k (by have := h t (List.mem_cons_self ..); omega)]

/-! ## The induction -/

variable {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem gb_terms {Gb : List (Poly ℕ)} (hGb : gbOK p Gb = true) {g : ℕ} :
    ∀ t ∈ Gb.getD g [], t.2.length ≤ 17 ∧ t.1 < p ∧ t.1 ≠ 0 := by
  intro t ht
  simp only [gbOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hGb
  rcases getD_mem_or_nil' (l := Gb) g with hm | hm
  · have := hGb _ hm t ht
    exact ⟨this.1.1, this.1.2, this.2⟩
  · rw [hm] at ht; simp at ht
where
  getD_mem_or_nil' {α : Type} {l : List (List α)} (k : ℕ) : l.getD k [] ∈ l ∨ l.getD k [] = [] := by
    by_cases hk : k < l.length
    · left; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    · right; rw [List.getD_eq_default _ _ (by omega)]

omit [NeZero p] in
theorem inF_terms {Gb : List (Poly ℕ)} (hGb : gbOK p Gb = true) (g : ℕ) (F : List ℕ) (hF : ∀ i ∈ F, i < (Gb.getD g []).length) :
    ∀ t ∈ inF (Gb.getD g []) F, t.2.length ≤ 17 := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  have hlt := hF i hi
  have hm : (Gb.getD g []).getD i (0, []) ∈ Gb.getD g [] := by
    rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
  exact (gb_terms hGb (g := g) _ hm).1

theorem zip_all_forall {α β : Type} {l1 : List α} {l2 : List β} (hlen : l1.length = l2.length)
    {P : α × β → Bool} (h : (l1.zip l2).all P = true) : ∀ a ∈ l1, ∃ b, P (a, b) = true := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have hk2 : k < l2.length := hlen ▸ hk
  refine ⟨l2[k], ?_⟩
  have hz : k < (l1.zip l2).length := by simp [hk, hk2]
  have := List.all_eq_true.mp h _ (List.getElem_mem hz)
  simpa [List.getElem_zip] using this

theorem chk_sound {Gb : List (Poly ℕ)} (hGb : gbOK p Gb = true) {hyps : List (List (Poly ℕ))}
    (hH : HypsOK p hyps) :
    ∀ (node : Node) (E S : List (List Int)) (faces : List (ℕ × List ℕ)),
      chk p Gb hyps E S faces node = true → (∀ f ∈ faces, f.1 < Gb.length ∧ ∀ i ∈ f.2, i < (Gb.getD f.1 []).length) →
      ∀ w, InCell E S w → (∀ f ∈ faces, FaceAt (Gb.getD f.1 []) f.2 w) → (∃ i < 17, w i < 0) →
        TorusEmpty p Gb w := by
  intro node
  induction node with
  | empty u y =>
    intro E S faces h _ w hc _ _
    exact absurd hc (not_inCell_of_emptyOK h)
  | split g i j gt lt eq ihgt ihlt iheq =>
    intro E S faces h hfv w hc hf hneg
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hgt⟩, hlt⟩, heq⟩ := h
    set hh := diffE (Gb.getD g []) i j
    rcases lt_trichotomy (dotQ w hh 0) 0 with hn | hz | hp'
    · refine ihlt E _ faces hlt hfv w ⟨hc.1, fun s hs => ?_⟩ hf hneg
      rcases List.mem_append.mp hs with hs | hs
      · exact hc.2 s hs
      · rw [List.mem_singleton.mp hs, dotQ_vsmul]; push_cast; linarith
    · refine iheq _ S faces heq hfv w ⟨fun e he => ?_, hc.2⟩ hf hneg
      rcases List.mem_append.mp he with he | he
      · exact hc.1 e he
      · rw [List.mem_singleton.mp he]; exact hz
    · refine ihgt E _ faces hgt hfv w ⟨hc.1, fun s hs => ?_⟩ hf hneg
      rcases List.mem_append.mp hs with hs | hs
      · exact hc.2 s hs
      · rw [List.mem_singleton.mp hs]; exact hp'
  | face g F eqc strict child ih =>
    intro E S faces h hfv w hc hf hneg
    cases F with
    | nil => simp [chk] at h
    | cons a0 rest =>
      simp only [chk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hg, hFlt⟩, hnd⟩, hl1⟩, heqc⟩, hl2⟩, hstr⟩, hchild⟩ := h
      set gg := Gb.getD g []
      have hFlt' : ∀ i ∈ a0 :: rest, i < gg.length := fun i hi => hFlt i hi
      have ha0 : a0 < gg.length := hFlt' a0 (List.mem_cons_self ..)
      -- equal weights on F
      have hEq : ∀ i ∈ a0 :: rest, wt w (term gg i).2 = wt w (term gg a0).2 := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · rfl
        · obtain ⟨c, hc'⟩ := zip_all_forall hl1 (P := fun t => eqOK E (diffE gg t.1 a0) t.2)
            (List.all_eq_true.mpr heqc) i hi
          have := dotQ_eq_zero_of_eqOK hc hc'
          rw [dotQ_diffE] at this
          linarith
      -- larger weights outside F
      have hGt : ∀ i < gg.length, i ∉ a0 :: rest → wt w (term gg a0).2 < wt w (term gg i).2 := by
        intro i hi hni
        have hmem : i ∈ (List.range gg.length).filter fun i => !((a0 :: rest).contains i) := by
          have hc : (a0 :: rest).contains i = false :=
            Bool.eq_false_iff.mpr fun hci => hni (List.contains_iff_mem.mp hci)
          simp only [List.mem_filter, List.mem_range, hc, Bool.not_false, and_true]
          exact hi
        obtain ⟨c, hc'⟩ := zip_all_forall hl2 (P := fun t => strictOK E S (diffE gg t.1 a0) t.2)
          (List.all_eq_true.mpr hstr) i hmem
        have := dotQ_pos_of_strictOK hc hc'
        rw [dotQ_diffE] at this
        linarith
      have hface : FaceAt gg (a0 :: rest) w := by
        refine ⟨by simpa using hnd, hFlt', fun i hi => ⟨fun hiF j hj => ?_, fun hmin => ?_⟩⟩
        · rw [hEq i hiF]
          by_cases hjF : j ∈ a0 :: rest
          · rw [hEq j hjF]
          · exact (hGt j hj hjF).le
        · by_contra hni
          have h1 := hGt i hi hni
          have h2 := hmin a0 ha0
          linarith
      refine ih E S ((g, a0 :: rest) :: faces) hchild ?_ w hc ?_ hneg
      · intro f hf'
        rcases List.mem_cons.mp hf' with rfl | hf'
        · exact ⟨hg, hFlt'⟩
        · exact hfv f hf'
      · intro f hf'
        rcases List.mem_cons.mp hf' with rfl | hf'
        · exact hface
        · exact hf f hf'
  | mono =>
    intro E S faces h hfv w hc hf hneg K _ _ x hx
    match faces, h, hfv, hf with
    | (g, [i]) :: _, h, hfv, hf =>
      have hgv := hfv (g, [i]) (List.mem_cons_self ..)
      have hface := hf (g, [i]) (List.mem_cons_self ..)
      refine ⟨Gb.getD g [], ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hgv.1]; exact List.getElem_mem hgv.1
      · rw [eval_initialForm _ x hface]
        have hi := hgv.2 i (List.mem_singleton_self _)
        have hm : (Gb.getD g []).getD i (0, []) ∈ Gb.getD g [] := by
          rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
        have ht := gb_terms hGb (g := g) _ hm
        simp only [inF, List.map_cons, List.map_nil, Poly.eval_cons, Poly.eval_nil, add_zero]
        refine mul_ne_zero ?_ (mono_eval_ne_zero _ 0 fun k _ hk => hx k (by omega))
        show ((((Gb.getD g []).getD i (0, [])).1 : ℕ) : K) ≠ 0
        rw [Ne, CharP.cast_eq_zero_iff K p]
        intro hdvd
        exact ht.2.2 (Nat.eq_zero_of_dvd_of_lt hdvd ht.2.1)
    | [], h, _, _ => simp [chk] at h
    | (g, []) :: _, h, _, _ => simp [chk] at h
    | (g, _ :: _ :: _) :: _, h, _, _ => simp [chk] at h
  | leaf cofs cofR =>
    intro E S faces h hfv w hc hf hneg K _ _ x hx
    classical
    set hK := modHomK p K
    set ins := faces.map fun f => inF (Gb.getD f.1 []) f.2
    have hprod : (∏ k ∈ Finset.range 17, x k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k hk =>
      hx k (Finset.mem_range.mp hk)
    let x' : ℕ → K := fun k => if k < 17 then x k else (∏ k ∈ Finset.range 17, x k)⁻¹
    have hxx' : ∀ k < 17, x' k = x k := fun k hk => by simp [x', hk]
    have h0 := Poly.isZero_sound hK x' h
    rw [Poly.eval_sub, Poly.eval_add, Poly.eval_sum, Poly.eval_mul, Poly.eval_const] at h0
    have hrab : Poly.eval hK x' (rabin p) = 0 := by
      simp only [rabin, Poly.eval_cons, Poly.eval_nil, add_zero, Mono.eval, mul_one, hK.map_neg, hK.map_one]
      rw [mono_eval_replicate_one, Finset.prod_range_succ]
      simp only [zero_add]
      have e1 : (∏ k ∈ Finset.range 17, x' k) = ∏ k ∈ Finset.range 17, x k :=
        Finset.prod_congr rfl fun k hk => hxx' k (Finset.mem_range.mp hk)
      have e2 : x' 17 = (∏ k ∈ Finset.range 17, x k)⁻¹ := by simp [x']
      rw [e1, e2, mul_inv_cancel₀ hprod]
      ring
    have hf1 : hK.f 1 = 1 := by simp [hK, modHomK]
    rw [hrab, mul_zero, add_zero, hf1, sub_eq_zero] at h0
    -- some initial form does not vanish at x'
    have hex : ∃ c ∈ cofs, Poly.eval hK x' (ins.getD c.1 []) ≠ 0 := by
      by_contra hall
      push Not at hall
      have hz : ∀ v ∈ (cofs.map fun c => Poly.mul (modC p) c.2 (ins.getD c.1 [])).map (Poly.eval hK x'), v = 0 := by
        intro v hv
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hq
        rw [Poly.eval_mul, hall c hc', mul_zero]
      have := List.sum_eq_zero hz
      rw [h0] at this
      exact one_ne_zero this
    obtain ⟨c, -, hcne⟩ := hex
    have hlt : c.1 < ins.length := by
      by_contra hge
      push Not at hge
      rw [List.getD_eq_default _ _ hge] at hcne
      exact hcne rfl
    have hins : ins.getD c.1 [] = inF (Gb.getD (faces[c.1]'(by simpa [ins] using hlt)).1 [])
        (faces[c.1]'(by simpa [ins] using hlt)).2 := by
      rw [List.getD_eq_getElem _ _ hlt]; simp [ins]
    set f := faces[c.1]'(by simpa [ins] using hlt)
    have hfmem : f ∈ faces := List.getElem_mem _
    have hgv := hfv f hfmem
    refine ⟨Gb.getD f.1 [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hgv.1]; exact List.getElem_mem hgv.1
    · rw [eval_initialForm _ x (hf f hfmem)]
      rw [hins] at hcne
      rwa [eval_congr17 hK (fun k hk => (hxx' k hk).symm) _ (inF_terms hGb f.1 f.2 hgv.2)]
  | nonneg certs =>
    intro E S faces h _ w hc _ hneg
    simp only [chk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨i, hi, hwi⟩ := hneg
    have hmem : i ∈ List.range 17 := List.mem_range.mpr hi
    obtain ⟨c, hc'⟩ := zip_all_forall (by simp [h.1]) (P := fun t => eqOK E (unitV t.1) t.2) h.2 i hmem
    have h0 := dotQ_eq_zero_of_eqOK hc hc'
    have : dotQ w (unitV i) 0 = w i := by
      have key : ∀ (n s : ℕ), dotQ w ((List.range' s n).map fun k => if k = i then (1 : Int) else 0) s =
          if s ≤ i ∧ i < s + n then w i else 0 := by
        intro n
        induction n with
        | zero => intro s; simp [dotQ]
        | succ n ihn =>
          intro s
          rw [List.range'_succ, List.map_cons, dotQ, ihn (s + 1)]
          by_cases hs : s = i
          · subst hs; simp
          · simp only [hs, ↓reduceIte, Int.cast_zero, zero_mul, zero_add]
            congr 1
            apply propext
            omega
      rw [unitV, List.range_eq_range', key 17 0]
      simp [hi]
    rw [this] at h0
    linarith
  | hyp k =>
    intro E S faces h hfv w hc hf hneg K _ _ x hx
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hk, heq⟩ := h
    have hmem : hyps.getD k [] ∈ hyps := by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    obtain ⟨f, hfm, hfne⟩ := hH _ hmem K x hx
    rw [← heq] at hfm
    obtain ⟨fc, hfc, rfl⟩ := List.mem_map.mp hfm
    have hgv := hfv fc hfc
    refine ⟨Gb.getD fc.1 [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hgv.1]; exact List.getElem_mem hgv.1
    · rw [eval_initialForm _ x (hf fc hfc)]
      exact hfne

/-- **Soundness of the covering.** -/
theorem cover_sound {Gb : List (Poly ℕ)} {hyps : List (List (Poly ℕ))} {root : Node} (hGb : gbOK p Gb = true)
    (hH : HypsOK p hyps) (h : chk p Gb hyps [] [] [] root = true) (w : ℕ → ℚ) (hneg : ∃ i < 17, w i < 0) :
    TorusEmpty p Gb w :=
  chk_sound hGb hH root [] [] [] h (by simp) w ⟨by simp, by simp⟩ (by simp) hneg

end Lean6.Special.D88.Trop
