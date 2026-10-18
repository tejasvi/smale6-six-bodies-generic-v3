import CC6Full.Interface
import CC6Full.Germ.Rules
import L6Sound.F1.Component
import L6Sound.F1.Classes

/-!
# Bridge to the enumeration of the certificate project: codes and germs

The generic part of the bridge of Proposition 3.1 (`Enum.lean`), which uses no check of the certificate project.

* `toDiagram d`: the labelled diagram (`Diagram 6`) of a code `d : L6F1.Diagram` (edge code in base 4 over the pair
  positions, circle bit masks): the strokes are the pairs `(k, l)`, `k < l`, of the kinds `z`, `zw` resp. `w`, `zw`,
  and the circled bodies are the bits of the masks. `toDiagram_ordered`: it is ordered.
* `toDiagram_actP`: the symmetry `L6F1.actP 6 σ s` of the codes (the body `k` becomes `σ k`, then the colours are
  exchanged if `s`) is sent to `Diagram.relabel σ⁻¹`, followed by `Diagram.swap` if `s`.
* `germCode G`: the code of the diagram of a germ on six bodies, in range (`germCode_inRange`), with diagram
  `toDiagram (germCode G)` (`hasDiagram_germCode`); `okRules_germCode`: for positive masses it satisfies the rules
  (E1)–(E6), (C1)–(C4) in both colours.
-/

namespace CC6Compose

open CC6Full Finset

noncomputable section

/-! ## Facts on the kinds `0` (none), `1` (`z`), `2` (`w`), `3` (`zw`) -/

theorem kind_inj_aux : ∀ u < 4, ∀ v < 4, (u == 1 || u == 3) = (v == 1 || v == 3) →
    (u == 2 || u == 3) = (v == 2 || v == 3) → u = v := by decide

theorem isEdge_aux : ∀ v < 4,
    ((v != 0) = true ↔ ((v == 1 || v == 3) = true ∨ (v == 2 || v == 3) = true)) := by decide

theorem isZW_aux : ∀ v < 4, ((v == 3) = true ↔ ((v == 1 || v == 3) = true ∧ (v == 2 || v == 3) = true)) := by
  decide

theorem swapKind_z_aux : ∀ v < 4, (L6F1.swapKind v == 1 || L6F1.swapKind v == 3) = (v == 2 || v == 3) := by
  decide

theorem swapKind_w_aux : ∀ v < 4, (L6F1.swapKind v == 2 || L6F1.swapKind v == 3) = (v == 1 || v == 3) := by
  decide

/-- The kind of a pair is determined by its strokes. -/
theorem kind_eq_of_strokes {e e' a b c d : ℕ} (hz : L6F1.zStroke e a b = L6F1.zStroke e' c d)
    (hw : L6F1.wStroke e a b = L6F1.wStroke e' c d) : L6F1.kind e a b = L6F1.kind e' c d :=
  kind_inj_aux _ (L6F1.kind_lt e a b) _ (L6F1.kind_lt e' c d) hz hw

theorem isEdge_iff (e a b : ℕ) :
    L6F1.isEdge e a b = true ↔ L6F1.zStroke e a b = true ∨ L6F1.wStroke e a b = true :=
  isEdge_aux _ (L6F1.kind_lt e a b)

theorem isZW_iff (e a b : ℕ) :
    L6F1.isZW e a b = true ↔ L6F1.zStroke e a b = true ∧ L6F1.wStroke e a b = true :=
  isZW_aux _ (L6F1.kind_lt e a b)

/-- The exchange of the colours on the codes exchanges the `z`-strokes and the `w`-strokes. -/
theorem zStroke_swapE (e : ℕ) (a b : Fin 6) : L6F1.zStroke (L6F1.swapE 6 e) a b = L6F1.wStroke e a b := by
  unfold L6F1.zStroke L6F1.wStroke
  rw [L6F1.kind_swapE le_rfl e a.isLt b.isLt]
  exact swapKind_z_aux _ (L6F1.kind_lt e a b)

theorem wStroke_swapE (e : ℕ) (a b : Fin 6) : L6F1.wStroke (L6F1.swapE 6 e) a b = L6F1.zStroke e a b := by
  unfold L6F1.zStroke L6F1.wStroke
  rw [L6F1.kind_swapE le_rfl e a.isLt b.isLt]
  exact swapKind_w_aux _ (L6F1.kind_lt e a b)

theorem invMap_val (σ : Equiv.Perm (Fin 6)) (k : Fin 6) : L6F1.invMap σ k = σ.symm k := by
  simp [L6F1.invMap]

/-- The relabelling of the codes: the pair `{a, b}` of `d.relabel 6 (invMap σ)` has the strokes of the pair
`{σ⁻¹ a, σ⁻¹ b}` of `d`. -/
theorem zStroke_relabel (σ : Equiv.Perm (Fin 6)) (d : L6F1.Diagram) (a b : Fin 6) :
    L6F1.zStroke (d.relabel 6 (L6F1.invMap σ)).e a b = L6F1.zStroke d.e (σ.symm a) (σ.symm b) := by
  unfold L6F1.zStroke
  rw [L6F1.kind_relabel le_rfl _ d a.isLt b.isLt, invMap_val, invMap_val]

theorem wStroke_relabel (σ : Equiv.Perm (Fin 6)) (d : L6F1.Diagram) (a b : Fin 6) :
    L6F1.wStroke (d.relabel 6 (L6F1.invMap σ)).e a b = L6F1.wStroke d.e (σ.symm a) (σ.symm b) := by
  unfold L6F1.wStroke
  rw [L6F1.kind_relabel le_rfl _ d a.isLt b.isLt, invMap_val, invMap_val]

/-! ## From codes to labelled diagrams -/

/-- The strokes `(a, b)`, `a < b`, of a stroke relation on the bodies given as natural numbers. -/
def strokesOf (s : ℕ → ℕ → Bool) : Finset (Fin 6 × Fin 6) :=
  univ.filter fun p => p.1 < p.2 ∧ s p.1 p.2 = true

/-- The circled bodies of a circle mask. -/
def circlesOf (c : ℕ) : Finset (Fin 6) := univ.filter fun k => L6F1.circled c k = true

/-- **The labelled diagram of a code** on six bodies. -/
def toDiagram (d : L6F1.Diagram) : Diagram 6 :=
  ⟨strokesOf (L6F1.zStroke d.e), strokesOf (L6F1.wStroke d.e), circlesOf d.zc, circlesOf d.wc⟩

theorem mem_strokesOf {s : ℕ → ℕ → Bool} {p : Fin 6 × Fin 6} :
    p ∈ strokesOf s ↔ p.1 < p.2 ∧ s p.1 p.2 = true := by
  simp only [strokesOf, Finset.mem_filter, Finset.mem_univ, true_and]

theorem strokesOf_lt (s : ℕ → ℕ → Bool) : ∀ e ∈ strokesOf s, e.1 < e.2 := fun _ he => (mem_strokesOf.mp he).1

theorem ord2_mem_strokesOf {s : ℕ → ℕ → Bool} (hs : ∀ a b, s a b = s b a) (a b : Fin 6) :
    Diagram.ord2 a b ∈ strokesOf s ↔ a ≠ b ∧ s a b = true := by
  rw [mem_strokesOf]
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [Diagram.ord2, min_eq_left h.le, max_eq_right h.le]
    exact ⟨fun h' => ⟨h.ne, h'.2⟩, fun h' => ⟨h, h'.2⟩⟩
  · simp [Diagram.ord2]
  · simp only [Diagram.ord2, min_eq_right h.le, max_eq_left h.le]
    rw [hs b a]
    exact ⟨fun h' => ⟨h.ne', h'.2⟩, fun h' => ⟨h, h'.2⟩⟩

theorem mem_circlesOf {c : ℕ} {k : Fin 6} : k ∈ circlesOf c ↔ L6F1.circled c k = true := by
  simp only [circlesOf, Finset.mem_filter, Finset.mem_univ, true_and]

theorem toDiagram_ordered (d : L6F1.Diagram) : (toDiagram d).Ordered :=
  ⟨fun e he => (strokesOf_lt _ e he).le, fun e he => (strokesOf_lt _ e he).le⟩

theorem toDiagram_zS (d : L6F1.Diagram) (k l : Fin 6) :
    (toDiagram d).zS k l ↔ k ≠ l ∧ L6F1.zStroke d.e k l = true := by
  show k ≠ l ∧ Diagram.ord2 k l ∈ strokesOf (L6F1.zStroke d.e) ↔ _
  rw [ord2_mem_strokesOf (L6F1.zStroke_comm d.e)]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem toDiagram_wS (d : L6F1.Diagram) (k l : Fin 6) :
    (toDiagram d).wS k l ↔ k ≠ l ∧ L6F1.wStroke d.e k l = true := by
  show k ≠ l ∧ Diagram.ord2 k l ∈ strokesOf (L6F1.wStroke d.e) ↔ _
  rw [ord2_mem_strokesOf (L6F1.wStroke_comm d.e)]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem mem_toDiagram_zCircles (d : L6F1.Diagram) (k : Fin 6) :
    k ∈ (toDiagram d).zCircles ↔ L6F1.circled d.zc k = true := mem_circlesOf

theorem mem_toDiagram_wCircles (d : L6F1.Diagram) (k : Fin 6) :
    k ∈ (toDiagram d).wCircles ↔ L6F1.circled d.wc k = true := mem_circlesOf

theorem diagram_eq_of {D D' : Diagram 6} (h1 : D.zStrokes = D'.zStrokes) (h2 : D.wStrokes = D'.wStrokes)
    (h3 : D.zCircles = D'.zCircles) (h4 : D.wCircles = D'.wCircles) : D = D' := by
  obtain ⟨a1, a2, a3, a4⟩ := D
  obtain ⟨b1, b2, b3, b4⟩ := D'
  change a1 = b1 at h1
  change a2 = b2 at h2
  change a3 = b3 at h3
  change a4 = b4 at h4
  rw [h1, h2, h3, h4]

/-! ## Relabelling and the exchange of the colours -/

/-- Membership in the strokes of `D.relabel σ`, for strokes stored as pairs `(k, l)` with `k < l`. -/
theorem mem_relabel_strokes {s : Finset (Fin 6 × Fin 6)} (hs : ∀ e ∈ s, e.1 < e.2) (σ : Equiv.Perm (Fin 6))
    (p : Fin 6 × Fin 6) :
    p ∈ s.image (fun e => Diagram.ord2 (σ.symm e.1) (σ.symm e.2)) ↔
      p.1 < p.2 ∧ Diagram.ord2 (σ p.1) (σ p.2) ∈ s := by
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨e, he, rfl⟩
    have hne : σ.symm e.1 ≠ σ.symm e.2 := σ.symm.injective.ne (hs e he).ne
    refine ⟨min_lt_max.mpr hne, ?_⟩
    rw [Diagram.ord2_map σ, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Diagram.ord2_of_le (hs e he).le]
    exact he
  · rintro ⟨hp, h⟩
    refine ⟨_, h, ?_⟩
    rw [Diagram.ord2_map σ.symm, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Diagram.ord2_of_le hp.le]

theorem strokesOf_relabel (σ : Equiv.Perm (Fin 6)) {s t : ℕ → ℕ → Bool} (hs : ∀ a b, s a b = s b a)
    (ht : ∀ a b : Fin 6, t a b = s (σ.symm a) (σ.symm b)) :
    strokesOf t = (strokesOf s).image (fun e => Diagram.ord2 (σ.symm.symm e.1) (σ.symm.symm e.2)) := by
  ext p
  rw [mem_relabel_strokes (strokesOf_lt s) σ.symm, mem_strokesOf, ord2_mem_strokesOf hs, ht]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, σ.symm.injective.ne hp.ne, h⟩
  · rintro ⟨hp, -, h⟩
    exact ⟨hp, h⟩

theorem strokesOf_congr {s t : ℕ → ℕ → Bool} (h : ∀ a b : Fin 6, s a b = t a b) : strokesOf s = strokesOf t := by
  ext p
  rw [mem_strokesOf, mem_strokesOf, h]

theorem circlesOf_relabel (σ : Equiv.Perm (Fin 6)) {c c' : ℕ}
    (h : ∀ k : Fin 6, L6F1.circled c' k = L6F1.circled c (σ.symm k)) :
    circlesOf c' = (circlesOf c).image σ.symm.symm := by
  ext k
  rw [mem_circlesOf, Finset.mem_image]
  constructor
  · intro hk
    exact ⟨σ.symm k, mem_circlesOf.mpr ((h k).symm.trans hk), σ.symm.symm_apply_apply k⟩
  · rintro ⟨j, hj, rfl⟩
    rw [h, Equiv.apply_symm_apply]
    exact mem_circlesOf.mp hj

/-- The relabelling of the codes by `σ` (`L6F1.Diagram.relabel` with the inverse map) is `Diagram.relabel σ⁻¹`. -/
theorem toDiagram_relabel (σ : Equiv.Perm (Fin 6)) (d : L6F1.Diagram) :
    toDiagram (d.relabel 6 (L6F1.invMap σ)) = (toDiagram d).relabel σ.symm := by
  apply diagram_eq_of
  · exact strokesOf_relabel σ (L6F1.zStroke_comm d.e) (zStroke_relabel σ d)
  · exact strokesOf_relabel σ (L6F1.wStroke_comm d.e) (wStroke_relabel σ d)
  · refine circlesOf_relabel σ fun k => ?_
    rw [L6F1.circled_relabel_zc _ _ k.isLt, invMap_val]
  · refine circlesOf_relabel σ fun k => ?_
    rw [L6F1.circled_relabel_wc _ _ k.isLt, invMap_val]

/-- The exchange of the colours of the codes is `Diagram.swap`. -/
theorem toDiagram_swap (d : L6F1.Diagram) : toDiagram (d.swap 6) = (toDiagram d).swap := by
  apply diagram_eq_of
  · exact strokesOf_congr (zStroke_swapE d.e)
  · exact strokesOf_congr (wStroke_swapE d.e)
  · rfl
  · rfl

/-- **The symmetries of the codes**: `toDiagram` sends `L6F1.actP 6 σ s` to the relabelling by `σ⁻¹`, followed by
the exchange of the colours if `s`. -/
theorem toDiagram_actP (σ : Equiv.Perm (Fin 6)) (s : Bool) (d : L6F1.Diagram) :
    toDiagram (L6F1.actP 6 σ s d) =
      bif s then ((toDiagram d).relabel σ.symm).swap else (toDiagram d).relabel σ.symm := by
  cases s
  · exact toDiagram_relabel σ d
  · show toDiagram ((d.relabel 6 (L6F1.invMap σ)).swap 6) = ((toDiagram d).relabel σ.symm).swap
    rw [toDiagram_swap, toDiagram_relabel]

/-! ## The code of the diagram of a germ -/

/-- The kind of a pair with the given strokes. -/
def kindOf (z w : Bool) : ℕ := (if z then 1 else 0) + (if w then 2 else 0)

theorem kindOf_lt (z w : Bool) : kindOf z w < 4 := by cases z <;> cases w <;> decide

theorem kindOf_z (z w : Bool) : (kindOf z w == 1 || kindOf z w == 3) = z := by cases z <;> cases w <;> rfl

theorem kindOf_w (z w : Bool) : (kindOf z w == 2 || kindOf z w == 3) = w := by cases z <;> cases w <;> rfl

theorem kindOf_ff : kindOf false false = 0 := rfl

open Classical in
/-- A relation on the six bodies as a Boolean function on the natural numbers (`false` outside the bodies). -/
def strokeB (R : Fin 6 → Fin 6 → Prop) (a b : ℕ) : Bool :=
  if h : a < 6 ∧ b < 6 then decide (R ⟨a, h.1⟩ ⟨b, h.2⟩) else false

open Classical in
/-- A set of bodies as a Boolean function on the natural numbers (`false` outside the bodies). -/
def circleB (P : Fin 6 → Prop) (k : ℕ) : Bool := if h : k < 6 then decide (P ⟨k, h⟩) else false

open Classical in
theorem strokeB_val (R : Fin 6 → Fin 6 → Prop) (a b : Fin 6) : strokeB R a b = true ↔ R a b := by
  unfold strokeB
  rw [dite_eq_left ⟨a.isLt, b.isLt⟩]
  exact decide_eq_true_iff

open Classical in
theorem circleB_val (P : Fin 6 → Prop) (k : Fin 6) : circleB P k = true ↔ P k := by
  unfold circleB
  rw [dite_eq_left k.isLt]
  exact decide_eq_true_iff

theorem strokeB_comm {R : Fin 6 → Fin 6 → Prop} (hR : ∀ a b, R a b → R b a) (a b : ℕ) :
    strokeB R a b = strokeB R b a := by
  unfold strokeB
  by_cases h : a < 6 ∧ b < 6
  · rw [dite_eq_left h, dite_eq_left h.symm]
    exact decide_eq_decide.mpr ⟨hR _ _, hR _ _⟩
  · rw [dite_eq_right h, dite_eq_right (fun h' => h h'.symm)]

open Classical in
theorem strokeB_self {R : Fin 6 → Fin 6 → Prop} (hR : ∀ a, ¬ R a a) (x : ℕ) : strokeB R x x = false := by
  unfold strokeB
  split_ifs with h
  · exact decide_eq_false (hR _)
  · rfl

variable {m : Fin 6 → ℝ}

/-- The kind of the pair `{a, b}` in the diagram of the germ `G`. -/
def germKind (G : Germ 6 m) (a b : ℕ) : ℕ := kindOf (strokeB G.zStroke a b) (strokeB G.wStroke a b)

theorem germKind_comm (G : Germ 6 m) (a b : ℕ) : germKind G a b = germKind G b a := by
  unfold germKind
  rw [strokeB_comm (fun _ _ h => G.zStroke_comm.mp h) a b, strokeB_comm (fun _ _ h => G.wStroke_comm.mp h) a b]

theorem germKind_self (G : Germ 6 m) (x : ℕ) : germKind G x x = 0 := by
  unfold germKind
  rw [strokeB_self (fun _ h => h.1 rfl), strokeB_self (fun _ h => h.1 rfl), kindOf_ff]

/-- **The code of the diagram of a germ** on six bodies. -/
def germCode (G : Germ 6 m) : L6F1.Diagram :=
  ⟨L6F1.codeOf 6 (germKind G), L6F1.maskOf 6 (circleB G.zCircle), L6F1.maskOf 6 (circleB G.wCircle)⟩

theorem germCode_kind (G : Germ 6 m) {x y : ℕ} (hx : x < 6) (hy : y < 6) :
    L6F1.kind (germCode G).e x y = germKind G x y :=
  L6F1.kind_codeOf (f := germKind G) le_rfl (fun _ _ => kindOf_lt _ _) (germKind_comm G) (germKind_self G) hx hy

theorem germCode_zStroke (G : Germ 6 m) (a b : Fin 6) :
    L6F1.zStroke (germCode G).e a b = true ↔ G.zStroke a b := by
  rw [L6F1.zStroke, germCode_kind G a.isLt b.isLt, germKind, kindOf_z]
  exact strokeB_val G.zStroke a b

theorem germCode_wStroke (G : Germ 6 m) (a b : Fin 6) :
    L6F1.wStroke (germCode G).e a b = true ↔ G.wStroke a b := by
  rw [L6F1.wStroke, germCode_kind G a.isLt b.isLt, germKind, kindOf_w]
  exact strokeB_val G.wStroke a b

theorem germCode_zc (G : Germ 6 m) (k : Fin 6) : L6F1.circled (germCode G).zc k = true ↔ G.zCircle k := by
  show L6F1.circled (L6F1.maskOf 6 (circleB G.zCircle)) k = true ↔ _
  rw [L6F1.circled_maskOf _ k.isLt]
  exact circleB_val G.zCircle k

theorem germCode_wc (G : Germ 6 m) (k : Fin 6) : L6F1.circled (germCode G).wc k = true ↔ G.wCircle k := by
  show L6F1.circled (L6F1.maskOf 6 (circleB G.wCircle)) k = true ↔ _
  rw [L6F1.circled_maskOf _ k.isLt]
  exact circleB_val G.wCircle k

theorem germCode_inRange (G : Germ 6 m) : L6F1.inRange 6 (germCode G) = true := by
  simp only [L6F1.inRange, germCode, Bool.and_eq_true]
  exact ⟨⟨decide_eq_true (L6F1.codeOf_lt fun _ _ => kindOf_lt _ _), decide_eq_true (L6F1.maskOf_lt _)⟩,
    decide_eq_true (L6F1.maskOf_lt _)⟩

/-- **The diagram of a germ is the labelled diagram of its code.** -/
theorem hasDiagram_germCode (G : Germ 6 m) : G.HasDiagram (toDiagram (germCode G)) := by
  refine ⟨fun k l => ?_, fun k l => ?_, fun k => ?_, fun k => ?_⟩
  · rw [toDiagram_zS, germCode_zStroke]
    exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  · rw [toDiagram_wS, germCode_wStroke]
    exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  · rw [mem_toDiagram_zCircles, germCode_zc]
  · rw [mem_toDiagram_wCircles, germCode_wc]

/-! ## The rules for the code of a germ -/

/-- If exactly one element of a list satisfies `P`, it is the only element of the list satisfying `P`. -/
theorem countP_eq_one_spec {α : Type*} {l : List α} {P : α → Bool} (h : l.countP P = 1) :
    ∃ x ∈ l, P x = true ∧ ∀ y ∈ l, P y = true → y = x := by
  rw [List.countP_eq_length_filter, List.length_eq_one_iff] at h
  obtain ⟨x, hx⟩ := h
  have hxm : x ∈ l.filter P := by rw [hx]; exact List.mem_singleton_self x
  rw [List.mem_filter] at hxm
  refine ⟨x, hxm.1, hxm.2, fun y hy hPy => ?_⟩
  have hym : y ∈ l.filter P := List.mem_filter.mpr ⟨hy, hPy⟩
  rw [hx, List.mem_singleton] at hym
  exact hym

theorem countP_ne_one_of {α : Type*} {l : List α} {P : α → Bool}
    (h : ∀ x ∈ l, P x = true → ∃ y ∈ l, y ≠ x ∧ P y = true) : l.countP P ≠ 1 := by
  intro h1
  obtain ⟨x, hx, hPx, hu⟩ := countP_eq_one_spec h1
  obtain ⟨y, hy, hyx, hPy⟩ := h x hx hPx
  exact hyx (hu y hy hPy)

theorem pairs6_spec : ∀ p ∈ L6F1.pairs 6, p.1 < p.2 ∧ p.2 < 6 := by decide

theorem pairs6_mem {a b : ℕ} (hab : a < b) (hb : b < 6) : (a, b) ∈ L6F1.pairs 6 := by
  simp only [L6F1.pairs, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  exact ⟨b, hb, a, hab, rfl, rfl⟩

/-- A walk of strokes of the germ is a walk of strokes of the code. -/
theorem rtg_to_nat {s : ℕ → ℕ → Bool} {R : Fin 6 → Fin 6 → Prop} (h : ∀ a b : Fin 6, s a b = true ↔ R a b)
    {k j : Fin 6} (hkj : Relation.ReflTransGen R k j) :
    Relation.ReflTransGen (L6F1.strokeRel 6 s) k j := by
  induction hkj with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨Fin.isLt _, Fin.isLt _, (h _ _).mpr hbc⟩

/-- A walk of strokes of the code from a body is a walk of strokes of the germ. -/
theorem rtg_of_nat {s : ℕ → ℕ → Bool} {R : Fin 6 → Fin 6 → Prop} (h : ∀ a b : Fin 6, s a b = true ↔ R a b)
    {k : Fin 6} {j : ℕ} (hkj : Relation.ReflTransGen (L6F1.strokeRel 6 s) k j) (hj : j < 6) :
    Relation.ReflTransGen R k ⟨j, hj⟩ := by
  revert hj
  induction hkj with
  | refl => intro _; exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    intro hj
    exact (ih hbc.1).tail ((h ⟨_, hbc.1⟩ ⟨_, hj⟩).mp hbc.2.2)

/-- **The rules of `L6F1.rulesZ 6`** (colour `z`) hold for an edge code `e` and a circle mask `c` whose strokes
and circles are those of a germ for positive masses. -/
theorem rulesZ_of_germ (hm : ∀ i, 0 < m i) (G : Germ 6 m) {e c : ℕ}
    (hz : ∀ a b : Fin 6, L6F1.zStroke e a b = true ↔ G.zStroke a b)
    (hw : ∀ a b : Fin 6, L6F1.wStroke e a b = true ↔ G.wStroke a b)
    (hc : ∀ k : Fin 6, L6F1.circled c k = true ↔ G.zCircle k) :
    L6F1.rulesZ 6 e c = true := by
  have hedge : ∀ a b : Fin 6, L6F1.isEdge e a b = true ↔ G.edge a b :=
    fun a b => (isEdge_iff e a b).trans (or_congr (hz a b) (hw a b))
  have hzw : ∀ a b : Fin 6, L6F1.isZW e a b = true ↔ G.zwEdge a b :=
    fun a b => (isZW_iff e a b).trans (and_congr (hz a b) (hw a b))
  have kindEq : ∀ a b c d : Fin 6, G.sameKind a b c d → L6F1.kind e a b = L6F1.kind e c d :=
    fun a b c d h => kind_eq_of_strokes (Bool.eq_iff_iff.mpr ((hz a b).trans (h.1.trans (hz c d).symm)))
      (Bool.eq_iff_iff.mpr ((hw a b).trans (h.2.trans (hw c d).symm)))
  -- (E1)
  have r1 : L6F1.ruleE1 6 e = true := by
    simp only [L6F1.ruleE1, decide_eq_true_eq]
    obtain ⟨k, l, hkl⟩ := G.E1_z
    exact ⟨k, k.isLt, l, l.isLt, fun h => hkl.1 (Fin.ext h), (hz k l).mpr hkl⟩
  -- (E2)
  have r2 : L6F1.ruleE2 6 e = true := by
    simp only [L6F1.ruleE2, decide_eq_true_eq]
    intro a ha b hb _ hab c hc' hca _ hbc
    exact (hzw ⟨a, ha⟩ ⟨c, hc'⟩).mpr (G.E2 ((hzw ⟨a, ha⟩ ⟨b, hb⟩).mp hab) ((hzw ⟨b, hb⟩ ⟨c, hc'⟩).mp hbc)
      (fun h => hca (congrArg Fin.val h).symm))
  -- (E3)
  have r3 : L6F1.ruleE3 6 e = true := by
    simp only [L6F1.ruleE3, decide_eq_true_eq]
    intro a ha b hb _ hab c hc' _ _ hbc hac
    have t := G.E3 ((hedge ⟨a, ha⟩ ⟨b, hb⟩).mp hab) ((hedge ⟨b, hb⟩ ⟨c, hc'⟩).mp hbc)
      (G.edge_comm.mp ((hedge ⟨a, ha⟩ ⟨c, hc'⟩).mp hac))
    exact ⟨kindEq ⟨a, ha⟩ ⟨b, hb⟩ ⟨b, hb⟩ ⟨c, hc'⟩ t.1.1,
      (kindEq ⟨b, hb⟩ ⟨c, hc'⟩ ⟨c, hc'⟩ ⟨a, ha⟩ t.1.2).trans (L6F1.kind_comm e c a)⟩
  -- (E4)
  have r4 : L6F1.ruleE4 6 e = true := by
    simp only [L6F1.ruleE4, decide_eq_true_eq]
    intro a ha b hb _ hab
    obtain ⟨j, hja, hjb, hj⟩ := G.E4_z hm ((hzw ⟨a, ha⟩ ⟨b, hb⟩).mp hab)
    refine ⟨j, j.isLt, fun h => hja (Fin.ext h), fun h => hjb (Fin.ext h), ?_⟩
    rcases hj with h | h
    · exact Or.inl ((hz ⟨a, ha⟩ j).mpr h)
    · exact Or.inr ((hz ⟨b, hb⟩ j).mpr h)
  -- (E5)
  have r5 : L6F1.ruleE5 6 e = true := by
    simp only [L6F1.ruleE5, decide_eq_true_eq]
    unfold L6F1.numZW
    apply countP_ne_one_of
    rintro ⟨a, b⟩ hp hab
    obtain ⟨hlt, hb⟩ := pairs6_spec _ hp
    obtain ⟨c, d, hcd, h1, h2⟩ := G.E5' hm ((hzw ⟨a, hlt.trans hb⟩ ⟨b, hb⟩).mp hab)
    rcases lt_or_gt_of_ne hcd.1.1 with h | h
    · refine ⟨((c : ℕ), (d : ℕ)), pairs6_mem h d.isLt, ?_, (hzw c d).mpr hcd⟩
      intro heq
      simp only [Prod.mk.injEq] at heq
      exact h1 ⟨Fin.ext heq.1, Fin.ext heq.2⟩
    · refine ⟨((d : ℕ), (c : ℕ)), pairs6_mem h c.isLt, ?_, (hzw d c).mpr (G.zwEdge_comm.mp hcd)⟩
      intro heq
      simp only [Prod.mk.injEq] at heq
      exact h2 ⟨Fin.ext heq.2, Fin.ext heq.1⟩
  -- (E6)
  have r6 : L6F1.ruleE6 6 e = true := by
    simp only [L6F1.ruleE6, decide_eq_true_eq]
    intro a ha b hb _ hab c hc' hca _ hbc d hd _ hdb _ hcd hda
    have t := G.E6 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (c := ⟨c, hc'⟩) (d := ⟨d, hd⟩)
      (fun h => hca (congrArg Fin.val h).symm) (fun h => hdb (congrArg Fin.val h).symm)
      ((hedge ⟨a, ha⟩ ⟨b, hb⟩).mp hab) ((hedge ⟨b, hb⟩ ⟨c, hc'⟩).mp hbc) ((hedge ⟨c, hc'⟩ ⟨d, hd⟩).mp hcd)
      ((hedge ⟨d, hd⟩ ⟨a, ha⟩).mp hda)
    exact ⟨kindEq _ _ _ _ t.1.2.2, kindEq _ _ _ _ t.2.2.2⟩
  -- (C1)
  have r7 : L6F1.ruleC1 6 e c = true := by
    simp only [L6F1.ruleC1, decide_eq_true_eq]
    intro k hk
    have hP : ∀ l : Fin 6, ((l : ℕ) != k && L6F1.zStroke e k l) = true ↔ G.zStroke ⟨k, hk⟩ l := by
      intro l
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
      constructor
      · rintro ⟨-, h⟩
        exact (hz ⟨k, hk⟩ l).mp h
      · intro h
        exact ⟨fun h' => h.1 (Fin.ext h'.symm), (hz ⟨k, hk⟩ l).mpr h⟩
    obtain ⟨c1, c2⟩ := G.C1_z hm ⟨k, hk⟩
    constructor
    · intro h0
      have hno : ∀ l : Fin 6, ¬ G.zStroke ⟨k, hk⟩ l := fun l hl =>
        (List.countP_eq_zero.mp h0 l (List.mem_range.mpr l.isLt)) ((hP l).mpr hl)
      cases hck : L6F1.circled c k
      · rfl
      · exact absurd ((hc ⟨k, hk⟩).mp hck) (c1 hno)
    · intro h1
      obtain ⟨x, hx, hPx, hu⟩ := countP_eq_one_spec h1
      have hx6 : x < 6 := List.mem_range.mp hx
      refine (hc ⟨k, hk⟩).mpr (c2 ⟨⟨x, hx6⟩, (hP ⟨x, hx6⟩).mp hPx, fun l hl => Fin.ext ?_⟩)
      exact hu l (List.mem_range.mpr l.isLt) ((hP l).mpr hl)
  -- (C2)
  have r8 : L6F1.ruleC2 6 e c = true := by
    simp only [L6F1.ruleC2, decide_eq_true_eq]
    intro k hk hck l hl _ hkl
    exact (hc ⟨l, hl⟩).mpr ((G.C2_z ((hw ⟨k, hk⟩ ⟨l, hl⟩).mp hkl)).mp ((hc ⟨k, hk⟩).mp hck))
  -- (C3)
  have r9 : L6F1.ruleC3 6 e c = true := by
    simp only [L6F1.ruleC3, decide_eq_true_eq]
    intro k hk hck
    obtain ⟨j, hzj, hcj, hwj⟩ := G.C3_z hm ((hc ⟨k, hk⟩).mp hck)
    refine ⟨(j : ℕ), j.isLt, (hc j).mpr hcj, (L6F1.mem_component_iff hk).mpr (rtg_to_nat hz hzj), ?_⟩
    rw [L6F1.mem_component_iff hk]
    exact fun h => hwj (rtg_of_nat (k := ⟨k, hk⟩) hw h j.isLt)
  -- (C4)
  have r10 : L6F1.ruleC4 6 e c = true := by
    simp only [L6F1.ruleC4, decide_eq_true_eq]
    intro l hl hcl k hk _ hck hkl j hj hjk _ hcj hlj
    refine (hz ⟨k, hk⟩ ⟨j, hj⟩).mpr (G.C4_z ((hc ⟨k, hk⟩).mp hck) ((hc ⟨j, hj⟩).mp hcj) ?_
      ((hz ⟨k, hk⟩ ⟨l, hl⟩).mp hkl) ((hz ⟨l, hl⟩ ⟨j, hj⟩).mp hlj) (fun h => hjk (congrArg Fin.val h).symm))
    intro h
    have h' := (hc ⟨l, hl⟩).mpr h
    rw [hcl] at h'
    exact Bool.false_ne_true h'
  simp only [L6F1.rulesZ, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, Bool.and_self]

/-- **The code of the diagram of a germ for positive masses satisfies the rules in both colours.** -/
theorem okRules_germCode (hm : ∀ i, 0 < m i) (G : Germ 6 m) : L6F1.okRules 6 (germCode G) = true := by
  rw [L6F1.okRules, Bool.and_eq_true]
  refine ⟨rulesZ_of_germ hm G (germCode_zStroke G) (germCode_wStroke G) (germCode_zc G), ?_⟩
  refine rulesZ_of_germ hm G.swap (fun a b => ?_) (fun a b => ?_) (germCode_wc G)
  · rw [zStroke_swapE]
    exact germCode_wStroke G a b
  · rw [wStroke_swapE]
    exact germCode_zStroke G a b

end

end CC6Compose
