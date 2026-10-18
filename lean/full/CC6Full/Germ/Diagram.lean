import CC6Full.Germ.Symm

/-!
# Labelled diagrams, the diagram of a germ, and the ten diagrams of Table 1

§2.4 (`ss:rules`) and §3 (`sec:diagrams`). A *labelled diagram* records the `z`-strokes, the `w`-strokes (as pairs
`(k, l)` with `k < l`) and the `z`- and `w`-circled bodies. `Germ.HasDiagram G D` says that `D` is the diagram of
the germ `G`. Relabelling and the exchange of the colours act on diagrams compatibly with `Germ.relabel` and
`Germ.swap` (Lemma 2.9, `lem:symm`).

`Diagram.d64`, …, `Diagram.d98`: the diagrams of Table 1 (`tab:ten`), numbered and labelled as in [CC23, Figs. 5,
6]; body `k` of the paper is `k - 1`.
-/

namespace CC6Full

open Finset

noncomputable section

/-- A labelled diagram on `n` bodies: strokes as pairs `(k, l)` with `k < l`, circles as sets of bodies. -/
structure Diagram (n : ℕ) where
  /-- the `z`-strokes -/
  zStrokes : Finset (Fin n × Fin n)
  /-- the `w`-strokes -/
  wStrokes : Finset (Fin n × Fin n)
  /-- the `z`-circled bodies -/
  zCircles : Finset (Fin n)
  /-- the `w`-circled bodies -/
  wCircles : Finset (Fin n)
  deriving DecidableEq

namespace Diagram

variable {n : ℕ}

/-- The pair `(min k l, max k l)`. -/
def ord2 (k l : Fin n) : Fin n × Fin n := (min k l, max k l)

/-- `kl` is a `z`-stroke of `D` (symmetric in `k, l`). -/
def zS (D : Diagram n) (k l : Fin n) : Prop := k ≠ l ∧ ord2 k l ∈ D.zStrokes

/-- `kl` is a `w`-stroke of `D`. -/
def wS (D : Diagram n) (k l : Fin n) : Prop := k ≠ l ∧ ord2 k l ∈ D.wStrokes

/-- The diagram with the colours exchanged. -/
def swap (D : Diagram n) : Diagram n := ⟨D.wStrokes, D.zStrokes, D.wCircles, D.zCircles⟩

/-- The relabelled diagram: body `k` of `D.relabel σ` is body `σ k` of `D` (the diagram of `G.relabel σ` when `D` is
the diagram of `G`). -/
def relabel (σ : Equiv.Perm (Fin n)) (D : Diagram n) : Diagram n where
  zStrokes := D.zStrokes.image fun e => ord2 (σ.symm e.1) (σ.symm e.2)
  wStrokes := D.wStrokes.image fun e => ord2 (σ.symm e.1) (σ.symm e.2)
  zCircles := D.zCircles.image σ.symm
  wCircles := D.wCircles.image σ.symm

/-- The labelled diagram given by lists in the paper's numbering (bodies `1, …, n`). -/
def ofLists (zs ws : List (ℕ × ℕ)) (zc wc : List ℕ) : Diagram n where
  zStrokes := ((zs.filterMap fun e => if h : e.1 - 1 < n ∧ e.2 - 1 < n then
      some (ord2 ⟨e.1 - 1, h.1⟩ ⟨e.2 - 1, h.2⟩) else none).toFinset)
  wStrokes := ((ws.filterMap fun e => if h : e.1 - 1 < n ∧ e.2 - 1 < n then
      some (ord2 ⟨e.1 - 1, h.1⟩ ⟨e.2 - 1, h.2⟩) else none).toFinset)
  zCircles := ((zc.filterMap fun k => if h : k - 1 < n then some ⟨k - 1, h⟩ else none).toFinset)
  wCircles := ((wc.filterMap fun k => if h : k - 1 < n then some ⟨k - 1, h⟩ else none).toFinset)

/-! ## Table 1 -/

/-- Diagram 64: `z`-strokes on all pairs of `{3,4,5,6}`, no `z`-circle; `w`-stroke `12`, `w`-circles `1, 2`. -/
def d64 : Diagram 6 :=
  ofLists [(3,4), (3,5), (3,6), (4,5), (4,6), (5,6)] [(1,2)] [] [1, 2]

/-- Diagram 66: as 64 with the `w`-strokes `12, 16, 26`. -/
def d66 : Diagram 6 :=
  ofLists [(3,4), (3,5), (3,6), (4,5), (4,6), (5,6)] [(1,2), (1,6), (2,6)] [] [1, 2]

/-- Diagram 88: `z`-stroke `56`, `z`-circles `5, 6`; `w`-strokes on all pairs of `{1,2,3,4}`, `w`-circles
`1, 2, 3, 4`. -/
def d88 : Diagram 6 :=
  ofLists [(5,6)] [(1,2), (1,3), (1,4), (2,3), (2,4), (3,4)] [5, 6] [1, 2, 3, 4]

/-- Diagram 89: `z`-strokes `45, 46, 56`, `z`-circles `5, 6`; `w`-strokes `23, 24, 34`, `w`-circles `2, 3`. -/
def d89 : Diagram 6 :=
  ofLists [(4,5), (4,6), (5,6)] [(2,3), (2,4), (3,4)] [5, 6] [2, 3]

/-- Diagram 93: `z`-strokes `45, 46, 56`, `z`-circles `5, 6`; `w`-strokes `12, 13, 23`, `w`-circles `1, 2, 3`. -/
def d93 : Diagram 6 :=
  ofLists [(4,5), (4,6), (5,6)] [(1,2), (1,3), (2,3)] [5, 6] [1, 2, 3]

/-- Diagram 94: `z`-strokes `45, 46, 56`, `z`-circles `5, 6`; `w`-strokes on all pairs of `{1,2,3,4}`,
`w`-circles `1, 2, 3`. -/
def d94 : Diagram 6 :=
  ofLists [(4,5), (4,6), (5,6)] [(1,2), (1,3), (1,4), (2,3), (2,4), (3,4)] [5, 6] [1, 2, 3]

/-- Diagram 98: `z`-strokes `45, 46, 56`, `z`-circles `4, 5, 6`; `w`-strokes `12, 13, 23`, `w`-circles
`1, 2, 3`. -/
def d98 : Diagram 6 :=
  ofLists [(4,5), (4,6), (5,6)] [(1,2), (1,3), (2,3)] [4, 5, 6] [1, 2, 3]

end Diagram

namespace Germ

variable {n : ℕ} {m : Fin n → ℝ}

/-- `D` is the diagram of the germ `G`. -/
def HasDiagram (G : Germ n m) (D : Diagram n) : Prop :=
  (∀ k l, G.zStroke k l ↔ D.zS k l) ∧ (∀ k l, G.wStroke k l ↔ D.wS k l) ∧
    (∀ k, G.zCircle k ↔ k ∈ D.zCircles) ∧ (∀ k, G.wCircle k ↔ k ∈ D.wCircles)

theorem HasDiagram.swap {G : Germ n m} {D : Diagram n} (h : G.HasDiagram D) : G.swap.HasDiagram D.swap := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun k l => ?_, fun k l => ?_, fun k => ?_, fun k => ?_⟩
  · rw [swap_zStroke]; exact h2 k l
  · rw [swap_wStroke]; exact h1 k l
  · rw [swap_zCircle]; exact h4 k
  · rw [swap_wCircle]; exact h3 k

end Germ

end

end CC6Full
