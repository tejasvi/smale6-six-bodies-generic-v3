import Lean6.Special.Cover.Comp.Basic

/-!
# Proposition 9.23: the lemmas at every positive mass (Lemmas 9.2–9.7)

The hypotheses of Lemmas 9.2 (`handT`), 9.3 (`handP`), 9.4 (`handC`), 9.5 (`handB0`), 9.6 (`handK`) and 9.7 (`handL`)
of the paper, read off the trees and the argmin sets of a stored cell (and, for Lemma 9.3, the diagram of its class).
Each predicate says that the hypotheses hold for some choice of the objects the lemma names (sets of bodies, bodies, a
colour); it is a literal transcription of the statement, with these readings:

* Nodes are those of the stored trees, points are the bodies `0, …, 5` and `O = 6`; `meet_c(p, q)` is `none` when `p`
  and `q` share a leaf, and a comparison `u ⪯ v` or an equality of nodes that involves `none` is false (`optPre`,
  `optEq`). A body that shares the leaf of `O` in `T_c` has `c_k ≡ 0`: its position is never minimal.
* Lemma 9.2: `J` ranges over the nonempty proper subsets of the bodies, the cross pairs of `J` are the ordered pairs
  `(p, q)` with exactly one of `p`, `q` in `J`, and the term of `(p, q)` is present unless `p` shares the leaf of `O` in
  `T_z` or `q` does in `T_w`. In (Z) and (W) "every cross pair" includes the pairs whose term is absent.
* Lemma 9.3: `x_kl > 0` is forced by (x1)–(x4); a `zw`-edge is a pair that is both a `z`-stroke and a `w`-stroke, and a
  `z`-stroke is any pair with a `z`-stroke (it may also be a `w`-stroke). In (x3) the term `m_k m_l p_kl` of `U = E` is
  the label `delta k l` of the argmin set of `U = E`, and the constant is the label `E`.
* Lemma 9.4: `J` is a set of at least two bodies (`lemC`: `2 ≤ |J| ≤ 6`, the statement); `lemCProg` restricts to
  `2 ≤ |J| ≤ 5`, as the two programs of the supplement do. The terms of `X` are the positions `pos k` and the forces
  `cross k l` with `l ∉ J` in the argmin sets `A^c_k`, `k ∈ J`.
* Lemmas 9.6 and 9.7: points lie below three distinct children of one node exactly when the node is their pairwise
  meet and the children on the paths to them are distinct.

The computations use per-cell tables (`TreeTab`: the ancestors of every node and the meets of all pairs of points),
which give the same values as `L6.F34.Tree.preceq` and `L6.F34.Tree.meetC`.
-/

namespace Lean6.Special.Cover.Every

open L6.F34

/-- The two colours: `true` for `z`, `false` for `w`. -/
def colours : List Bool := [true, false]

/-! ## Tables of a tree -/

/-- A tree with the ancestors of each node id `< maxNode` and the meets of the points `0, …, 6` (at `7 * p + q`). -/
structure TreeTab where
  t : Tree
  anc : Array (List Nat)
  meets : Array (Option Nat)

/-- The tables of a tree. -/
def TreeTab.ofTree (t : Tree) : TreeTab :=
  { t, anc := (Array.range maxNode).map t.ancestors, meets := (Array.range 49).map fun i => t.meet (i / 7) (i % 7) }

/-- `meet(p, q)`. -/
def TreeTab.meet (tt : TreeTab) (p q : Nat) : Option Nat := tt.meets.getD (7 * p + q) none

/-- `u ⪯ v`. -/
def TreeTab.pre (tt : TreeTab) (u v : Nat) : Bool := (tt.anc.getD v []).contains u

/-- `u ⪯ v` for nodes that exist; false if one of them is `none`. -/
def TreeTab.optPre (tt : TreeTab) : Option Nat → Option Nat → Bool
  | some u, some v => tt.pre u v
  | _, _ => false

/-- Two nodes that exist are equal; false if one of them is `none`. -/
def optEq : Option Nat → Option Nat → Bool
  | some u, some v => u == v
  | _, _ => false

/-- `O` lies below the node (false for `none`). -/
def belowO (t : Tree) : Option Nat → Bool
  | some v => t.below v O
  | none => false

/-! ## Lemma 9.2 (`handT`): a single term of least exponent in a torque -/

/-- The nonempty proper subsets of the bodies. -/
def properSubsets : List (List Nat) := [1, 2, 3, 4, 5].flatMap fun r => subsets r bodies

/-- The cross pairs of `J`: the ordered pairs `(p, q)` of bodies with exactly one of `p`, `q` in `J`. -/
def crossPairs (J : List Nat) : List (Nat × Nat) :=
  bodies.flatMap fun p => (bodies.filter fun q => J.contains p != J.contains q).map fun q => (p, q)

/-- The term `± m_p m_q p_pq³ z_p w_q` of the cross pair `(p, q)` is present: `z_p, w_q ≢ 0`. -/
def present (x : Cell) (pq : Nat × Nat) : Bool := !x.zt.atO pq.1 && !x.wt.atO pq.2

/-- The nodes `meet_z(p, q)`, `meet_z(p, O)`, `meet_w(p, q)`, `meet_w(q, O)` of a cross pair (condition (S)). -/
def sigT (tz tw : TreeTab) (pq : Nat × Nat) : Option Nat × Option Nat × Option Nat × Option Nat :=
  (tz.meet pq.1 pq.2, tz.meet pq.1 O, tw.meet pq.1 pq.2, tw.meet pq.2 O)

/-- (Z), (W) and (S) of Lemma 9.2 for the present cross pair `(p, q)` of `J`. -/
def condT (x : Cell) (tz tw : TreeTab) (cps : List (Nat × Nat)) (pq : Nat × Nat) : Bool :=
  let (p, q) := pq
  let nz := tz.meet p q
  let nw := tw.meet p q
  present x pq &&
    -- (Z)
    tz.optPre (tz.meet p O) nz && cps.all (fun kl => tz.optPre (tz.meet kl.1 kl.2) nz) &&
    -- (W)
    tw.optPre (tw.meet q O) nw && cps.all (fun kl => tw.optPre (tw.meet kl.1 kl.2) nw) &&
    -- (S)
    cps.all fun kl => kl == pq || !present x kl || sigT tz tw kl != sigT tz tw pq

/-- **Lemma 9.2**: for some nonempty proper subset `J` some present cross pair satisfies (Z), (W), (S). -/
def lemT (x : Cell) : Bool :=
  let tz := TreeTab.ofTree x.zt
  let tw := TreeTab.ofTree x.wt
  properSubsets.any fun J =>
    let cps := crossPairs J
    cps.any (condT x tz tw cps)

/-! ## Lemma 9.3 (`handP`): the constant `E` alone of least exponent -/

/-- A `zw`-edge of the diagram: a pair that is a `z`-stroke and a `w`-stroke. -/
def zwEdge (d : Diagram) (k l : Nat) : Bool := d.zstroke k l && d.wstroke k l

/-- (x4) in colour `c` for the force of `l` on `k`: it is minimal in the `c`-equation of `k`, the position of `k` is
not, and `meet_c(k, O) = meet_c(k, l)`. -/
def x4 (x : Cell) (c : Bool) (k l : Nat) : Bool :=
  x.forceMin c k l && !x.posMin c k && optEq ((x.tree c).meetC k O) ((x.tree c).meetC k l)

/-- `x_kl > 0` is forced: one of (x1)–(x4) holds. -/
def forced (x : Cell) (d : Diagram) (k l : Nat) : Bool :=
  -- (x1)
  zwEdge d k l ||
  -- (x2)
  (d.zstroke k l && !d.zc.getD k false && !d.zc.getD l false) ||
  (d.wstroke k l && !d.wc.getD k false && !d.wc.getD l false) ||
  -- (x3)
  (let aU := x.am .U
   (aU.contains (.delta k l) || aU.contains (.delta l k)) && !aU.contains .E) ||
  -- (x4)
  colours.any fun c => x4 x c k l || x4 x c l k

/-- **Lemma 9.3**: every body `k` with `z_k, w_k ≢ 0` has a body `l` such that `O` lies below `meet_z(k, l)` and
below `meet_w(k, l)` and `x_kl > 0` is forced. -/
def lemP (x : Cell) (d : Diagram) : Bool :=
  bodies.all fun k => x.zt.atO k || x.wt.atO k ||
    bodies.any fun l => l != k && belowO x.zt (x.zt.meetC k l) && belowO x.wt (x.wt.meetC k l) && forced x d k l

/-! ## Lemma 9.4 (`handC`): a cluster sum -/

/-- The edge of the graph of (C1) in colour `c`: the forces of `l` on `k` and of `k` on `l` are minimal, or the
positions of `k` and `l` are minimal and `meet_c(k, O) = meet_c(l, O)`. -/
def joined (x : Cell) (c : Bool) (k l : Nat) : Bool :=
  (x.forceMin c k l && x.forceMin c l k) ||
    (x.posMin c k && x.posMin c l && optEq ((x.tree c).meetC k O) ((x.tree c).meetC l O))

/-- The graph on `J` with the edges `adj` is connected. -/
def connected (J : List Nat) (adj : Nat → Nat → Bool) : Bool :=
  match J with
  | [] => true
  | j :: _ => Id.run do
    let mut seen := [j]
    let mut frontier := [j]
    for _ in [0:J.length] do
      let new := J.filter fun u => !seen.contains u && frontier.any (adj · u)
      seen := seen ++ new
      frontier := new
    return J.all seen.contains

/-- The set `X` of (C2): the minimal terms of the `c`-equations of the bodies of `J` that are positions or forces of
bodies outside `J`. -/
def termsX (x : Cell) (c : Bool) (J : List Nat) : List Lab :=
  J.flatMap fun k => (x.eqSet c k).toList.filter fun t =>
    match t with
    | .pos i => i == k
    | .cross i l => i == k && !J.contains l
    | _ => false

/-- (C2) in colour `c`: `X` is not empty, and it is one term, or the positions of the bodies of a set `I` that lie
below one child of a node `v` with `meet_c(k, O) = v` for all `k ∈ I`. -/
def condC2 (x : Cell) (c : Bool) (J : List Nat) : Bool :=
  let X := termsX x c J
  let t := x.tree c
  let posOnly := X.all fun l => match l with | .pos _ => true | _ => false
  let I := X.filterMap fun l => match l with | .pos i => some i | _ => none
  !X.isEmpty && (X.length == 1 ||
    (posOnly &&
      match I with
      | [] => false
      | i :: _ =>
        match t.meetC i O with
        | none => false
        | some v =>
          let ci := t.childTo v i
          ci.isSome && I.all fun k => t.meetC k O == some v && t.childTo v k == ci))

/-- Lemma 9.4 for the sets `J` with a size in `sizes`. -/
def lemCSizes (sizes : List Nat) (x : Cell) : Bool :=
  colours.any fun c => sizes.any fun r => (subsets r bodies).any fun J => connected J (joined x c) && condC2 x c J

/-- **Lemma 9.4**: in some colour, some set `J` of at least two bodies satisfies (C1) and (C2). -/
def lemC (x : Cell) : Bool := lemCSizes [2, 3, 4, 5, 6] x

/-- Lemma 9.4 with `2 ≤ |J| ≤ 5`, as in the programs of the supplement. -/
def lemCProg (x : Cell) : Bool := lemCSizes [2, 3, 4, 5] x

/-! ## Lemma 9.5 (`handB0`) -/

/-- (i) in colour `c` and (ii) in the other colour for the bodies `k ≠ l`. -/
def condB0 (x : Cell) (c : Bool) (k l : Nat) : Bool :=
  let t := x.tree c
  let t' := x.tree (!c)
  -- (i)
  x.eqSetIs c l true [k] &&
    (match t.meetC l k, t.meetC l O with
     | some v, some v' => v == v' && t.inOChild v k
     | _, _ => false) &&
  -- (ii)
  x.eqSetIs (!c) l true [k] &&
    (match t'.meetC l k, t'.meetC l O with
     | some u, some u' =>
       u == u' &&
         (match t'.childTo u k, t'.childTo u O with
          | some a, some b => a != b
          | _, _ => false)
     | _, _ => false)

/-- **Lemma 9.5**: for some colour `c` and bodies `k ≠ l`, (i) holds in `c` and (ii) in the other colour. -/
def lemB0 (x : Cell) : Bool :=
  colours.any fun c => bodies.any fun l => bodies.any fun k => k != l && condB0 x c k l

/-! ## Lemma 9.6 (`handK`) -/

/-- `k`, `l` and `O` lie below three distinct children of one node of `t`. -/
def threeKids (t : Tree) (k l : Nat) : Bool :=
  match t.meetC k l with
  | none => false
  | some v =>
    match t.childTo v k, t.childTo v l, t.childTo v O with
    | some a, some b, some o => a != b && a != o && b != o
    | _, _, _ => false

/-- (i) in colour `c` and (ii) in the other colour for the bodies `k ≠ l`. -/
def condK (x : Cell) (c : Bool) (k l : Nat) : Bool :=
  -- (i)
  threeKids (x.tree c) k l && x.eqSetIs c k true [l] && x.eqSetIs c l true [k] &&
  -- (ii)
  threeKids (x.tree (!c)) k l &&
    [(k, l), (l, k)].any fun (p, q) =>
      x.eqSetIs (!c) p true [q] && bodies.any fun j => j != k && j != l && x.eqSetIs (!c) q true [p, j]

/-- **Lemma 9.6**: for some colour `c` and bodies `k ≠ l`, (i) holds in `c` and (ii) in the other colour. -/
def lemK (x : Cell) : Bool :=
  colours.any fun c => bodies.any fun k => bodies.any fun l => k != l && condK x c k l

/-! ## Lemma 9.7 (`handL`) -/

/-- The node `v = meet(a, b)` and the children of `v` below which `a`, `b`, `s` lie, if these three children are
distinct (then `v` is the meet of each pair). -/
def tripleNode (t : Tree) (a b s : Nat) : Option (Nat × Nat × Nat × Nat) :=
  match t.meetC a b with
  | none => none
  | some v =>
    match t.childTo v a, t.childTo v b, t.childTo v s with
    | some ca, some cb, some cs => if ca != cb && ca != cs && cb != cs then some (v, ca, cb, cs) else none
    | _, _, _ => none

/-- (L1) in colour `c` and (L2) in the other colour for `T = {a, b, s}`. -/
def condL (x : Cell) (c : Bool) (a b s : Nat) : Bool :=
  let t := x.tree c
  let t' := x.tree (!c)
  let T := [a, b, s]
  -- (L1)
  (match tripleNode t a b s with
   | some (v, ca, cb, cs) =>
     t.below v O &&
       (match t.childTo v O with
        | some o => o != ca && o != cb && o != cs
        | none => false)
   | none => false) &&
  T.all (fun k => x.eqSetIs c k true (T.filter (· != k))) &&
  -- (L2)
  (match tripleNode t' a b s with
   | some (v', _, _, _) => t'.inOChild v' s
   | none => false) &&
  x.eqSetIs (!c) s false [a, b] && x.eqSetIs (!c) a true [s, b] && x.eqSetIs (!c) b true [s, a]

/-- **Lemma 9.7**: for some colour `c`, three bodies `T` and a choice of `s ∈ T`, (L1) holds in `c` and (L2) in the
other colour. -/
def lemL (x : Cell) : Bool :=
  colours.any fun c => (subsets 3 bodies).any fun T =>
    match T with
    | [p, q, r] => [(p, q, r), (p, r, q), (q, r, p)].any fun (a, b, s) => condL x c a b s
    | _ => false

/-! ## All six -/

/-- The lemmas among 9.2–9.7 whose hypotheses hold in the cell, by the names of the supplement (`T`, `P`, `C`, `B0`,
`K`, `L`). -/
def everyNames (x : Cell) (d : Diagram) : List String :=
  [("T", lemT x), ("P", lemP x d), ("C", lemC x), ("B0", lemB0 x), ("K", lemK x), ("L", lemL x)].filterMap
    fun (n, b) => if b then some n else none

end Lean6.Special.Cover.Every
