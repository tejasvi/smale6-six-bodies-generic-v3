import L6F34.Basic

/-!
# F3, F4 on the cells of the specification search: the identities as term lists

The identities of §2.3 that the exclusions of Proposition 5.3 use, as lists of terms, each term a coefficient times a
product of factors `z_p − z_q`, `w_p − w_q` and `p_kl` (points `0, …, 5` and `O = 6`; the position `z_k` is the factor
`(k, O)`, the separation `z_kl` the factor `(k, l)`, and `Z_kl = p_kl³ z_kl` has three factors `p_kl`). The families,
their parameters, the order of the terms and the coefficients are those of the full formalization (`Identity.bodyZ`,
`bodyW`, `potU`, `lagr`, `subsetSumZ`, `subsetSumW`, `torque`, `partialVirial`, `differenceZ`, `differenceW`,
`potVirial`, `virialE`): an identity `A = B` is written `A − B = 0`, sums over `k ∈ J` run over increasing `k`, sums
over `k ∈ J`, `l ∉ J` over the pairs in lexicographic order, and terms whose position factor vanishes (a body on the
leaf of `O`) are kept, with exponent `⊤`. Each term also carries the label of the engine's term (`L6.F34.Lab`), by
which the stored claims name terms.

The engine multiplies the equation of body `k` by `m_k`; the term lists here do not (as in the full formalization),
and the factor is accounted for where the initial forms are compared with the certificates (`XId.scale`).
-/

namespace L6.F34S

open L6.F34 (Lab IdName)

/-- A coefficient `num / den · Π_{i ∈ masses} m_i · (Σ_k m_k)^[msum] · E^[e]`. -/
structure XCoef where
  num : Int
  den : Nat := 1
  masses : List Nat := []
  msum : Bool := false
  e : Bool := false
  deriving Inhabited, Repr, DecidableEq

/-- A term `c · Π (z_p − z_q) · Π (w_p − w_q) · Π p_kl`, with the label of the engine's term. -/
structure XTerm where
  lab : Lab
  coef : XCoef
  zs : List (Nat × Nat)
  ws : List (Nat × Nat)
  ps : List (Nat × Nat)
  deriving Inhabited

/-- The centre of mass. -/
def O : Nat := 6

/-- The bodies of `J`, in increasing order. -/
def bodiesIn (J : List Nat) : List Nat := (List.range 6).filter fun k => J.contains k

/-- The bodies not in `J`, in increasing order. -/
def bodiesOut (J : List Nat) : List Nat := (List.range 6).filter fun k => !J.contains k

/-- The pairs `(k, l)`, `k ∈ J`, `l ∉ J`, in lexicographic order. -/
def crossOf (J : List Nat) : List (Nat × Nat) := (bodiesIn J).flatMap fun k => (bodiesOut J).map fun l => (k, l)

/-- The pairs `(k, l)`, `k < l`, of `J`, in lexicographic order. -/
def pairsIn (J : List Nat) : List (Nat × Nat) :=
  (bodiesIn J).flatMap fun k => ((bodiesIn J).filter fun l => k < l).map fun l => (k, l)

/-- The pairs `(k, l)`, `k < l`, of all six bodies, in lexicographic order. -/
def pairsAll : List (Nat × Nat) := pairsIn (List.range 6)

/-- Three factors `p_kl`. -/
def p3 (k l : Nat) : List (Nat × Nat) := [(k, l), (k, l), (k, l)]

/-- The bodies other than `k`, in increasing order. -/
def others (k : Nat) : List Nat := (List.range 6).filter fun j => j != k

/-- The identities used by the exclusions (families and parameters). -/
inductive XId where
  | bodyZ (k : Nat) | bodyW (k : Nat) | potU | lagr
  | subsetZ (J : List Nat) | subsetW (J : List Nat) | torque (J : List Nat) | virial (J : List Nat)
  | diffZ (k l : Nat) | diffW (k l : Nat) | potVirial | virialE
  deriving Inhabited, DecidableEq, Repr

/-- `J` is a strictly increasing list of bodies. -/
def incBodies (J : List Nat) : Bool := J.all (· < 6) && (J.zip (J.drop 1)).all fun ab => ab.1 < ab.2

/-- The conditions of the list of §5.1 (and of the base identities): bodies `< 6`; subset sums for `2 ≤ |J| ≤ 4`,
torques for `0 ∈ J`, `|J| ≤ 5`, partial virials for `1 ≤ |J| ≤ 5`, differences for `k < l`. -/
def XId.valid : XId → Bool
  | .bodyZ k | .bodyW k => k < 6
  | .potU | .lagr | .potVirial | .virialE => true
  | .subsetZ J | .subsetW J => incBodies J && 2 ≤ J.length && J.length ≤ 4
  | .torque J => incBodies J && J.contains 0 && J.length ≤ 5
  | .virial J => incBodies J && 1 ≤ J.length && J.length ≤ 5
  | .diffZ k l | .diffW k l => k < l && l < 6

/-- The terms of an identity, in the order of the full formalization. -/
def XId.terms : XId → List XTerm
  | .bodyZ k =>
    ⟨.pos k, { num := 1 }, [(k, O)], [], []⟩ ::
      (others k).map fun l => ⟨.cross k l, { num := -1, masses := [l] }, [(k, l)], [], p3 k l⟩
  | .bodyW k =>
    ⟨.pos k, { num := 1 }, [], [(k, O)], []⟩ ::
      (others k).map fun l => ⟨.cross k l, { num := -1, masses := [l] }, [], [(k, l)], p3 k l⟩
  | .potU =>
    pairsAll.map (fun kl => ⟨.delta kl.1 kl.2, { num := 1, masses := [kl.1, kl.2] }, [], [], [kl]⟩) ++
      [⟨.E, { num := -1, e := true }, [], [], []⟩]
  | .lagr =>
    pairsAll.map (fun kl => ⟨.zw kl.1 kl.2, { num := 1, masses := [kl.1, kl.2] }, [kl], [kl], []⟩) ++
      [⟨.E, { num := -1, msum := true, e := true }, [], [], []⟩]
  | .subsetZ J =>
    (bodiesIn J).map (fun k => ⟨.SP true k, { num := 1, masses := [k] }, [(k, O)], [], []⟩) ++
      (crossOf J).map fun kl => ⟨.SC true kl.1 kl.2, { num := -1, masses := [kl.1, kl.2] }, [kl], [], p3 kl.1 kl.2⟩
  | .subsetW J =>
    (bodiesIn J).map (fun k => ⟨.SP false k, { num := 1, masses := [k] }, [], [(k, O)], []⟩) ++
      (crossOf J).map fun kl => ⟨.SC false kl.1 kl.2, { num := -1, masses := [kl.1, kl.2] }, [], [kl], p3 kl.1 kl.2⟩
  | .torque J =>
    (crossOf J).flatMap fun kl =>
      [⟨.T1 kl.1 kl.2, { num := 1, masses := [kl.1, kl.2] }, [(kl.1, O)], [(kl.2, O)], p3 kl.1 kl.2⟩,
       ⟨.T2 kl.1 kl.2, { num := -1, masses := [kl.1, kl.2] }, [(kl.2, O)], [(kl.1, O)], p3 kl.1 kl.2⟩]
  | .virial J =>
    (bodiesIn J).map (fun k => ⟨.V0 k, { num := 1, masses := [k] }, [(k, O)], [(k, O)], []⟩) ++
      (pairsIn J).map (fun kl => ⟨.V1 kl.1 kl.2, { num := -1, masses := [kl.1, kl.2] }, [], [], [kl]⟩) ++
      (crossOf J).flatMap fun kl =>
        [⟨.V2 kl.1 kl.2, { num := -1, den := 2, masses := [kl.1, kl.2] }, [kl], [(kl.1, O)], p3 kl.1 kl.2⟩,
         ⟨.V3 kl.1 kl.2, { num := -1, den := 2, masses := [kl.1, kl.2] }, [(kl.1, O)], [kl], p3 kl.1 kl.2⟩]
  | .diffZ k l =>
    ⟨.D0 true k l, { num := 1 }, [(k, l)], [], []⟩ ::
      ((others k).map (fun j => ⟨.D1 true k j, { num := -1, masses := [j] }, [(k, j)], [], p3 k j⟩) ++
       (others l).map fun j => ⟨.D2 true l j, { num := 1, masses := [j] }, [(l, j)], [], p3 l j⟩)
  | .diffW k l =>
    ⟨.D0 false k l, { num := 1 }, [], [(k, l)], []⟩ ::
      ((others k).map (fun j => ⟨.D1 false k j, { num := -1, masses := [j] }, [], [(k, j)], p3 k j⟩) ++
       (others l).map fun j => ⟨.D2 false l j, { num := 1, masses := [j] }, [], [(l, j)], p3 l j⟩)
  | .potVirial =>
    pairsAll.map (fun kl => ⟨.U kl.1 kl.2, { num := 1, masses := [kl.1, kl.2] }, [], [], [kl]⟩) ++
      (List.range 6).map fun k => ⟨.Ip k, { num := -1, masses := [k] }, [(k, O)], [(k, O)], []⟩
  | .virialE =>
    (List.range 6).map (fun k => ⟨.V0 k, { num := 1, masses := [k] }, [(k, O)], [(k, O)], []⟩) ++
      [⟨.E0, { num := -1, e := true }, [], [], []⟩]

/-- The factor by which the engine multiplied the identity: `m_k` for the equation of body `k`, else `1`
(as a list of masses). -/
def XId.scale : XId → List Nat
  | .bodyZ k | .bodyW k => [k]
  | _ => []

/-- The identity of an engine name (`none` for the rows `D_kl` and unknown names). -/
def XId.ofName : IdName → Option XId
  | .body true k => some (.bodyZ k)
  | .body false k => some (.bodyW k)
  | .U => some .potU
  | .I => some .lagr
  | .torque J => some (.torque J)
  | .virial J => some (.virial J)
  | .diff true k l => some (.diffZ k l)
  | .diff false k l => some (.diffW k l)
  | .subset true J => some (.subsetZ J)
  | .subset false J => some (.subsetW J)
  | .Ip => some .virialE
  | .UI => some .potVirial
  | .dist _ _ => none

/-- A factor `z_p − z_q`: a body `p` and the centre of mass, or two distinct bodies. -/
def goodSep (pq : Nat × Nat) : Bool := pq.1 < 6 && (pq.2 == O || (pq.2 < 6 && pq.1 != pq.2))

/-- A factor `p_kl`: two distinct bodies. -/
def goodP (kl : Nat × Nat) : Bool := kl.1 < 6 && kl.2 < 6 && kl.1 != kl.2

/-- The factors of a term are of these forms, and its coefficient has denominator `1` or `2` dividing twice its
numerator and masses `< 6`. -/
def XTerm.good (t : XTerm) : Bool :=
  t.zs.all goodSep && t.ws.all goodSep && t.ps.all goodP && (t.coef.den == 1 || t.coef.den == 2) &&
    (2 * t.coef.num) % t.coef.den == 0 && t.coef.masses.all (· < 6)

/-- A valid identity whose terms are good. -/
def XId.good (I : XId) : Bool := I.valid && I.terms.all XTerm.good && I.scale.all (· < 6)

/-- The position of the term with label `l`. -/
def findLabX (ts : List XTerm) (l : Lab) : Option Nat := ts.findIdx? (·.lab == l)

end L6.F34S
