import Mathlib
import L6F34S.Check
import L6Sound.F2S.Defs
import L6Sound.Poly.Sound

/-!
# F3, F4 on the cells of the specification search: semantic definitions

The objects of the meaning of the exclusions (Lemmas 5.1, 5.2) at a pair of complete trees with heights `(Xz, Xw)`:

* `texp Xz Xw t`: the exponent of a term (`L6F34S.Ids`), the sum of the exponents of its factors: `e(z_p − z_q)` the
  height of the lowest common ancestor (`⊤` if `p`, `q` share a leaf), `e(p_kl) = −x_kl`;
* `IsArgminX ts Xz Xw S`: `S` is the argmin set of the terms `ts` (the form of `Identity.IsArgmin` of the full
  formalization); with `S = [i]` the hypothesis of Lemma 5.1;
* `lcVal`, `termVal2`, `itemVal`: the values of the leading coefficients (Lemma 4.2) and of the initial forms of §5 at
  given node coordinates `X`, `Y` (a value for each node and child, both given as sets of points), `P_kl`, `E` and
  masses, in any commutative ring; `itemVal` is twice the initial form times the engine's factor of the identity, or
  the polynomial `P_kl² lc(z_kl) lc(w_kl) − 1` of a row;
* `phiOf vars …`: the point at which a certificate is evaluated: the masses, and for each variable of the link the
  difference of the node coordinates of its child and of its base child, `P_kl` or `E`;
* `ClaimMeaning Xz Xw`: a single-term identity, or a core: items holding at `(Xz, Xw)` and a certificate with
  `CertMeaning` whose generators are the values of the items at `phiOf` (up to the factor `1` or `2`).
-/

namespace L6.F34S

open L6.F2S (ExpTree TS xkl Cond argminString)

/-- A tree with its nodes in increasing order (the tree of the key of `T`). -/
def canon (T : TS) : TS := ⟨T.key.1, T.key.2⟩

/-! ## Exponents -/

/-- The exponent of a factor `z_p − z_q` at a tree with heights: the height of the lowest common ancestor, `⊤` if `p`
and `q` share a leaf. -/
noncomputable def sepExp (X : ExpTree) (pq : Nat × Nat) : WithTop ℚ :=
  if X.T.sameLeaf pq.1 pq.2 then ⊤ else ((X.e pq.1 pq.2 : ℚ) : WithTop ℚ)

/-- The exponent of a term at a pair of trees with heights, with `e(p_kl) = −x_kl`. -/
noncomputable def texp (Xz Xw : ExpTree) (t : XTerm) : WithTop ℚ :=
  (t.zs.map (sepExp Xz)).sum + (t.ws.map (sepExp Xw)).sum +
    (((t.ps.map fun kl => -xkl Xz Xw kl.1 kl.2).sum : ℚ) : WithTop ℚ)

/-- `S` is the argmin set of the terms `ts` at `(Xz, Xw)`: a nonempty set of positions whose terms have one finite
exponent `e`, all other terms having larger exponents. -/
def IsArgminX (ts : List XTerm) (Xz Xw : ExpTree) (S : List Nat) : Prop :=
  S ≠ [] ∧ (∀ i ∈ S, i < ts.length) ∧ ∃ e : ℚ, (∀ i ∈ S, texp Xz Xw ts[i]! = e) ∧
    ∀ i < ts.length, i ∉ S → (e : WithTop ℚ) < texp Xz Xw ts[i]!

/-! ## Values of initial forms -/

section Values

variable {R : Type*} [CommRing R]

/-- The value of `lc(z_p − z_q)` at the node coordinates `X`: `X(v, c(p)) − X(v, c(q))`, with `v` the lowest common
ancestor of `p`, `q` in `T` and `c(p)` its child containing `p`. -/
def lcVal (T : TS) (X : Nat → Nat → R) (pq : Nat × Nat) : R :=
  match T.lca pq.1 pq.2 with
  | some v => X v (childOf T v pq.1) - X v (childOf T v pq.2)
  | none => 0

/-- Twice the value of a coefficient at the masses `m` and the energy `E`. -/
def coefVal2 (c : XCoef) (m : Nat → R) (E : R) : R :=
  ((2 * c.num / c.den : Int) : R) * (c.masses.map m).prod *
    (if c.msum then ((List.range 6).map m).sum else 1) * (if c.e then E else 1)

/-- Twice the value of the leading coefficient of a term (Lemma 4.2). -/
def termVal2 (Tz Tw : TS) (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) (t : XTerm) : R :=
  coefVal2 t.coef m E * ((t.zs.map (lcVal Tz X)).prod * (t.ws.map (lcVal Tw Y)).prod *
    (t.ps.map fun kl => P (min kl.1 kl.2) (max kl.1 kl.2)).prod)

end Values

/-- A member of an initial system: the initial form of an identity with an argmin set, or the row
`D_kl² z_kl w_kl − 1`. -/
inductive ItemX where
  | init (I : XId) (S : List Nat)
  | dist (k l : Nat)
  deriving Inhabited

section Values2

variable {R : Type*} [CommRing R]

/-- Twice the value of the initial form of an item times the engine's factor of its identity; for a row, the value of
`P_kl² lc(z_kl) lc(w_kl) − 1`. -/
def itemVal (Tz Tw : TS) (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) : ItemX → R
  | .init I S => (I.scale.map m).prod * (S.map fun i => termVal2 Tz Tw X Y P E m I.terms[i]!).sum
  | .dist k l => P k l ^ 2 * lcVal Tz X (k, l) * lcVal Tw Y (k, l) - 1

/-- The point of the variables of a certificate. -/
def phiOf (vars : Array VarM) (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) (i : Nat) : R :=
  if i < 6 then m i else
  match vars[i - 6]? with
  | some (.X v c c0) => X v c - X v c0
  | some (.Y v c c0) => Y v c - Y v c0
  | some (.D k l) => P k l
  | some .E => E
  | _ => 0

end Values2

/-- The item holds at `(Xz, Xw)`: a good identity with its argmin set, or a pair of distinct bodies. -/
def ItemX.Holds (Xz Xw : ExpTree) : ItemX → Prop
  | .init I S => I.good = true ∧ IsArgminX I.terms Xz Xw S
  | .dist k l => k < l ∧ l < 6

/-- **The meaning of the claim of a cell** at a pair `(Xz, Xw)` that lies in it: a single-term identity (the
hypothesis of Lemma 5.1), or a core: a certificate with `CertMeaning` (fixing no mass, or the mass `F < 6`) each of
whose generators, at the point `phiOf vars X Y P E m` (with `m_F = 1` when the mass `F` is fixed), is the value of
an item holding at `(Xz, Xw)` (times `1` or `2`), for all node coordinates `X`, `Y`, `P`, `E` and masses in every
commutative ring (the hypothesis of Lemma 5.2, with explicit cofactors). -/
def ClaimMeaning (Xz Xw : ExpTree) : Prop :=
  (∃ I : XId, I.good = true ∧ ∃ i, IsArgminX I.terms Xz Xw [i]) ∨
  (∃ (c : L6.Poly.Cert) (vars : Array VarM),
    L6.Poly.CertMeaning c ∧ c.fixed < 6 ∧ vars.size = c.nvar ∧
    ∀ j < c.gens.length, ∃ it : ItemX, it.Holds Xz Xw ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P : Nat → Nat → R) (E : R) (m : Nat → R),
        (0 ≤ c.fixed → m c.fixed.toNat = 1) →
        (s : R) * L6.Poly.eval (6 + c.nvar) (phiOf vars X Y P E m) c.gens[j]! =
          itemVal Xz.T Xw.T X Y P E m it)

/-- The classes of the 43 open cells (diagrams 89, 64, 88, 93, 98, 66, 94). -/
def openClasses : List Nat := [31, 124, 127, 132, 133, 143, 147]

end L6.F34S
