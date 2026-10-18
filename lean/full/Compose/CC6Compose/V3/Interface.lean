import CC6Compose.ClaimCore
import CC6Compose.OpenCore
import CC6Compose.CellsCore

/-!
# The kernel-only composition: the statements consumed from the certificate projects

The string-free statements on which the kernel-only proof of Theorem 1.1 rests (`FULL_PLAN.md` §14–15). They refer
to a class list `L` given as data (for the checks, a literal such as `classes6Lit`), not to the reading of `n6.json`:

* `F1Cover L` (Proposition 3.1, the parts used): `L` has 191 classes, and every labelled diagram satisfying the
  rules lies in the orbit of a representative.
* `FusedExclusion L` (Propositions 4.5 and 5.3): for each class `k < 191` there is a finite list of certificates
  such that every pair of exponent trees with heights satisfying the conditions of Lemma 4.3 for the diagram of
  class `k` either lies in a class with open cells or carries a claim (`ClaimMeaningIn`): a single-term identity
  (Lemma 5.1) or a core with a certificate from the list (Lemma 5.2).
* `OpenCheck L`: the representatives of the classes with open cells have diagrams of Table 1.

`ClaimMeaningIn` is `L6.F34S.ClaimMeaning` with the certificate drawn from a list and the items `ItemOK` (the argmin
list of an initial form without repetition), which Lemma 5.2 needs.
-/

namespace CC6Compose.V3

open CC6Full
open L6.F2S (ExpTree Cond)
open L6.F34S (XId ItemX VarM IsArgminX itemVal phiOf openClasses)

/-- The diagram of class `k` of a class list. -/
def diagOfL (L : List (L6F1.Diagram × ℕ)) (k : ℕ) : L6.F2.Diag :=
  L6.F2.Diag.ofF1 (L.getD k (default, 0)).1

/-- **The claim of a pair** `(Xz, Xw)` with the certificate of a core drawn from `cs`: a good identity with a term
of strictly least exponent (Lemma 5.1), or a certificate from `cs` with `CertMeaning` each of whose generators is, at
the point `phiOf vars X Y P E m` (`m_F = 1` when the mass `F` is fixed), `1` or `2` times the value of an item of
the initial system at `(Xz, Xw)` (Lemma 5.2). -/
def ClaimMeaningIn (cs : List L6.Poly.Cert) (Xz Xw : ExpTree) : Prop :=
  (∃ I : XId, I.good = true ∧ ∃ i, IsArgminX I.terms Xz Xw [i]) ∨
  (∃ c ∈ cs, ∃ vars : Array VarM, L6.Poly.CertMeaning c ∧ c.fixed < 6 ∧ vars.size = c.nvar ∧
    ∀ j < c.gens.length, ∃ it : ItemX, ItemOK Xz Xw it ∧ ∃ s : ℕ, (s = 1 ∨ s = 2) ∧
      ∀ {R : Type} [CommRing R] (X Y P : ℕ → ℕ → R) (E : R) (m : ℕ → R),
        (0 ≤ c.fixed → m c.fixed.toNat = 1) →
        (s : R) * L6.Poly.eval (6 + c.nvar) (phiOf vars X Y P E m) c.gens[j]! = itemVal Xz.T Xw.T X Y P E m it)

/-- **Proposition 3.1 for a class list** (the parts the composition uses). -/
def F1Cover (L : List (L6F1.Diagram × ℕ)) : Prop :=
  L.length = 191 ∧ ∀ d ∈ L6F1.allDiagrams 6, L6F1.okRules 6 d = true → ∃ x ∈ L, d ∈ L6F1.orbit 6 x.1

/-- **Propositions 4.5 and 5.3 for a class list**, with finitely many certificates per class. -/
def FusedExclusion (L : List (L6F1.Diagram × ℕ)) : Prop :=
  ∀ k < 191, ∃ cs : List L6.Poly.Cert, ∀ Xz Xw : ExpTree, Cond (diagOfL L k) Xz Xw →
    k ∈ openClasses ∨ ClaimMeaningIn cs Xz Xw

/-- **The classes with open cells are diagrams of Table 1**, as a check on the class list. -/
def OpenCheck (L : List (L6F1.Diagram × ℕ)) : Prop :=
  ∀ k ∈ openClasses, ∃ D ∈ specials, diagBEq (toDiagram (L.getD k (default, 0)).1) D = true

/-- `OpenCheck` for the literal class list, by kernel evaluation. -/
theorem openCheck_lit : OpenCheck classes6Lit := open_specials_lit

end CC6Compose.V3
