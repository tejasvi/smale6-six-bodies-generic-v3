import Lean6.Special.Comp
import Lean6.Special.Poly.Sem
import Lean6.Special.Hand
import Lean6.Special.D98
import Lean6.Special.Comp.D98
import Lean6.Special.D88.Boxes
import Lean6.Special.D88.Trop
import Lean6.Special.D88.Count
import Lean6.Special.K4.E4
import Lean6.Special.K4.C4

/-!
# Lean checks of the computations of Sections 6–9

Of the paper "Smale's sixth problem for six bodies in the plane: finiteness of central configurations for generic
masses". See `LEAN_CHECKS.md` for the list of the claims, the theorems that check them and the claims not checked.

* `Lean6.Special.Hand`: the algebra and the finite computations inside the hand proofs of Sections 2–9.
* `Lean6.Special.D98`: Lemma 6.9, Lemma 6.13 (and its check at `(1, 2, 7)`), Theorem 6.15 (`P93(1, 2, 7) ≠ 0`).
* `Lean6.Special.D88.Trop`: Lemma 6.19(a), also for weights in any ordered abelian group.
* `Lean6.Special.D88.Count`: Lemma 6.19(b), the dimension bounds 4788 (KC′) and 20,316 (S12).
* `Lean6.Special.D88.Boxes`: Lemma 6.19(c), (d) and the last paragraph of Section 6.7.
* `Lean6.Special.K4.E4`: Lemma 7.7, the check after Proposition 7.8 (with the determinants), Remark 7.14.
* `Lean6.Special.K4.C4`: Lemma 7.9 and the check at `(1, 1, 1, 1)` of Section 7.4.
-/
