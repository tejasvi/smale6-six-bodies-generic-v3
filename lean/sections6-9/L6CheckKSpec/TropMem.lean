import L6SoundKSpec.TropMem
import Lean6.Special.Comp.D88.Trop.LitN4
import Lean6.Special.Comp.D88.Trop.LitKC

/-!
# Lemma 6.19(a)(i) in the kernel

`Lean6.Special.D88.TropK.n4_G_mem` and `kc_G_mem` have the statements of lean6_special's `n4_G_mem`, `kc_G_mem`
(checked in `L6CheckKSpec.TropSame`): every polynomial of `G` lies in the ideal of the system, with the cofactors
`cofN4`, `cofKC` of lean6_special, at every point of every commutative ring at which `μ_u i_u = 1`. The identities are
checked by the kernel (`checkMemK`, with the systems written with `normalizeK`), in place of `native_decide` on
`checkMem`; `mem_soundK` and the equality of the values of the systems (`eval_n4FK`, `eval_n4σK`, `eval_n4relK`, …)
give the statements. The cofactors are the literals of `LitN4`, `LitKC`.
-/

namespace Lean6.Special.D88.TropK

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.D88.Trop L6KSpec.Trop

theorem n4_mem_okK : checkMemK n4σK n4FK n4relK GN4 cofN4 c0N4 = true := by decide +kernel

theorem kc_mem_okK : checkMemK kcσK kcFK kcrelK GKC cofKC c0KC = true := by decide +kernel

/-- **(i) for `S12`**, by the kernel. -/
theorem n4_G_mem (i : ℕ) (hi : i < GN4.length) {R : Type*} [CommRing R] (x : ℕ → R) (hu : x 14 * x 15 = 1) :
    Poly.eval (intHom R) (fun j => Poly.eval (intHom R) x (n4σ j)) (flat GN4[i]) =
      (((cofN4.getD i []).zip n4F).map fun cf =>
        Poly.eval (intHom R) x cf.1 * Poly.eval (intHom R) x cf.2).sum := by
  have hrel : Poly.eval (intHom R) x n4relK = 0 := by
    rw [eval_n4relK]
    simp [n4rel, ps, pm, V, K, Poly.eval_normalize, Poly.eval_sub, Poly.eval_mul, Poly.eval_var, Poly.eval_const, hu,
      intHom]
  have hσ : (fun j => Poly.eval (intHom R) x (n4σ j)) = fun j => Poly.eval (intHom R) x (n4σK j) :=
    funext fun j => (eval_n4σK x j).symm
  rw [hσ, mem_soundK n4_mem_okK hi x hrel]
  exact congrArg List.sum (zip_map_eq _ _ _ _ _ (eval_n4FK x))

/-- **(i) for `KC12`**, by the kernel. -/
theorem kc_G_mem (i : ℕ) (hi : i < GKC.length) {R : Type*} [CommRing R] (x : ℕ → R) (hu : x 14 * x 16 = 1) :
    Poly.eval (intHom R) (fun j => Poly.eval (intHom R) x (kcσ j)) (flat GKC[i]) =
      (((cofKC.getD i []).zip kcF).map fun cf =>
        Poly.eval (intHom R) x cf.1 * Poly.eval (intHom R) x cf.2).sum := by
  have hrel : Poly.eval (intHom R) x kcrelK = 0 := by
    rw [eval_kcrelK]
    simp [kcrel, ps, pm, V, K, Poly.eval_normalize, Poly.eval_sub, Poly.eval_mul, Poly.eval_var, Poly.eval_const, hu,
      intHom]
  have hσ : (fun j => Poly.eval (intHom R) x (kcσ j)) = fun j => Poly.eval (intHom R) x (kcσK j) :=
    funext fun j => (eval_kcσK x j).symm
  rw [hσ, mem_soundK kc_mem_okK hi x hrel]
  exact congrArg List.sum (zip_map_eq _ _ _ _ _ (eval_kcFK x))

end Lean6.Special.D88.TropK
