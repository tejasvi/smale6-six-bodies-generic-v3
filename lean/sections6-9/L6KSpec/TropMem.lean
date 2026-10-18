import L6KSpec.TropNorm
import Lean6.Special.Comp.D88.Trop.Sys

/-!
# Lemma 6.19(a)(i) for the kernel: the systems with `normalizeK`, and the membership check

`Lean6.Special.Comp.D88.Trop.Sys` builds the systems `S12`, `KC12`, the coordinates `ξ(v)` and the relation
`μ_u i_u − 1` with `Poly.normalize` after each operation, and `checkMem` tests the identities with `Poly.isZero`; the
kernel unfolds neither. Here the same constructions with `normalizeK` (`paK`, `psK`, `pmK`, `psumK`, `powK`, `eqnK`,
`DK`; `n4FK`, `n4σK`, `n4relK`, `kcFK`, `kcσK`, `kcrelK`), the substitution `substK`, and `checkMemK`, which is
`checkMem` with `substK` and `isZeroK`. `L6SoundKSpec.TropMem` proves that the values agree with those of lean6_special
and that `checkMemK` gives the identities of `mem_sound`.
-/

namespace L6KSpec.Trop

open Lean6.Special.Comp Lean6.Special.Comp.D88.Trop

noncomputable section

variable {α : Type}

/-- `Poly.pow` with `normalizeK`. -/
def powK (C : Coeff α) (p : Poly α) : Nat → Poly α
  | 0 => Poly.const C.one
  | n + 1 => normalizeK C (Poly.mul C (powK C p n) p)

/-- `Poly.substMono` with `normalizeK`. -/
def substMonoK (C : Coeff α) (σ : Nat → Poly α) : Mono → Nat → Poly α
  | [], _ => Poly.const C.one
  | e :: m, i => normalizeK C (Poly.mul C (powK C (σ i) e) (substMonoK C σ m (i + 1)))

/-- `Poly.subst` with `normalizeK`. -/
def substK (C : Coeff α) (σ : Nat → Poly α) (p : Poly α) : Poly α :=
  normalizeK C (p.flatMap fun t => Poly.mul C (Poly.const t.1) (substMonoK C σ t.2 0))

/-- `pa` with `normalizeK`. -/
def paK (a b : Poly Int) : Poly Int := normalizeK intC (Poly.add a b)
/-- `ps` with `normalizeK`. -/
def psK (a b : Poly Int) : Poly Int := normalizeK intC (Poly.sub intC a b)
/-- `pm` with `normalizeK`. -/
def pmK (a b : Poly Int) : Poly Int := normalizeK intC (Poly.mul intC a b)
/-- `psum` with `normalizeK`. -/
def psumK (l : List (Poly Int)) : Poly Int := normalizeK intC (Poly.sum l)

/-- `Bodies.eqn` with `normalizeK`. -/
def eqnK (B : Bodies) (Z : Nat → Poly Int) (k : Nat) : Poly Int :=
  psK (Z k) (psumK (([1, 2, 3, 4].filter (· ≠ k)).map fun l =>
    pmK (pmK (B.mu l) (powK intC (B.P k l) 3)) (psK (Z k) (Z l))))

/-- `Bodies.D` with `normalizeK`. -/
def DK (B : Bodies) (k l : Nat) : Poly Int :=
  psK (pmK (pmK (powK intC (B.P k l) 2) (psK (B.X k) (B.X l))) (psK (B.Y k) (B.Y l))) (K 1)

/-! ## N4 -/

/-- `n4Bodies` with `normalizeK`. -/
def n4BodiesK : Bodies where
  X := fun k => match k with
    | 1 => paK (V 0) (K 1)
    | 2 => V 0
    | 3 => V 1
    | _ => pmK (K (-1)) (pmK (psumK [pmK (V 11) (paK (V 0) (K 1)), pmK (V 12) (V 0), pmK (V 13) (V 1)]) (V 15))
  Y := fun k => match k with
    | 1 => V 2
    | 2 => V 3
    | 3 => V 4
    | _ => pmK (K (-1)) (pmK (psumK [pmK (V 11) (V 2), pmK (V 12) (V 3), pmK (V 13) (V 4)]) (V 15))
  p0 := 5
  mu0 := 11

/-- `n4F` with `normalizeK`. -/
def n4FK : List (Poly Int) :=
  [eqnK n4BodiesK n4BodiesK.X 1, eqnK n4BodiesK n4BodiesK.X 2, eqnK n4BodiesK n4BodiesK.X 3,
    eqnK n4BodiesK n4BodiesK.Y 1, eqnK n4BodiesK n4BodiesK.Y 2, eqnK n4BodiesK n4BodiesK.Y 3] ++
    pairs.map fun kl => DK n4BodiesK kl.1 kl.2

/-- `n4σ` with `normalizeK`. -/
def n4σK (i : Nat) : Poly Int :=
  let X := n4BodiesK.X
  let Y := n4BodiesK.Y
  match i with
  | 0 => psK (X 1) (X 3)
  | 1 => psK (X 1) (X 4)
  | 2 => psK (X 2) (X 3)
  | 3 => psK (X 2) (X 4)
  | 4 => psK (X 3) (X 4)
  | 5 => psK (Y 1) (Y 2)
  | 6 => psK (Y 1) (Y 3)
  | 7 => psK (Y 1) (Y 4)
  | 8 => psK (Y 2) (Y 3)
  | 9 => psK (Y 2) (Y 4)
  | 10 => psK (Y 3) (Y 4)
  | i => if i < 17 then V (i - 6) else V (i - 6)

/-- `n4rel` with `normalizeK`. -/
def n4relK : Poly Int := psK (pmK (V 14) (V 15)) (K 1)

/-! ## KC -/

/-- `kcBodies` with `normalizeK`. -/
def kcBodiesK : Bodies where
  X := fun k => match k with
    | 1 => K 1
    | 2 => V 0
    | 3 => V 1
    | _ => K 0
  Y := fun k => match k with
    | 1 => V 2
    | 2 => V 3
    | 3 => V 4
    | _ => V 5
  p0 := 6
  mu0 := 12

/-- `kcF` with `normalizeK`. -/
def kcFK : List (Poly Int) :=
  [eqnK kcBodiesK kcBodiesK.X 1, eqnK kcBodiesK kcBodiesK.X 2, eqnK kcBodiesK kcBodiesK.X 3,
    eqnK kcBodiesK kcBodiesK.X 4, eqnK kcBodiesK kcBodiesK.Y 1, eqnK kcBodiesK kcBodiesK.Y 2] ++
    pairs.map fun kl => DK kcBodiesK kl.1 kl.2

/-- `kcσ` with `normalizeK`. -/
def kcσK (i : Nat) : Poly Int :=
  let X := kcBodiesK.X
  let Y := kcBodiesK.Y
  match i with
  | 0 => V 0
  | 1 => V 1
  | 2 => psK (X 1) (X 2)
  | 3 => psK (X 1) (X 3)
  | 4 => psK (X 2) (X 3)
  | 5 => psK (Y 1) (Y 4)
  | 6 => psK (Y 2) (Y 4)
  | 7 => psK (Y 3) (Y 4)
  | 8 => psK (Y 1) (Y 2)
  | 9 => psK (Y 1) (Y 3)
  | 10 => psK (Y 2) (Y 3)
  | i => V (i - 5)

/-- `kcrel` with `normalizeK`. -/
def kcrelK : Poly Int := psK (pmK (V 14) (V 16)) (K 1)

/-! ## The membership check -/

/-- `memOK` with `substK` and `isZeroK`. -/
def memOKK (σ : Nat → Poly Int) (F : List (Poly Int)) (rel : Poly Int) (g : GPoly) (cof : List (Poly Int))
    (c0 : Poly Int) : Bool :=
  isZeroK intC
    (Poly.sub intC (substK intC σ (flat g))
      (Poly.add (Poly.sum ((cof.zip F).map fun cf => Poly.mul intC cf.1 cf.2)) (Poly.mul intC c0 rel)))

/-- `checkMem` with `memOKK`. -/
def checkMemK (σ : Nat → Poly Int) (F : List (Poly Int)) (rel : Poly Int) (G : List GPoly)
    (cofs : List (List (Poly Int))) (c0s : List (Poly Int)) : Bool :=
  G.length == cofs.length && G.length == c0s.length && cofs.all (fun c => c.length == F.length) &&
    ((G.zip (cofs.zip c0s)).all fun t => memOKK σ F rel t.1 t.2.1 t.2.2)

end

end L6KSpec.Trop
