import Lean
import L6KSpec.E4
import Lean6.Special.Comp.K4.E4.Run

/-!
# The selection and the inverse of a Macaulay block, computed at elaboration (untrusted)

`e4_data N F [μ₁, μ₂, μ₃, μ₄] i` (or `G` for the forms `G_σ`) runs lean6_special's own untrusted code
(`selectRows`, `inverseMod` of `Comp.K4.E4.Mac`) for the pattern `i` (`patsF.getD i []`, `patsG.getD i []`) at the
masses `μ`, modulo `pE = 2147483629` with `sE = 2·882503254 + 1` (`Comp.K4.E4.Run`), and defines `N.sel : List Nat`
and `N.B : List (List Nat)` as literals (built as terms, without elaboration). Nothing here is trusted: the kernel
checks `macCheckK` on these values, and a wrong selection or inverse makes that check fail.
-/

open Lean Elab Command
open Lean6.Special.Comp Lean6.Special.Comp.E4

namespace L6KSpec.E4

private def natListE (xs : List Nat) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) (mkRawNatLit x) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))

private def natListT : Expr := mkApp (mkConst ``List [0]) (mkConst ``Nat)

private def natListListE (xss : List (List Nat)) : Expr :=
  xss.foldr (fun xs acc => mkApp3 (mkConst ``List.cons [0]) natListT (natListE xs) acc)
    (mkApp (mkConst ``List.nil [0]) natListT)

/-- The selection and the inverse for the forms `fs` in `n` variables in degree `D` (lean6_special's code). -/
def selInv (n D : Nat) (fs : List (Poly ZJ × Nat)) : List Nat × List (List Nat) :=
  let ms := monos n D
  let m := ms.length
  let A := (macRows n D fs).map (coeffVec ms)
  let Ap := modMat pE sE A
  let sel := selectRows pE m Ap
  let B := inverseMod pE m (sel.map fun r => Ap.getD r #[])
  (sel.toList, (B.map (·.toList)).toList)

syntax "e4_data " ident ident "[" num,* "]" num : command

elab_rules : command
  | `(e4_data $name $fam [$mus,*] $idx) => do
    let μ : List Int := mus.getElems.toList.map fun n => (n.getNat : Int)
    let i := idx.getNat
    let (sel, B) ← match fam.getId with
      | `F => pure (selInv 4 7 (formsF μ (patsF.getD i [])))
      | `G => pure (selInv 3 8 (formsG μ (patsG.getD i [])))
      | _ => throwError "e4_data: family F or G"
    let ns := (← getCurrNamespace) ++ name.getId
    liftCoreM <| addDecl <| Declaration.defnDecl {
      name := ns ++ `sel, levelParams := [], type := natListT, value := natListE sel, hints := .abbrev,
      safety := .safe }
    liftCoreM <| addDecl <| Declaration.defnDecl {
      name := ns ++ `B, levelParams := [], type := mkApp (mkConst ``List [0]) natListT, value := natListListE B,
      hints := .abbrev, safety := .safe }

end L6KSpec.E4
