import Lean
import L6K.Load
import L6K.F2S.Keep

/-!
# Loading a certificate table

`load_ctree T "file"` defines `T : CTree` from a text file of lines `C hash i:y i:y …` (one certificate per line,
sorted by hash; several lines may share a hash): the balanced binary search tree on the hashes, built directly as a
term (no elaboration of a literal), with the certificates of each hash in the order of the file.
-/

open Lean Elab Command

namespace L6K.F2S

private def natE (n : Nat) : Expr := mkRawNatLit n

private def intE (z : Int) : Expr :=
  match z with
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (natE n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (natE n)

private def listE (t : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) t x acc) (mkApp (mkConst ``List.nil [0]) t)

private def pairT : Expr := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) (mkConst ``Int)

private def certE (c : Array (Nat × Int)) : Expr :=
  listE pairT (c.map fun (i, y) => mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Int) (natE i) (intE y))

private def certsT : Expr := mkApp (mkConst ``List [0]) (mkApp (mkConst ``List [0]) pairT)

/-- The balanced tree of the entries `es[lo:hi]` (sorted by hash). -/
private partial def treeE (es : Array (Nat × Array (Array (Nat × Int)))) (lo hi : Nat) : Expr :=
  if hi ≤ lo then mkConst ``CTree.leaf
  else
    let m := (lo + hi) / 2
    let (k, cs) := es[m]!
    mkApp4 (mkConst ``CTree.node) (treeE es lo m) (natE k) (listE (mkApp (mkConst ``List [0]) pairT) (cs.map certE))
      (treeE es (m + 1) hi)

elab "load_ctree " id:ident path:str : command => do
  let lines ← IO.FS.lines (← L6K.dataPath path.getString)
  let mut es : Array (Nat × Array (Array (Nat × Int))) := #[]
  for line in lines do
    let ws := (line.splitOn " ").filter (· ≠ "")
    match ws with
    | "C" :: h :: rest =>
      let k := h.toNat!
      let cert : Array (Nat × Int) := rest.toArray.map fun w =>
        match w.splitOn ":" with
        | [i, y] => (i.toNat!, y.toInt!)
        | _ => (0, 0)
      if es.size > 0 && es[es.size - 1]!.1 == k then
        es := es.modify (es.size - 1) fun e => (e.1, e.2.push cert)
      else
        if es.size > 0 && es[es.size - 1]!.1 > k then throwError "load_ctree: hashes not sorted"
        es := es.push (k, #[cert])
    | [] => pure ()
    | _ => throwError "load_ctree: bad line {line}"
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addDecl <| Declaration.defnDecl {
    name, levelParams := [], type := mkConst ``CTree, value := treeE es 0 es.size,
    hints := .abbrev, safety := .safe }

end L6K.F2S
