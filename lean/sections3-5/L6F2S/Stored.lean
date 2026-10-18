import Lean.Data.Json
import Std.Data.HashSet
import L6F2S.Search

/-!
# The stored cells as keys

A stored line of `data/cells/c<N>.jsonl` (the engine's output) is read into the key of `SCell.key`: its two trees as
families of point sets (each internal node as the set of the points below it) with the body on the leaf of `O`, and
the argmin part of the line (the text between `"argmin": [` and `], "x": `). `checkBelow` tests that every cell of the
specification below some pairs of partial trees has the key of a stored cell.
-/

namespace L6.F2S

open Lean

/-- The text between the first occurrence of `a` and the next occurrence of `b` after it. -/
def between (s a b : String) : Option String :=
  match s.splitOn a with
  | _ :: rest =>
    match (a.intercalate rest).splitOn b with
    | x :: _ :: _ => some x
    | _ => none
  | _ => none

/-- The (key, value) pairs of a JSON object. -/
def jPairs? (j : Json) : Option (List (String × Json)) :=
  match j with
  | .obj kvs => some (kvs.toList.map fun (k, v) => (k, v))
  | _ => none

/-- The masks of the internal nodes of a tree given by its children (internal node `v ↦` children), its leaf map
(point `↦` leaf node) and its root: the set of points below each internal node (`fuel` bounds the depth). -/
def nodeMask (children : List (Nat × List Nat)) (leaf : List (Nat × Nat)) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, v =>
    match children.lookup v with
    | some cs => cs.foldl (fun acc c => acc ||| nodeMask children leaf fuel c) 0
    | none => leaf.foldl (fun acc pl => if pl.2 == v then acc ||| single pl.1 else acc) 0

/-- A tree of a stored line (`{"children": {...}, "leaf": {...}, "root": r}`) as a `TS`. -/
def tsOfJson (j : Json) : Option TS := do
  let ch ← (j.getObjVal? "children").toOption
  let lf ← (j.getObjVal? "leaf").toOption
  let chs ← jPairs? ch
  let lfs ← jPairs? lf
  let children ← chs.mapM fun (k, v) => do
    let kv ← k.toNat?
    let arr ← (v.getArr?).toOption
    let cs ← arr.toList.mapM fun x => (x.getNat?).toOption
    some (kv, cs)
  let leaf ← lfs.mapM fun (k, v) => do
    let kv ← k.toNat?
    let lv ← (v.getNat?).toOption
    some (kv, lv)
  let nodes := children.map fun (v, _) => nodeMask children leaf 16 v
  let leafO := (leaf.find? fun (p, l) => p != O && l == O).map (·.1)
  some ⟨nodes, leafO⟩

/-- The key of a stored line. -/
def keyOfLine (line : String) :
    Option ((List Nat × Option Nat) × (List Nat × Option Nat) × String) := do
  let zt ← between line "\"ztree\": " ", \"wtree\": "
  let wt ← between line "\"wtree\": " ", \"argmin\": ["
  let am ← between line "\"argmin\": [" "], \"x\": "
  let zj ← (Json.parse zt).toOption
  let wj ← (Json.parse wt).toOption
  let tz ← tsOfJson zj
  let tw ← tsOfJson wj
  some (tz.key, tw.key, am)

/-- The keys of the stored lines of a class (`none` if a line does not parse). -/
def storedKeys (text : String) : Option (List ((List Nat × Option Nat) × (List Nat × Option Nat) × String)) :=
  ((text.splitOn "\n").filter (· != "")).mapM keyOfLine

/-- Every cell of the specification below the pairs `xs` (after the first `d` insertions) has the key of a stored
line. -/
def checkBelow (keep : Array Row → Nat → Bool) (D : L6.F2.Diag) (d : Nat) (text : String)
    (xs : List (Nat × TS × TS)) : Bool :=
  match storedKeys text with
  | none => false
  | some ks =>
    let set : Std.HashSet ((List Nat × Option Nat) × (List Nat × Option Nat) × String) := Std.HashSet.ofList ks
    xs.all fun x => (below keep D d x).all fun c => set.contains c.key

end L6.F2S
