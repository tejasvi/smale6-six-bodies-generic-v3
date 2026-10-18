import Lean.Data.Json

/-!
# F3, F4: the stored cells, the diagrams, and the names of identities and terms

The stored cells (`data/cells/c<N>.jsonl`, one JSON object per line, as written by the engine) give two trees and
the argmin sets of the base identities. A tree is read as its internal nodes with their children (in the stored
order, which fixes the node coordinates `X<v>_<i>`), the leaf of each point (`0, …, 5` the bodies, `6` the centre of
mass `O`; a body at `O` shares the leaf `6`), and the root. The class representatives are read from `n6.json`.

Names of identities and terms are the engine's tuples written without spaces and quotes, e.g. `(z,S,(0,))`, `(U,)`,
`(D,2,4)`, `(D,w,0,4)`, `(S,z,(3,4))`, `(T,(0,2,4))`, `(V,(2,))`, `(Ip,)`, `(UI,)` for identities and `(T1,0,5)`,
`(SC,w,3,1)`, `(E0,)` for terms; the JSON names `["z","S",[0]]`, `["pos",0]` are read into the same types.
-/

namespace L6.F34

open Lean (Json)

/-! ## Tuples -/

/-- A parsed tuple: an atom or a list. -/
inductive Tup where
  | atom (s : String)
  | list (xs : List Tup)
  deriving Inhabited, BEq, Repr

/-- Parses a tuple from position `i` of `cs`; returns the tuple and the next position (fuel bounds the depth). -/
partial def parseTupAt (cs : Array Char) (i : Nat) : Option (Tup × Nat) :=
  if h : i < cs.size then
    if cs[i] == '(' then
      let rec go (j : Nat) (acc : List Tup) : Option (Tup × Nat) :=
        if hj : j < cs.size then
          if cs[j] == ')' then some (.list acc.reverse, j + 1)
          else if cs[j] == ',' then go (j + 1) acc
          else match parseTupAt cs j with
            | some (t, k) => go k (t :: acc)
            | none => none
        else none
      go (i + 1) []
    else
      let rec atom (j : Nat) (acc : String) : Tup × Nat :=
        if hj : j < cs.size then
          let c := cs[j]
          if c == '(' || c == ')' || c == ',' then (.atom acc, j) else atom (j + 1) (acc.push c)
        else (.atom acc, j)
      let (t, k) := atom i ""
      if k == i then none else some (t, k)
  else none

/-- Parses a whole token as a tuple. -/
def parseTup (s : String) : Option Tup :=
  let cs := s.toList.toArray
  match parseTupAt cs 0 with
  | some (t, k) => if k == cs.size then some t else none
  | none => none

def Tup.nat? : Tup → Option Nat
  | .atom s => s.toNat?
  | _ => none

def Tup.natList? : Tup → Option (List Nat)
  | .list xs => xs.mapM Tup.nat?
  | _ => none

/-- The colour of an atom `z`/`w` (`true` = `z`). -/
def Tup.colour? : Tup → Option Bool
  | .atom "z" => some true
  | .atom "w" => some false
  | _ => none

/-! ## Identities and terms -/

/-- The identities of Sections 2.3 and 5.1 (`texact.identities`, the rows `D`, `tsec.secondary`). -/
inductive IdName where
  /-- equation of body `k` in a colour (`(z,S,(k,))`), a base identity -/
  | body (z : Bool) (k : Nat)
  /-- `U = E` (`(U,)`) and `Σ m m z w = M E` (`(I,)`), base identities -/
  | U | I
  /-- the row `D_kl² z_kl w_kl = 1` (`(D,k,l)`) -/
  | dist (k l : Nat)
  /-- torque `T_J` (`(T,J)`) -/
  | torque (J : List Nat)
  /-- partial virial (`(V,J)`) -/
  | virial (J : List Nat)
  /-- difference of two body equations (`(D,c,k,l)`) -/
  | diff (z : Bool) (k l : Nat)
  /-- subset sum, `2 ≤ |J| ≤ 4` (`(S,c,J)`) -/
  | subset (z : Bool) (J : List Nat)
  /-- `Σ m z w = E` (`(Ip,)`) and `U = Σ m z w` (`(UI,)`) -/
  | Ip | UI
  deriving Inhabited, DecidableEq, Repr

def IdName.ofTup : Tup → Option IdName
  | .list [c, .atom "S", .list [k]] => do let z ← c.colour?; let k ← k.nat?; some (.body z k)
  | .list [.atom "U"] => some .U
  | .list [.atom "I"] => some .I
  | .list [.atom "Ip"] => some .Ip
  | .list [.atom "UI"] => some .UI
  | .list [.atom "D", c, k, l] => do some (.diff (← c.colour?) (← k.nat?) (← l.nat?))
  | .list [.atom "D", k, l] => do let k ← k.nat?; let l ← l.nat?; some (.dist k l)
  | .list [.atom "T", J] => do let J ← J.natList?; some (.torque J)
  | .list [.atom "V", J] => do let J ← J.natList?; some (.virial J)
  | .list [.atom "S", c, J] => do let z ← c.colour?; let J ← J.natList?; some (.subset z J)
  | _ => none

def IdName.parse (s : String) : Option IdName := (parseTup s).bind IdName.ofTup

/-- Labels of the terms of the identities (`texact.identities`, `tsec.secondary`). -/
inductive Lab where
  | pos (i : Nat) | cross (i j : Nat) | delta (k l : Nat) | zw (k l : Nat) | E | zkwk (k : Nat)
  | T1 (k l : Nat) | T2 (k l : Nat) | V0 (k : Nat) | V1 (k l : Nat) | V2 (k l : Nat) | V3 (k l : Nat)
  | D0 (z : Bool) (a b : Nat) | D1 (z : Bool) (a b : Nat) | D2 (z : Bool) (a b : Nat)
  | SP (z : Bool) (i : Nat) | SC (z : Bool) (i j : Nat) | E0 | U (k l : Nat) | Ip (k : Nat)
  deriving Inhabited, DecidableEq, Repr

def Lab.ofTup : Tup → Option Lab
  | .list [.atom "T1", k, l] => do some (.T1 (← k.nat?) (← l.nat?))
  | .list [.atom "T2", k, l] => do some (.T2 (← k.nat?) (← l.nat?))
  | .list [.atom "V0", k] => do some (.V0 (← k.nat?))
  | .list [.atom "V1", k, l] => do some (.V1 (← k.nat?) (← l.nat?))
  | .list [.atom "V2", k, l] => do some (.V2 (← k.nat?) (← l.nat?))
  | .list [.atom "V3", k, l] => do some (.V3 (← k.nat?) (← l.nat?))
  | .list [.atom "D0", c, a, b] => do some (.D0 (← c.colour?) (← a.nat?) (← b.nat?))
  | .list [.atom "D1", c, a, b] => do some (.D1 (← c.colour?) (← a.nat?) (← b.nat?))
  | .list [.atom "D2", c, a, b] => do some (.D2 (← c.colour?) (← a.nat?) (← b.nat?))
  | .list [.atom "SP", c, i] => do some (.SP (← c.colour?) (← i.nat?))
  | .list [.atom "SC", c, i, j] => do some (.SC (← c.colour?) (← i.nat?) (← j.nat?))
  | .list [.atom "E0"] => some .E0
  | .list [.atom "U", k, l] => do some (.U (← k.nat?) (← l.nat?))
  | .list [.atom "Ip", k] => do some (.Ip (← k.nat?))
  | _ => none

def Lab.parse (s : String) : Option Lab := (parseTup s).bind Lab.ofTup

/-! ## JSON helpers -/

def jNat? (j : Json) : Option Nat := (j.getNat?).toOption

def jStr? (j : Json) : Option String := (j.getStr?).toOption

def jArr? (j : Json) : Option (Array Json) := (j.getArr?).toOption

def jField? (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

/-- The (key, value) pairs of a JSON object. -/
def jPairs? (j : Json) : Option (List (String × Json)) :=
  match j with
  | .obj kvs => some (kvs.toList.map fun (k, v) => (k, v))
  | _ => none

/-- A name of the stored argmin lists: `["z","S",[0]]`, `["U"]`, `["I"]`. -/
def IdName.ofJson (j : Json) : Option IdName := do
  let a ← jArr? j
  match a.toList with
  | [c, s, J] =>
    let c ← jStr? c
    let s ← jStr? s
    let J ← jArr? J
    if s != "S" then none
    let z ← (Tup.atom c).colour?
    match J.toList with
    | [k] => some (.body z (← jNat? k))
    | _ => none
  | [u] =>
    match ← jStr? u with
    | "U" => some .U
    | "I" => some .I
    | _ => none
  | _ => none

/-- A label of the stored argmin lists: `["pos",i]`, `["cross",i,j]`, `["delta",k,l]`, `["zw",k,l]`, `["E"]`,
`["zkwk",k]`. -/
def Lab.ofJson (j : Json) : Option Lab := do
  let a ← jArr? j
  match a.toList with
  | [t] => if (← jStr? t) == "E" then some .E else none
  | [t, i] =>
    match ← jStr? t with
    | "pos" => some (.pos (← jNat? i))
    | "zkwk" => some (.zkwk (← jNat? i))
    | _ => none
  | [t, i, k] =>
    match ← jStr? t with
    | "cross" => some (.cross (← jNat? i) (← jNat? k))
    | "delta" => some (.delta (← jNat? i) (← jNat? k))
    | "zw" => some (.zw (← jNat? i) (← jNat? k))
    | _ => none
  | _ => none

/-! ## Trees, diagrams, cells -/

/-- The number of bodies; the point `6` is the centre of mass `O`. -/
abbrev nB : Nat := 6

/-- Node ids are below this bound (leaves `0 … 6`, internal nodes from `7`). -/
abbrev maxNode : Nat := 64

/-- A tree: internal nodes with their children in the stored order, the leaf of each point, the root, and the parent
of each node (`maxNode` for none). -/
structure Tree where
  kids : Array (Nat × Array Nat)
  leaf : Array Nat
  root : Nat
  par : Array Nat
  deriving Inhabited, Repr

/-- Reads a stored tree `{"children": {...}, "leaf": {...}, "root": r}`. -/
def Tree.ofJson (j : Json) : Option Tree := do
  let ch ← jField? j "children"
  let lf ← jField? j "leaf"
  let root ← jNat? (← jField? j "root")
  let chs ← jPairs? ch
  let mut kids : Array (Nat × Array Nat) := #[]
  for (k, v) in chs do
    let node ← k.toNat?
    let cs ← jArr? v
    let cs ← cs.mapM jNat?
    kids := kids.push (node, cs)
  let lfs ← jPairs? lf
  let mut leaf : Array Nat := Array.replicate (nB + 1) maxNode
  for (k, v) in lfs do
    let p ← k.toNat?
    let l ← jNat? v
    if p > nB then none
    leaf := leaf.set! p l
  if leaf.any (· ≥ maxNode) then none
  if root ≥ maxNode then none
  let mut par : Array Nat := Array.replicate maxNode maxNode
  for (v, cs) in kids do
    if v ≥ maxNode then none
    for c in cs do
      if c ≥ maxNode then none
      par := par.set! c v
  some { kids, leaf, root, par }

/-- The children of an internal node (empty for a leaf). -/
def Tree.children (t : Tree) (v : Nat) : Array Nat :=
  match t.kids.find? (·.1 == v) with
  | some (_, cs) => cs
  | none => #[]

/-- The ancestors of a node, from the node to the root (at most `maxNode` steps). -/
def Tree.ancestors (t : Tree) (v : Nat) : List Nat := Id.run do
  let mut out := [v]
  let mut u := v
  for _ in [0:maxNode] do
    let p := t.par.getD u maxNode
    if p ≥ maxNode then break
    out := p :: out
    u := p
  return out.reverse

/-- The meet of the leaves of the points `p` and `q`, or `none` if they share a leaf. -/
def Tree.meet (t : Tree) (p q : Nat) : Option Nat :=
  let u := t.leaf.getD p maxNode
  let v := t.leaf.getD q maxNode
  if u == v then none
  else
    let au := t.ancestors u
    (t.ancestors v).find? (fun w => au.contains w)

/-- The index (in the stored order) of the child of `v` whose subtree contains the node `x`. -/
def Tree.childIdx (t : Tree) (v x : Nat) : Option Nat := Id.run do
  let mut u := x
  for _ in [0:maxNode] do
    let p := t.par.getD u maxNode
    if p == v then return (t.children v).idxOf? u
    if p ≥ maxNode then return none
    u := p
  return none

/-- A class representative: strokes and circles. -/
structure Diagram where
  zs : Array Bool   -- by pair index `pairIdx k l`
  ws : Array Bool
  zc : Array Bool
  wc : Array Bool
  deriving Inhabited

/-- Index of the pair `{k, l}` (`k ≠ l`) in a 6 × 6 table. -/
@[inline] def pairIdx (k l : Nat) : Nat := if k < l then 6 * k + l else 6 * l + k

def Diagram.zstroke (d : Diagram) (k l : Nat) : Bool := d.zs.getD (pairIdx k l) false
def Diagram.wstroke (d : Diagram) (k l : Nat) : Bool := d.ws.getD (pairIdx k l) false

/-- Reads class `c` of `n6.json`. -/
def Diagram.ofN6 (n6 : Json) (c : Nat) : Option Diagram := do
  let cls ← jArr? (← jField? n6 "classes")
  let e ← cls[c]?
  let edges ← jPairs? (← jField? e "edges")
  let mut zs := Array.replicate 36 false
  let mut ws := Array.replicate 36 false
  for (k, v) in edges do
    let cs := k.toList
    let (a, b) ← match cs with
      | [a, b] => some (a.toNat - '0'.toNat, b.toNat - '0'.toNat)
      | _ => none
    if a ≥ 6 || b ≥ 6 || a == b then none
    let x ← jNat? v
    if x % 2 == 1 then zs := zs.set! (pairIdx a b) true
    if x / 2 % 2 == 1 then ws := ws.set! (pairIdx a b) true
  let zcl ← (← jArr? (← jField? e "zcircles")).mapM jNat?
  let wcl ← (← jArr? (← jField? e "wcircles")).mapM jNat?
  let zc := (List.range 6).toArray.map fun k => zcl.contains k
  let wc := (List.range 6).toArray.map fun k => wcl.contains k
  some { zs, ws, zc, wc }

/-- A stored cell: two trees and the argmin sets of the base identities (in the stored order). -/
structure Cell where
  zt : Tree
  wt : Tree
  argmin : Array (IdName × Array Lab)
  deriving Inhabited

def Cell.ofJson (j : Json) : Option Cell := do
  let zt ← Tree.ofJson (← jField? j "ztree")
  let wt ← Tree.ofJson (← jField? j "wtree")
  let am ← jArr? (← jField? j "argmin")
  let mut argmin := #[]
  for x in am do
    let pr ← jArr? x
    match pr.toList with
    | [nm, labs] =>
      let nm ← IdName.ofJson nm
      let labs ← (← jArr? labs).mapM Lab.ofJson
      argmin := argmin.push (nm, labs)
    | _ => none
  some { zt, wt, argmin }

/-- The cells of a stored file (one JSON object per nonempty line). -/
def parseCells (s : String) : Option (Array Cell) := do
  let mut out := #[]
  for line in s.splitOn "\n" do
    if line.isEmpty then continue
    let j ← (Json.parse line).toOption
    out := out.push (← Cell.ofJson j)
  some out

end L6.F34
