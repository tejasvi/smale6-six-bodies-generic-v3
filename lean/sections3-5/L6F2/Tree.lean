/-!
# Trees of the search of Proposition 4.5

A replica of the class `Tree` of the engine (`types/tengine.py`, tag generic-v1): a rooted tree on the points
`0, …, n` (`n` = the centre of mass `O`), internal nodes numbered from `n + 1` in order of creation. The engine
keeps three dictionaries (`parent`, `children`, `leaf`) whose insertion orders determine the order in which the
insertions of a point are listed (`options`) and the numbering of the heights of a linear program (the internal
nodes in the order of `children`). We store each dictionary as the list of its keys in insertion order together
with an array indexed by the key, so that `options` lists the trees in exactly the engine's order, with the same
node numbers, and the cells can be written back byte for byte.
-/

namespace L6.F2

/-- Marker for an absent entry. -/
def NONE : Nat := 255

/-- Size of the arrays indexed by node numbers (leaves `0 … 6`, internal nodes `7 … 12`). -/
def SZ : Nat := 32

/-- A tree: the dictionaries `parent`, `children`, `leaf` of the engine (keys in insertion order, values indexed by
the key), the root (`NONE` before the first insertion) and the next node number. -/
structure Tree where
  parentOrder : Array Nat
  parentOf : Array Nat
  childOrder : Array Nat
  childrenOf : Array (Array Nat)
  root : Nat
  leafOrder : Array Nat
  leafOf : Array Nat
  nextId : Nat
  deriving Inhabited, BEq, Repr

namespace Tree

/-- `Tree(n)` of the engine. -/
def empty (n : Nat) : Tree :=
  { parentOrder := #[], parentOf := Array.replicate SZ NONE, childOrder := #[],
    childrenOf := Array.replicate SZ #[], root := NONE, leafOrder := #[], leafOf := Array.replicate SZ NONE,
    nextId := n + 1 }

/-- `d[k] = v` for the parent dictionary (append the key if it is new). -/
def setParent (t : Tree) (k v : Nat) : Tree :=
  if t.parentOf[k]! == NONE then { t with parentOrder := t.parentOrder.push k, parentOf := t.parentOf.set! k v }
  else { t with parentOf := t.parentOf.set! k v }

/-- `d[k] = v` for the children dictionary. -/
def setChildren (t : Tree) (k : Nat) (v : Array Nat) : Tree :=
  if t.childOrder.contains k then { t with childrenOf := t.childrenOf.set! k v }
  else { t with childOrder := t.childOrder.push k, childrenOf := t.childrenOf.set! k v }

/-- `d[k] = v` for the leaf dictionary. -/
def setLeaf (t : Tree) (k v : Nat) : Tree :=
  if t.leafOf[k]! == NONE then { t with leafOrder := t.leafOrder.push k, leafOf := t.leafOf.set! k v }
  else { t with leafOf := t.leafOf.set! k v }

/-- `v` is an internal node (a key of `children`). -/
@[inline] def isInternal (t : Tree) (v : Nat) : Bool := t.childOrder.contains v

/-- The ancestors of `v`, `v` first (fuel bounds the depth). -/
def ancestors (t : Tree) (v : Nat) : List Nat :=
  go SZ v
where
  go : Nat → Nat → List Nat
    | 0, v => [v]
    | fuel + 1, v => if t.parentOf[v]! == NONE then [v] else v :: go fuel t.parentOf[v]!

/-- The meet of the leaves of the points `p` and `q`, or `none` if they share a leaf. -/
def meet (t : Tree) (p q : Nat) : Option Nat :=
  let u := t.leafOf[p]!
  let v := t.leafOf[q]!
  if u == v then none
  else
    let sv := ancestors t v
    (ancestors t u).find? (fun w => sv.contains w)

/-- `Tree.options`: the trees obtained by inserting the point `p`, in the engine's order: at `O` (bodies only, when
no body is there yet), attached to each internal node (in the order of `children`), subdividing each edge
`parent(c) → c` (in the order of `parent`), and as a new root. -/
def options (n : Nat) (t : Tree) (p : Nat) : Array Tree := Id.run do
  if t.root == NONE then
    return #[(({ t with root := p } : Tree)).setLeaf p p]
  let mut out : Array Tree := #[]
  -- at O
  if p != n && t.leafOf[n]! != NONE && !(t.leafOrder.any fun q => q != n && t.leafOf[q]! == n) then
    out := out.push (t.setLeaf p n)
  -- attach to an internal node
  for v in t.childOrder do
    let t1 := t.setChildren v (t.childrenOf[v]!.push p)
    let t2 := t1.setParent p v
    out := out.push (t2.setLeaf p p)
  -- subdivide an edge parent(c) → c
  for c in t.parentOrder do
    let u := t.parentOf[c]!
    let w := t.nextId
    let t0 := { t with nextId := t.nextId + 1 }
    let t1 := t0.setChildren u (t0.childrenOf[u]!.map fun x => if x == c then w else x)
    let t2 := t1.setParent w u
    let t3 := t2.setChildren w #[c, p]
    let t4 := t3.setParent c w
    let t5 := t4.setParent p w
    out := out.push (t5.setLeaf p p)
  -- a new root
  let w := t.nextId
  let t0 := { t with nextId := t.nextId + 1 }
  let t1 := t0.setChildren w #[t.root, p]
  let t2 := t1.setParent t.root w
  let t3 := t2.setParent p w
  let t4 := { t3 with root := w }
  out := out.push (t4.setLeaf p p)
  return out

/-- The centre-of-mass rule: the root has at least three children. -/
def comOk (t : Tree) : Bool := t.childrenOf[t.root]!.size ≥ 3

/-- The position of each internal node in the order of `children` (`NONE` for other numbers). -/
def indexMap (t : Tree) (offset : Nat) : Array Nat := Id.run do
  let mut m := Array.replicate SZ NONE
  for i in [0:t.childOrder.size] do
    m := m.set! t.childOrder[i]! (offset + i)
  return m

/-- `json.dumps` of the engine's `tree_json`: the children dictionary in insertion order, the leaf dictionary,
the root. -/
def render (t : Tree) : String :=
  let ch := ", ".intercalate (t.childOrder.toList.map fun v =>
    "\"" ++ toString v ++ "\": [" ++ ", ".intercalate (t.childrenOf[v]!.toList.map toString) ++ "]")
  let lf := ", ".intercalate (t.leafOrder.toList.map fun p => "\"" ++ toString p ++ "\": " ++ toString t.leafOf[p]!)
  "{\"children\": {" ++ ch ++ "}, \"leaf\": {" ++ lf ++ "}, \"root\": " ++ toString t.root ++ "}"

end Tree

end L6.F2
