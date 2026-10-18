import L6F2.Tree

/-!
# The trees of the insertion procedure, without pruning

The proof of Proposition 4.5 says that each tree arises exactly once from the insertions: without pruning they
produce 55,720 distinct trees, the 39,208 trees with seven leaves and the 16,512 trees with a body on the leaf of `O`.
`treeCounts` inserts `O` and then the bodies `0, …, 5` in all ways (`Tree.options`, the procedure of the search) and
returns the number of trees, the number of distinct canonical forms (leaves as sorted lists of points, internal
nodes as sorted lists of the forms of their children), and the number of trees with a body on the leaf of `O`.
-/

namespace L6.F2

/-- The canonical form of the subtree at the node `v` (fuel bounds the depth). -/
def canonAt (t : Tree) : Nat → Nat → String
  | 0, _ => "?"
  | fuel + 1, v =>
    if t.isInternal v then
      let cs := (t.childrenOf[v]!.toList.map (canonAt t fuel)).mergeSort fun a b => decide (a ≤ b)
      "(" ++ ",".intercalate cs ++ ")"
    else
      let pts := (t.leafOrder.toList.filter fun p => t.leafOf[p]! == v).mergeSort fun a b => decide (a ≤ b)
      "[" ++ ",".intercalate (pts.map toString) ++ "]"

/-- The canonical form of a tree. -/
def canon (t : Tree) : String := canonAt t SZ t.root

/-- All trees obtained by inserting `O` and then the bodies `0, …, 5` in all ways. -/
def allTrees : Array Tree :=
  (List.range 6).foldl (fun ts p => ts.flatMap fun t => t.options 6 p) ((Tree.empty 6).options 6 6)

/-- The number of distinct entries of a sorted list. -/
def countDistinct : List String → Nat
  | [] => 0
  | x :: rest => 1 + go x rest
where
  go (prev : String) : List String → Nat
    | [] => 0
    | y :: ys => (if y == prev then 0 else 1) + go y ys

/-- (trees, distinct canonical forms, trees with a body on the leaf of `O`). -/
def treeCounts : Nat × Nat × Nat :=
  let ts := allTrees
  let cs := (ts.toList.map canon).mergeSort fun a b => decide (a ≤ b)
  let atO := (ts.filter fun t => (List.range 6).any fun p => t.leafOf[p]! == 6).size
  (ts.size, countDistinct cs, atO)

end L6.F2
