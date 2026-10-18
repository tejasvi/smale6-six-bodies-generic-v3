import L6F1.Search
import L6F1.Json

/-!
# The checks of Proposition 3.1

`checkAll n lex json numEdge numLabelled numClasses` runs the search on `n` bodies and checks:

1. the edge stage: `edgeLeaves n` has `numEdge` entries, without repetitions, each a code `< 4 ^ numPairs n`
   satisfying (E2), (E3), (E6) (`edgeRules`);
2. the search: `search n` has `numLabelled` entries, without repetitions (their codes `dcode` are distinct), each a
   labelled diagram on `n` bodies satisfying `okRules`;
3. the permutations: `perms n` has `n!` entries, without repetitions, each a permutation of `0, …, n - 1`;
4. the class file: it is read as `(n, numLabelled, cls)` with `numClasses` classes and written back identically by
   `renderFile`; each representative is a labelled diagram on `n` bodies whose orbit has the listed number of
   elements and whose key (`keyOf n lex`) is the least key of its orbit; the keys of the representatives increase
   strictly along the file; and the orbits of the representatives, put together, are exactly the labelled diagrams
   found by the search, each once.
-/

namespace L6F1

/-- `n!`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The list `p` is a permutation of `0, …, n - 1`. -/
def isPermOf (n : Nat) (p : List Nat) : Bool := sortNat p == List.range n

/-- A code of a list of numbers `< n` of length `n` (injective on these lists). -/
def listCode (n : Nat) (p : List Nat) : Nat := p.foldr (fun x acc => x + n * acc) 0

/-- The checks of `perms n`. -/
def checkPerms (n : Nat) : Bool :=
  (perms n).length == fact n && (perms n).all (isPermOf n) && strictSorted (sortNat ((perms n).map (listCode n)))

/-- The checks of the edge stage. -/
def checkEdges (n numEdge : Nat) (EL : List Nat) : Bool :=
  EL.length == numEdge && strictSorted (sortNat EL) && EL.all (fun e => decide (e < 4 ^ numPairs n) && edgeRules n e)

/-- The checks of the search. -/
def checkSearch (n numLabelled : Nat) (L : List Diagram) : Bool :=
  L.length == numLabelled && strictSorted (sortNat (L.map (dcode n))) && L.all (fun d => inRange n d && okRules n d)

/-- The checks of one class `x = (representative, count)`. -/
def checkClass (n : Nat) (lex : Bool) (x : Diagram × Nat) : Bool :=
  inRange n x.1 && strictSorted (orbitCodes n x.1) && (orbitCodes n x.1).length == x.2 &&
    (orbitList n x.1).all (fun d => keyOf n lex x.1 ≤ keyOf n lex d)

/-- The checks of the class file against the labelled diagrams `L`. -/
def checkFile (n : Nat) (lex : Bool) (json : String) (numLabelled numClasses : Nat) (L : List Diagram) : Bool :=
  match parseFile json with
  | none => false
  | some (n', total, cls) =>
    renderFile n' total cls == json && n' == n && total == numLabelled && cls.length == numClasses &&
      cls.all (checkClass n lex) && strictSorted (cls.map fun x => keyOf n lex x.1) &&
      sortNat (cls.flatMap fun x => orbitCodes n x.1) == sortNat (L.map (dcode n))

/-- **All checks of Proposition 3.1 for `n` bodies.** -/
def checkAll (n : Nat) (lex : Bool) (json : String) (numEdge numLabelled numClasses : Nat) : Bool :=
  let EL := edgeLeaves n
  let L := searchFrom n EL
  checkEdges n numEdge EL && checkSearch n numLabelled L && checkPerms n &&
    checkFile n lex json numLabelled numClasses L

end L6F1
