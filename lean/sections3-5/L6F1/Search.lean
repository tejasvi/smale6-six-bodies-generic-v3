import L6F1.Rules

/-!
# The search of Proposition 3.1, the keys and the orbits

* `edgeLeaves n`: a search over the positions `0, 1, …` of the pairs that assigns a kind to each pair and checks (E2),
  (E3) and (E6), as conditions on the kinds, on every triangle and every 4-cycle as soon as its last pair has a kind
  (`trianglesAt`, `cyclesAt`, `stageOK`). The checks are the instances of the rules of `L6F1.Rules` (`e2At`, `e3At`,
  `e6At`), so a code that satisfies the rules passes them.
* `search n`: at each leaf `e` it checks (E1), (E4), (E5) in both colours, enumerates the circle masks of each colour
  allowed by (C1) (`candsUpTo`) and tests (C1)–(C4) (`circles`). `L6Sound.F1.Complete` proves that every labelled
  diagram satisfying `okRules` is listed; the checks of `L6Check.F1` test that everything listed satisfies `okRules`.
* `rawKey`: the key of a labelled diagram used to order and to choose the classes for six bodies (the digits of the
  kinds with the position `0` most significant, then the `z`-circles and the `w`-circles with the body `0` most
  significant); `rawKeyLex`: the key of the files for four and five bodies (the same edge part, then the circle masks
  as numbers). `canonKey`: the least key over the orbit of the `2 · n!` symmetries (`perms`, `act`).
-/

namespace L6F1

/-! ## The edge stage -/

/-- (E2) at the triangle `a, b, c` with the middle body `b`. -/
def e2At (e a b c : Nat) : Bool := !(isZW e a b && isZW e b c) || isZW e a c

/-- (E3) at the triangle `a, b, c`. -/
def e3At (e a b c : Nat) : Bool :=
  !(isEdge e a b && isEdge e b c && isEdge e a c) || (kind e a b == kind e b c && kind e b c == kind e a c)

/-- (E6) at the 4-cycle `ab, bc, cd, da`. -/
def e6At (e a b c d : Nat) : Bool :=
  !(isEdge e a b && isEdge e b c && isEdge e c d && isEdge e d a) ||
    (kind e a b == kind e c d && kind e b c == kind e d a)

/-- (E2) with each of the three bodies in the middle, and (E3), at the triangle `a, b, c`. -/
def triOK (e a b c : Nat) : Bool := e2At e a b c && e2At e b a c && e2At e a c b && e3At e a b c

/-- The triangles `a < b < c < n` whose last pair (in the order of the positions) is at the position `j`. -/
def trianglesAt (n j : Nat) : List (Nat × Nat × Nat) :=
  ((List.range n).flatMap fun c => (List.range c).flatMap fun b => (List.range b).map fun a => (a, b, c)).filter
    fun t => max (ppos t.1 t.2.1) (max (ppos t.1 t.2.2) (ppos t.2.1 t.2.2)) == j

/-- The 4-cycles `(a, b, c, d)` (the pairs `ab, bc, cd, da`) on the bodies `< n`, three for each set of four bodies,
whose last pair is at the position `j`. -/
def cyclesAt (n j : Nat) : List (Nat × Nat × Nat × Nat) :=
  ((List.range n).flatMap fun d => (List.range d).flatMap fun c => (List.range c).flatMap fun b =>
      (List.range b).flatMap fun a => [(a, b, c, d), (a, b, d, c), (a, c, b, d)]).filter
    fun q => max (max (ppos q.1 q.2.1) (ppos q.2.1 q.2.2.1)) (max (ppos q.2.2.1 q.2.2.2) (ppos q.2.2.2 q.1)) == j

/-- The checks of the triangles `ts` and the 4-cycles `cs` on the edge code `e`. -/
def stageOK (ts : List (Nat × Nat × Nat)) (cs : List (Nat × Nat × Nat × Nat)) (e : Nat) : Bool :=
  ts.all (fun t => triOK e t.1 t.2.1 t.2.2) && cs.all (fun q => e6At e q.1 q.2.1 q.2.2.1 q.2.2.2)

/-- The four extensions `e + v 4^j` (`v < 4`) of the codes `L` at the position `j` that pass the checks of the
triangles and 4-cycles completed at `j`. -/
def extendAt (n j : Nat) (L : List Nat) : List Nat :=
  let ts := trianglesAt n j
  let cs := cyclesAt n j
  L.flatMap fun e => ([0, 1, 2, 3].map fun v => e + v * 4 ^ j).filter (stageOK ts cs)

/-- The edge codes with digits at the positions `< j` that pass the checks of the positions `< j`. -/
def edgesUpTo (n : Nat) : Nat → List Nat
  | 0 => [0]
  | j + 1 => extendAt n j (edgesUpTo n j)

/-- The leaves of the edge stage: the kind assignments to all pairs that pass (E2), (E3), (E6). -/
def edgeLeaves (n : Nat) : List Nat := edgesUpTo n (numPairs n)

/-! ## The leaves -/

/-- (E1), (E5), (E4) in the colour `z`. -/
def edgeColourOK (n e : Nat) : Bool := ruleE1 n e && ruleE5 n e && ruleE4 n e

/-- The values of the circle bit of the body `k` allowed by (C1): `0` without a `z`-stroke, `1` with one. -/
def choices (n e k : Nat) : List Nat :=
  if zDeg n e k = 0 then [0] else if zDeg n e k = 1 then [1] else [0, 1]

/-- The circle masks of the bodies `< k` allowed by (C1). -/
def candsUpTo (n e : Nat) : Nat → List Nat
  | 0 => [0]
  | k + 1 => (candsUpTo n e k).flatMap fun c => (choices n e k).map fun v => c + v * 2 ^ k

/-- (C2), (C4), (C1), (C3) in the colour `z`. -/
def circleOK (n e c : Nat) : Bool := ruleC2 n e c && ruleC4 n e c && ruleC1 n e c && ruleC3 n e c

/-- The `z`-circle masks allowed by (C1) that pass (C1)–(C4). -/
def circles (n e : Nat) : List Nat := (candsUpTo n e n).filter (circleOK n e)

/-- The labelled diagrams with the edge code `e` found at a leaf. -/
def diagramsAt (n e : Nat) : List Diagram :=
  if edgeColourOK n e then
    let e' := swapE n e
    if edgeColourOK n e' then
      let cws := circles n e'
      (circles n e).flatMap fun cz => cws.map fun cw => ⟨e, cz, cw⟩
    else []
  else []

/-- **The search**: the labelled diagrams found at the leaves of the edge stage. -/
def searchFrom (n : Nat) (leaves : List Nat) : List Diagram := leaves.flatMap (diagramsAt n)

/-- **The search** on `n` bodies. -/
def search (n : Nat) : List Diagram := searchFrom n (edgeLeaves n)

/-! ## Keys, symmetries and orbits -/

/-- A single number coding a labelled diagram on `n` bodies (injective on `inRange n`). -/
def dcode (n : Nat) (d : Diagram) : Nat := d.e + 4 ^ numPairs n * (d.zc + 2 ^ n * d.wc)

/-- The edge part of the keys: the kinds read as a number in base 4 with the position `0` as the most significant
digit. -/
def edgeKey (n e : Nat) : Nat := digitsVal 4 (fun i => digit e (numPairs n - 1 - i)) (numPairs n)

/-- A circle mask read with the body `0` as the most significant bit. -/
def circKey (n c : Nat) : Nat := maskOf n fun k => circled c (n - 1 - k)

/-- The key of a labelled diagram on six bodies: `((Σ_i v_i 4^(14-i)) << 12) + ((Σ_k cz_k 2^(5-k)) << 6)
+ Σ_k cw_k 2^(5-k)` for `n = 6`, with the kinds `v_i` and the circle bits `cz_k`, `cw_k`. -/
def rawKey (n : Nat) (d : Diagram) : Nat := (edgeKey n d.e * 2 ^ n + circKey n d.zc) * 2 ^ n + circKey n d.wc

/-- The key of the files for four and five bodies: the lexicographic order of (the kinds by position, the `z`-circle
mask, the `w`-circle mask). -/
def rawKeyLex (n : Nat) (d : Diagram) : Nat := (edgeKey n d.e * 2 ^ n + d.zc) * 2 ^ n + d.wc

/-- The key used for `n` bodies: `rawKeyLex` if `lex`, else `rawKey`. -/
def keyOf (n : Nat) (lex : Bool) (d : Diagram) : Nat := if lex then rawKeyLex n d else rawKey n d

/-- The permutations of `0, …, n - 1` as lists `[τ 0, …, τ (n - 1)]`: `n - 1` inserted at each place of each
permutation of `0, …, n - 2`. -/
def perms : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (perms n).flatMap fun p => (List.range (n + 1)).map fun i => p.take i ++ n :: p.drop i

/-- The symmetry given by the list `p` (relabelling by `k ↦ p[k]`, read as the map `τ`) and the exchange of the
colours if `s`. -/
def act (n : Nat) (p : List Nat) (s : Bool) (d : Diagram) : Diagram :=
  let d' := d.relabel n (fun k => p.getD k k)
  if s then d'.swap n else d'

/-- The images of `d` under the `2 · n!` symmetries. -/
def orbitList (n : Nat) (d : Diagram) : List Diagram :=
  (perms n).flatMap fun p => [act n p false d, act n p true d]

/-- The least key over the orbit of `d`. -/
def canonKey (n : Nat) (lex : Bool) (d : Diagram) : Nat :=
  (orbitList n d).foldl (fun m x => min m (keyOf n lex x)) (keyOf n lex d)

/-! ## Sorted lists -/

/-- The list is strictly increasing. -/
def strictSorted : List Nat → Bool
  | a :: b :: l => a < b && strictSorted (b :: l)
  | _ => true

/-- Removes the repetitions of adjacent equal entries. -/
def dedupSorted : List Nat → List Nat
  | a :: b :: l => if a = b then dedupSorted (b :: l) else a :: dedupSorted (b :: l)
  | l => l

/-- Sorting of natural numbers. -/
def sortNat (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (a ≤ b))

/-- The codes of the orbit of `d`, sorted, without repetitions. -/
def orbitCodes (n : Nat) (d : Diagram) : List Nat := dedupSorted (sortNat ((orbitList n d).map (dcode n)))

end L6F1
