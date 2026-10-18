import L6K.F1.Orderly
import L6K.F1.Sort
import L6K.Words

/-!
# The checks of Proposition 3.1 for the kernel

Everything a kernel proof of `F1_main` needs to evaluate, in functions that the kernel reduces (structural recursion,
natural numbers, lists; no strings, no well-founded recursion):

* `run` (`L6K.F1.Orderly`): the orderly edge search with its witness stream, whose leaves are the canonical edge codes;
* `searchFrom 6` (`L6F1.Search`) on the leaves: the labelled diagrams with a canonical edge code;
* `foundOK`: each of them is mapped by a given symmetry onto a given representative;
* `repOK`: a representative satisfies the rules, its orbit has the listed size, its key is the least of its orbit;
* `edgeOrbitSize`: the size of the orbit of a canonical edge code, which must be the least code of its orbit.
-/

namespace L6K.F1

open L6F1

/-- The number of distinct entries of a sorted list. -/
def countDistinct : List Nat → Nat
  | a :: b :: l => (if a = b then 0 else 1) + countDistinct (b :: l)
  | [_] => 1
  | [] => 0

/-- The symmetries `(p, s)` in the order of `orbitList`. -/
def syms : List (List Nat × Bool) := (perms 6).flatMap fun p => [(p, false), (p, true)]

/-- A representative `x = (d, size)`: in range, satisfies the rules, its orbit has `size` labelled diagrams, and its
key is at most the key of each of its images (so `canonKey` is its key). -/
def repOK (x : Diagram × Nat) : Bool :=
  let imgs := orbitList 6 x.1
  inRange 6 x.1 && okRules 6 x.1 &&
    countDistinct (msort 12 (imgs.map (dcode 6))) == x.2 &&
    imgs.all (fun d => decide (rawKey 6 x.1 ≤ rawKey 6 d))

/-- The size of the orbit of the edge code `c` if `c` has the least key of its orbit, else `0`. -/
def edgeOrbitSize (c : Nat) : Nat :=
  let imgs := syms.map fun g => actE g.1 g.2 c
  if imgs.all (fun c' => decide (edgeKey 6 c ≤ edgeKey 6 c')) then countDistinct (msort 12 imgs) else 0

/-- A found diagram `d` with its witness word `w = encodeWit p s + 2^20 i`: `p` is a permutation of `0, …, 5` and
`act 6 p s d` is the representative number `i`. -/
def foundOK (reps : List Diagram) (d : Diagram) (w : Nat) : Bool :=
  let pw := decodeWit (w % 2 ^ 20)
  permOK 5 pw.1 && (reps[w / 2 ^ 20]? == some (act 6 pw.1 pw.2 d))

/-- The diagrams of 64-bit words `e + 2^30 zc + 2^36 wc`. -/
def diagOfWord (x : Nat) : Diagram := ⟨x % 2 ^ 30, x / 2 ^ 30 % 64, x / 2 ^ 36 % 64⟩

end L6K.F1
