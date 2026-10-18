import L6K.F1.Sort
import L6F1.Check

/-!
# Proposition 3.1 in shards, for the kernel

The search of `L6F1.Search` split by the partial codes of the first `m` positions: `edgeLeaves 6` is the union over
the prefixes `p ∈ edgesUpTo 6 m` of `extendFrom m p`, the extensions of `p` through the positions `m, …, 14` by the
same steps (`extendAt`). Each shard is checked by one kernel evaluation (`shardOK`); the checks that need the whole
search compare sorted lists of codes. Sorting is the merge sort `msort` (structural; `L6F1.sortNat` is a well-founded
merge sort, which the kernel does not evaluate); `L6SoundK` proves that the two sorts agree.
-/

namespace L6K.F1

open L6F1

/-- The extensions of the partial code `p` (positions `< m` set) through the positions `m, …, 14`. -/
def extendFrom (m p : Nat) : List Nat :=
  (List.range (15 - m)).foldl (fun L j => extendAt 6 (m + j) L) [p]

/-- The check of the shard of the prefix `p`: its leaves are `cnt` codes below `4^15` satisfying (E2), (E3), (E6),
without repetitions; the diagrams found at them are in range and satisfy the rules; their codes, sorted, are `codes`. -/
def shardOK (m p cnt : Nat) (codes : List Nat) : Bool :=
  let L := extendFrom m p
  let F := searchFrom 6 L
  L.length == cnt && L.all (fun e => decide (e < 4 ^ 15) && edgeRules 6 e) && strictSorted (msort 20 L) &&
    F.all (fun d => inRange 6 d && okRules 6 d) && msort 20 (F.map (dcode 6)) == codes

/-- `orbitCodes` with `msort`. -/
def orbitCodesK (d : Diagram) : List Nat := dedupSorted (msort 12 ((orbitList 6 d).map (dcode 6)))

/-- `checkClass 6 false` with `orbitCodesK`. -/
def checkClassK (x : Diagram × Nat) : Bool :=
  inRange 6 x.1 && strictSorted (orbitCodesK x.1) && (orbitCodesK x.1).length == x.2 &&
    (orbitList 6 x.1).all (fun d => decide (rawKey 6 x.1 ≤ rawKey 6 d))

/-- `isPermOf` and `checkPerms` with `msort`. -/
def isPermOfK (n : Nat) (p : List Nat) : Bool := msort 10 p == List.range n

def checkPermsK (n : Nat) : Bool :=
  (perms n).length == fact n && (perms n).all (isPermOfK n) && strictSorted (msort 12 ((perms n).map (listCode n)))

end L6K.F1
