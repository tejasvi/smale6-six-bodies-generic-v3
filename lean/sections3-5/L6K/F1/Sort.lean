/-!
# Merge sort for the kernel

`L6F1.sortNat` is the merge sort of the core library, defined by well-founded recursion, which the kernel does not
evaluate; `msort` is a merge sort by structural recursion on fuel. `L6SoundK.F1.Sort` proves that the two agree when the
fuel suffices.
-/

namespace L6K.F1

/-- Merge of two sorted lists (fuel: at least the total length). -/
def merge : Nat → List Nat → List Nat → List Nat
  | 0, a, b => a ++ b
  | f + 1, [], b => b
  | f + 1, a, [] => a
  | f + 1, x :: a, y :: b => if x ≤ y then x :: merge f a (y :: b) else y :: merge f (x :: a) b

/-- Merge sort with fuel `d` for the depth (`2^d` at least the length). -/
def msort : Nat → List Nat → List Nat
  | 0, l => l
  | d + 1, l =>
    match l with
    | [] => []
    | [x] => [x]
    | _ =>
      let h := l.length / 2
      merge l.length (msort d (l.take h)) (msort d (l.drop h))

end L6K.F1
