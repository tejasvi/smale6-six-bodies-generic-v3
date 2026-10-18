import L6Common.Rows

/-!
# The decisions of the search from certificate data, for the kernel

`keepK T rows nv` decides a linear program of the specification search (`L6F2S`) without floating point: the program
is discarded only if the table `T` holds, under the hash of its rows, a certificate that `Farkas.check` accepts;
otherwise it is kept. Keeping is always allowed, so the hash only has to find the certificates, not to be injective.
The table is a binary search tree on the hashes, built from data; `L6SoundK.F2S.Keep` proves `KeepSound (keepK T)`.
-/

namespace L6K.F2S

open L6

/-- The zigzag code of an integer. -/
def zz : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

/-- The code of an optional bound. -/
def optCode : Option Int → Nat
  | none => 0
  | some x => zz x + 1

/-- One step of the hash (modulo the prime `2^61 − 1`). -/
def mix (h x : Nat) : Nat := (h * 1000003 + x) % 2305843009213693951

/-- The hash of a row, after `h`. -/
def rowHash (h : Nat) (r : Row) : Nat :=
  mix (mix (mix (r.a.toList.foldl (fun h x => mix h (zz x)) h) (zz r.c)) (optCode r.lo)) (optCode r.hi)

/-- The hash of the rows of a program: its number of rows, its first and its last row (cheap; several programs may
share a hash, the table keeps all their certificates). -/
def rowsHash (rows : Array Row) : Nat :=
  match rows.toList with
  | [] => 0
  | r :: rest => mix (rowHash (rowHash rows.size r) (rest.getLastD r)) 1

/-- A certificate table: a binary search tree on hashes, with the certificates of each hash. -/
inductive CTree where
  | leaf
  | node (l : CTree) (k : Nat) (certs : List (List (Nat × Int))) (r : CTree)

/-- The certificates stored under the hash `k`. -/
def CTree.find : CTree → Nat → List (List (Nat × Int))
  | .leaf, _ => []
  | .node l k' c r, k => if k < k' then l.find k else if k' < k then r.find k else c

/-- The balanced tree of a list sorted by hash (`fuel` bounds the depth). -/
def CTree.ofSorted : Nat → List (Nat × List (List (Nat × Int))) → CTree
  | 0, _ => .leaf
  | _ + 1, [] => .leaf
  | f + 1, l@(_ :: _) =>
    let m := l.length / 2
    match l.drop m with
    | [] => .leaf
    | (k, c) :: rest => .node (CTree.ofSorted f (l.take m)) k c (CTree.ofSorted f rest)

/-- **The decision from data**: discard only with a stored certificate that `Farkas.check` accepts. -/
def keepK (T : CTree) (rows : Array Row) (nv : Nat) : Bool :=
  !(T.find (rowsHash rows)).any (Farkas.check nv rows)

end L6K.F2S
