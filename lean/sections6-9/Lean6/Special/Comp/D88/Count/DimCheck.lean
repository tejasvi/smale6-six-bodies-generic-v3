import Lean6.Special.Comp.D88.Count.Order
import Std.Data.HashSet
import Std.Data.HashMap

/-!
# The dimension check of Lemma 6.19(b) (no Mathlib)

`dimCheck p n B N`: every polynomial of `B` is a nonempty list of terms with coefficients in `[1, p)`, exponent
lists of length `n`, strictly decreasing in `grevGtStd`; the staircase `S` of the leading monomials, computed by a
breadth-first search from `0` (`staircase`, not trusted), contains `0`, has at most `N` elements and is closed under
the border: for `s ∈ S` and every variable `i`, `s + eᵢ ∈ S` or a leading monomial divides `s + eᵢ` (the search
records the index of such a divisor; the check verifies the divisibility). `Lean6.Special.D88.Count.dimCheck_sound`
turns a successful check into the dimension bound.
-/

namespace Lean6.Special.Comp.Count

open Lean6.Special.Comp

/-- The terms are strictly decreasing. -/
def sortedStrict : Poly Nat → Bool
  | t :: u :: rest => grevGtStd t.2 u.2 && sortedStrict (u :: rest)
  | _ => true

/-- The shape of a polynomial of the basis. -/
def polyOK (p n : Nat) (g : Poly Nat) : Bool :=
  !g.isEmpty && g.all (fun t => decide (0 < t.1) && decide (t.1 < p) && t.2.length == n) && sortedStrict g

/-- The leading monomial (the first term). -/
def leadOf : Poly Nat → Mono
  | t :: _ => t.2
  | [] => []

/-- Add `1` to the exponent of the variable `i`. -/
def addVar : Mono → Nat → Mono
  | [], _ => []
  | a :: m, 0 => (a + 1) :: m
  | a :: m, i + 1 => a :: addVar m i

/-- `l` divides `m` (exponent lists of the same length). -/
def mdvdS : Mono → Mono → Bool
  | [], [] => true
  | a :: l, b :: m => decide (a ≤ b) && mdvdS l m
  | _, _ => false

/-- The exponent list of `1`. -/
def zeroMono (n : Nat) : Mono := List.replicate n 0

/-- One level of the search: the successors of the monomials of `front` that are new and not divisible by a leading
monomial form the next level; a successor divisible by a leading monomial is recorded with the index of one. -/
def level (n : Nat) (L : Array Mono) (front : List Mono) (seen : Std.HashSet Mono) (wit : Std.HashMap Mono Nat) :
    List Mono × Std.HashSet Mono × Std.HashMap Mono Nat :=
  front.foldl (fun st s =>
    (List.range n).foldl (fun st i =>
      let s' := addVar s i
      if st.2.1.contains s' || st.2.2.contains s' then st
      else match L.findIdx? (fun l => mdvdS l s') with
        | some w => (st.1, st.2.1, st.2.2.insert s' w)
        | none => (s' :: st.1, st.2.1.insert s', st.2.2))
      st)
    ([], seen, wit)

/-- The staircase by levels (at most `fuel` levels, stopping early beyond `cap` monomials). -/
def staircaseAux (n : Nat) (L : Array Mono) (cap : Nat) :
    Nat → List Mono → Std.HashSet Mono → Std.HashMap Mono Nat → List Mono → List Mono × Std.HashMap Mono Nat
  | 0, _, _, wit, acc => (acc, wit)
  | fuel + 1, front, seen, wit, acc =>
    if front.isEmpty || acc.length > cap then (acc, wit)
    else
      let r := level n L front seen wit
      staircaseAux n L cap fuel r.1 r.2.1 r.2.2 (r.1 ++ acc)

/-- The staircase of the leading monomials `L` (not trusted) and the divisor indices of its border. -/
def staircase (n : Nat) (L : Array Mono) (cap fuel : Nat) : List Mono × Std.HashMap Mono Nat :=
  let z := zeroMono n
  if L.any (fun l => mdvdS l z) then ([], {})
  else staircaseAux n L cap fuel [z] (Std.HashSet.ofList [z]) {} [z]

/-- The border test of one successor. -/
def borderAt (L : Array Mono) (hs : Std.HashSet Mono) (wit : Std.HashMap Mono Nat) (s' : Mono) : Bool :=
  hs.contains s' ||
    match wit.get? s' with
    | some w => mdvdS (L.getD w []) s'
    | none => false

/-- **The dimension check.** -/
def dimCheck (p n : Nat) (B : List (Poly Nat)) (N : Nat) : Bool :=
  B.all (polyOK p n) &&
    let L := (B.map leadOf).toArray
    let r := staircase n L N (N + 2)
    let S := r.1
    let hs := Std.HashSet.ofList S
    hs.contains (zeroMono n) && S.all (fun s => s.length == n) && decide (S.length ≤ N) &&
      S.all (fun s => (List.range n).all fun i => borderAt L hs r.2 (addVar s i))

end Lean6.Special.Comp.Count
