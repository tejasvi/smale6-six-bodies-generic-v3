import L6F1.Search

/-!
# The orderly edge search (for the kernel)

The edge stage of `L6F1.Search` (`edgesUpTo`) assigns a kind to the pairs in the order of their positions
`01, 02, 12, 03, 13, 23, …`; after the position count `bnd k = (k + 1) k / 2` the positions set are exactly the pairs
of the bodies `0, …, k`. A prefix complete on `0, …, k` that some symmetry `(p, s)` fixing the set `{0, …, k}` maps to a
prefix with a smaller key (position `0` most significant, the order of `edgeKey`) cannot be the prefix of the least
code of an orbit, because the order of `edgeKey` on full codes is decided by such a prefix first. The search
discards such prefixes; which ones, and by which symmetry, is given as a witness stream, and every witness is checked
here. A prefix without a witness is kept (always safe).

`search` is written for the kernel: structural recursion on fuel, data in natural numbers and lists, no strings.
`searchGen` (compiled code) produces the witness stream with the same traversal.
-/

namespace L6K.F1

open L6F1

/-- The number of positions of the pairs of the bodies `0, …, k`. -/
def bnd (k : Nat) : Nat := (k + 1) * k / 2

/-- `some k` if the position count `m` is `bnd k` with `1 ≤ k ≤ 5`. -/
def bndK (m : Nat) : Option Nat :=
  if m == 1 then some 1 else if m == 3 then some 2 else if m == 6 then some 3
  else if m == 10 then some 4 else if m == 15 then some 5 else none

/-- The key of the first `m` positions of the code `e`, position `0` most significant (the order of `edgeKey`). -/
def preKey (m e : Nat) : Nat := digitsVal 4 (fun i => digit e (m - 1 - i)) m

/-- The image of the edge code `e` under the symmetry `(p, s)` of `act`. -/
def actE (p : List Nat) (s : Bool) (e : Nat) : Nat := (act 6 p s ⟨e, 0, 0⟩).e

/-- `p` is a permutation of `0, …, 5` that maps each of `0, …, k` into `0, …, k`. -/
def permOK (k : Nat) (p : List Nat) : Bool :=
  p.length == 6 &&
    (List.range 6).all (fun i => decide (p.getD i 0 < 6) && (!decide (i ≤ k) || decide (p.getD i 0 ≤ k))) &&
    (List.range 6).all (fun i => (List.range 6).all fun j => i == j || p.getD i 0 != p.getD j 0)

/-- A witness entry: `0` keeps the prefix; otherwise `1 + s + 2 Σ p[i] 8^i`. -/
def decodeWit (w : Nat) : List Nat × Bool :=
  ((List.range 6).map fun i => (w - 1) / 2 / 8 ^ i % 8, (w - 1) % 2 == 1)

def encodeWit (p : List Nat) (s : Bool) : Nat :=
  1 + (if s then 1 else 0) + 2 * ((List.range 6).foldl (fun acc i => acc + p.getD i 0 * 8 ^ i) 0)

/-- The state of the search: leaves found (newest first), rest of the witness stream, all witnesses accepted. -/
structure St where
  leaves : List Nat
  ws : List Nat
  ok : Bool

/-- **The orderly search** from position `j` with the partial code `e`. -/
def search : Nat → Nat → Nat → St → St
  | 0, _, _, st => { st with ok := false }
  | fuel + 1, j, e, st =>
    if j == 15 then { st with leaves := e :: st.leaves }
    else
      [0, 1, 2, 3].foldl (fun st v =>
        let e' := e + v * 4 ^ j
        if stageOK (trianglesAt 6 j) (cyclesAt 6 j) e' then
          match bndK (j + 1) with
          | none => search fuel (j + 1) e' st
          | some k =>
            match st.ws with
            | [] => { st with ok := false }
            | w :: ws =>
              if w == 0 then search fuel (j + 1) e' { st with ws }
              else
                let pw := decodeWit w
                { st with ws, ok := st.ok && permOK k pw.1 &&
                    decide (preKey (j + 1) (actE pw.1 pw.2 e') < preKey (j + 1) e') }
        else st) st

/-- The search from the root: (leaves in search order, witness stream fully used, all witnesses accepted). -/
def run (ws : List Nat) : List Nat × Bool :=
  let st := search 16 0 0 ⟨[], ws, true⟩
  (st.leaves.reverse, st.ok && st.ws.isEmpty)

/-! ## The witness stream (compiled code) -/

/-- The symmetries fixing `{0, …, k}` setwise and every body above `k`: permutations of `0, …, k` extended by the
identity, with and without the exchange of the colours. -/
def stab (k : Nat) : List (List Nat × Bool) :=
  (perms (k + 1)).flatMap fun p =>
    let q := p ++ (List.range (5 - k)).map (· + (k + 1))
    [(q, false), (q, true)]

/-- The same traversal as `search`, producing the witness stream (newest first) and the leaves (newest first). -/
partial def searchGen (j e : Nat) (acc : List Nat × List Nat) : List Nat × List Nat :=
  if j == 15 then (e :: acc.1, acc.2)
  else
    [0, 1, 2, 3].foldl (fun acc v =>
      let e' := e + v * 4 ^ j
      if stageOK (trianglesAt 6 j) (cyclesAt 6 j) e' then
        match bndK (j + 1) with
        | none => searchGen (j + 1) e' acc
        | some k =>
          let key := preKey (j + 1) e'
          match (stab k).find? (fun g => decide (preKey (j + 1) (actE g.1 g.2 e') < key)) with
          | some g => (acc.1, encodeWit g.1 g.2 :: acc.2)
          | none => searchGen (j + 1) e' (acc.1, 0 :: acc.2)
      else acc) acc

/-- (leaves in search order, witness stream in search order). -/
def generate : List Nat × List Nat :=
  let r := searchGen 0 0 ([], [])
  (r.1.reverse, r.2.reverse)

end L6K.F1
