import Lean6.Special.Comp.Poly

/-!
# A Buchberger engine over `ℤ/p` whose positive answers are certificates (no Mathlib)

`unitTest p n fuel F` runs Buchberger's algorithm (sugar strategy, the update of Gebauer and Möller) on the polynomials
`F` with coefficients in `ℤ/p` (natural numbers, `modC p`) and answers `true` when it produces a nonzero constant.

The answer `true` is a certificate by construction: every polynomial the engine adds to its basis is
`reduce (spoly g_i g_j)`, and both operations are built from `axpy f c m g = f − c·x^m·g` and `mulTerm`, so every
basis element is a combination of the input with polynomial multipliers. `Lean6.Special.K4.C4.GBSound` proves this
invariant (`unitTest_sound`): a nonzero constant in the basis means that `F` has no common zero in any nontrivial
commutative ring of characteristic `p`. The bookkeeping (the order of the terms, the choice of pairs and reducers, the
criteria) plays no role in that proof; it only decides whether and how fast the engine finds the constant.

Terms are `(c, m)` with `c` reduced modulo `p` and `m` a monomial of fixed length `n`; polynomials are kept sorted by
a degree reverse lexicographic order (`grevGt`) so that the first term is the leading one.
-/

namespace Lean6.Special.Comp.GB

/-- Pad a monomial with zeros to length `n` (longer monomials are kept). -/
def pad (n : Nat) (m : Mono) : Mono := m ++ List.replicate (n - m.length) 0

/-- Total degree. -/
def mdeg (m : Mono) : Nat := m.foldl (· + ·) 0

/-- At the first position where `m` and `k` differ, `m` has the smaller exponent. -/
def firstSmaller : Mono → Mono → Bool
  | a :: m, b :: k => if a == b then firstSmaller m k else a < b
  | _, _ => false

/-- The monomial order: degree first, then `firstSmaller` (a degree reverse lexicographic order). -/
def grevGt (m k : Mono) : Bool :=
  let dm := mdeg m
  let dk := mdeg k
  if dm == dk then firstSmaller m k else dk < dm

/-- `m` divides `k` (equal lengths). -/
def mdvd : Mono → Mono → Bool
  | a :: m, b :: k => a ≤ b && mdvd m k
  | [], _ => true
  | _ :: _, [] => false

/-- `k / m` (exponents subtracted, equal lengths). -/
def mquo : Mono → Mono → Mono
  | b :: k, a :: m => (b - a) :: mquo k m
  | k, [] => k
  | [], _ => []

/-- Least common multiple (equal lengths). -/
def mlcm : Mono → Mono → Mono
  | a :: m, b :: k => max a b :: mlcm m k
  | m, [] => m
  | [], k => k

/-- Coprime monomials. -/
def mcoprime : Mono → Mono → Bool
  | a :: m, b :: k => (a == 0 || b == 0) && mcoprime m k
  | _, _ => true

/-- Inverse modulo a prime `p` (Fermat). -/
def inv (p a : Nat) : Nat := Id.run do
  let mut r := 1
  let mut b := a % p
  let mut e := p - 2
  while e > 0 do
    if e % 2 == 1 then r := r * b % p
    b := b * b % p
    e := e / 2
  return r

/-- `acc.reverse ++ (f − c·x^m·g)`, merging the two sorted lists (tail-recursive). -/
def axpyAux (p c : Nat) (m : Mono) : Poly Nat → Poly Nat → Poly Nat → Poly Nat
  | f, [], acc => acc.reverseAux f
  | [], (b, k) :: g, acc => axpyAux p c m [] g (((modC p).neg ((modC p).mul c b), Mono.mul m k) :: acc)
  | (a, mf) :: f, (b, k) :: g, acc =>
    let mk := Mono.mul m k
    if mf == mk then
      let d := (modC p).add a ((modC p).neg ((modC p).mul c b))
      if d == 0 then axpyAux p c m f g acc else axpyAux p c m f g ((d, mf) :: acc)
    else if grevGt mf mk then axpyAux p c m f ((b, k) :: g) ((a, mf) :: acc)
    else axpyAux p c m ((a, mf) :: f) g (((modC p).neg ((modC p).mul c b), mk) :: acc)
termination_by f g => f.length + g.length

/-- `f − c·x^m·g`. -/
def axpy (p c : Nat) (m : Mono) (f g : Poly Nat) : Poly Nat := axpyAux p c m f g []

/-- `c·x^m·g` (order preserved). -/
def mulT (p c : Nat) (m : Mono) (g : Poly Nat) : Poly Nat := g.map fun t => ((modC p).mul c t.1, Mono.mul m t.2)

/-- A basis element whose leading monomial divides `m`, among the indices `idx`. -/
def findRed (basis : Array (Poly Nat)) (lead : Array Mono) (m : Mono) : List Nat → Option Nat
  | [] => none
  | i :: is => if mdvd (lead.getD i []) m then some i else findRed basis lead m is

/-- Full reduction of `h` by the basis elements with indices `idx`: the irreducible terms go to `out` (reversed). -/
def reduceAux (p : Nat) (basis : Array (Poly Nat)) (lead : Array Mono) (idx : List Nat) :
    Nat → Poly Nat → Poly Nat → Poly Nat
  | 0, h, out => out.reverseAux h
  | _ + 1, [], out => out.reverse
  | fuel + 1, (a, m) :: h, out =>
    match findRed basis lead m idx with
    | none => reduceAux p basis lead idx fuel h ((a, m) :: out)
    | some i =>
      let g := basis.getD i []
      match g with
      | [] => reduceAux p basis lead idx fuel h ((a, m) :: out)
      | (b, k) :: _ =>
        reduceAux p basis lead idx fuel (axpy p (a * inv p b % p) (mquo m k) ((a, m) :: h) g) out

/-- Make a polynomial monic (leading coefficient `1`). -/
def monic (p : Nat) : Poly Nat → Poly Nat
  | [] => []
  | (a, m) :: h => mulT p (inv p a) (List.replicate m.length 0) ((a, m) :: h)

/-- The S-polynomial of two monic polynomials. -/
def spoly (p : Nat) (f g : Poly Nat) : Poly Nat :=
  match f, g with
  | (_, mf) :: _, (_, mg) :: _ =>
    let l := mlcm mf mg
    axpy p 1 (mquo l mg) (mulT p 1 (mquo l mf) f) g
  | _, _ => []

/-- A critical pair with its least common multiple and sugar. -/
structure Pair where
  i : Nat
  j : Nat
  lcm : Mono
  sugar : Nat

/-- The state of the engine. -/
structure St where
  basis : Array (Poly Nat)
  lead : Array Mono
  sugar : Array Nat
  /-- indices of the basis elements still used for pairs and reductions -/
  act : List Nat
  pairs : List Pair
  found : Bool

/-- Insert a pair, keeping the list sorted by sugar, then by the degree of the lcm. -/
def insertPair (q : Pair) : List Pair → List Pair
  | [] => [q]
  | r :: rs =>
    if q.sugar < r.sugar || (q.sugar == r.sugar && mdeg q.lcm < mdeg r.lcm) then q :: r :: rs
    else r :: insertPair q rs

/-- The pairs after adding the basis element `t`: the update of Gebauer and Möller (Becker–Weispfenning's UPDATE). -/
def newPairs (s : St) (t : Nat) : List Pair := Id.run do
  let lt := s.lead.getD t []
  let st := s.sugar.getD t 0
  let mkPair (i : Nat) : Pair :=
    let li := s.lead.getD i []
    let l := mlcm li lt
    let sg := max (s.sugar.getD i 0 + mdeg (mquo l li)) (st + mdeg (mquo l lt))
    ⟨i, t, l, sg⟩
  -- the new pairs
  let C := s.act.map mkPair
  -- first loop: keep (i, t) if coprime, or if no other pair of C ∪ D (other than itself) has an lcm dividing its lcm
  let mut D : List Pair := []
  let mut rest := C
  for q in C do
    rest := rest.drop 1
    let li := s.lead.getD q.i []
    if mcoprime li lt || !((rest ++ D).any fun r => mdvd r.lcm q.lcm) then
      D := q :: D
  -- second loop: drop the coprime ones
  let E := D.filter fun q => !mcoprime (s.lead.getD q.i []) lt
  -- the old pairs
  let B := s.pairs.filter fun q =>
    !mdvd lt q.lcm || mlcm (s.lead.getD q.i []) lt == q.lcm || mlcm (s.lead.getD q.j []) lt == q.lcm
  return E.foldl (fun acc q => insertPair q acc) B

/-- The active basis after adding `t`: the elements whose leading monomial `t`'s divides are dropped. -/
def newAct (s : St) (t : Nat) : List Nat :=
  let lt := s.lead.getD t []
  (s.act.filter fun i => !mdvd lt (s.lead.getD i [])) ++ [t]

/-- The update after adding the basis element `t` (the basis and `found` are unchanged). -/
def update (s : St) (t : Nat) : St := ⟨s.basis, s.lead, s.sugar, newAct s t, newPairs s t, s.found⟩

/-- Is `h` a constant that is not zero modulo `p`? -/
def isUnitPoly (p : Nat) : Poly Nat → Bool
  | [(a, m)] => a % p != 0 && m.all (· == 0)
  | _ => false

/-- Add a (reduced, nonzero) polynomial with its sugar to the basis and update the pairs. -/
def addPoly (p : Nat) (s : St) (h : Poly Nat) (sg : Nat) : St :=
  let h := monic p h
  match h with
  | [] => s
  | (_, m) :: _ =>
    let t := s.basis.size
    let s' : St := ⟨s.basis.push h, s.lead.push m, s.sugar.push sg, s.act, s.pairs, s.found || isUnitPoly p h⟩
    update s' t

/-- One step: take the first pair, reduce its S-polynomial, add the remainder if it is not zero. -/
def step (p rfuel : Nat) (s : St) : St :=
  match s.pairs with
  | [] => s
  | q :: qs =>
    let s : St := ⟨s.basis, s.lead, s.sugar, s.act, qs, s.found⟩
    let h := reduceAux p s.basis s.lead s.act rfuel (spoly p (s.basis.getD q.i []) (s.basis.getD q.j [])) []
    match h with
    | [] => s
    | _ => addPoly p s h q.sugar

/-- Run at most `fuel` steps, stopping when a nonzero constant is found or no pair is left. -/
def loop (p rfuel : Nat) : Nat → St → St
  | 0, s => s
  | fuel + 1, s => if s.found || s.pairs.isEmpty then s else loop p rfuel fuel (step p rfuel s)

/-- Reduce the coefficients modulo `p`, drop zeros, pad the monomials to length `n` and sort. -/
def prep (p n : Nat) (f : Poly Nat) : Poly Nat :=
  ((f.map fun t => (t.1 % p, pad n t.2)).filter fun t => t.1 != 0).mergeSort fun t u => !grevGt u.2 t.2

/-- The initial state: the input polynomials added one by one (each fully reduced by the previous ones). -/
def init (p n rfuel : Nat) (F : List (Poly Nat)) : St :=
  F.foldl (fun s f =>
    let f := prep p n f
    let h := reduceAux p s.basis s.lead s.act rfuel f []
    match h with
    | [] => s
    | (_, m) :: _ => addPoly p s h (mdeg m))
    ⟨#[], #[], #[], [], [], false⟩

/-- The final state of a run. -/
def run (p n fuel rfuel : Nat) (F : List (Poly Nat)) : St := loop p rfuel fuel (init p n rfuel F)

/-- **The test**: the engine finds a nonzero constant in the ideal generated by `F` over `ℤ/p`. -/
def unitTest (p n fuel rfuel : Nat) (F : List (Poly Nat)) : Bool := (run p n fuel rfuel F).found

end Lean6.Special.Comp.GB
