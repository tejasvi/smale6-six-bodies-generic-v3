/-!
# Sparse polynomials over ℤ with packed exponents, and the cofactor certificates of Lemma 5.2

A polynomial is a list of terms `(key, c)`: `c` is a nonzero integer coefficient and the exponent of variable `i` is
byte `i` of the natural number `key`. Variables `0, …, 5` are the masses `m₀, …, m₅`, and variable `6 + j` is the
unknown `x_j` of a core. Multiplying two monomials adds their keys, provided no byte overflows; the checker requires
every exponent of every factor to be `< 128`. Normalization sorts by key and adds equal keys.

A certificate (format in `scripts/f4/README.md`) gives generators `gᵢ`, cofactors `cᵢ` and `h`; it is
accepted when `Σ cᵢ gᵢ − h` normalizes to the empty list, `h` involves only the masses, and `h` is nonzero at the
point `(3, 5, 7, 11, 13, 17)` (with `m_F = 1` when a mass `F` is fixed, in which case `m_F` occurs nowhere).
The meaning is proved in `L6Sound.Poly`.

This module is the shared interface of the polynomial code (used by the certificate checks and by the links of the
cores to the cells); its definitions are kept stable.
-/

namespace L6.Poly

/-- A sparse polynomial: `(key, coefficient)` terms. -/
abbrev Poly := List (Nat × Int)

/-- Exponent of variable `i` in a key. -/
@[inline] def keyExp (key i : Nat) : Nat := (key >>> (8 * i)) % 256

/-- The key of a monomial given by `(variable, exponent)` pairs (exponents of repeated variables add up). -/
def packExp (es : List (Nat × Nat)) : Nat := es.foldl (fun acc ve => acc + ve.2 * 256 ^ ve.1) 0

/-- Every exponent of the key is `< 128` among the first `nv` variables, and the key has no other bytes. -/
def keyBounded (nv key : Nat) : Bool :=
  decide (key < 256 ^ nv) && (List.range nv).all fun i => decide (keyExp key i < 128)

/-- Adds the coefficients of runs of equal keys of a list sorted by key and drops zero coefficients
(accumulator `acc` in reverse order; tail recursive). -/
def combineRev (k : Nat) (c : Int) (acc : Poly) : Poly → Poly
  | [] => if c = 0 then acc else (k, c) :: acc
  | u :: rest =>
    if u.1 = k then combineRev k (c + u.2) acc rest
    else combineRev u.1 u.2 (if c = 0 then acc else (k, c) :: acc) rest

/-- See `combineRev`. -/
def combineSorted : Poly → Poly
  | [] => []
  | t :: rest => (combineRev t.1 t.2 [] rest).reverse

/-- The normal form: sorted by key, equal keys merged, no zero coefficient. -/
def normalize (p : Poly) : Poly := combineSorted (p.mergeSort fun a b => decide (a.1 ≤ b.1))

/-- Terms multiplied pairwise (not normalized). -/
def mulRaw (p q : Poly) : Poly := p.flatMap fun a => q.map fun b => (a.1 + b.1, a.2 * b.2)

def mul (p q : Poly) : Poly := normalize (mulRaw p q)

def add (p q : Poly) : Poly := normalize (p ++ q)

def neg (p : Poly) : Poly := p.map fun t => (t.1, -t.2)

def smul (c : Int) (p : Poly) : Poly := normalize (p.map fun t => (t.1, c * t.2))

/-- A normalized polynomial from terms `(c, [(variable, exponent)])`. -/
def ofTerms (ts : List (Int × List (Nat × Nat))) : Poly := normalize (ts.map fun t => (packExp t.2, t.1))

/-- Set variable `v` to `1`. -/
def substOne (v : Nat) (p : Poly) : Poly := normalize (p.map fun t => (t.1 - keyExp t.1 v * 256 ^ v, t.2))

/-- Value at an integer point (`pt[i]` for variable `i`, missing entries `0`), over the variables `0 … nv-1`. -/
def evalAt (nv : Nat) (pt : Array Int) (p : Poly) : Int :=
  p.foldl (fun acc t => acc + t.2 * (List.range nv).foldl (fun m i => m * pt.getD i 0 ^ keyExp t.1 i) 1) 0

/-! ## Certificates -/

structure Cert where
  nvar : Nat
  fixed : Int
  gens : List Poly
  cofs : List Poly
  h : Poly
  deriving Inhabited

/-- Tokens of the certificate text: unsigned decimal numbers with an optional `-`, and words. -/
inductive Tok where
  | num (z : Int)
  | word (s : String)
  | eof
  deriving Inhabited, BEq

/-- The next token at byte position `i` and the position after it. -/
def nextTok (b : ByteArray) (i0 : Nat) : Tok × Nat := Id.run do
  let mut i := i0
  -- skip blanks
  while i < b.size && (b[i]! == 32 || b[i]! == 10 || b[i]! == 13 || b[i]! == 9) do
    i := i + 1
  if i ≥ b.size then return (.eof, i)
  let c := b[i]!
  if c == 45 || (48 ≤ c && c ≤ 57) then
    let neg := c == 45
    if neg then i := i + 1
    let mut v : Nat := 0
    while i < b.size && 48 ≤ b[i]! && b[i]! ≤ 57 do
      v := v * 10 + (b[i]! - 48).toNat
      i := i + 1
    return (.num (if neg then -(v : Int) else v), i)
  let j0 := i
  while i < b.size && !(b[i]! == 32 || b[i]! == 10 || b[i]! == 13 || b[i]! == 9) do
    i := i + 1
  return (.word (String.fromUTF8! (b.extract j0 i)), i)

/-- Reads `count` terms `c e0 … e5 k v1 a1 … vk ak` from position `i`; variables are shifted by `6`. -/
def readTerms (b : ByteArray) (i0 count : Nat) : Option (Poly × Nat) := Id.run do
  let mut i := i0
  let mut out : Poly := []
  for _ in [0:count] do
    let (t, i1) := nextTok b i
    let .num c := t | return none
    i := i1
    let mut key : Nat := 0
    for v in [0:6] do
      let (t, i2) := nextTok b i
      let .num e := t | return none
      if e < 0 then return none
      key := key + e.toNat * 256 ^ v
      i := i2
    let (t, i3) := nextTok b i
    let .num k := t | return none
    i := i3
    for _ in [0:k.toNat] do
      let (t, i4) := nextTok b i
      let .num v := t | return none
      let (t', i5) := nextTok b i4
      let .num e := t' | return none
      if v < 0 || e < 0 then return none
      key := key + e.toNat * 256 ^ (6 + v.toNat)
      i := i5
    out := (key, c) :: out
  return some (out.reverse, i)

/-- Expects the word `w` at position `i`. -/
def expectWord (b : ByteArray) (i : Nat) (w : String) : Option Nat :=
  match nextTok b i with
  | (.word s, j) => if s == w then some j else none
  | _ => none

/-- Expects a number at position `i`. -/
def expectNum (b : ByteArray) (i : Nat) : Option (Int × Nat) :=
  match nextTok b i with
  | (.num z, j) => some (z, j)
  | _ => none

/-- Reads `count` blocks `tag idx T` + terms, with `idx = 0, 1, …`. -/
def readBlocks (b : ByteArray) (i0 : Nat) (tag : String) (count : Nat) : Option (List Poly × Nat) := Id.run do
  let mut i := i0
  let mut out : List Poly := []
  for idx in [0:count] do
    let some i1 := expectWord b i tag | return none
    let some (k, i2) := expectNum b i1 | return none
    if k != idx then return none
    let some (t, i3) := expectNum b i2 | return none
    if t < 0 then return none
    let some (p, i4) := readTerms b i3 t.toNat | return none
    out := p :: out
    i := i4
  return some (out.reverse, i)

/-- Parses a certificate text. -/
def parseCert (s : String) : Option Cert := do
  let b := s.toUTF8
  let i ← expectWord b 0 "L6CERT"
  let (ver, i) ← expectNum b i
  if ver != 1 then none
  let i ← expectWord b i "nmass"
  let (nm, i) ← expectNum b i
  if nm != 6 then none
  let i ← expectWord b i "nvar"
  let (nv, i) ← expectNum b i
  let i ← expectWord b i "fixed"
  let (fx, i) ← expectNum b i
  let i ← expectWord b i "ngens"
  let (g, i) ← expectNum b i
  if nv < 0 || g < 0 then none
  let (gens, i) ← readBlocks b i "gen" g.toNat
  let (cofs, i) ← readBlocks b i "cof" g.toNat
  let i ← expectWord b i "h"
  let (t, i) ← expectNum b i
  if t < 0 then none
  let (h, i) ← readTerms b i t.toNat
  match nextTok b i with
  | (.eof, _) => some { nvar := nv.toNat, fixed := fx, gens, cofs, h }
  | _ => none

/-- The evaluation point of `h`: `(3, 5, 7, 11, 13, 17)`, with `m_F = 1` if `F ≥ 0`. -/
def hPoint (fixed : Int) : Array Int :=
  let base : Array Int := #[3, 5, 7, 11, 13, 17]
  if 0 ≤ fixed && fixed < 6 then base.set! fixed.toNat 1 else base

/-- The check of a parsed certificate: sizes; all keys bounded (exponents `< 128` in `6 + nvar` variables); if a
mass `F` is fixed, it occurs nowhere; `h` involves only masses; `Σ cᵢ gᵢ − h` normalizes to `[]`; `h ≠ 0` at
`hPoint`. -/
def checkParsed (c : Cert) : Bool :=
  let nv := 6 + c.nvar
  let all := c.gens ++ c.cofs ++ [c.h]
  c.gens.length == c.cofs.length &&
  decide (-1 ≤ c.fixed ∧ c.fixed < 6) &&
  all.all (fun p => p.all fun t => keyBounded nv t.1) &&
  (decide (c.fixed < 0) || all.all (fun p => p.all fun t => keyExp t.1 c.fixed.toNat == 0)) &&
  c.h.all (fun t => decide (t.1 < 256 ^ 6)) &&
  (normalize ((List.zipWith mulRaw c.cofs c.gens).flatten ++ neg c.h)).isEmpty &&
  evalAt 6 (hPoint c.fixed) c.h != 0

/-- Parse and check a certificate text. -/
def checkCert (s : String) : Bool :=
  match parseCert s with
  | some c => checkParsed c
  | none => false

end L6.Poly
