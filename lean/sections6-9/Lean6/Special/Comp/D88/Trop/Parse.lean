import Lean6.Special.Comp.D88.Trop.Check

/-!
# Lemma 6.19(a): reading the data (no Mathlib)

The data are strings of decimal tokens separated by spaces (written by `gen/d88trop/emit.py`). The readers are total
functions (structural recursion on a fuel argument), so every statement about their output has a definite meaning;
what they read is then checked by the checkers of `Check`, whose soundness does not depend on the readers.

Formats (all numbers decimal, `-` for negative integers):
* monomial: `n v₁ e₁ … vₙ eₙ` (sparse exponents);
* polynomial: `t` then `t` terms `c monomial`;
* `GPoly`: `t` then `t` terms `monomial polynomial` (the `ξ`-monomial and its coefficient in the masses);
* node: `E u y` | `S g i j node node node` | `F g n f₁ … fₙ eqcerts strictcerts node` | `M` | `L k (pos poly)* poly`
  | `N cert¹⁷`, with sparse vectors `n k₁ c₁ … kₙ cₙ`, an equality certificate `k sparse`, a strict certificate
  `z sparse sparse` (for `S`, then for `E`).
-/

namespace Lean6.Special.Comp.D88.Trop

open Lean6.Special.Comp

/-- The tokens of a string. -/
def tokens (s : String) : List String := (s.splitOn " ").filter fun t => !t.isEmpty && t != "\n"

/-- An integer token. -/
def tokInt (t : String) : Int := (t.trimAscii.toString.toInt?).getD 0

/-- A natural-number token. -/
def tokNat (t : String) : Nat := (t.trimAscii.toString.toNat?).getD 0

/-- Read `n` items with a reader. -/
def readN {α : Type} (rd : List String → Option (α × List String)) : Nat → List String → Option (List α × List String)
  | 0, ts => some ([], ts)
  | n + 1, ts => do
    let (a, ts) ← rd ts
    let (as, ts) ← readN rd n ts
    pure (a :: as, ts)

/-- A natural number. -/
def rdNat : List String → Option (Nat × List String)
  | t :: ts => some (tokNat t, ts)
  | [] => none

/-- An integer. -/
def rdInt : List String → Option (Int × List String)
  | t :: ts => some (tokInt t, ts)
  | [] => none

/-- A sparse monomial. -/
def rdMono (ts : List String) : Option (Mono × List String) := do
  let (n, ts) ← rdNat ts
  let (ps, ts) ← readN (fun ts => do let (v, ts) ← rdNat ts; let (e, ts) ← rdNat ts; pure ((v, e), ts)) n ts
  let len := ps.foldl (fun m ve => max m (ve.1 + 1)) 0
  pure ((List.range len).map (fun i => ps.foldl (fun acc ve => if ve.1 = i then acc + ve.2 else acc) 0), ts)

/-- A polynomial with integer coefficients. -/
def rdPolyZ (ts : List String) : Option (Poly Int × List String) := do
  let (n, ts) ← rdNat ts
  readN (fun ts => do let (c, ts) ← rdInt ts; let (m, ts) ← rdMono ts; pure ((c, m), ts)) n ts

/-- A polynomial with natural-number coefficients. -/
def rdPolyN (ts : List String) : Option (Poly Nat × List String) := do
  let (n, ts) ← rdNat ts
  readN (fun ts => do let (c, ts) ← rdNat ts; let (m, ts) ← rdMono ts; pure ((c, m), ts)) n ts

/-- A `GPoly`. -/
def rdGPoly (ts : List String) : Option (GPoly × List String) := do
  let (n, ts) ← rdNat ts
  readN (fun ts => do let (m, ts) ← rdMono ts; let (c, ts) ← rdPolyZ ts; pure ((m, c), ts)) n ts

/-- A sparse vector. -/
def rdSparse (ts : List String) : Option (List (Nat × Int) × List String) := do
  let (n, ts) ← rdNat ts
  readN (fun ts => do let (k, ts) ← rdNat ts; let (c, ts) ← rdInt ts; pure ((k, c), ts)) n ts

/-- An equality certificate. -/
def rdEq (ts : List String) : Option ((Int × List (Nat × Int)) × List String) := do
  let (k, ts) ← rdInt ts
  let (u, ts) ← rdSparse ts
  pure ((k, u), ts)

/-- A strict certificate. -/
def rdStrict (ts : List String) : Option ((Int × List (Nat × Int) × List (Nat × Int)) × List String) := do
  let (z, ts) ← rdInt ts
  let (y, ts) ← rdSparse ts
  let (u, ts) ← rdSparse ts
  pure ((z, y, u), ts)

/-- A node of the covering; `sz g` is the number of terms of polynomial `g` (needed to count the strict
certificates of a face). -/
def rdNode (sz : Nat → Nat) : Nat → List String → Option (Node × List String)
  | 0, _ => none
  | fuel + 1, t :: ts =>
    if t = "E" then do
      let (u, ts) ← rdSparse ts
      let (y, ts) ← rdSparse ts
      pure (.empty u y, ts)
    else if t = "S" then do
      let (g, ts) ← rdNat ts
      let (i, ts) ← rdNat ts
      let (j, ts) ← rdNat ts
      let (a, ts) ← rdNode sz fuel ts
      let (b, ts) ← rdNode sz fuel ts
      let (c, ts) ← rdNode sz fuel ts
      pure (.split g i j a b c, ts)
    else if t = "F" then do
      let (g, ts) ← rdNat ts
      let (n, ts) ← rdNat ts
      let (F, ts) ← readN rdNat n ts
      let (eqc, ts) ← readN rdEq (n - 1) ts
      let (strict, ts) ← readN rdStrict (sz g - n) ts
      let (child, ts) ← rdNode sz fuel ts
      pure (.face g F eqc strict child, ts)
    else if t = "M" then pure (.mono, ts)
    else if t = "L" then do
      let (k, ts) ← rdNat ts
      let (cofs, ts) ← readN (fun ts => do let (pos, ts) ← rdNat ts; let (q, ts) ← rdPolyN ts; pure ((pos, q), ts)) k ts
      let (r, ts) ← rdPolyN ts
      pure (.leaf cofs r, ts)
    else if t = "N" then do
      let (certs, ts) ← readN rdEq 17 ts
      pure (.nonneg certs, ts)
    else if t = "H" then do
      let (k, ts) ← rdNat ts
      pure (.hyp k, ts)
    else none
  | _ + 1, [] => none

/-- The covering tree of a string (the leaf `.mono` if the string does not parse). -/
def parseTree (Gb : List (Poly Nat)) (s : String) : Node :=
  let ts := tokens s
  match rdNode (fun g => (Gb.getD g []).length) (ts.length + 1) ts with
  | some (n, []) => n
  | _ => .mono

/-- A list of `GPoly`s. -/
def parseG (s : String) : List GPoly :=
  let ts := tokens s
  match rdNat ts with
  | some (n, ts) => match readN rdGPoly n ts with
    | some (gs, []) => gs
    | _ => []
  | none => []

/-- A list of lists of integer polynomials (`n` then `n` groups of `k` polynomials). -/
def parseCof (k : Nat) (s : String) : List (List (Poly Int)) :=
  let ts := tokens s
  match rdNat ts with
  | some (n, ts) => match readN (readN rdPolyZ k) n ts with
    | some (cs, []) => cs
    | _ => []
  | none => []

/-- A list of lists of polynomials over `ℤ/p` (`n`, then for each list its length and its polynomials). -/
def parseHyps (s : String) : List (List (Poly Nat)) :=
  let ts := tokens s
  match rdNat ts with
  | some (n, ts) => match readN (fun ts => do let (k, ts) ← rdNat ts; readN rdPolyN k ts) n ts with
    | some (hs, []) => hs
    | _ => []
  | none => []

/-- A list of integer polynomials. -/
def parsePolys (s : String) : List (Poly Int) :=
  let ts := tokens s
  match rdNat ts with
  | some (n, ts) => match readN rdPolyZ n ts with
    | some (ps, []) => ps
    | _ => []
  | none => []

end Lean6.Special.Comp.D88.Trop
