/-!
# Labelled diagrams and the rules (E1)–(E6), (C1)–(C4)

Proposition 3.1 of the paper counts the labelled diagrams on six bodies that satisfy the combinatorial parts of the
rules (E1)–(E6) and (C1)–(C4) of Lemma 2.11 in both colours. This file defines labelled diagrams on `n` bodies and
these rules as computable Boolean functions, written from the statements of Lemma 2.11 with explicit quantifiers over
the bodies. Rules (E3) and (E6) are reduced to their statements on the kinds of the edges, as in Proposition 3.1.

* The bodies are `0, …, n - 1`. A *pair* `{a, b}` (`a ≠ b`) has a *position* (`pos`, `ppos`): the pairs in the
  order of their positions are `01, 02, 12, 03, 13, 23, 04, …`, ordered by the larger body, then by the smaller.
* A labelled diagram (`Diagram`) is coded by three natural numbers: the *edge code* `e`, whose digit in base 4 at the
  position of a pair is its *kind* (`0` none, `1` `z`, `2` `w`, `3` `zw`), and the circle masks `zc`, `wc`, whose bit
  `k` says whether the body `k` is `z`-circled, `w`-circled. The labelled diagrams on `n` bodies are the codes with
  `e < 4 ^ numPairs n` and `zc, wc < 2 ^ n` (`inRange`).
* A pair is a `z`-stroke if its kind is `z` or `zw`, a `w`-stroke if its kind is `w` or `zw`, and an edge if its kind
  is not `0`.
* `rulesZ n e c` is the conjunction of (E1)–(E6) and (C1)–(C4) as stated in the lemma (colour `z`), for the edge code
  `e` and the `z`-circle mask `c`. The exchange of the colours (`swapE`) exchanges the kinds `z` and `w` and the two
  circle masks, so the rules "with `z` and `w` exchanged" are `rulesZ n (swapE n e) wc`, and
  `okRules n d = rulesZ n d.e d.zc && rulesZ n (swapE n d.e) d.wc`.

No library beyond the core of Lean is used; `native_decide` evaluates these functions as compiled code.
-/

namespace L6F1

/-! ## Positions of pairs and digit codes -/

/-- The position of the pair `{a, b}` of bodies with `a < b`: `b (b - 1) / 2 + a`. -/
def pos (a b : Nat) : Nat := b * (b - 1) / 2 + a

/-- The position of the pair `{a, b}`, `a ≠ b`, given in either order. -/
def ppos (a b : Nat) : Nat := if a < b then pos a b else pos b a

/-- The number of pairs of `n` bodies, `n (n - 1) / 2`. -/
def numPairs (n : Nat) : Nat := n * (n - 1) / 2

/-- The pairs `(a, b)` with `a < b < n`, in the order of their positions. -/
def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun b => (List.range b).map fun a => (a, b)

/-- The pair `(a, b)`, `a < b`, at the position `i` (the inverse of `pos`). -/
def pairAt (i : Nat) : Nat × Nat := go (i + 1) 0 i
where
  /-- The pair at the position `pos 0 (b + 1) + r`, found within `fuel` steps. -/
  go : Nat → Nat → Nat → Nat × Nat
    | 0, _, _ => (0, 0)
    | fuel + 1, b, r => if r < b + 1 then (r, b + 1) else go fuel (b + 1) (r - (b + 1))

/-- `Σ_{i < m} g i * base ^ i`: the number with the digits `g 0, g 1, …, g (m - 1)` in base `base`. -/
def digitsVal (base : Nat) (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => digitsVal base g m + g m * base ^ m

/-- The digit at the position `i` of `e` in base 4. -/
def digit (e i : Nat) : Nat := e / 4 ^ i % 4

/-- Bit `k` of `c`. -/
def bit (c k : Nat) : Bool := c / 2 ^ k % 2 == 1

/-- `digit` computed with a shift (used by the compiler in place of `digit`, see `digit_eq_digitShift`). -/
def digitShift (e i : Nat) : Nat := (e >>> (2 * i)) % 4

/-- `bit` computed with a shift (used by the compiler in place of `bit`, see `bit_eq_bitShift`). -/
def bitShift (c k : Nat) : Bool := (c >>> k) % 2 == 1

/-- The compiled code computes `digit` by a shift: the two functions are equal. -/
@[csimp] theorem digit_eq_digitShift : @digit = @digitShift := by
  funext e i
  show e / 4 ^ i % 4 = (e >>> (2 * i)) % 4
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- The compiled code computes `bit` by a shift: the two functions are equal. -/
@[csimp] theorem bit_eq_bitShift : @bit = @bitShift := by
  funext c k
  show (c / 2 ^ k % 2 == 1) = ((c >>> k) % 2 == 1)
  rw [Nat.shiftRight_eq_div_pow]

/-! ## Labelled diagrams -/

/-- A labelled diagram: the edge code `e` (the kind of the pair at the position `i` is the digit `i` of `e` in base
4: `0` none, `1` `z`, `2` `w`, `3` `zw`), the `z`-circle mask `zc` and the `w`-circle mask `wc` (bit `k`: the body `k`
is circled). -/
structure Diagram where
  /-- The edge code. -/
  e : Nat
  /-- The `z`-circled bodies, as a bit mask. -/
  zc : Nat
  /-- The `w`-circled bodies, as a bit mask. -/
  wc : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `d` is a labelled diagram on `n` bodies: its codes are below `4 ^ numPairs n`, `2 ^ n`, `2 ^ n`. -/
def inRange (n : Nat) (d : Diagram) : Bool :=
  d.e < 4 ^ numPairs n && d.zc < 2 ^ n && d.wc < 2 ^ n

/-- The kind of the pair `{a, b}` in the edge code `e`: `0` (none), `1` (`z`), `2` (`w`) or `3` (`zw`); `0` if
`a = b`. -/
def kind (e a b : Nat) : Nat := if a = b then 0 else digit e (ppos a b)

/-- `ab` is a `z`-stroke: its kind is `z` or `zw`. -/
def zStroke (e a b : Nat) : Bool := kind e a b == 1 || kind e a b == 3

/-- `ab` is a `w`-stroke: its kind is `w` or `zw`. -/
def wStroke (e a b : Nat) : Bool := kind e a b == 2 || kind e a b == 3

/-- `ab` is an edge: a stroke of some colour. -/
def isEdge (e a b : Nat) : Bool := kind e a b != 0

/-- `ab` is a `zw`-edge. -/
def isZW (e a b : Nat) : Bool := kind e a b == 3

/-- The body `k` is circled in the circle mask `c`. -/
def circled (c k : Nat) : Bool := bit c k

/-- The edge code on `n` bodies whose pair `(a, b)`, `a < b`, has the kind `f a b`. -/
def codeOf (n : Nat) (f : Nat → Nat → Nat) : Nat :=
  digitsVal 4 (fun i => f (pairAt i).1 (pairAt i).2) (numPairs n)

/-- The circle mask on `n` bodies in which the body `k` is circled if and only if `f k`. -/
def maskOf (n : Nat) (f : Nat → Bool) : Nat := digitsVal 2 (fun k => if f k then 1 else 0) n

/-! ## The exchange of the colours and relabelling -/

/-- The exchange of the colours on a kind: `z ↔ w`, while none and `zw` are fixed. -/
def swapKind (v : Nat) : Nat := if v = 1 then 2 else if v = 2 then 1 else v

/-- The edge code with the colours exchanged. -/
def swapE (n e : Nat) : Nat := codeOf n fun a b => swapKind (kind e a b)

/-- The diagram with the colours exchanged: the kinds `z` and `w` and the two circle masks are exchanged. -/
def Diagram.swap (n : Nat) (d : Diagram) : Diagram := ⟨swapE n d.e, d.wc, d.zc⟩

/-- The diagram whose pair `{a, b}` has the kind of the pair `{τ a, τ b}` of `d` and whose body `k` has the circles of
the body `τ k` of `d`. If `τ` is the inverse of a permutation `σ` of the bodies, this is the image of `d` under the
relabelling `k ↦ σ k`. -/
def Diagram.relabel (n : Nat) (τ : Nat → Nat) (d : Diagram) : Diagram :=
  ⟨codeOf n (fun a b => kind d.e (τ a) (τ b)), maskOf n (fun k => circled d.zc (τ k)),
    maskOf n (fun k => circled d.wc (τ k))⟩

/-! ## Components -/

/-- At most `r` rounds of growth of the list of bodies `S`: each round adds the bodies `j < n` not in `S` that are
joined by a stroke to a body of `S` (`s a b` says that `ab` is a stroke), and the growth stops when a round adds
nothing. -/
def grow (n : Nat) (s : Nat → Nat → Bool) : Nat → List Nat → List Nat
  | 0, S => S
  | r + 1, S =>
    let N := (List.range n).filter fun j => !S.contains j && S.any fun i => s i j
    if N.isEmpty then S else grow n s r (S ++ N)

/-- The component of the body `k` in the graph of the strokes `s` on the bodies `0, …, n - 1`: the bodies reached from
`k` by at most `n` rounds of growth. (A round that adds nothing ends the growth, and each other round adds a body, so
`n` rounds reach every body joined to `k` by a walk of strokes; `L6Sound.F1.Component` proves that this is the
connected component.) -/
def component (n : Nat) (s : Nat → Nat → Bool) (k : Nat) : List Nat := grow n s n [k]

/-! ## The rules (Lemma 2.11), colour `z`

`e` is the edge code and `c` the mask of the `z`-circled bodies. Each hypothesis is placed right after the bodies it
involves, so that the compiled decision procedures stop early. The `Decidable` instances of the nested bounded
quantifiers are found by instance search (which needs a larger size bound than the default). -/

set_option synthInstance.maxSize 100000

/-- The number of `z`-strokes at the body `k`. -/
def zDeg (n e k : Nat) : Nat := (List.range n).countP fun l => l != k && zStroke e k l

/-- The number of `zw`-edges. -/
def numZW (n e : Nat) : Nat := (pairs n).countP fun p => isZW e p.1 p.2

/-- (E1) There is a `z`-stroke. -/
def ruleE1 (n e : Nat) : Bool :=
  decide (∃ a < n, ∃ b < n, a ≠ b ∧ zStroke e a b = true)

/-- (E2) If `ab` and `bc` are `zw`-edges, then `ac` is a `zw`-edge. -/
def ruleE2 (n e : Nat) : Bool :=
  decide (∀ a < n, ∀ b < n, a ≠ b → isZW e a b = true →
    ∀ c < n, c ≠ a → c ≠ b → isZW e b c = true → isZW e a c = true)

/-- (E3), on the kinds: the three edges of a triangle of edges have the same kind. -/
def ruleE3 (n e : Nat) : Bool :=
  decide (∀ a < n, ∀ b < n, a ≠ b → isEdge e a b = true →
    ∀ c < n, c ≠ a → c ≠ b → isEdge e b c = true → isEdge e a c = true →
    kind e a b = kind e b c ∧ kind e b c = kind e a c)

/-- (E4) From each `zw`-edge `ab` another `z`-stroke leaves `a` or `b`. -/
def ruleE4 (n e : Nat) : Bool :=
  decide (∀ a < n, ∀ b < n, a ≠ b → isZW e a b = true →
    ∃ c < n, c ≠ a ∧ c ≠ b ∧ (zStroke e a c = true ∨ zStroke e b c = true))

/-- (E5) The number of `zw`-edges is not `1`. -/
def ruleE5 (n e : Nat) : Bool := decide (numZW n e ≠ 1)

/-- (E6), on the kinds: if `ab`, `bc`, `cd` and `da` are edges, then `ab` and `cd` have the same kind, and so have
`bc` and `da`. -/
def ruleE6 (n e : Nat) : Bool :=
  decide (∀ a < n, ∀ b < n, a ≠ b → isEdge e a b = true →
    ∀ c < n, c ≠ a → c ≠ b → isEdge e b c = true →
    ∀ d < n, d ≠ a → d ≠ b → d ≠ c → isEdge e c d = true → isEdge e d a = true →
    kind e a b = kind e c d ∧ kind e b c = kind e d a)

/-- (C1) A body without a `z`-stroke is not `z`-circled, and a body with exactly one `z`-stroke is `z`-circled. -/
def ruleC1 (n e c : Nat) : Bool :=
  decide (∀ k < n, (zDeg n e k = 0 → circled c k = false) ∧ (zDeg n e k = 1 → circled c k = true))

/-- (C2) No `w`-stroke joins a `z`-circled body to a body that is not `z`-circled. -/
def ruleC2 (n e c : Nat) : Bool :=
  decide (∀ k < n, circled c k = true → ∀ l < n, l ≠ k → wStroke e k l = true → circled c l = true)

/-- (C3) If `k` is `z`-circled, some `z`-circled body of the `z`-component `K` of `k` lies outside the `w`-component
`L` of `k`. -/
def ruleC3 (n e c : Nat) : Bool :=
  decide (∀ k < n, circled c k = true →
    let K := component n (zStroke e) k
    let L := component n (wStroke e) k
    ∃ j < n, circled c j = true ∧ j ∈ K ∧ j ∉ L)

/-- (C4) If `k` and `j` are `z`-circled, `l` is not, and `kl` and `lj` are `z`-strokes, then `kj` is a `z`-stroke. -/
def ruleC4 (n e c : Nat) : Bool :=
  decide (∀ l < n, circled c l = false → ∀ k < n, k ≠ l → circled c k = true → zStroke e k l = true →
    ∀ j < n, j ≠ k → j ≠ l → circled c j = true → zStroke e l j = true → zStroke e k j = true)

/-- The rules (E1)–(E6) and (C1)–(C4) of Lemma 2.11 in the colour `z`, for the edge code `e` and the `z`-circle mask
`c`. -/
def rulesZ (n e c : Nat) : Bool :=
  ruleE1 n e && ruleE2 n e && ruleE3 n e && ruleE4 n e && ruleE5 n e && ruleE6 n e &&
    ruleC1 n e c && ruleC2 n e c && ruleC3 n e c && ruleC4 n e c

/-- **The rules in both colours**: the rules for `d`, and the same rules with `z` and `w` exchanged, that is, the rules
for the diagram with the colours exchanged. -/
def okRules (n : Nat) (d : Diagram) : Bool :=
  rulesZ n d.e d.zc && rulesZ n (swapE n d.e) d.wc

/-- The rules (E2), (E3), (E6), which involve only the kinds of the pairs (they are symmetric in the colours). -/
def edgeRules (n e : Nat) : Bool := ruleE2 n e && ruleE3 n e && ruleE6 n e

end L6F1
