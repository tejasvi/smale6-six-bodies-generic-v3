/-!
# Cofactor certificates modulo a prime, checked by the kernel (Lemma 7.9)

For `decide +kernel`: natural-number arithmetic only (accelerated in the kernel), explicit recursors, data in packed
literals. A polynomial is a list of terms `(key, c)`, the exponent of variable `i` in byte `i` of the key (`KPoly`).

A certificate gives generators `gᵢ` and `h` and cofactors `cᵢ`, each cofactor stored as a list of *pieces*; a piece is
a polynomial split into its positive and its negative part (lists of terms with natural coefficients). The identity
`Σᵢ cᵢ gᵢ ≡ h (mod p)` (coefficient by coefficient) is checked in *buckets*: a bucket names a list of products, each the
product of a term `j` of a generator `i` with a piece `q` of the cofactor `i` (a code `(i, j, q)`), and a part of `h`;
its check (`bucketOKp`) is that, after merging,
  `Σ (products with sign +) + (part of h)⁻ + (p − 1) · (Σ (products with sign −) + (part of h)⁺)`
has all its coefficients divisible by `p`. Over all buckets, every code must occur exactly once (`coverOK`: the sorted
codes are the list of all codes) and the parts of `h` must make up `h` (`hOK`). The checks are those of the F4 kernel
modules of `lean6` (`L6K.F4`), with the comparison of a bucket taken modulo `p`; the soundness (`L6SoundKSpec.C4Cert`)
uses only the checks: the cofactor `cᵢ` is the sum of its pieces.
-/

namespace L6KSpec.C4

/-- A packed polynomial: terms `(key, c)`, the exponent of variable `i` in byte `i` of the key. -/
abbrev KPoly := List (Nat × Int)

/-- Terms `(key, c)` with natural coefficients. -/
abbrev NTerms := List (Nat × Nat)

/-- A polynomial with integer coefficients as its positive and its negative part. -/
structure Piece where
  pos : NTerms
  neg : NTerms

noncomputable section

/-- Records of `RB` bits, `c` of them, low record first, put in front of `acc`. Binary splitting keeps the
copies of big numbers small. The first argument is fuel for the depth. -/
def decode (RB : Nat) : Nat → Nat → Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat → List Nat)
    (fun c n acc =>
      Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ acc => acc)
        (fun _ ih n acc => (n % 2 ^ RB) :: ih (n / 2 ^ RB) acc) c n acc)
    (fun _ ih c n acc =>
      let h := c / 2
      Bool.rec
        (ih h (n % 2 ^ (h * RB)) (ih (c - h) (n / 2 ^ (h * RB)) acc))
        (Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ acc => acc)
          (fun _ ih n acc => (n % 2 ^ RB) :: ih (n / 2 ^ RB) acc) c n acc)
        (Nat.ble c 8))

/-- The terms of `cnt` records `key + c · 2^KB` of `KB + CB` bits packed in `n`. -/
def terms (KB CB cnt n : Nat) : NTerms :=
  (decode (KB + CB) 40 cnt n []).map fun r => (r % 2 ^ KB, r / 2 ^ KB)

/-- The codes of a bucket: `cnt` records of 32 bits packed in `n`. -/
def codesOf (cnt n : Nat) : List Nat := decode 32 40 cnt n []

/-- Bit 7 of each of the bytes `0, …, nv - 1`. -/
def guardMask : Nat → Nat
  | 0 => 0
  | n + 1 => guardMask n ||| 2 ^ (8 * n + 7)

/-- Every key has the bits of `G` clear. -/
def guards (G : Nat) : NTerms → Bool :=
  List.rec true fun t _ ih => Bool.rec false ih (Nat.beq (Nat.land t.1 G) 0)

/-- The product of the monomial `c · X^k` with a term list: shift every key by `k`, scale by `c`. -/
def shift (k c : Nat) : NTerms → NTerms :=
  List.rec [] fun t _ ih => (t.1 + k, t.2 * c) :: ih

/-- Merge of two term lists (equal keys add); the first argument is fuel, at least the total length. -/
def merge : Nat → NTerms → NTerms → NTerms :=
  Nat.rec (motive := fun _ => NTerms → NTerms → NTerms)
    (fun a b => a ++ b)
    (fun _ ih a b =>
      List.rec (motive := fun _ => NTerms) b
        (fun x a' _ =>
          List.rec (motive := fun _ => NTerms) a
            (fun y b' _ =>
              Bool.rec
                (Bool.rec ((y.1, y.2) :: ih a b') ((x.1, x.2 + y.2) :: ih a' b') (Nat.beq x.1 y.1))
                ((x.1, x.2) :: ih a' b)
                (Nat.blt x.1 y.1))
            b)
        a)

/-- One round of pairwise merges of a list of term lists. -/
def mergeRound (f : Nat) : List NTerms → List NTerms
  | a :: b :: rest => merge f a b :: mergeRound f rest
  | l => l

/-- `R` rounds of pairwise merges, then the rest merged in a row. -/
def mergeAll (f : Nat) : Nat → List NTerms → NTerms :=
  Nat.rec (motive := fun _ => List NTerms → NTerms)
    (fun ls => ls.foldr (merge f) [])
    (fun _ ih ls => ih (mergeRound f ls))

/-- Every coefficient is divisible by `p`. -/
def zeroMod (p : Nat) : NTerms → Bool :=
  List.rec true fun t _ ih => Nat.beq (t.2 % p) 0 && ih

/-- Entry `i` of a list, or `d`. -/
def nth {α : Type} (d : α) : List α → Nat → α :=
  List.rec (fun _ => d) fun x _ ih i => Nat.rec x (fun j _ => ih j) i

/-- The code of the product of term `j` of generator `i` with piece `q` of cofactor `i` (`j < 64`, `q < 2^20`). -/
def code (i j q : Nat) : Nat := i * 2 ^ 26 + j * 2 ^ 20 + q

/-- The generator term of a code. -/
def genTerm (gens : List KPoly) (t : Nat) : Nat × Int := nth (0, 0) (nth [] gens (t / 2 ^ 26)) (t / 2 ^ 20 % 64)

/-- The cofactor piece of a code. -/
def piece (pcs : List (List Piece)) (t : Nat) : Piece := nth ⟨[], []⟩ (nth [] pcs (t / 2 ^ 26)) (t % 2 ^ 20)

/-- The keys of the generator term and of the piece of a code have the bits of `G` clear. -/
def codeOK (G : Nat) (gens : List KPoly) (pcs : List (List Piece)) (t : Nat) : Bool :=
  Nat.beq (Nat.land (genTerm gens t).1 G) 0 && guards G (piece pcs t).pos && guards G (piece pcs t).neg

/-- The products of the codes, on the side of their sign: `(products with sign +, products with sign −)`. -/
def sides (gens : List KPoly) (pcs : List (List Piece)) : List Nat → List NTerms × List NTerms :=
  List.rec ([], []) fun t _ ih =>
    Int.rec (motive := fun _ => List NTerms × List NTerms)
      (fun c => (shift (genTerm gens t).1 c (piece pcs t).pos :: ih.1, shift (genTerm gens t).1 c (piece pcs t).neg :: ih.2))
      (fun c => (shift (genTerm gens t).1 (c + 1) (piece pcs t).neg :: ih.1,
        shift (genTerm gens t).1 (c + 1) (piece pcs t).pos :: ih.2))
      (genTerm gens t).2

/-- **The check of a bucket modulo `p`**: the keys are guarded and, after merging (fuel `F`, `R` rounds of pairwise
merges), `Σ products⁺ + h⁻ + (p − 1) (Σ products⁻ + h⁺)` has all its coefficients divisible by `p`. -/
def bucketOKp (p G F R : Nat) (gens : List KPoly) (pcs : List (List Piece)) (ts : List Nat) (hp : Piece) : Bool :=
  ts.all (codeOK G gens pcs) &&
    zeroMod p (mergeAll F R ((hp.neg :: (sides gens pcs ts).1) ++
      (hp.pos :: (sides gens pcs ts).2).map (shift 0 (p - 1))))

/-- All codes, in increasing order. -/
def allCodes (gens : List KPoly) (pcs : List (List Piece)) : List Nat :=
  (List.range gens.length).flatMap fun i =>
    (List.range (nth [] gens i).length).flatMap fun j =>
      (List.range (nth [] pcs i).length).map fun q => code i j q

/-- Merge of two lists (fuel: at least the total length): if `x ≤ y` then `x` first. -/
def mergeR : Nat → List Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat → List Nat)
    (fun a b => a ++ b)
    (fun _ ih a b =>
      List.rec (motive := fun _ => List Nat) b
        (fun x a' _ =>
          List.rec (motive := fun _ => List Nat) a
            (fun y b' _ => Bool.rec (y :: ih a b') (x :: ih a' b) (Nat.ble x y)) b)
        a)

/-- Merge sort with fuel `d` for the depth (`2^d` at least the length). -/
def msortR : Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat)
    (fun l => l)
    (fun _ ih l =>
      List.rec (motive := fun _ => List Nat) []
        (fun x t _ =>
          List.rec (motive := fun _ => List Nat) [x]
            (fun _ _ _ => mergeR l.length (ih (l.take (l.length / 2))) (ih (l.drop (l.length / 2)))) t)
        l)

/-- **Every product occurs exactly once**: the generators have at most 64 terms, the cofactors at most `2^20`
pieces, and the codes of the buckets, sorted (fuel `D`), are all codes. -/
def coverOK (D : Nat) (gens : List KPoly) (pcs : List (List Piece)) (ts : List Nat) : Bool :=
  gens.all (fun g => Nat.ble g.length 64) && pcs.all (fun l => Nat.ble l.length (2 ^ 20)) &&
    msortR D ts == allCodes gens pcs

/-- `lo ≤ c < hi`, with `hi = 0` for no upper end. -/
def inIvl (lo hi c : Nat) : Bool := decide (lo ≤ c) && (hi == 0 || decide (c < hi))

/-- The intervals start at `lo`, each ends where the next starts, and the last has no upper end. -/
def chainOK : Nat → List (Nat × Nat) → Bool
  | _, [] => false
  | lo, [(a, b)] => a == lo && b == 0
  | lo, (a, b) :: rest => a == lo && decide (a < b) && chainOK b rest

/-- On `[lo, hi)`: the sorted codes of `C` are the sorted codes of `R`. -/
def ivlCheck (C R : List Nat) (lo hi : Nat) : Bool :=
  msortR 20 (C.filter (inIvl lo hi)) == msortR 20 (R.filter (inIvl lo hi))

/-- **Every product occurs exactly once**, the codes compared interval by interval (one kernel declaration per
interval): the generators have at most 64 terms, the cofactors at most `2^20` pieces, and the intervals `L` cover ℕ
(`ivlCheck` on each is checked apart). -/
def coverHead (gens : List KPoly) (pcs : List (List Piece)) (L : List (Nat × Nat)) : Bool :=
  gens.all (fun g => Nat.ble g.length 64) && pcs.all (fun l => Nat.ble l.length (2 ^ 20)) && chainOK 0 L

/-- The code of a signed term (injective for coefficients `|c| < 2^CB`). -/
def termCode (CB k : Nat) (c : Int) : Nat :=
  k * 2 ^ (CB + 1) + Int.rec (motive := fun _ => Nat) (fun n => 2 * n) (fun n => 2 * n + 1) c

/-- The signed terms of a piece. -/
def signed (P : Piece) : KPoly :=
  P.pos.map (fun t => (t.1, (t.2 : Int))) ++ P.neg.map (fun t => (t.1, -(t.2 : Int)))

/-- **The parts of `h` make up `h`**: the sorted codes of their signed terms are those of `h`, all coefficients
below `2^CB` in absolute value. -/
def hOK (CB D : Nat) (h : KPoly) (parts : List Piece) : Bool :=
  let ps := parts.flatMap signed
  (ps ++ h).all (fun t => Nat.blt t.2.natAbs (2 ^ CB)) &&
    msortR D (ps.map fun t => termCode CB t.1 t.2) == msortR D (h.map fun t => termCode CB t.1 t.2)

end

end L6KSpec.C4
