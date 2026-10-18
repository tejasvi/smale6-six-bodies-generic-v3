import Lean6.Special.Comp.Poly
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# An F4 engine over `ℤ/p` whose basis is sound by construction (no Mathlib)

**Keys.** A monomial in the variables `x₀, …, x_{n−1}` of total degree at most `L = 31` is the natural number
`key = deg · Bⁿ + Σᵢ (L − eᵢ) Bⁱ` with `B = 32` (`encK`; the digit of `xᵢ` sits at position `i`). For such keys the
order of the natural numbers is the degree reverse lexicographic order of msolve (first variable largest; at equal
degree the monomial with the smaller exponent at the last differing variable is larger), and the product of two
monomials is `a + b − (Bⁿ − 1)` as long as the degrees add up to at most `L` (`shiftS` checks it).

**Soundness by construction.** Polynomials are `SPoly` (parallel arrays of keys and coefficients modulo `p`), rows of
a matrix are `CRow` (column indices into an array `cols` of keys, and coefficients). Every polynomial or row that the
engine keeps carries a proof of the inductive predicate `Good`, whose constructors are exactly the operations allowed
to create them: an input, a monomial multiple (`shiftS`), a scalar multiple (`scaleS`, `scaleR`), the conversion of a
polynomial into a row (`toColImpl`, all-or-nothing) and back (`decodeV`, all-or-nothing on the validity of the keys),
and the reduction of a row by rows (`reduceC`, a dense accumulator). The engine itself (pair selection, criteria,
symbolic preprocessing, the choice of pivots, the order of the work) only decides which of these operations to apply;
it may be `partial`, since its results are values of subtypes. `Lean6.Special.D88.Count.F4Sound` proves that a
`Good` polynomial vanishes at every common zero of the inputs in every commutative `ZMod p`-algebra.
-/

namespace Lean6.Special.Comp.Count

open Lean6.Special.Comp

/-! ## Keys -/

/-- The digit base. -/
def B : Nat := 32

/-- The largest digit, and the largest total degree of a key. -/
def L : Nat := 31

/-- The low part of the key of an exponent list: `Σ (L − eᵢ) Bⁱ`. -/
def encLow : List Nat → Nat
  | [] => 0
  | a :: e => (L - a) + B * encLow e

/-- The key of an exponent list (of length `n`). -/
def encK (n : Nat) (e : List Nat) : Nat := e.sum * B ^ n + encLow e

/-- The exponent of the variable `i` in the key `k`. -/
def expK (k i : Nat) : Nat := L - k / B ^ i % B

/-- The exponent list of a key. -/
def decK (n k : Nat) : List Nat := (List.range n).map (expK k)

/-- A valid key: the key of its own exponents, of total degree at most `L`. -/
def validK (n k : Nat) : Bool := decide (k / B ^ n ≤ L) && encK n (decK n k) == k

/-! ## Polynomials and rows -/

/-- A polynomial: keys and coefficients modulo `p` (parallel arrays). -/
structure SPoly where
  keys : Array Nat
  coefs : Array Nat
deriving Inhabited, DecidableEq, Repr

/-- A row of a matrix: column indices and coefficients. -/
structure CRow where
  idx : Array Nat
  coef : Array Nat
deriving Inhabited, DecidableEq, Repr

/-- The zero polynomial. -/
def SPoly.zero : SPoly := ⟨#[], #[]⟩

/-- The zero row. -/
def CRow.zero : CRow := ⟨#[], #[]⟩

/-- **Monomial multiple**: `x^m · f`, if `m` is valid and every degree stays at most `L`; else `0`. -/
def shiftS (n Bn m : Nat) (f : SPoly) : SPoly :=
  if validK n m && f.keys.all (fun k => k / Bn + m / Bn ≤ L) then
    ⟨f.keys.map (fun k => k + m - (Bn - 1)), f.coefs⟩
  else SPoly.zero

/-- **Scalar multiple** of a polynomial. -/
def scaleS (p c : Nat) (f : SPoly) : SPoly := ⟨f.keys, f.coefs.map (fun a => a * c % p)⟩

/-- **Scalar multiple** of a row. -/
def scaleR (p c : Nat) (r : CRow) : CRow := ⟨r.idx, r.coef.map (fun a => a * c % p)⟩

/-- The polynomial of a row: the terms whose column index is in range. -/
def decodeCAux (cols : Array Nat) (r : CRow) (k : Nat) (ks cs : Array Nat) : SPoly :=
  if h : k < r.idx.size then
    let j := r.idx[k]
    if hj : j < cols.size then decodeCAux cols r (k + 1) (ks.push cols[j]) (cs.push (r.coef.getD k 0))
    else decodeCAux cols r (k + 1) ks cs
  else ⟨ks, cs⟩
termination_by r.idx.size - k

/-- The polynomial of a row. -/
def decodeC (cols : Array Nat) (r : CRow) : SPoly := decodeCAux cols r 0 #[] #[]

/-- **Row to polynomial**, all or nothing: the polynomial of the row if all its keys are valid, else `0`. -/
def decodeV (n : Nat) (cols : Array Nat) (r : CRow) : SPoly :=
  let f := decodeC cols r
  if f.keys.all (validK n) then f else SPoly.zero

/-- Whether `cols[idx[k]] = keys[k]` for all `k ≥ k₀` (and the sizes agree). -/
def colsMatch (cols idx keys : Array Nat) (k : Nat) : Bool :=
  if h : k < idx.size then
    (cols[idx[k]]? == keys[k]?) && colsMatch cols idx keys (k + 1)
  else true
termination_by idx.size - k

/-- **Polynomial to row**, all or nothing: the column indices `look k` of the keys, if they point to the keys; else the
zero row. -/
def toColImpl (cols : Array Nat) (look : Nat → Nat) (f : SPoly) : CRow :=
  let idx := f.keys.map look
  if idx.size == f.coefs.size && colsMatch cols idx f.keys 0 then ⟨idx, f.coefs⟩ else CRow.zero

/-! ## Dense reduction -/

/-- `acc[idx[k]] := acc[idx[k]] + c · coef[k]`, for `k ≥ k₀` (indices out of range are skipped). The entries are not
reduced modulo `p` here: the reduction reads them modulo `p`. -/
def addMulAux (c : Nat) (idx coef : Array Nat) (k : Nat) (acc : Array Nat) : Array Nat :=
  if h : k < idx.size then
    let j := idx[k]
    let acc := if hj : j < acc.size then acc.set j (acc[j] + c * coef.getD k 0) hj else acc
    addMulAux c idx coef (k + 1) acc
  else acc
termination_by idx.size - k

/-- `acc[idx[k]] := acc[idx[k]] + coef[k]` modulo `p`, for `k ≥ k₀`. -/
def addRowAux (p : Nat) (idx coef : Array Nat) (k : Nat) (acc : Array Nat) : Array Nat :=
  if h : k < idx.size then
    let j := idx[k]
    let acc := if hj : j < acc.size then acc.set j ((acc[j] + coef.getD k 0 % p) % p) hj else acc
    addRowAux p idx coef (k + 1) acc
  else acc
termination_by idx.size - k

/-- The dense vector of a row (length `ncols`). -/
def toDense (p ncols : Nat) (r : CRow) : Array Nat := addRowAux p r.idx r.coef 0 (Array.replicate ncols 0)

/-- Reduce the dense vector by the pivot rows, column by column from `j`: at a column with an entry `a ≠ 0` modulo `p`
and a pivot row `q`, add `(p − a) · q` (that is, subtract `a · q` modulo `p`). -/
def reduceDenseAux (p : Nat) (pivs : Array (Option CRow)) (ncols : Nat) (j : Nat) (acc : Array Nat) : Array Nat :=
  if j < ncols then
    let v := acc.getD j 0
    if v == 0 || v % p == 0 then reduceDenseAux p pivs ncols (j + 1) acc
    else
      let a := v % p
      match pivs[j]? with
      | some (some q) => reduceDenseAux p pivs ncols (j + 1) (addMulAux (p - a) q.idx q.coef 0 acc)
      | _ => reduceDenseAux p pivs ncols (j + 1) acc
  else acc
termination_by ncols - j

/-- The sparse row of a dense vector (nonzero entries modulo `p`). -/
def toSparseAux (p : Nat) (acc : Array Nat) (j : Nat) (is cs : Array Nat) : CRow :=
  if h : j < acc.size then
    let v := acc[j]
    if v == 0 || v % p == 0 then toSparseAux p acc (j + 1) is cs
    else toSparseAux p acc (j + 1) (is.push j) (cs.push (v % p))
  else ⟨is, cs⟩
termination_by acc.size - j

/-- **Reduction of a row** by the pivot rows (from the column `start`). -/
def reduceC (p ncols : Nat) (pivs : Array (Option CRow)) (start : Nat) (r : CRow) : CRow :=
  toSparseAux p (reduceDenseAux p pivs ncols start (toDense p ncols r)) 0 #[] #[]

/-! ## The certificate predicate -/

/-- The objects of the engine: a polynomial, or a row with its array of column keys. -/
inductive Obj where
  | abs (f : SPoly)
  | row (cols : Array Nat) (r : CRow)

/-- **Derivable objects.** Every constructor is one operation of the engine; `F` is the list of inputs. -/
inductive Good (n Bn p : Nat) (F : List SPoly) : Obj → Prop
  | zero : Good n Bn p F (.abs SPoly.zero)
  | input {f : SPoly} : f ∈ F → Good n Bn p F (.abs f)
  | shift {f : SPoly} (m : Nat) : Good n Bn p F (.abs f) → Good n Bn p F (.abs (shiftS n Bn m f))
  | scaleA {f : SPoly} (c : Nat) : Good n Bn p F (.abs f) → Good n Bn p F (.abs (scaleS p c f))
  | ofRow {cols : Array Nat} {r : CRow} : Good n Bn p F (.row cols r) → Good n Bn p F (.abs (decodeV n cols r))
  | ofAbs {f : SPoly} (cols : Array Nat) (look : Nat → Nat) :
      Good n Bn p F (.abs f) → Good n Bn p F (.row cols (toColImpl cols look f))
  | reduce {cols : Array Nat} (pivs : Array (Option CRow)) (start : Nat) {r : CRow} :
      (∀ (j : Nat) (q : CRow), pivs[j]? = some (some q) → Good n Bn p F (.row cols q)) →
      Good n Bn p F (.row cols r) → Good n Bn p F (.row cols (reduceC p cols.size pivs start r))
  | scaleR {cols : Array Nat} {r : CRow} (c : Nat) :
      Good n Bn p F (.row cols r) → Good n Bn p F (.row cols (scaleR p c r))

/-- A derivable polynomial. -/
abbrev BPoly (n Bn p : Nat) (F : List SPoly) := {f : SPoly // Good n Bn p F (.abs f)}

/-- A derivable row. -/
abbrev BRow (n Bn p : Nat) (F : List SPoly) (cols : Array Nat) := {r : CRow // Good n Bn p F (.row cols r)}

instance {n Bn p : Nat} {F : List SPoly} : Inhabited (BPoly n Bn p F) := ⟨⟨SPoly.zero, Good.zero⟩⟩

/-- A table of derivable pivot rows, indexed by column. -/
structure PivTab (n Bn p : Nat) (F : List SPoly) (cols : Array Nat) where
  tab : Array (Option CRow)
  inv : ∀ (j : Nat) (q : CRow), tab[j]? = some (some q) → Good n Bn p F (.row cols q)

/-- The empty table. -/
def PivTab.empty {n Bn p : Nat} {F : List SPoly} {cols : Array Nat} (sz : Nat) : PivTab n Bn p F cols :=
  ⟨Array.replicate sz none, by
    intro j q h
    rw [Array.getElem?_replicate] at h
    split at h <;> simp at h⟩

/-- Insert a pivot row. -/
def PivTab.insert {n Bn p : Nat} {F : List SPoly} {cols : Array Nat} (P : PivTab n Bn p F cols) (j : Nat)
    (q : BRow n Bn p F cols) : PivTab n Bn p F cols :=
  ⟨P.tab.setIfInBounds j (some q.1), by
    intro j' q' h
    rw [Array.getElem?_setIfInBounds] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        rw [← h]
        exact q.2
      · simp at h
    · exact P.inv j' q' h⟩

/-- **Reduce a derivable row** by a table of derivable pivot rows. -/
def reduceB {n Bn p : Nat} {F : List SPoly} {cols : Array Nat} (P : PivTab n Bn p F cols) (start : Nat)
    (r : BRow n Bn p F cols) : BRow n Bn p F cols :=
  ⟨reduceC p cols.size P.tab start r.1, Good.reduce P.tab start P.inv r.2⟩

/-! ## Fast monomial arithmetic (untrusted: only for decisions) -/

/-- The digit of the variable `i`. -/
@[inline] def dig (k i : Nat) : Nat := (k >>> (5 * i)) &&& 31

/-- `a ∣ b` for valid keys (every exponent of `a` at most that of `b`). -/
def divK (n a b : Nat) : Bool := go 0
where
  go (i : Nat) : Bool := if i < n then decide (dig b i ≤ dig a i) && go (i + 1) else true
  termination_by n - i

/-- A divisibility mask: bit `i` for `eᵢ ≥ 1`, bit `n + i` for `eᵢ ≥ 2`, bit `2n + i` for `eᵢ ≥ 4`. -/
def maskK (n k : Nat) : Nat := go 0 0
where
  go (i acc : Nat) : Nat :=
    if i < n then
      let d := dig k i
      let acc := if d < 31 then acc ||| (1 <<< i) else acc
      let acc := if d < 30 then acc ||| (1 <<< (n + i)) else acc
      let acc := if d < 28 then acc ||| (1 <<< (2 * n + i)) else acc
      go (i + 1) acc
    else acc
  termination_by n - i

/-- The least common multiple of two valid keys. -/
def lcmK (n Bn a b : Nat) : Nat := go 0 0 0
where
  go (i low deg : Nat) : Nat :=
    if i < n then
      let d := min (dig a i) (dig b i)
      go (i + 1) (low + (d <<< (5 * i))) (deg + (31 - d))
    else deg * Bn + low
  termination_by n - i

/-- Coprime valid keys (no variable in both). -/
def coprimeK (n a b : Nat) : Bool := go 0
where
  go (i : Nat) : Bool := if i < n then (dig a i == 31 || dig b i == 31) && go (i + 1) else true
  termination_by n - i

/-- The key of `b / a` (for `a ∣ b`). -/
@[inline] def quoK (Bn a b : Nat) : Nat := b + (Bn - 1) - a

/-- Inverse modulo a prime `p` (Fermat). -/
def invMod (p a : Nat) : Nat := go 64 1 (a % p) (p - 2)
where
  go : Nat → Nat → Nat → Nat → Nat
    | 0, r, _, _ => r
    | fuel + 1, r, b, e => if e == 0 then r else go fuel (if e % 2 == 1 then r * b % p else r) (b * b % p) (e / 2)

/-! ## Inputs and outputs -/

/-- The key of a monomial of a list polynomial (exponents beyond `n` must be zero). -/
def monoKey (n : Nat) (m : Mono) : Nat := encK n ((List.range n).map (fun i => m.getD i 0))

/-- **An input polynomial as a key polynomial**: normalized, coefficients reduced, sorted by decreasing key; `0` if some
monomial is not valid (degree above `L` or a variable beyond `n`). -/
def encodeInput (n p : Nat) (f : Poly Nat) : SPoly :=
  let g := Poly.normalize (modC p) f
  let ok := g.all (fun t => validK n (monoKey n t.2) && (t.2.drop n).all (· == 0))
  if ok then
    let ts := (g.map (fun t => (monoKey n t.2, t.1 % p))).mergeSort (fun a b => decide (b.1 ≤ a.1))
    ⟨(ts.map Prod.fst).toArray, (ts.map Prod.snd).toArray⟩
  else SPoly.zero

/-- A key polynomial as a list polynomial (exponent lists of length `n`). -/
def toPolyS (n : Nat) (f : SPoly) : Poly Nat :=
  (List.range f.keys.size).map (fun t => (f.coefs.getD t 0, decK n (f.keys.getD t 0)))

/-! ## The engine (untrusted control) -/

/-- A critical pair: indices, lcm key, its degree and mask. -/
structure Pair where
  i : Nat
  j : Nat
  lcm : Nat
  deg : Nat
  mask : Nat
deriving Inhabited

/-- Statistics of a run. -/
structure Stats where
  steps : Nat := 0
  rows : Nat := 0
  cols : Nat := 0
  zero : Nat := 0
  added : Nat := 0
  maxMatrix : Nat × Nat := (0, 0)
  /-- the number of batches of the echelon forms -/
  batches : Nat := 0
  /-- the largest number of columns of the rows left after the reduction by the basis multiples -/
  maxCols2 : Nat := 0
deriving Inhabited, Repr

/-- The state of the engine. -/
structure St (n Bn p : Nat) (F : List SPoly) where
  basis : Array (BPoly n Bn p F)
  lead : Array Nat
  mask : Array Nat
  active : Array Bool
  pairs : Array Pair
  stats : Stats

instance {n Bn p : Nat} {F : List SPoly} : Inhabited (St n Bn p F) := ⟨⟨#[], #[], #[], #[], #[], {}⟩⟩

section Engine

variable {n Bn p : Nat} {F : List SPoly}

/-- Add a nonzero monic derivable polynomial (keys sorted decreasingly) to the basis: the update of Gebauer and Möller
(chain criterion through the minimal quotient monomials, product criterion, criterion B on the old pairs). -/
def addElem (st : St n Bn p F) (f : BPoly n Bn p F) : St n Bn p F := Id.run do
  let t := st.basis.size
  let lt := f.1.keys[0]!
  let mt := maskK n lt
  -- candidate pairs with the active elements, by quotient monomial u = lcm / lt
  let mut cand : Array (Nat × Nat × Nat) := #[]   -- (u, i, lcm)
  for i in [0:t] do
    if st.active[i]! then
      let li := st.lead[i]!
      let l := lcmK n Bn li lt
      cand := cand.push (quoK Bn lt l, i, l)
  cand := cand.qsort (fun a b => a.1 < b.1)
  let mut kept : Array (Nat × Nat × Nat × Nat) := #[]   -- (u, mask u, i, lcm)
  for c in cand do
    let u := c.1
    let mu := maskK n u
    let mut red := false
    for k in kept do
      if (k.2.1 &&& mu) == k.2.1 && divK n k.1 u then
        red := true
        break
    if !red then kept := kept.push (u, mu, c.2.1, c.2.2)
  let mut pairs : Array Pair := #[]
  -- criterion B on the old pairs
  for q in st.pairs do
    let drop := (mt &&& q.mask) == mt && divK n lt q.lcm &&
      lcmK n Bn st.lead[q.i]! lt != q.lcm && lcmK n Bn st.lead[q.j]! lt != q.lcm
    if !drop then pairs := pairs.push q
  for k in kept do
    let i := k.2.2.1
    if !coprimeK n st.lead[i]! lt then
      let l := k.2.2.2
      pairs := pairs.push ⟨i, t, l, l / Bn, maskK n l⟩
  let mut active := st.active
  for i in [0:t] do
    if active[i]! then
      let li := st.lead[i]!
      if (mt &&& st.mask[i]!) == mt && divK n lt li then active := active.set! i false
  return { basis := st.basis.push f, lead := st.lead.push lt, mask := st.mask.push mt, active := active.push true,
           pairs := pairs, stats := { st.stats with added := st.stats.added + 1 } }

/-- Make a nonzero derivable polynomial monic. -/
def monicB (f : BPoly n Bn p F) : BPoly n Bn p F :=
  ⟨scaleS p (invMod p (f.1.coefs[0]!)) f.1, Good.scaleA _ f.2⟩

/-- An active basis element whose leading key divides `m`. -/
def findReducer (st : St n Bn p F) (m : Nat) : Option Nat := Id.run do
  let mm := maskK n m
  for i in [0:st.basis.size] do
    if st.active[i]! then
      let mi := st.mask[i]!
      if (mi &&& mm) == mi && divK n st.lead[i]! m then return some i
  return none

/-- The row `x^mult · basis[g]` as a derivable row of the matrix with columns `cols`. -/
def mkRow (st : St n Bn p F) (cols : Array Nat) (look : Nat → Nat) (g mult : Nat) : BRow n Bn p F cols :=
  let f := st.basis[g]!
  let fs : BPoly n Bn p F := ⟨shiftS n Bn mult f.1, Good.shift mult f.2⟩
  ⟨toColImpl cols look fs.1, Good.ofAbs cols look fs.2⟩

/-- `f` on `chunks` consecutive parts of an array, in parallel, concatenated. -/
def parChunks {α β : Type} (chunks : Nat) (xs : Array α) (f : Array α → Array β) : Array β :=
  if chunks ≤ 1 || xs.size < 2 * chunks then f xs
  else
    let sz := (xs.size + chunks - 1) / chunks
    let tasks := (List.range chunks).map (fun c =>
      Task.spawn (prio := Task.Priority.dedicated) (fun _ => f (xs.extract (c * sz) ((c + 1) * sz))))
    tasks.foldl (fun acc tk => acc ++ tk.get) #[]

/-- A map over an array in `chunks` parallel chunks. -/
def parMap {α β : Type} (chunks : Nat) (xs : Array α) (f : α → β) : Array β :=
  parChunks chunks xs (fun part => part.map f)

/-- The column indices of the keys (every task builds its own map, which keeps the lookups free of shared reference
counts). -/
def colMap (cols : Array Nat) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for j in [0:cols.size] do
    m := m.insert cols[j]! j
  return m

/-- The matrix of a step: the pivot of each key that has one (basis element and multiplier), the rows to reduce and
the columns (all keys, decreasing). -/
structure Sym where
  pivOf : Std.HashMap Nat (Nat × Nat)
  toRed : Array (Nat × Nat)
  cols : Array Nat

/-- The pairs of least degree (normal strategy), and the others. -/
def selectPairs (st : St n Bn p F) : Array Pair × Array Pair :=
  let d := st.pairs.foldl (fun m q => min m q.deg) (st.pairs[0]?.map (·.deg) |>.getD 0)
  (st.pairs.filter (·.deg == d), st.pairs.filter (·.deg != d))

/-- **Symbolic preprocessing**: the rows of the pairs, and a pivot row for every key of the matrix that a leading key
of the basis divides. -/
def symbolic (st : St n Bn p F) (sel : Array Pair) : Sym := Id.run do
  let C := Bn - 1
  -- symbolic preprocessing
  let mut pivOf : Std.HashMap Nat (Nat × Nat) := {}
  let mut seen : Std.HashSet Nat := {}
  let mut toRed : Array (Nat × Nat) := #[]
  let mut monos : Std.HashSet Nat := {}
  let mut queue : Array Nat := #[]
  for q in sel do
    let mi := quoK Bn st.lead[q.i]! q.lcm
    let mj := quoK Bn st.lead[q.j]! q.lcm
    let ci := mi * 1048576 + q.i
    let cj := mj * 1048576 + q.j
    -- the row of i: pivot of the lcm if it has none, else a row to reduce
    if !seen.contains ci then
      seen := seen.insert ci
      if !pivOf.contains q.lcm then pivOf := pivOf.insert q.lcm (q.i, mi)
      else toRed := toRed.push (q.i, mi)
      for k in st.basis[q.i]!.1.keys do
        let m := k + mi - C
        if !monos.contains m then
          monos := monos.insert m
          queue := queue.push m
    if !seen.contains cj then
      seen := seen.insert cj
      if !pivOf.contains q.lcm then pivOf := pivOf.insert q.lcm (q.j, mj)
      else toRed := toRed.push (q.j, mj)
      for k in st.basis[q.j]!.1.keys do
        let m := k + mj - C
        if !monos.contains m then
          monos := monos.insert m
          queue := queue.push m
  let mut qi := 0
  while qi < queue.size do
    let m := queue[qi]!
    qi := qi + 1
    if !pivOf.contains m then
      match findReducer st m with
      | some g =>
        let mult := quoK Bn st.lead[g]! m
        pivOf := pivOf.insert m (g, mult)
        for k in st.basis[g]!.1.keys do
          let m' := k + mult - C
          if !monos.contains m' then
            monos := monos.insert m'
            queue := queue.push m'
      | none => pure ()
  return ⟨pivOf, toRed, queue.qsort (fun a b => b < a)⟩

/-- The pivot rows, built in parallel. -/
def pivRows (chunks : Nat) (st : St n Bn p F) (cols : Array Nat) (pivOf : Std.HashMap Nat (Nat × Nat)) :
    PivTab n Bn p F cols := Id.run do
  let piv := parChunks chunks pivOf.toArray (fun part =>
    let m := colMap cols
    let look : Nat → Nat := fun k => m.getD k 0
    part.map (fun mg => (look mg.1, mkRow st cols look mg.2.1 mg.2.2)))
  let mut P : PivTab n Bn p F cols := PivTab.empty cols.size
  for jr in piv do
    if jr.2.1.idx.size > 0 then P := P.insert jr.1 jr.2
  return P

/-- The rows to reduce, built and reduced by the pivot rows, in parallel. -/
def reduceRows {cols : Array Nat} (chunks : Nat) (st : St n Bn p F) (P : PivTab n Bn p F cols)
    (toRed : Array (Nat × Nat)) : Array (BRow n Bn p F cols) :=
  parChunks chunks toRed (fun part =>
    let m := colMap cols
    let look : Nat → Nat := fun k => m.getD k 0
    part.map (fun gm =>
      let r := mkRow st cols look gm.1 gm.2
      reduceB P (r.1.idx.getD 0 0) r))

/-- **Echelon form** of the reduced rows: the new basis elements, the number of rows reduced to zero, the number of
batches and the number of columns left. The nonzero rows are moved to the columns that occur in them (far fewer: the
columns of the basis multiples are gone) and sorted by leading column. They are processed in batches: the rows of a
batch are reduced by all pivots found so far (in parallel), then one by one by the pivots found in the batch; a
nonzero result becomes a (monic) pivot. The new pivots are finally reduced by the others beyond their leading column
(in parallel). -/
def echelon (chunks : Nat) (cols : Array Nat) (red : Array (BRow n Bn p F cols)) :
    Array (BPoly n Bn p F) × Nat × Nat × Nat := Id.run do
  let nzr := red.filter (fun r => r.1.idx.size > 0)
  let mut zeros := red.size - nzr.size
  let mut mark : Array Bool := Array.replicate cols.size false
  for r in nzr do
    for j in r.1.idx do
      mark := mark.set! j true
  let mut cols2 : Array Nat := #[]
  for j in [0:cols.size] do
    if mark[j]! then cols2 := cols2.push cols[j]!
  let rows2 := parChunks chunks nzr (fun part =>
    let m := colMap cols2
    let look : Nat → Nat := fun k => m.getD k 0
    part.map (fun r =>
      let f : BPoly n Bn p F := ⟨decodeV n cols r.1, Good.ofRow r.2⟩
      (⟨toColImpl cols2 look f.1, Good.ofAbs cols2 look f.2⟩ : BRow n Bn p F cols2)))
  let srt := (rows2.filter (fun r => r.1.idx.size > 0)).qsort (fun a b => a.1.idx[0]! < b.1.idx[0]!)
  zeros := zeros + (rows2.size - srt.size)
  let mut P2 : PivTab n Bn p F cols2 := PivTab.empty cols2.size
  let mut lead : Array (BRow n Bn p F cols2) := #[]
  let bsz := max 1 (4 * chunks)
  let nb := (srt.size + bsz - 1) / bsz
  for b in [0:nb] do
    let red1 := parMap chunks (srt.extract (b * bsz) ((b + 1) * bsz)) (fun r => reduceB P2 (r.1.idx.getD 0 0) r)
    let mut Pb : PivTab n Bn p F cols2 := PivTab.empty cols2.size
    let mut nPb := 0
    for r in red1 do
      let r2 := if r.1.idx.size > 0 && nPb > 0 then reduceB Pb (r.1.idx.getD 0 0) r else r
      if r2.1.idx.size > 0 then
        let c := invMod p (r2.1.coef[0]!)
        let r3 : BRow n Bn p F cols2 := ⟨scaleR p c r2.1, Good.scaleR c r2.2⟩
        Pb := Pb.insert (r3.1.idx[0]!) r3
        nPb := nPb + 1
        P2 := P2.insert (r3.1.idx[0]!) r3
        lead := lead.push r3
      else zeros := zeros + 1
  let newPolys := parMap chunks lead (fun r =>
    let r' := reduceB P2 (r.1.idx.getD 0 0 + 1) r
    (⟨decodeV n cols2 r'.1, Good.ofRow r'.2⟩ : BPoly n Bn p F))
  return (newPolys, zeros, nb, cols2.size)

/-- The state after a step: the statistics, and the new basis elements added one by one. -/
def finish (st : St n Bn p F) (S : Sym) (newPolys : Array (BPoly n Bn p F)) (zeros batches ncols2 : Nat) :
    St n Bn p F := Id.run do
  let nrows := S.pivOf.size + S.toRed.size
  let mut st := { st with stats := { st.stats with
    steps := st.stats.steps + 1, rows := st.stats.rows + nrows, zero := st.stats.zero + zeros,
    cols := max st.stats.cols S.cols.size, batches := st.stats.batches + batches,
    maxCols2 := max st.stats.maxCols2 ncols2,
    maxMatrix := if nrows > st.stats.maxMatrix.1 then (nrows, S.cols.size) else st.stats.maxMatrix } }
  for f in newPolys do
    if f.1.keys.size > 0 then st := addElem st f
  return st

/-- **One F4 step**: the pairs of least degree, symbolic preprocessing, reduction, echelon form, new basis
elements. -/
def step (chunks : Nat) (st : St n Bn p F) : St n Bn p F :=
  if st.pairs.isEmpty then st
  else
    let (sel, rest) := selectPairs st
    let st := { st with pairs := rest }
    let S := symbolic st sel
    let P := pivRows chunks st S.cols S.pivOf
    let red := reduceRows chunks st P S.toRed
    let (newPolys, zeros, batches, ncols2) := echelon chunks S.cols red
    finish st S newPolys zeros batches ncols2

/-- Run the steps until no pair is left (at most `fuel` steps). -/
def loop (chunks : Nat) : Nat → St n Bn p F → St n Bn p F
  | 0, st => st
  | fuel + 1, st => if st.pairs.isEmpty then st else loop chunks fuel (step chunks st)

/-- The initial state: the inputs, made monic, added one by one. -/
def init (inputs : List SPoly) (hin : ∀ f ∈ inputs, f ∈ F) : St n Bn p F :=
  let bs : List (BPoly n Bn p F) := inputs.attach.map (fun f => ⟨f.1, Good.input (hin f.1 f.2)⟩)
  bs.foldl (fun st f => if f.1.keys.size > 0 then addElem st (monicB f) else st) default

end Engine

/-- The configuration of a run. -/
structure Cfg where
  /-- the number of variables (at most `11`) -/
  n : Nat
  /-- the prime -/
  p : Nat
  /-- the number of parallel chunks for the reduction -/
  chunks : Nat := 1
  /-- the maximal number of steps -/
  fuel : Nat := 100000

/-- `B ^ n`. -/
def Cfg.Bn (c : Cfg) : Nat := B ^ c.n

/-- The encoded inputs. -/
def encInputs (c : Cfg) (F : List (Poly Nat)) : List SPoly := F.map (encodeInput c.n c.p)

/-- **The final state of a run** on the list polynomials `F`. -/
def f4State (c : Cfg) (F : List (Poly Nat)) : St c.n c.Bn c.p (encInputs c F) :=
  loop c.chunks c.fuel (init (encInputs c F) (fun _ h => h))

/-- **The output basis**: the active elements, as list polynomials whose terms are sorted by decreasing keys (strictly
decreasing in the degree reverse lexicographic order `Comp.Count.grevGtStd`). -/
def f4Basis (c : Cfg) (F : List (Poly Nat)) : List (Poly Nat) :=
  let st := f4State c F
  ((List.range st.basis.size).filter (fun i => st.active.getD i false)).map
    (fun i => toPolyS c.n (st.basis.getD i default).1)

/-- Whether the run finished (no pair left). -/
def f4Done (c : Cfg) (F : List (Poly Nat)) : Bool := (f4State c F).pairs.isEmpty

end Lean6.Special.Comp.Count
