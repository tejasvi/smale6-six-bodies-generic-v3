/-!
# Complex balls in biased fixed point: the definitions the kernel evaluates

No Mathlib: the per-point checks import only this module and their data, so that a process starts small (README §17).
The semantics and the soundness theorems are in `Ball/Sem.lean` and the modules after it.

**Numbers.** A precision `P : ℕ` is fixed per computation. A biased natural `X` stands for the integer `X − B`,
`B = bias P = 2^(3P+1)`, and the real number `(X − B)/2^P`. All operations are straight-line natural arithmetic (the
kernel evaluates `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.pow` with GMP); a subtraction is
exact as long as the magnitudes stay below `smax P = 2^(3P)`, which the history field `s` certifies.

**Balls.** `CB`: the center `((re − B) + (im − B) i)/2^P`, one radius `r/2^P` for the real and the imaginary part, a bound
`a ≥ |re − B| + |im − B|` and a history bound `s`: the sum of the `a` and `s` of everything that went into the ball. A
checker asks `s ≤ smax P` of its final balls only.

**Fused sums of products** (`Acc`): `Σ x_i y_i + Σ z_j` is accumulated in four naturals (positive and negative parts of
the real and imaginary parts, at scale `2^{2P}`) and rounded once (`Acc.fin`).
-/

namespace Lean6.Special.Ball

/-- A complex ball (see the module docstring). -/
structure CB where
  re : Nat
  im : Nat
  r : Nat
  a : Nat
  s : Nat
deriving Repr, DecidableEq

section ops

variable (P : Nat)

/-- The bias `2^(3P+1)`. -/
def bias : Nat := Nat.pow 2 (Nat.add (Nat.mul 3 P) 1)

/-- The bound on the history field. -/
def smax : Nat := Nat.pow 2 (Nat.mul 3 P)

/-- The ball `{0}`. -/
def zero : CB := ⟨bias P, bias P, 0, 0, 0⟩

/-- The exact ball of an integer `c` (the center `c`, scaled by `2^P`). -/
def ofInt (c : Int) : CB :=
  match c with
  | .ofNat n => ⟨Nat.add (bias P) (Nat.shiftLeft n P), bias P, 0, Nat.shiftLeft n P, Nat.shiftLeft n P⟩
  | .negSucc n =>
    ⟨Nat.sub (bias P) (Nat.shiftLeft (Nat.succ n) P), bias P, 0, Nat.shiftLeft (Nat.succ n) P,
      Nat.shiftLeft (Nat.succ n) P⟩

/-- The ball `{1}`. -/
def one : CB := ofInt P 1

/-- The exact ball of a Gaussian integer `a + b i`. -/
def ofGauss (a b : Int) : CB :=
  ⟨(ofInt P a).re, (ofInt P b).re, 0, Nat.add (ofInt P a).a (ofInt P b).a, Nat.add (ofInt P a).a (ofInt P b).a⟩

/-- Sum. -/
def add (x y : CB) : CB :=
  ⟨Nat.sub (Nat.add x.re y.re) (bias P), Nat.sub (Nat.add x.im y.im) (bias P), Nat.add x.r y.r, Nat.add x.a y.a,
    Nat.add x.s y.s⟩

/-- Difference. -/
def sub (x y : CB) : CB :=
  ⟨Nat.sub (Nat.add x.re (bias P)) y.re, Nat.sub (Nat.add x.im (bias P)) y.im, Nat.add x.r y.r, Nat.add x.a y.a,
    Nat.add x.s y.s⟩

/-- Negation. -/
def neg (x : CB) : CB :=
  ⟨Nat.sub (Nat.mul 2 (bias P)) x.re, Nat.sub (Nat.mul 2 (bias P)) x.im, x.r, x.a, x.s⟩

/-- The accumulator of a fused sum `Σ x_i y_i + Σ z_j`: `pr − nr` and `pi − ni` are the real and imaginary parts of the sum,
scaled by `2^{2P}`; `r`, `a`, `s` accumulate the radius, magnitude and history terms. -/
structure Acc where
  pr : Nat
  nr : Nat
  pi : Nat
  ni : Nat
  r : Nat
  a : Nat
  s : Nat

/-- The empty sum. -/
def Acc.zero : Acc := ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- Add the product `x y`. -/
def Acc.mac (c : Acc) (x y : CB) : Acc :=
  ⟨Nat.add c.pr (Nat.add (Nat.mul x.re y.re) (Nat.mul (bias P) (Nat.add x.im y.im))),
   Nat.add c.nr (Nat.add (Nat.mul x.im y.im) (Nat.mul (bias P) (Nat.add x.re y.re))),
   Nat.add c.pi (Nat.add (Nat.add (Nat.mul x.re y.im) (Nat.mul x.im y.re)) (Nat.mul (Nat.mul 2 (bias P)) (bias P))),
   Nat.add c.ni (Nat.mul (bias P) (Nat.add (Nat.add x.re y.im) (Nat.add x.im y.re))),
   Nat.add c.r (Nat.add (Nat.add (Nat.mul x.a y.r) (Nat.mul x.r y.a)) (Nat.mul (Nat.mul 2 x.r) y.r)),
   Nat.add c.a (Nat.mul x.a y.a),
   Nat.add c.s (Nat.add x.s y.s)⟩

/-- Add the ball `z`. -/
def Acc.addB (c : Acc) (z : CB) : Acc :=
  ⟨Nat.add c.pr (Nat.shiftLeft z.re P), Nat.add c.nr (Nat.shiftLeft (bias P) P),
   Nat.add c.pi (Nat.shiftLeft z.im P), Nat.add c.ni (Nat.shiftLeft (bias P) P),
   Nat.add c.r (Nat.shiftLeft z.r P), Nat.add c.a (Nat.shiftLeft z.a P), Nat.add c.s z.s⟩

/-- The biased rounding `⌊(pr − nr)/2^P⌋ + B` of a sum held as `pr − nr` at scale `2^{2P}`. -/
def rnd (pr nr : Nat) : Nat := Nat.shiftRight (Nat.sub (Nat.add pr (Nat.shiftLeft (bias P) P)) nr) P

/-- Round the sum to a ball. -/
def Acc.fin (c : Acc) : CB :=
  ⟨rnd P c.pr c.nr, rnd P c.pi c.ni, Nat.add (Nat.shiftRight c.r P) 2, Nat.add (Nat.shiftRight c.a P) 2,
   Nat.add c.s (Nat.add (Nat.shiftRight c.a P) 2)⟩

/-- Product. -/
def mul (x y : CB) : CB := Acc.fin P (Acc.mac P Acc.zero x y)

/-- `Σ x_i y_i` into the accumulator (the shorter list decides the length). -/
def Acc.dot : Acc → List CB → List CB → Acc
  | c, x :: xs, y :: ys => Acc.dot (Acc.mac P c x y) xs ys
  | c, _, _ => c

/-- `Σ x_i y_i`. -/
def dot (xs ys : List CB) : CB := Acc.fin P (Acc.dot P Acc.zero xs ys)

/-- `|X − B|`. -/
def absB (X : Nat) : Nat := if Nat.ble (bias P) X then Nat.sub X (bias P) else Nat.sub (bias P) X

/-- The exact magnitude `|re − B| + |im − B|` as the bound `a`. -/
def tight (x : CB) : CB :=
  ⟨x.re, x.im, x.r, Nat.add (absB P x.re) (absB P x.im), Nat.add x.s (Nat.add (absB P x.re) (absB P x.im))⟩

/-- The center alone, as an exact ball with its exact magnitude. -/
def center (x : CB) : CB :=
  ⟨x.re, x.im, 0, Nat.add (absB P x.re) (absB P x.im), Nat.add (absB P x.re) (absB P x.im)⟩

/-- An upper bound of `|z|` (scaled) for `z` in the ball: `|re − B| + |im − B| + 2r`. -/
def magB (x : CB) : Nat := Nat.add (Nat.add (absB P x.re) (absB P x.im)) (Nat.mul 2 x.r)

/-- The history is small enough. -/
def okS (x : CB) : Bool := Nat.ble x.s (smax P)

/-- The ball does not contain `0` (and its history is small enough). -/
def excl0 (x : CB) : Bool :=
  okS P x && (Nat.blt x.r (absB P x.re) || Nat.blt x.r (absB P x.im))

end ops

/-! ## Truncated series: the coefficients `0, …, N` as a list -/

section ser

variable (P : Nat)

/-- The zero series of length `N + 1`. -/
def serZero (N : Nat) : List CB := List.replicate (Nat.succ N) (zero P)

/-- The series `1` of length `N + 1`. -/
def serOne (N : Nat) : List CB := one P :: List.replicate N (zero P)

/-- Coefficientwise sum. -/
def serAdd (S T : List CB) : List CB := List.zipWith (add P) S T

/-- The product, coefficients `0, …, N`. -/
def serMul (N : Nat) (S T : List CB) : List CB :=
  (List.range (Nat.succ N)).map fun k => dot P (S.take (Nat.succ k)) (T.take (Nat.succ k)).reverse

/-- The power `S^e`, coefficients `0, …, N`. -/
def serPow (N : Nat) (S : List CB) : Nat → List CB
  | 0 => serOne P N
  | Nat.succ e => serMul P N (serPow N S e) S

/-- A ball times a series. -/
def serScale (c : CB) (S : List CB) : List CB := S.map (mul P c)

end ser

/-! ## Polynomials in the eighteen coordinates with coefficients in `ℤ[m₁, …, m₅]` (degree at most one in the masses) -/

/-- A term `c · m · ∏ y_v^e`: `c` an integer, `m = 0` for no mass and `m = l + 1` for the mass `m_{l}` (`l < 5`), the
monomial as pairs (coordinate index, exponent); coordinate indices `0–3` are `u`, `4–7` `v`, `8–17` `p`. -/
structure Term where
  c : Int
  m : Nat
  mono : List (Nat × Nat)
deriving Repr, DecidableEq

/-- A polynomial as a list of terms. -/
abbrev MPoly := List Term

/-- Well-formed: coordinate indices below `18`, exponents positive, each coordinate at most once per monomial, mass
index at most `5`. -/
def Term.wf (t : Term) : Bool :=
  Nat.ble t.m 5 && t.mono.all (fun ve => Nat.blt ve.1 18 && Nat.blt 0 ve.2) &&
    (t.mono.map Prod.fst).Nodup

/-- Every term is well formed. -/
def MPoly.wf (p : MPoly) : Bool := p.all Term.wf

section eval

variable (P : Nat)

/-- The power table: for each coordinate series `S`, `[S, S², S³]`, coefficients `0, …, N`. -/
def powTab (N : Nat) (Ss : List (List CB)) : List (List (List CB)) :=
  Ss.map fun S => let S2 := serMul P N S S; [S, S2, serMul P N S2 S]

/-- `S_v^e` from the table (by repeated products beyond the cube). -/
def getPow (N : Nat) (Ss : List (List CB)) (pw : List (List (List CB))) (v e : Nat) : List CB :=
  if Nat.ble e 3 then (pw.getD v []).getD (Nat.sub e 1) (serZero P N)
  else serPow P N (Ss.getD v (serZero P N)) e

/-- The coefficient ball of a term. -/
def coefBall (masses : List CB) (t : Term) : CB :=
  if t.m == 0 then ofInt P t.c else mul P (ofInt P t.c) (masses.getD (Nat.sub t.m 1) (zero P))

/-- The series of a monomial. -/
def evalMono (N : Nat) (Ss : List (List CB)) (pw : List (List (List CB))) : List (Nat × Nat) → List CB
  | [] => serOne P N
  | ve :: rest => serMul P N (getPow P N Ss pw ve.1 ve.2) (evalMono N Ss pw rest)

/-- The series of a term. -/
def evalTerm (masses : List CB) (N : Nat) (Ss : List (List CB)) (pw : List (List (List CB))) (t : Term) : List CB :=
  serScale P (coefBall P masses t) (evalMono P N Ss pw t.mono)

/-- The series of a polynomial, coefficients `0, …, N`. -/
def evalPoly (masses : List CB) (N : Nat) (Ss : List (List CB)) (pw : List (List (List CB))) : MPoly → List CB
  | [] => serZero P N
  | t :: rest => serAdd P (evalTerm P masses N Ss pw t) (evalPoly masses N Ss pw rest)

end eval

/-- The derivative of a monomial in the coordinate `v`: the exponent of `v` and the monomial with that exponent lowered by
one (`none` if `v` does not occur). -/
def monoDeriv (v : Nat) : List (Nat × Nat) → Option (Nat × List (Nat × Nat))
  | [] => none
  | ve :: rest =>
    if ve.1 == v then some (ve.2, if ve.2 == 1 then rest else (ve.1, Nat.sub ve.2 1) :: rest)
    else match monoDeriv v rest with
      | none => none
      | some er => some (er.1, ve :: er.2)

/-- The derivative of a term in the coordinate `v` (`none` if `v` does not occur). -/
def Term.deriv (v : Nat) (t : Term) : Option Term :=
  match monoDeriv v t.mono with
  | none => none
  | some er => some ⟨t.c * (er.1 : Int), t.m, er.2⟩

/-- The derivative of a polynomial in the coordinate `v`. -/
def MPoly.deriv (v : Nat) (p : MPoly) : MPoly := p.filterMap (Term.deriv v)

/-! ## The weighted parts of the rows -/

/-- The part `G_{r,i}` of a row from its list of parts (`[]` if absent). -/
def partOf (rp : List (Nat × MPoly)) (i : Nat) : MPoly :=
  match rp.find? (fun ip => ip.1 == i) with
  | some ip => ip.2
  | none => []

section lift

variable (P : Nat)

/-- The Jacobian of the parts `G_{r,0}` at the balls `y0`: rows `rows`, columns `unk`. -/
def jacMat (masses : List CB) (parts : List (List (Nat × MPoly))) (y0 : List CB) (rows unk : List Nat) :
    List (List CB) :=
  let Ss := y0.map fun x => [x]
  let pw := powTab P 0 Ss
  rows.map fun r => unk.map fun c =>
    (evalPoly P masses 0 Ss pw (MPoly.deriv c (partOf (parts.getD r []) 0))).getD 0 (zero P)

/-- Matrix times vector (rows of balls). -/
def matVec (M : List (List CB)) (x : List CB) : List CB := M.map fun row => dot P row x

/-- The signed integer of a biased natural. -/
def sval (X : Nat) : Int := Int.subNatNat X (bias P)

/-- An approximate reciprocal of the center (not verified: used only to build the preconditioner). -/
def recipApprox (x : CB) : CB :=
  let a := sval P x.re
  let b := sval P x.im
  let d := a * a + b * b
  let k : Int := Int.ofNat (Nat.shiftLeft 1 (2 * P))
  let re := (a * k) / d
  let im := (-b * k) / d
  ⟨(re + Int.ofNat (bias P)).toNat, (im + Int.ofNat (bias P)).toNat, 0, re.natAbs + im.natAbs, 0⟩

/-- Swap the rows `i` and `k`. -/
def swapRows (rows : List (List CB)) (i k : Nat) : List (List CB) :=
  let ri := rows.getD i []
  let rk := rows.getD k []
  rows.zipIdx.map fun (row, j) => if j == i then rk else if j == k then ri else row

/-- The row index `≥ k` with the largest pivot in column `k`. -/
def pivotIdx (rows : List (List CB)) (k : Nat) : Nat :=
  (rows.zipIdx.foldl (fun (best : Nat × Nat) (row, j) =>
    if Nat.ble k j then
      let m := Nat.add (absB P (row.getD k (zero P)).re) (absB P (row.getD k (zero P)).im)
      if Nat.blt best.2 m then (j, m) else best
    else best) (k, 0)).1

/-- One step of Gauss–Jordan elimination with partial pivoting, on the centers. -/
def gjStep (k : Nat) (rows0 : List (List CB)) : List (List CB) :=
  let rows := swapRows rows0 (pivotIdx P rows0 k) k
  let pr := rows.getD k []
  let piv := recipApprox P (pr.getD k (zero P))
  let prn := pr.map fun x => center P (mul P piv x)
  rows.zipIdx.map fun (row, i) =>
    if i == k then prn else
      let f := center P (row.getD k (zero P))
      List.zipWith (fun x y => center P (sub P x (mul P f y))) row prn

/-- An approximate inverse of the centers (not verified: any matrix serves as preconditioner); its entries are exact balls
with their exact magnitudes. -/
def approxInv (A : List (List CB)) : List (List CB) :=
  let n := A.length
  let aug := A.zipIdx.map fun (row, i) =>
    row.map (center P) ++ (List.range n).map fun j => if i == j then one P else zero P
  let red := (List.range n).foldl (fun rows k => gjStep P k rows) aug
  red.map fun row => (row.drop n).map (center P)

/-- A matrix cut or padded to `n × n`, with every entry replaced by its exact center. -/
def fixMat (n : Nat) (rows : List (List CB)) : List (List CB) :=
  ((rows.map fun row => ((row.map (center P)) ++ List.replicate n (zero P)).take n) ++
    List.replicate n (List.replicate n (zero P))).take n

/-- The matrix `I − M A` in balls, `M` given by rows and `A` by columns. -/
def resMat (M At : List (List CB)) : List (List CB) :=
  M.zipIdx.map fun (mrow, i) => At.zipIdx.map fun (col, j) =>
    let e := dot P mrow col
    if i == j then sub P (one P) e else e

/-- The bound `max_i Σ_j |E_ij|` (scaled) of a ball matrix, and the sum of the histories of its entries. -/
def rowSumBound (E : List (List CB)) : Nat × Nat :=
  E.foldl (fun (acc : Nat × Nat) row =>
    let q := row.foldl (fun t x => Nat.add t (magB P x)) 0
    (if Nat.blt acc.1 q then q else acc.1, row.foldl (fun t x => Nat.add t x.s) acc.2)) (0, 0)

/-- The columns of a matrix given by rows (all rows of length `n`). -/
def transpose (n : Nat) (A : List (List CB)) : List (List CB) :=
  (List.range n).map fun j => A.map fun row => row.getD j (zero P)

/-- The enclosure of the solution of `A y = −b`: `x̃ = −M b` (centers), the residual `b + A x̃`, `w = M (b + A x̃)`,
`e = max |w_i|`, and the radius `e 2^P/(2^P − q)` (`q` the bound of `‖I − M A‖`); the history of `w` is added to each
entry. -/
def solve (M A : List (List CB)) (q : Nat) (b : List CB) : List CB :=
  let xt := (matVec P M (b.map (neg P))).map (center P)
  let res := List.zipWith (fun bi ri => add P bi ri) b (matVec P A xt)
  let w := matVec P M res
  let e := w.foldl (fun t x => if Nat.blt t (magB P x) then magB P x else t) 0
  let sw := w.foldl (fun t x => Nat.add t x.s) 0
  let R := Nat.add (Nat.div (Nat.shiftLeft e P) (Nat.sub (Nat.pow 2 P) q)) 1
  xt.map fun x => ⟨x.re, x.im, R, x.a, Nat.add x.s sw⟩

/-- The coordinate series `[y₀(c), …, y_{k−1}(c), 0]` of the list `Ys = [y₀, …, y_{k−1}]` (vectors of 18 balls). -/
def coordSer (Ys : List (List CB)) : List (List CB) :=
  (List.range 18).map fun c => (Ys.map fun y => y.getD c (zero P)) ++ [zero P]

/-- `β_n` of one row: the coefficient of `τⁿ` in `Σ_{i ≤ n} τ^i G_{r,i}(Y)`, i.e. `Σ_{i ≤ n}` of the coefficient of
`τ^{n−i}` in `G_{r,i}(Y)` (the parts `rp` of the row, `partOf rp i = []` if absent). -/
def betaRow (masses : List CB) (n : Nat) (Ss : List (List CB)) (pw : List (List (List CB)))
    (rp : List (Nat × MPoly)) : CB :=
  (List.range (Nat.succ n)).foldl (fun acc i =>
    add P acc ((evalPoly P masses (Nat.sub n i) Ss pw (partOf rp i)).getD (Nat.sub n i) (zero P))) (zero P)

/-- `β_n` for every row, where `Ys = [y₀, …, y_{n−1}]`. -/
def beta (masses : List CB) (parts : List (List (Nat × MPoly))) (Ys : List (List CB)) (n : Nat) : List CB :=
  let Ss := coordSer P Ys
  parts.map (betaRow P masses n Ss (powTab P n Ss))

/-- A vector on the unknowns extended by zero balls to the eighteen coordinates. -/
def extend (unk : List Nat) (yR : List CB) : List CB :=
  (List.range 18).map fun c =>
    match unk.idxOf? c with
    | some j => yR.getD j (zero P)
    | none => zero P

/-- One step of the recursion: append `y_n` (`n = Ys.length`). -/
def liftStep (masses : List CB) (parts : List (List (Nat × MPoly))) (rows unk : List Nat) (M A : List (List CB))
    (q : Nat) (Ys : List (List CB)) : List (List CB) :=
  let b := beta P masses parts Ys Ys.length
  Ys ++ [extend P unk (solve P M A q (rows.map fun r => b.getD r (zero P)))]

/-- The list `[y₀, …, y_k]`. -/
def liftYs (masses : List CB) (parts : List (List (Nat × MPoly))) (rows unk : List Nat) (M A : List (List CB))
    (q : Nat) (y0 : List CB) : Nat → List (List CB)
  | 0 => [y0]
  | Nat.succ k => liftStep P masses parts rows unk M A q (liftYs masses parts rows unk M A q y0 k)

/-- The ball of `η_{R,n}` at the row `rc`. -/
def etaBall (masses : List CB) (parts : List (List (Nat × MPoly))) (rows unk : List Nat) (rc n : Nat)
    (M A : List (List CB)) (q : Nat) (y0 : List CB) : CB :=
  let Ys := liftYs P masses parts rows unk M A q y0 (Nat.sub n 1)
  let b := beta P masses parts Ys n
  let yn := solve P M A q (rows.map fun r => b.getD r (zero P))
  let Jc := (jacMat P masses parts y0 [rc] unk).getD 0 []
  Acc.fin P (Acc.addB P (Acc.dot P Acc.zero Jc yn) (b.getD rc (zero P)))

/-- **The check of one leading solution**: `J₀[R]` is invertible (`‖I − M J₀[R]‖ < 1`) and the ball of `η_{R,n}` at the row
`rc` excludes `0`. -/
def liftCheck (masses : List CB) (parts : List (List (Nat × MPoly))) (rows unk : List Nat) (rc n : Nat)
    (y0 : List CB) : Bool :=
  let A := jacMat P masses parts y0 rows unk
  let M := fixMat P unk.length (approxInv P A)
  let E := resMat P M (transpose P unk.length A)
  let qs := rowSumBound P E
  Nat.blt qs.1 (Nat.pow 2 P) && Nat.ble qs.2 (smax P) &&
    excl0 P (etaBall P masses parts rows unk rc n M A qs.1 y0)

end lift


/-! ## Covering the roots of `α z^k = β` (`k = 2, 3`) -/

section cover

variable (P : Nat)

/-- A lower bound of `‖x‖ · 2^P` on the ball: `max(|re|, |im|) − r`. -/
def normLo (x : CB) : Nat :=
  Nat.sub (if Nat.ble (absB P x.re) (absB P x.im) then absB P x.im else absB P x.re) x.r

/-- The ball of `ω = (−1 + i√3)/2` from bounds `s3lo ≤ √3 · 2^P ≤ s3hi`. -/
def omegaBall (s3lo s3hi : Nat) : CB :=
  ⟨Nat.sub (bias P) (Nat.pow 2 (Nat.sub P 1)), Nat.add (bias P) (Nat.div s3lo 2),
    Nat.add (Nat.div (Nat.sub s3hi s3lo) 2) 1, Nat.add (Nat.pow 2 (Nat.sub P 1)) (Nat.div s3lo 2),
    Nat.add (Nat.pow 2 (Nat.sub P 1)) (Nat.div s3lo 2)⟩

/-- The bounds on `√3` are correct (and `P ≥ 1`). -/
def omegaOK (s3lo s3hi : Nat) : Bool :=
  Nat.ble 1 P && Nat.ble (Nat.mul s3lo s3lo) (Nat.mul 3 (Nat.pow 4 P)) &&
    Nat.ble (Nat.mul 3 (Nat.pow 4 P)) (Nat.mul s3hi s3hi) && Nat.ble s3lo s3hi

/-- The ball `β − α a²`. -/
def coverE2 (A B a : CB) : CB := sub P B (mul P A (mul P a a))

/-- The ball `β − α a³`. -/
def coverE3 (A B a : CB) : CB := sub P B (mul P A (mul P a (mul P a a)))

/-- A lower bound of `‖a‖ · 2^P` for an exact center: `max(|re|, |im|)`. -/
def normLoC (a : CB) : Nat := if Nat.ble (absB P a.re) (absB P a.im) then absB P a.im else absB P a.re

/-- `σ · 2^P` for square roots: `2‖a‖ − ρ`. -/
def sigma2 (a : CB) (rho : Nat) : Nat := Nat.sub (Nat.mul 2 (normLoC P a)) rho

/-- `σ · 2^P` for cube roots: `√3 ‖a‖ − ρ`. -/
def sigma3 (s3lo : Nat) (a : CB) (rho : Nat) : Nat := Nat.sub (Nat.shiftRight (Nat.mul s3lo (normLoC P a)) P) rho

/-- The check of the covering of the square roots: `a` exact, `‖α‖ > 0`, `δ < ρ²`, `ρ < σ`. -/
def cover2OK (A B a : CB) (rho : Nat) : Bool :=
  Nat.beq a.r 0 && Nat.blt 0 (normLo P A) &&
    Nat.blt (Nat.mul (magB P (coverE2 P A B a)) (Nat.pow 2 (Nat.mul 2 P))) (Nat.mul (normLo P A) (Nat.mul rho rho)) &&
    Nat.blt rho (sigma2 P a rho)

/-- The radius `R · 2^P` of the square-root candidates: `e 2^{2P}/(l σ) + 1`. -/
def cover2R (A B a : CB) (rho : Nat) : Nat :=
  Nat.add (Nat.div (Nat.mul (magB P (coverE2 P A B a)) (Nat.pow 2 (Nat.mul 2 P)))
    (Nat.mul (normLo P A) (sigma2 P a rho))) 1

/-- A candidate ball: the ball `W` of the candidate center enlarged by `R`, with the history of `E` added. -/
def candBall (W E : CB) (R : Nat) : CB := ⟨W.re, W.im, Nat.add W.r R, W.a, Nat.add W.s E.s⟩

/-- The two square-root candidates `±a`. -/
def cover2Balls (A B a : CB) (rho : Nat) : List CB :=
  [candBall a (coverE2 P A B a) (cover2R P A B a rho), candBall (neg P a) (coverE2 P A B a) (cover2R P A B a rho)]

/-- The check of the covering of the cube roots. -/
def cover3OK (s3lo : Nat) (A B a : CB) (rho : Nat) : Bool :=
  Nat.beq a.r 0 && Nat.blt 0 (normLo P A) &&
    Nat.blt (Nat.mul (magB P (coverE3 P A B a)) (Nat.pow 2 (Nat.mul 3 P)))
      (Nat.mul (normLo P A) (Nat.mul rho (Nat.mul rho rho))) &&
    Nat.blt rho (sigma3 P s3lo a rho)

/-- The radius of the cube-root candidates: `e 2^{3P}/(l σ²) + 1`. -/
def cover3R (s3lo : Nat) (A B a : CB) (rho : Nat) : Nat :=
  Nat.add (Nat.div (Nat.mul (magB P (coverE3 P A B a)) (Nat.pow 2 (Nat.mul 3 P)))
    (Nat.mul (normLo P A) (Nat.mul (sigma3 P s3lo a rho) (sigma3 P s3lo a rho)))) 1

/-- The three cube-root candidates `a`, `ωa`, `ω²a`. -/
def cover3Balls (s3lo s3hi : Nat) (A B a : CB) (rho : Nat) : List CB :=
  let E := coverE3 P A B a
  let R := cover3R P s3lo A B a rho
  let w := omegaBall P s3lo s3hi
  [candBall a E R, candBall (mul P w a) E R, candBall (mul P (mul P w w) a) E R]

end cover

end Lean6.Special.Ball
