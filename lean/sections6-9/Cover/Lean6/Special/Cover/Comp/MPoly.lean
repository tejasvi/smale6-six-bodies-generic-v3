/-!
# Polynomials in the six masses with integer coefficients

A small exact type for the linear algebra over `ℚ(m)` of Lemmas 9.13 and 9.14: sparse polynomials in `m₀, …, m₅` (the
masses of the bodies `0, …, 5` of the stored cells, the paper's `m₁, …, m₆`) with integer coefficients.

* `MPoly.terms` is kept in the canonical form of `MPoly.norm`: sorted by exponent vector, no monomial twice, no zero
  coefficient. So a polynomial is zero exactly when its list of terms is empty (`MPoly.isZero`).
* `det n A`: the determinant of an `n × n` matrix of polynomials, expanded along the first row.
* `MPoly.eval pt p`: the value at an integer point.
-/

namespace Lean6.Special.Cover.MP

/-- An exponent vector `(e₀, …, e₅)` of the monomial `m₀^e₀ ⋯ m₅^e₅`. -/
abbrev Mono := List Nat

/-- The number of variables. -/
abbrev nVar : Nat := 6

/-- A polynomial: its terms, in the canonical form of `norm`. -/
structure MPoly where
  terms : List (Mono × Int)
  deriving BEq

/-- The strict lexicographic order of exponent vectors. -/
def monoLt : Mono → Mono → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && monoLt as bs)

/-- The product of two monomials. -/
def monoMul (a b : Mono) : Mono := List.zipWith (· + ·) a b

/-- Merges the equal monomials of a sorted list of terms and drops zero coefficients. -/
def mergeSorted (s : List (Mono × Int)) : List (Mono × Int) :=
  let r := s.foldl (fun acc t => match acc with
    | (m, c) :: rest => if m == t.1 then (m, c + t.2) :: rest else t :: acc
    | [] => [t]) []
  (r.filter (·.2 != 0)).reverse

/-- The canonical form of a list of terms. -/
def norm (ts : List (Mono × Int)) : MPoly :=
  ⟨mergeSorted (ts.mergeSort fun x y => monoLt x.1 y.1 || x.1 == y.1)⟩

namespace MPoly

/-- The monomial `1`. -/
def one0 : Mono := List.replicate nVar 0

def zero : MPoly := ⟨[]⟩

def const (c : Int) : MPoly := norm [(one0, c)]

def one : MPoly := const 1

/-- The variable `m_i`. -/
def var (i : Nat) : MPoly := ⟨[(one0.set i 1, 1)]⟩

def isZero (p : MPoly) : Bool := p.terms.isEmpty

def add (p q : MPoly) : MPoly := norm (p.terms ++ q.terms)

def neg (p : MPoly) : MPoly := ⟨p.terms.map fun t => (t.1, -t.2)⟩

def sub (p q : MPoly) : MPoly := add p (neg q)

def mul (p q : MPoly) : MPoly :=
  norm (p.terms.flatMap fun t => q.terms.map fun u => (monoMul t.1 u.1, t.2 * u.2))

def smul (c : Int) (p : MPoly) : MPoly := norm (p.terms.map fun t => (t.1, c * t.2))

instance : Add MPoly := ⟨add⟩
instance : Sub MPoly := ⟨sub⟩
instance : Mul MPoly := ⟨mul⟩
instance : Neg MPoly := ⟨neg⟩

/-- The sum of a list of polynomials. -/
def sum (ps : List MPoly) : MPoly := norm (ps.flatMap (·.terms))

/-- The power `p ^ n`. -/
def pow (p : MPoly) : Nat → MPoly
  | 0 => one
  | n + 1 => mul (pow p n) p

/-- The value of a monomial at an integer point. -/
def monoEval (pt : List Int) (m : Mono) : Int :=
  (List.zipWith (fun x e => x ^ e) pt m).foldl (· * ·) 1

/-- The value at an integer point `pt = (m₀, …, m₅)`. -/
def eval (pt : List Int) (p : MPoly) : Int := p.terms.foldl (fun s t => s + t.2 * monoEval pt t.1) 0

/-- The total degree (`0` for the zero polynomial). -/
def degree (p : MPoly) : Nat := p.terms.foldl (fun d t => max d (t.1.foldl (· + ·) 0)) 0

/-- A monomial as text, e.g. `m0^2*m3`. -/
def monoStr (m : Mono) : String :=
  let fs := ((List.range nVar).zip m).filterMap fun (i, e) =>
    if e == 0 then none else if e == 1 then some s!"m{i}" else some s!"m{i}^{e}"
  String.intercalate "*" fs

/-- A polynomial as text, e.g. `m1*m4 - m2*m5` (terms in the canonical order). -/
def toStr (p : MPoly) : String :=
  match p.terms with
  | [] => "0"
  | ts =>
    let fmt (first : Bool) (t : Mono × Int) : String :=
      let ms := monoStr t.1
      let a := t.2.natAbs
      let body := if ms.isEmpty then s!"{a}" else if a == 1 then ms else s!"{a}*{ms}"
      if first then (if t.2 < 0 then "-" ++ body else body)
      else (if t.2 < 0 then " - " ++ body else " + " ++ body)
    match ts with
    | [] => "0"
    | t :: rest => rest.foldl (fun s u => s ++ fmt false u) (fmt true t)

end MPoly

/-- The matrix `A` without its column `j`. -/
def dropCol (A : List (List MPoly)) (j : Nat) : List (List MPoly) := A.map (·.eraseIdx j)

/-- The determinant of an `n × n` matrix (a list of `n` rows of length `n`), expanded along the first row. -/
def det : Nat → List (List MPoly) → MPoly
  | 0, _ => MPoly.one
  | _ + 1, [] => MPoly.zero
  | n + 1, r :: rest =>
    MPoly.sum ((List.range r.length).zip r |>.map fun (j, a) =>
      if a.isZero then MPoly.zero
      else
        let m := MPoly.mul a (det n (dropCol rest j))
        if j % 2 == 0 then m else MPoly.neg m)

/-- The submatrix on the rows `R` and the columns `C` (indices). -/
def sub (A : List (List MPoly)) (R C : List Nat) : List (List MPoly) :=
  R.map fun i => C.map fun j => (A.getD i []).getD j MPoly.zero

end Lean6.Special.Cover.MP
