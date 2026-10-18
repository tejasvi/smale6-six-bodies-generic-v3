import Lean6.Special.Comp.Ball.TPoly
import Lean6.Special.Ball.Sem

/-!
# Polynomials with a coefficient table: denotation and the soundness of the ball evaluation

`TTerm.eval κ x t = c · κ_k · ∏ x_v^e`, `TPoly.eval κ x p` the sum over the terms. **`mem_tEval`**: if the table balls
contain `κ` and the variable balls contain `x`, `tEval` contains the value (no well-formedness condition: indices beyond
the lists read the zero ball, and the hypotheses ask the corresponding values to be `0`).
-/

namespace Lean6.Special.Kraw

open Lean6.Special.Ball

variable {P : ℕ}

/-- The value of a term. -/
def TTerm.eval (κ x : ℕ → ℂ) (t : TTerm) : ℂ := (t.c : ℂ) * κ t.k * (t.mono.map fun ve => x ve.1 ^ ve.2).prod

/-- The value of a polynomial. -/
def TPoly.eval (κ x : ℕ → ℂ) (p : TPoly) : ℂ := (p.map (TTerm.eval κ x)).sum

@[simp] theorem TPoly.eval_nil (κ x : ℕ → ℂ) : TPoly.eval κ x [] = 0 := rfl

@[simp] theorem TPoly.eval_cons (κ x : ℕ → ℂ) (t : TTerm) (p : TPoly) :
    TPoly.eval κ x (t :: p) = t.eval κ x + TPoly.eval κ x p := by
  simp [TPoly.eval]

/-- The balls `bs` contain the values `f` (beyond the list, the zero ball must contain the value). -/
def ListMemF (P : ℕ) (f : ℕ → ℂ) (bs : List CB) : Prop := ∀ v, (bs.getD v (zero P)).Mem P (f v)

theorem mem_tPow {x : CB} {z : ℂ} (hx : x.Mem P z) : ∀ e, (tPow P x e).Mem P (z ^ e)
  | 0 => by simpa [tPow] using mem_one
  | e + 1 => by rw [pow_succ]; exact mem_mul (mem_tPow hx e) hx

theorem mem_tMono {xs : List CB} {x : ℕ → ℂ} (hx : ListMemF P x xs) :
    ∀ mono : List (ℕ × ℕ), (tMono P xs mono).Mem P (mono.map fun ve => x ve.1 ^ ve.2).prod
  | [] => by simpa [tMono] using mem_one
  | ve :: rest => by
    simp only [tMono, List.map_cons, List.prod_cons]
    exact mem_mul (mem_tPow (hx ve.1) ve.2) (mem_tMono hx rest)

theorem mem_tTerm {tab xs : List CB} {κ x : ℕ → ℂ} (hκ : ListMemF P κ tab) (hx : ListMemF P x xs) (t : TTerm) :
    (tTerm P tab xs t).Mem P (t.eval κ x) :=
  mem_mul (mem_mul (mem_ofInt t.c) (hκ t.k)) (mem_tMono hx t.mono)

/-- **The ball evaluation of a polynomial contains its value.** -/
theorem mem_tEval {tab xs : List CB} {κ x : ℕ → ℂ} (hκ : ListMemF P κ tab) (hx : ListMemF P x xs) :
    ∀ p : TPoly, (tEval P tab xs p).Mem P (p.eval κ x)
  | [] => by simpa [tEval] using mem_zero
  | t :: rest => by
    simp only [tEval, TPoly.eval_cons]
    exact mem_add (mem_tTerm hκ hx t) (mem_tEval hκ hx rest)

end Lean6.Special.Kraw
