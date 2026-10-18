import L6Sound.F34S.Defs

/-!
# The initial forms as polynomials: values

* `UPoly.eval`: the value of an unpacked polynomial; it is multiplicative and additive, and setting a variable whose
  value is `1` to `1` does not change it;
* `eval_pack`: packing (`UPoly.pack`) does not change the value when every exponent is `< 128` (`UPoly.small`);
* `eval_halve`: halving the coefficients divides the value by `2`;
* `itemPoly_spec`, `distPoly_spec`: at the point `phiOf` of the variables of the link, the generator written from the
  trees has the value `itemVal` of its item (up to the factor `1` or `2` of the halving).
-/

namespace L6.F34S

open L6.Poly
open Finset

section UEval

variable {R : Type*} [CommRing R]

/-- The value of an unpacked polynomial. -/
def UPoly.eval (φ : ℕ → R) (p : UPoly) : R :=
  (p.map fun a => (a.1 : R) * (a.2.map fun ve => φ ve.1 ^ ve.2).prod).sum

theorem UPoly.eval_nil (φ : ℕ → R) : UPoly.eval φ ([] : UPoly) = 0 := rfl

theorem UPoly.eval_cons (φ : ℕ → R) (a : Int × List (Nat × Nat)) (p : UPoly) :
    UPoly.eval φ (a :: p) = (a.1 : R) * (a.2.map fun ve => φ ve.1 ^ ve.2).prod + UPoly.eval φ p := by
  simp [UPoly.eval]

theorem UPoly.eval_append (φ : ℕ → R) (p q : UPoly) : UPoly.eval φ (p ++ q) = UPoly.eval φ p + UPoly.eval φ q := by
  simp [UPoly.eval, List.sum_append]

theorem UPoly.eval_neg (φ : ℕ → R) (p : UPoly) : UPoly.eval φ p.neg = - UPoly.eval φ p := by
  unfold UPoly.neg
  induction p with
  | nil => simp [UPoly.eval]
  | cons a p ih =>
    rw [List.map_cons, UPoly.eval_cons, UPoly.eval_cons, ih]
    push_cast
    ring

theorem UPoly.eval_mul (φ : ℕ → R) (p q : UPoly) : UPoly.eval φ (p.mul q) = UPoly.eval φ p * UPoly.eval φ q := by
  unfold UPoly.mul
  induction p with
  | nil => simp [UPoly.eval]
  | cons a p ih =>
    rw [List.flatMap_cons, UPoly.eval_append, ih, UPoly.eval_cons, add_mul]
    congr 1
    unfold UPoly.eval
    rw [List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp, List.map_append, List.prod_append]
    push_cast
    ring

theorem UPoly.eval_one (φ : ℕ → R) : UPoly.eval φ ([(1, [])] : UPoly) = 1 := by
  simp [UPoly.eval]

theorem UPoly.eval_prod (φ : ℕ → R) (ps : List UPoly) :
    UPoly.eval φ (UPoly.prod ps) = (ps.map (UPoly.eval φ)).prod := by
  unfold UPoly.prod
  induction ps with
  | nil => simp [UPoly.eval_one]
  | cons p ps ih => rw [List.foldr_cons, UPoly.eval_mul, ih, List.map_cons, List.prod_cons]

theorem UPoly.eval_var (φ : ℕ → R) (v : Nat) : UPoly.eval φ (UPoly.var v) = φ v := by
  simp [UPoly.eval, UPoly.var]

theorem UPoly.eval_flatten (φ : ℕ → R) (ls : List UPoly) :
    UPoly.eval φ ls.flatten = (ls.map (UPoly.eval φ)).sum := by
  induction ls with
  | nil => simp [UPoly.eval]
  | cons l ls ih => rw [List.flatten_cons, UPoly.eval_append, ih, List.map_cons, List.sum_cons]

theorem prod_filter_one (φ : ℕ → R) (v : Nat) (hv : φ v = 1) (mono : List (Nat × Nat)) :
    ((mono.filter fun ve => ve.1 != v).map fun ve => φ ve.1 ^ ve.2).prod = (mono.map fun ve => φ ve.1 ^ ve.2).prod := by
  induction mono with
  | nil => rfl
  | cons ve rest ih =>
    by_cases h : ve.1 = v
    · have : (ve.1 != v) = false := by simp [h]
      rw [List.filter_cons, this, if_neg (by simp), ih, List.map_cons, List.prod_cons, h, hv, one_pow, one_mul]
    · have : (ve.1 != v) = true := by simp [h]
      rw [List.filter_cons, this, if_pos rfl, List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]

theorem UPoly.eval_substOne (φ : ℕ → R) (F : Int) (hF : 0 ≤ F → φ F.toNat = 1) (p : UPoly) :
    UPoly.eval φ (p.substOne F) = UPoly.eval φ p := by
  unfold UPoly.substOne
  split_ifs with h
  · rfl
  · have h1 := hF (by omega)
    unfold UPoly.eval
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp]
    rw [prod_filter_one φ F.toNat h1]

end UEval

/-! ## Packing -/

theorem degIn_append_single (es : List (Nat × Nat)) (v e i : Nat) :
    degIn (es ++ [(v, e)]) i = degIn es i + if v = i then e else 0 := by
  unfold degIn
  rw [List.filter_append, List.foldl_append]
  by_cases h : v = i
  · subst h
    simp
  · have : ((v, e).1 == i) = false := by simp [h]
    simp [List.filter_cons, this, h]

theorem degIn_le_append (es : List (Nat × Nat)) (v e i : Nat) : degIn es i ≤ degIn (es ++ [(v, e)]) i := by
  rw [degIn_append_single]
  omega

theorem degIn_nil (i : Nat) : degIn [] i = 0 := rfl

theorem packExp_append_single (es : List (Nat × Nat)) (v e : Nat) :
    packExp (es ++ [(v, e)]) = packExp es + e * 256 ^ v := by
  unfold packExp
  rw [List.foldl_append]
  rfl

theorem keyExp_single (e v i : Nat) (he : e < 256) : keyExp (e * 256 ^ v) i = if v = i then e else 0 := by
  rw [keyExp_eq_div]
  rcases lt_trichotomy i v with h | h | h
  · rw [if_neg (by omega)]
    have hv : 256 ^ v = 256 ^ i * (256 * 256 ^ (v - i - 1)) := by
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
    rw [hv, show e * (256 ^ i * (256 * 256 ^ (v - i - 1))) = 256 ^ i * (e * (256 * 256 ^ (v - i - 1))) by ring,
      Nat.mul_div_cancel_left _ (by positivity)]
    rw [show e * (256 * 256 ^ (v - i - 1)) = 256 * (e * 256 ^ (v - i - 1)) by ring]
    exact Nat.mul_mod_right _ _
  · subst h
    rw [if_pos rfl, Nat.mul_div_cancel _ (by positivity)]
    exact Nat.mod_eq_of_lt he
  · rw [if_neg (by omega)]
    have hi : 256 ^ i = 256 ^ v * 256 ^ (i - v) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hi, Nat.mul_comm (256 ^ v), Nat.mul_div_mul_right _ _ (by positivity)]
    have : e < 256 ^ (i - v) := by
      calc e < 256 := he
        _ = 256 ^ 1 := by norm_num
        _ ≤ 256 ^ (i - v) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.div_eq_of_lt this]

theorem keyExp_packExp : ∀ (es : List (Nat × Nat)), (∀ j, degIn es j < 128) → ∀ i, keyExp (packExp es) i = degIn es i := by
  intro es
  induction es using List.reverseRecOn with
  | nil => intro _ i; simp [packExp, keyExp, degIn_nil]
  | append_singleton es ve ih =>
    intro hdeg i
    obtain ⟨v, e⟩ := ve
    have hdeg' : ∀ j, degIn es j < 128 := fun j => lt_of_le_of_lt (degIn_le_append es v e j) (hdeg j)
    have he : e < 128 := by
      have := hdeg v
      rw [degIn_append_single] at this
      simp at this
      omega
    rw [packExp_append_single, keyExp_add _ _ i (fun j _ => by rw [ih hdeg' j]; exact hdeg' j)
      (fun j _ => by rw [keyExp_single e v j (by omega)]; split_ifs <;> omega),
      ih hdeg' i, keyExp_single e v i (by omega), degIn_append_single]

section Pack

variable {R : Type*} [CommRing R]

theorem monoEval_packExp (nv : Nat) (φ : ℕ → R) :
    ∀ (es : List (Nat × Nat)), (∀ ve ∈ es, ve.1 < nv) → (∀ j, degIn es j < 128) →
      monoEval nv φ (packExp es) = (es.map fun ve => φ ve.1 ^ ve.2).prod := by
  intro es hv hdeg
  unfold monoEval
  rw [Finset.prod_congr rfl fun i _ => by rw [keyExp_packExp es hdeg i]]
  clear hdeg
  induction es using List.reverseRecOn with
  | nil => simp [degIn_nil]
  | append_singleton es ve ih =>
    obtain ⟨v, e⟩ := ve
    have hv' : ∀ x ∈ es, x.1 < nv := fun x hx => hv x (List.mem_append_left _ hx)
    have hvn : v < nv := hv (v, e) (List.mem_append_right _ (List.mem_singleton_self _))
    rw [List.map_append, List.prod_append, ← ih hv']
    simp only [degIn_append_single, pow_add, Finset.prod_mul_distrib, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    congr 1
    rw [Finset.prod_congr rfl (fun i _ => show φ i ^ (if v = i then e else 0) = if v = i then φ i ^ e else 1 by
      split_ifs <;> simp)]
    rw [Finset.prod_ite_eq, if_pos (Finset.mem_range.mpr hvn)]

theorem eval_pack (nv : Nat) (φ : ℕ → R) (p : UPoly) (hs : p.small nv = true) :
    L6.Poly.eval nv φ p.pack = UPoly.eval φ p := by
  unfold UPoly.pack
  rw [eval_normalize]
  unfold L6.Poly.eval UPoly.eval
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun a ha => ?_
  unfold UPoly.small at hs
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_range] at hs
  obtain ⟨h1, h2⟩ := hs a ha
  have hdeg : ∀ j, degIn a.2 j < 128 := by
    intro j
    by_cases hj : j < nv
    · exact h2 j hj
    · have : degIn a.2 j = 0 := by
        unfold degIn
        have : a.2.filter (fun ve => ve.1 == j) = [] := by
          rw [List.filter_eq_nil_iff]
          intro ve hve
          have := h1 ve hve
          simp only [beq_iff_eq]
          omega
        rw [this]
        rfl
      omega
  simp only [Function.comp]
  rw [monoEval_packExp nv φ a.2 h1 hdeg]

theorem eval_halve (nv : Nat) (φ : ℕ → R) (p : Poly) :
    ((if (halve p).2 then 2 else 1 : R)) * L6.Poly.eval nv φ (halve p).1 = L6.Poly.eval nv φ p := by
  unfold halve
  by_cases h : (p.all fun t => t.2 % 2 == 0) = true
  · rw [if_pos h]
    dsimp only
    rw [if_pos rfl]
    unfold L6.Poly.eval
    rw [← List.sum_map_mul_left, List.map_map]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    simp only [List.all_eq_true, beq_iff_eq] at h
    have h2 : (2 : Int) ∣ t.2 := Int.dvd_of_emod_eq_zero (h t ht)
    simp only [Function.comp]
    rw [← mul_assoc]
    congr 1
    rw [show (2 : R) = ((2 : Int) : R) by push_cast; rfl, ← Int.cast_mul, Int.mul_ediv_cancel' h2]
  · rw [if_neg h]
    dsimp only
    rw [if_neg (by simp), one_mul]

end Pack

/-! ## The generators written from the trees -/

theorem findVar_spec {vars : Array VarM} {x : VarM} {j : Nat} (h : findVar vars x = some j) :
    j < vars.size ∧ vars[j]! = x := by
  unfold findVar at h
  have h1 := List.find?_some h
  have h2 := List.mem_range.mp (List.mem_of_find?_eq_some h)
  exact ⟨h2, by simpa using h1⟩

section Gen

variable {R : Type*} [CommRing R]

theorem phiOf_lt (vars : Array VarM) (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) {i : Nat} (hi : i < 6) :
    phiOf vars X Y P E m i = m i := by
  unfold phiOf
  rw [if_pos hi]

theorem phiOf_var (vars : Array VarM) (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) {j : Nat}
    (hj : j < vars.size) :
    phiOf vars X Y P E m (6 + j) = match vars[j]! with
      | .X v c c0 => X v c - X v c0
      | .Y v c c0 => Y v c - Y v c0
      | .D k l => P k l
      | .E => E
      | .bad => 0 := by
  unfold phiOf
  rw [if_neg (by omega), show 6 + j - 6 = j by omega, Array.getElem?_eq_getElem hj, ← getElem!_pos vars j hj]
  cases vars[j]! <;> rfl

theorem coordU_spec (x : PCtx) (z : Bool) (v c : Nat) {u : UPoly} (h : coordU x z v c = some u)
    (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) :
    ∃ c0, baseChild (if z then x.ez else x.ew) v = some c0 ∧
      UPoly.eval (phiOf x.vars X Y P E m) u = (if z then X else Y) v c - (if z then X else Y) v c0 := by
  cases hb : baseChild (if z then x.ez else x.ew) v with
  | none => simp [coordU, hb] at h
  | some c0 =>
    refine ⟨c0, rfl, ?_⟩
    by_cases hc : c = c0
    · subst hc
      simp only [coordU, hb, beq_self_eq_true, ite_true, Option.some.injEq] at h
      subst h
      simp [UPoly.eval]
    · have hc' : (c == c0) = false := by simp [hc]
      cases hf : findVar x.vars (if z then VarM.X v c c0 else VarM.Y v c c0) with
      | none => simp [coordU, hb, hc', hf] at h
      | some j =>
        simp only [coordU, hb, hc', Bool.false_eq_true, ite_false, hf, Option.some.injEq] at h
        subst h
        obtain ⟨hj, hvj⟩ := findVar_spec hf
        rw [UPoly.eval_var, phiOf_var _ _ _ _ _ _ hj, hvj]
        cases z <;> rfl

theorem lcU_spec (x : PCtx) (z : Bool) (pq : Nat × Nat) {u : UPoly} (h : lcU x z pq = some u)
    (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) :
    UPoly.eval (phiOf x.vars X Y P E m) u =
      lcVal (if z then x.P.tz else x.P.tw) (if z then X else Y) pq := by
  unfold lcVal
  cases hl : (if z then x.P.tz else x.P.tw).lca pq.1 pq.2 with
  | none => simp [lcU, hl] at h
  | some v =>
    dsimp only
    cases ha : coordU x z v (childOf (if z then x.P.tz else x.P.tw) v pq.1) with
    | none => simp [lcU, hl, ha] at h
    | some a =>
      cases hb : coordU x z v (childOf (if z then x.P.tz else x.P.tw) v pq.2) with
      | none => simp [lcU, hl, ha, hb] at h
      | some b =>
        simp only [lcU, hl, ha, hb, Option.some.injEq] at h
        subst h
        obtain ⟨c0, hc0, hva⟩ := coordU_spec x z v _ ha X Y P E m
        obtain ⟨c0', hc0', hvb⟩ := coordU_spec x z v _ hb X Y P E m
        rw [hc0] at hc0'
        cases hc0'
        rw [UPoly.eval_append, UPoly.eval_neg, hva, hvb]
        ring

theorem dU_spec (x : PCtx) (kl : Nat × Nat) {u : UPoly} (h : dU x kl = some u)
    (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) :
    UPoly.eval (phiOf x.vars X Y P E m) u = P (min kl.1 kl.2) (max kl.1 kl.2) := by
  cases hf : findVar x.vars (VarM.D (min kl.1 kl.2) (max kl.1 kl.2)) with
  | none => simp [dU, hf] at h
  | some j =>
    simp only [dU, hf, Option.some.injEq] at h
    subst h
    obtain ⟨hj, hvj⟩ := findVar_spec hf
    rw [UPoly.eval_var, phiOf_var _ _ _ _ _ _ hj, hvj]

theorem eval_coefBase (x : PCtx) (c : XCoef) (hms : ∀ k ∈ c.masses, k < 6) (ev : List (Nat × Nat))
    (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) :
    UPoly.eval (phiOf x.vars X Y P E m) (coefBase c ev) =
      ((2 * c.num / c.den : Int) : R) * (c.masses.map m).prod *
        (ev.map fun ve => phiOf x.vars X Y P E m ve.1 ^ ve.2).prod := by
  have hm : ((c.masses.map (·, 1)).map fun ve => phiOf x.vars X Y P E m ve.1 ^ ve.2).prod = (c.masses.map m).prod := by
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp, pow_one]
    exact phiOf_lt _ _ _ _ _ _ (hms k hk)
  simp only [coefBase, UPoly.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    List.map_append, List.prod_append, hm]
  ring

theorem eval_withMassSum (x : PCtx) (msum : Bool) (u : UPoly) (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) :
    UPoly.eval (phiOf x.vars X Y P E m) (withMassSum msum u) =
      UPoly.eval (phiOf x.vars X Y P E m) u * (if msum then ((List.range 6).map m).sum else 1) := by
  unfold withMassSum
  cases msum with
  | false => simp
  | true =>
    simp only [ite_true, UPoly.eval_mul]
    congr 1
    simp only [UPoly.eval, List.map_map]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    simp only [Function.comp, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one,
      Int.cast_one, one_mul]
    exact phiOf_lt _ _ _ _ _ _ (List.mem_range.mp hk)

theorem coefU2_spec (x : PCtx) (c : XCoef) (hms : ∀ k ∈ c.masses, k < 6) {u : UPoly} (h : coefU2 x c = some u)
    (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) :
    UPoly.eval (phiOf x.vars X Y P E m) u = coefVal2 c m E := by
  unfold coefVal2
  cases he : c.e with
  | true =>
    cases hf : findVar x.vars VarM.E with
    | none => simp [coefU2, he, hf] at h
    | some j =>
      simp only [coefU2, he, ite_true, hf, Option.some.injEq] at h
      subst h
      obtain ⟨hj, hvj⟩ := findVar_spec hf
      rw [eval_withMassSum, eval_coefBase x c hms]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_one, ite_true]
      rw [phiOf_var _ _ _ _ _ _ hj, hvj]
      ring
  | false =>
    simp only [coefU2, he, Bool.false_eq_true, ite_false, Option.some.injEq] at h
    subst h
    rw [eval_withMassSum, eval_coefBase x c hms]
    simp only [List.map_nil, List.prod_nil, mul_one, Bool.false_eq_true, ite_false]

theorem mapM_spec {α β : Type*} (f : α → Option β) (P : α → β → Prop) (hf : ∀ a b, f a = some b → P a b) :
    ∀ (l : List α) (bs : List β), l.mapM f = some bs → List.Forall₂ P l bs := by
  intro l
  induction l with
  | nil => intro bs h; simp at h; subst h; exact List.Forall₂.nil
  | cons a l ih =>
    intro bs h
    cases ha : f a with
    | none => simp [List.mapM_cons, ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [List.mapM_cons, ha, hl] at h
      | some bs' =>
        simp [List.mapM_cons, ha, hl] at h
        subst h
        exact List.Forall₂.cons (hf a b ha) (ih bs' hl)

theorem prod_forall₂ {α : Type*} (g : α → R) (F : UPoly → R) :
    ∀ (l : List α) (us : List UPoly), List.Forall₂ (fun a u => F u = g a) l us → (us.map F).prod = (l.map g).prod := by
  intro l us h
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, hab, ih]

theorem sum_forall₂ {α : Type*} (g : α → R) (F : UPoly → R) :
    ∀ (l : List α) (us : List UPoly), List.Forall₂ (fun a u => F u = g a) l us → (us.map F).sum = (l.map g).sum := by
  intro l us h
  induction h with
  | nil => rfl
  | cons hab _ ih => rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, hab, ih]

theorem termU2_spec (x : PCtx) (t : XTerm) (ht : t.good = true) {u : UPoly} (h : termU2 x t = some u)
    (X Y P : Nat → Nat → R) (E : R) (m : Nat → R) :
    UPoly.eval (phiOf x.vars X Y P E m) u = termVal2 x.P.tz x.P.tw X Y P E m t := by
  unfold XTerm.good at ht
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
  have hms := ht.2
  cases hc : coefU2 x t.coef with
  | none => simp [termU2, hc] at h
  | some c =>
    cases hz : t.zs.mapM (lcU x true) with
    | none => simp [termU2, hc, hz] at h
    | some zs =>
      cases hw : t.ws.mapM (lcU x false) with
      | none => simp [termU2, hc, hz, hw] at h
      | some ws =>
        cases hd : t.ps.mapM (dU x) with
        | none => simp [termU2, hc, hz, hw, hd] at h
        | some ds =>
          simp only [termU2, hc, hz, hw, hd, Option.some.injEq] at h
          subst h
          rw [UPoly.eval_prod]
          simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
          rw [coefU2_spec x t.coef hms hc X Y P E m]
          have hZ := prod_forall₂ (lcVal x.P.tz X) (UPoly.eval (phiOf x.vars X Y P E m)) t.zs zs
            (mapM_spec (lcU x true) (fun pq u => UPoly.eval (phiOf x.vars X Y P E m) u = lcVal x.P.tz X pq)
              (fun pq u hu => by simpa using lcU_spec x true pq hu X Y P E m) t.zs zs hz)
          have hW := prod_forall₂ (lcVal x.P.tw Y) (UPoly.eval (phiOf x.vars X Y P E m)) t.ws ws
            (mapM_spec (lcU x false) (fun pq u => UPoly.eval (phiOf x.vars X Y P E m) u = lcVal x.P.tw Y pq)
              (fun pq u hu => by simpa using lcU_spec x false pq hu X Y P E m) t.ws ws hw)
          have hD := prod_forall₂ (fun kl => P (min kl.1 kl.2) (max kl.1 kl.2))
            (UPoly.eval (phiOf x.vars X Y P E m)) t.ps ds
            (mapM_spec (dU x) (fun kl u => UPoly.eval (phiOf x.vars X Y P E m) u = P (min kl.1 kl.2) (max kl.1 kl.2))
              (fun kl u hu => dU_spec x kl hu X Y P E m) t.ps ds hd)
          rw [hZ, hW, hD]
          unfold termVal2
          ring

/-- **The generator of an initial form.** If `itemPoly` writes `g`, then for a factor `s ∈ {1, 2}` (the halving)
and at every point `phiOf` with `m_F = 1` (when `F ≥ 0`), `s · g = itemVal` of the item. -/
theorem itemPoly_spec (x : PCtx) (I : XId) (S : List Nat) (fixed : Int) (hI : I.good = true) (hF6 : fixed < 6)
    {g : Poly} (h : itemPoly x I S fixed = some g) :
    ∃ s : ℕ, (s = 1 ∨ s = 2) ∧ ∀ {R : Type} [CommRing R] (X Y P : Nat → Nat → R) (E : R) (m : Nat → R),
      (0 ≤ fixed → m fixed.toNat = 1) →
      (s : R) * L6.Poly.eval (6 + x.vars.size) (phiOf x.vars X Y P E m) g =
        itemVal x.P.tz x.P.tw X Y P E m (.init I S) := by
  unfold XId.good at hI
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hI
  obtain ⟨⟨-, hterms⟩, hscale⟩ := hI
  cases hts : S.mapM (fun i => (I.terms[i]?).bind (termU2 x)) with
  | none => simp [itemPoly, itemU, hts] at h
  | some ts =>
    set u := ((UPoly.prod (I.scale.map UPoly.var)).mul ts.flatten).substOne fixed with hu
    have hiu : itemU x I S fixed = some u := by simp only [itemU, hts, hu]
    by_cases hsm : u.small (6 + x.vars.size) = true
    · simp only [itemPoly, hiu, hsm, ite_true, Option.some.injEq] at h
      subst h
      refine ⟨if (halve u.pack).2 then 2 else 1, by split_ifs <;> simp, ?_⟩
      intro R _ X Y P E m hm
      have hφF : 0 ≤ fixed → phiOf x.vars X Y P E m fixed.toNat = 1 := fun h0 =>
        (phiOf_lt _ _ _ _ _ _ (by omega)).trans (hm h0)
      have hcast : (((if (halve u.pack).2 then 2 else 1 : ℕ)) : R) = (if (halve u.pack).2 then 2 else 1 : R) := by
        split_ifs <;> simp
      rw [hcast, eval_normalize, eval_halve, eval_pack _ _ _ hsm, hu, UPoly.eval_substOne _ _ hφF, UPoly.eval_mul,
        UPoly.eval_prod, UPoly.eval_flatten]
      unfold itemVal
      congr 1
      · rw [List.map_map]
        congr 1
        refine List.map_congr_left fun k hk => ?_
        simp only [Function.comp, UPoly.eval_var]
        exact phiOf_lt _ _ _ _ _ _ (hscale k hk)
      · have hF2 := mapM_spec (fun i => (I.terms[i]?).bind (termU2 x))
          (fun i v => UPoly.eval (phiOf x.vars X Y P E m) v = termVal2 x.P.tz x.P.tw X Y P E m I.terms[i]!)
          (fun i v hv => by
            cases hti : I.terms[i]? with
            | none => simp [hti] at hv
            | some t =>
              simp only [hti, Option.bind_some] at hv
              have hlt : i < I.terms.length := by
                rcases Nat.lt_or_ge i I.terms.length with hl | hl
                · exact hl
                · rw [List.getElem?_eq_none hl] at hti; exact absurd hti (by simp)
              have ht : I.terms[i]! = t := by
                rw [getElem!_pos I.terms i hlt]
                rw [List.getElem?_eq_getElem hlt] at hti
                exact Option.some.inj hti
              rw [ht]
              exact termU2_spec x t (hterms t (List.mem_of_getElem? hti)) hv X Y P E m)
          S ts hts
        exact sum_forall₂ _ _ S ts hF2
    · simp [itemPoly, hiu, hsm] at h

/-- **The generator of a row** `D_kl² z_kl w_kl − 1`. -/
theorem distPoly_spec (x : PCtx) (k l : Nat) (hkl : k ≤ l) {g : Poly} (h : distPoly x k l = some g) :
    ∀ {R : Type} [CommRing R] (X Y P : Nat → Nat → R) (E : R) (m : Nat → R),
      L6.Poly.eval (6 + x.vars.size) (phiOf x.vars X Y P E m) g = itemVal x.P.tz x.P.tw X Y P E m (.dist k l) := by
  intro R _ X Y P E m
  cases hd : dU x (k, l) with
  | none => simp [distPoly, hd] at h
  | some d =>
    cases ha : lcU x true (k, l) with
    | none => simp [distPoly, hd, ha] at h
    | some a =>
      cases hb : lcU x false (k, l) with
      | none => simp [distPoly, hd, ha, hb] at h
      | some b =>
        by_cases hsm : (distU d a b).small (6 + x.vars.size) = true
        · simp only [distPoly, hd, ha, hb, hsm, ite_true, Option.some.injEq] at h
          subst h
          rw [eval_pack _ _ _ hsm]
          unfold distU
          rw [UPoly.eval_append, UPoly.eval_prod]
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
          rw [dU_spec x (k, l) hd X Y P E m, lcU_spec x true (k, l) ha X Y P E m,
            lcU_spec x false (k, l) hb X Y P E m]
          simp only [min_eq_left hkl, max_eq_right hkl, ite_true, Bool.false_eq_true, ite_false]
          unfold itemVal
          simp only [UPoly.eval, List.map_cons, List.map_nil, List.prod_nil, List.sum_cons, List.sum_nil]
          push_cast
          ring
        · simp [distPoly, hd, ha, hb, hsm] at h

end Gen

end L6.F34S
