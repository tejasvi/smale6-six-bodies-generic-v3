import L6SoundKSpec.TropNorm
import L6SoundKSpec.C4Cert
import Lean6.Special.D88.Trop.Cover

/-!
# The torus emptiness of a system from a certificate

Three ways to `TorusEmptySys p s` (an entry of `HypsOK` of `Lean6.Special.D88.Trop`):

* `sysEmpty_of_leafOKK`: the leaf test `leafOKK` (the identity `Σ c · s[pos] + cofR · (1 − x₁₇ x₀ ⋯ x₁₆) = 1` of a
  leaf of the covering, by `isZeroK`); the proof is the leaf case of `chk_soundG`;
* `sysEmpty_of_ident`: a cofactor identity `Σ c_k s_{i_k} = 1` checked by `L6KSpec.C4` on packed polynomials of the
  system (`packN`; the indices `i_k` of the polynomials with a cofactor); `sysEmpty_of_monoIdent`: the same with a
  monomial in place of `1`;
* `sysEmpty_of_leafIdent`: the identity of a leaf checked by `L6KSpec.C4` on packed polynomials of the system and the
  Rabinowitsch polynomial `rabin p`, in eighteen variables.

`eval_packN`: a packed polynomial has the value of the polynomial when its monomials have at most `nv` entries, each
below `256`.
-/

namespace L6KSpec.Trop

open Lean6.Special Lean6.Special.Comp Lean6.Special.Comp.D88.Trop Lean6.Special.D88.Trop

/-! ## The extension of a point of the torus by `x₁₇ = (x₀ ⋯ x₁₆)⁻¹` -/

/-- `x` with `x₁₇ = (x₀ ⋯ x₁₆)⁻¹` (and all later coordinates). -/
noncomputable def ext17 {K : Type*} [Field K] (x : ℕ → K) : ℕ → K :=
  fun k => if k < 17 then x k else (∏ k ∈ Finset.range 17, x k)⁻¹

theorem ext17_lt {K : Type*} [Field K] (x : ℕ → K) {k : ℕ} (hk : k < 17) : ext17 x k = x k := by
  simp [ext17, hk]

theorem eval_rabin_ext17 {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharP K p] (x : ℕ → K)
    (hx : ∀ i < 17, x i ≠ 0) : Poly.eval (modHomK p K) (ext17 x) (rabin p) = 0 := by
  set hK := modHomK p K
  have hprod : (∏ k ∈ Finset.range 17, x k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k hk =>
    hx k (Finset.mem_range.mp hk)
  simp only [rabin, Poly.eval_cons, Poly.eval_nil, add_zero, Mono.eval, mul_one, hK.map_neg, hK.map_one]
  rw [mono_eval_replicate_one, Finset.prod_range_succ]
  simp only [zero_add]
  have e1 : (∏ k ∈ Finset.range 17, ext17 x k) = ∏ k ∈ Finset.range 17, x k :=
    Finset.prod_congr rfl fun k hk => ext17_lt x (Finset.mem_range.mp hk)
  have e2 : ext17 x 17 = (∏ k ∈ Finset.range 17, x k)⁻¹ := by simp [ext17]
  rw [e1, e2, mul_inv_cancel₀ hprod]
  ring

/-! ## Leaves checked by `leafOKK` -/

/-- **A leaf checked by `leafOKK`**: the system of its initial forms has no common zero in the torus. -/
theorem sysEmpty_of_leafOKK {p : ℕ} [NeZero p] {s : List (Comp.Poly ℕ)} {cofs : List (ℕ × Comp.Poly ℕ)}
    {cofR : Comp.Poly ℕ} (h : leafOKK p s cofs cofR = true) : TorusEmptySys p s := by
  simp only [leafOKK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, hz⟩ := h
  intro K _ _ x hx
  set hK := modHomK p K
  have h0 := isZeroK_sound hK (ext17 x) hz
  rw [Poly.eval_sub, Poly.eval_add, Poly.eval_sum, Poly.eval_mul, Poly.eval_const] at h0
  have hf1 : hK.f 1 = 1 := by simp [hK, modHomK]
  rw [eval_rabin_ext17 x hx, mul_zero, add_zero, hf1, sub_eq_zero] at h0
  have hex : ∃ c ∈ cofs, Poly.eval hK (ext17 x) (s.getD c.1 []) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hz' : ∀ v ∈ (cofs.map fun c => Poly.mul (modC p) c.2 (s.getD c.1 [])).map (Poly.eval hK (ext17 x)),
        v = 0 := by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hq
      rw [Poly.eval_mul, hall c hc', mul_zero]
    have := List.sum_eq_zero hz'
    rw [h0] at this
    exact one_ne_zero this
  obtain ⟨c, -, hcne⟩ := hex
  have hlt : c.1 < s.length := by
    by_contra hge
    push Not at hge
    rw [List.getD_eq_default _ _ hge] at hcne
    exact hcne rfl
  have hmem : s.getD c.1 [] ∈ s := by
    rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
  refine ⟨s.getD c.1 [], hmem, ?_⟩
  rwa [eval_congr17 hK (fun k hk => (ext17_lt x hk).symm) _ (hlen _ hmem)]

/-! ## Lists of systems -/

theorem hypsOK_nil (p : ℕ) [NeZero p] : HypsOK p [] := fun _ h => absurd h List.not_mem_nil

theorem hypsOK_cons {p : ℕ} [NeZero p] {s : List (Comp.Poly ℕ)} {rest : List (List (Comp.Poly ℕ))}
    (h : TorusEmptySys p s) (hr : HypsOK p rest) : HypsOK p (s :: rest) := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  exacts [h, hr t ht]

/-! ## Packed polynomials -/

theorem keyExp_packKey : ∀ (m : Mono), (∀ e ∈ m, e < 256) → ∀ i, L6KSpec.C4.keyExp (packKey m) i = m.getD i 0
  | [], _, i => by
    show L6KSpec.C4.keyExp 0 i = ([] : Mono).getD i 0
    simp [L6KSpec.C4.keyExp]
  | e :: m, h, i => by
    have he : e < 256 := h e List.mem_cons_self
    have ih := keyExp_packKey m fun a ha => h a (List.mem_cons_of_mem _ ha)
    show L6KSpec.C4.keyExp (e + 256 * packKey m) i = (e :: m).getD i 0
    rw [L6KSpec.C4.keyExp_eq_div]
    cases i with
    | zero =>
      simp only [pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
    | succ i =>
      have hk : (e + 256 * packKey m) / 256 = packKey m := by omega
      rw [List.getD_cons_succ, ← ih i, L6KSpec.C4.keyExp_eq_div, pow_succ', ← Nat.div_div_eq_div_mul, hk]

theorem prod_getD_eq_monoEval {R : Type*} [CommRing R] (φ : ℕ → R) :
    ∀ (m : Mono) (n j : ℕ), m.length ≤ n → ∏ i ∈ Finset.range n, φ (j + i) ^ m.getD i 0 = Mono.eval φ m j
  | [], n, j, _ => by simp [Mono.eval]
  | e :: m, n, j, hl => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hl; omega⟩
    rw [Finset.prod_range_succ', Mono.eval]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [mul_comm, ← prod_getD_eq_monoEval φ m n (j + 1) (by simp at hl; omega)]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show j + (i + 1) = j + 1 + i by omega]

theorem monoEval_packKey {R : Type*} [CommRing R] (nv : ℕ) (φ : ℕ → R) (m : Mono) (hl : m.length ≤ nv)
    (he : ∀ e ∈ m, e < 256) : L6KSpec.C4.monoEval nv φ (packKey m) = Mono.eval φ m 0 := by
  unfold L6KSpec.C4.monoEval
  rw [← prod_getD_eq_monoEval φ m nv 0 hl]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [keyExp_packKey m he, zero_add]

/-- **A packed polynomial has the value of the polynomial.** -/
theorem eval_packN {p : ℕ} [NeZero p] {K : Type*} [CommRing K] [CharP K p] (nv : ℕ) (x : ℕ → K) :
    ∀ (f : Comp.Poly ℕ), (∀ t ∈ f, t.2.length ≤ nv ∧ ∀ e ∈ t.2, e < 256) →
      L6KSpec.C4.eval nv x (packN f) = Poly.eval (modHomK p K) x f
  | [], _ => rfl
  | t :: f, hf => by
    have ht := hf t List.mem_cons_self
    have ih := eval_packN nv x f fun u hu => hf u (List.mem_cons_of_mem _ hu)
    show L6KSpec.C4.eval nv x ((packKey t.2, (t.1 : ℤ)) :: packN f) = _
    rw [L6KSpec.C4.eval_cons, Poly.eval_cons, ih]
    dsimp only
    rw [monoEval_packKey nv x t.2 ht.1 ht.2]
    simp [modHomK]

theorem sysSmall_spec {nv : ℕ} {s : List (Comp.Poly ℕ)} (h : sysSmall nv s = true) :
    ∀ f ∈ s, ∀ t ∈ f, t.2.length ≤ nv ∧ ∀ e ∈ t.2, e < 256 := by
  simpa [sysSmall] using h

/-! ## Systems checked by `L6KSpec.C4` -/

theorem getD_mem_or_nilP {α : Type*} {l : List (List α)} (i : ℕ) : l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · right
    push Not at hi
    exact List.getD_eq_default _ _ hi

/-- **A cofactor identity `Σ c_k s_{i_k} = 1`** (in every field of characteristic `p`, on the packed polynomials of
`s` at the indices `idx`) gives the torus emptiness of `s`. -/
theorem sysEmpty_of_ident {p : ℕ} [NeZero p] {nv : ℕ} {s : List (Comp.Poly ℕ)} (idx : List ℕ)
    (hs : sysSmall nv s = true)
    (hid : ∀ (K : Type) [Field K] [CharP K p] (x : ℕ → K),
      (∀ g ∈ (idx.map fun i => s.getD i []).map packN, L6KSpec.C4.eval nv x g = 0) → (1 : K) = 0) :
    TorusEmptySys p s := by
  intro K _ _ x _
  by_contra hall
  push Not at hall
  refine one_ne_zero (hid K x fun g hg => ?_)
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
  rcases getD_mem_or_nilP (l := s) i with hm | hm
  · rw [eval_packN nv x _ (sysSmall_spec hs _ hm)]
    exact hall _ hm
  · rw [hm]
    rfl

/-- **A cofactor identity `Σ c_k s_{i_k} = x^a`** for a monomial `x^a` of the first seventeen variables (in every
field of characteristic `p`, on the packed polynomials of `s` at the indices `idx`) gives the torus emptiness of `s`:
on the torus the monomial does not vanish. -/
theorem sysEmpty_of_monoIdent {p : ℕ} [NeZero p] {s : List (Comp.Poly ℕ)} (idx : List ℕ) (a : Mono)
    (ha : sysSmall 17 [[(1, a)]] = true) (hs : sysSmall 17 s = true)
    (hid : ∀ (K : Type) [Field K] [CharP K p] (x : ℕ → K),
      (∀ g ∈ (idx.map fun i => s.getD i []).map packN, L6KSpec.C4.eval 17 x g = 0) →
        L6KSpec.C4.eval 17 x (packN [(1, a)]) = 0) :
    TorusEmptySys p s := by
  intro K _ _ x hx
  by_contra hall
  push Not at hall
  have h0 := hid K x fun g hg => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
    rcases getD_mem_or_nilP (l := s) i with hm | hm
    · rw [eval_packN 17 x _ (sysSmall_spec hs _ hm)]
      exact hall _ hm
    · rw [hm]
      rfl
  have ha' := sysSmall_spec ha _ List.mem_cons_self
  have hal : a.length ≤ 17 := (ha' _ List.mem_cons_self).1
  rw [eval_packN 17 x _ ha', Poly.eval_cons, Poly.eval_nil, add_zero] at h0
  have h1 : (modHomK p K).f 1 = 1 := by simp [modHomK]
  rw [h1, one_mul] at h0
  exact mono_eval_ne_zero a 0 (fun k _ hk => hx k (by omega)) h0

/-- **The identity of a leaf** `Σ c_k s_{i_k} + cofR · rabin p = 1` (in every field of characteristic `p`, on the
packed polynomials of `s` at the indices `idx` and `rabin p`, eighteen variables) gives the torus emptiness of `s`. -/
theorem sysEmpty_of_leafIdent {p : ℕ} [NeZero p] {s : List (Comp.Poly ℕ)} (idx : List ℕ)
    (hs : sysSmall 17 s = true)
    (hid : ∀ (K : Type) [Field K] [CharP K p] (x : ℕ → K),
      (∀ g ∈ ((idx.map fun i => s.getD i []) ++ [rabin p]).map packN, L6KSpec.C4.eval 18 x g = 0) →
        (1 : K) = 0) :
    TorusEmptySys p s := by
  intro K _ _ x hx
  by_contra hall
  push Not at hall
  refine one_ne_zero (hid K (ext17 x) fun g hg => ?_)
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
    rcases getD_mem_or_nilP (l := s) i with hm | hm
    · have hsm := sysSmall_spec hs _ hm
      rw [eval_packN 18 (ext17 x) _ fun t ht => ⟨(hsm t ht).1.trans (by norm_num), (hsm t ht).2⟩,
        eval_congr17 (modHomK p K) (fun k hk => ext17_lt x hk) _ fun t ht => (hsm t ht).1]
      exact hall _ hm
    · rw [hm]
      rfl
  · rw [List.mem_singleton.mp hf, eval_packN 18 (ext17 x) (rabin p) ?_]
    · exact eval_rabin_ext17 x hx
    · intro t ht
      simp only [rabin, List.mem_cons, List.mem_nil_iff, or_false] at ht
      rcases ht with rfl | rfl <;> simp

end L6KSpec.Trop
