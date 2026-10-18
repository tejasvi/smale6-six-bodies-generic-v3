import L6SoundK.F4.Terms
import L6SoundK.F1.SortR
import L6SoundK.F1.Ivl

/-!
# Soundness of the kernel check of a cofactor certificate

`cert_sound`: if every bucket passes `bucketOK`, every product occurs exactly once (`coverOK`), the parts of `h` make
up `h` (`hOK`), `h` involves only the masses and is nonzero at `hPoint F`, then the certificate has its meaning
`L6.Poly.CertMeaning` (lean6's interface, the conclusion of `checkCert_sound`): in every commutative ring, at every
assignment at which all generators vanish, `h` vanishes, and `h` is nonzero at `hPoint F`. The cofactors are the sums of
their pieces; they are never formed.
-/

namespace L6K.F4

open L6.Poly Finset

theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (f : α → List β) (g : β → M) :
    ∀ l : List α, ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_map_flatMap f g l, List.map_cons, List.sum_cons]

theorem nth_mem {α : Type} {d : α} : ∀ {l : List α} {i : ℕ}, i < l.length → nth d l i ∈ l
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: _, _ + 1, h => List.mem_cons_of_mem _ (nth_mem (Nat.lt_of_succ_lt_succ h))

theorem nth_mem_or {α : Type} {d : α} : ∀ (l : List α) (i : ℕ), nth d l i ∈ l ∨ nth d l i = d
  | [], _ => Or.inr rfl
  | _ :: _, 0 => Or.inl List.mem_cons_self
  | _ :: l, i + 1 => (nth_mem_or l i).imp (List.mem_cons_of_mem _) id

theorem sum_range_nth {α : Type} {M : Type*} [AddCommMonoid M] (d : α) (F : α → M) :
    ∀ l : List α, ((List.range l.length).map fun j => F (nth d l j)).sum = (l.map F).sum
  | [] => rfl
  | x :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, List.map_cons,
      List.sum_cons]
    congr 1
    exact sum_range_nth d F l

theorem code_div {i j p : ℕ} (hj : j < 16) (hp : p < 2 ^ 20) : code i j p / 2 ^ 24 = i := by
  unfold code
  norm_num at hp ⊢
  omega

theorem code_mid {i j p : ℕ} (hj : j < 16) (hp : p < 2 ^ 20) : code i j p / 2 ^ 20 % 16 = j := by
  unfold code
  norm_num at hp ⊢
  omega

theorem code_mod {i j p : ℕ} (hp : p < 2 ^ 20) : code i j p % 2 ^ 20 = p := by
  unfold code
  norm_num at hp ⊢
  omega

section Values

variable {R : Type*} [CommRing R] (nv : ℕ) (φ : ℕ → R)

/-- The value of a piece. -/
def pval (P : Piece) : R := den nv φ P.pos - den nv φ P.neg

/-- The value of a term. -/
def tval (t : ℕ × ℤ) : R := (t.2 : R) * monoEval nv φ t.1

theorem eval_eq_tval (p : Poly) : eval nv φ p = (p.map (tval nv φ)).sum := rfl

theorem eval_signed (P : Piece) : eval nv φ (signed P) = pval nv φ P := by
  have h1 : ∀ l : NTerms, eval nv φ (l.map fun t => (t.1, (t.2 : ℤ))) = den nv φ l := by
    intro l
    induction l with
    | nil => rfl
    | cons t l ih =>
      rw [List.map_cons, eval_cons, den_cons, ih]
      push_cast
      ring
  have h2 : ∀ l : NTerms, eval nv φ (l.map fun t => (t.1, -(t.2 : ℤ))) = - den nv φ l := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih =>
      rw [List.map_cons, eval_cons, den_cons, ih]
      push_cast
      ring
  unfold signed pval
  rw [eval_append, h1, h2]
  ring

theorem eval_flatMap_signed : ∀ parts : List Piece,
    eval nv φ (parts.flatMap signed) = (parts.map (pval nv φ)).sum
  | [] => rfl
  | P :: parts => by
    rw [List.flatMap_cons, eval_append, eval_signed, eval_flatMap_signed parts, List.map_cons, List.sum_cons]

theorem sides_spec {G : ℕ} (hG : G = guardMask nv) (gens : List Poly) (pcs : List (List Piece)) :
    ∀ ts : List ℕ, ts.all (codeOK G gens pcs) = true →
      ((sides gens pcs ts).1.map (den nv φ)).sum - ((sides gens pcs ts).2.map (den nv φ)).sum =
        (ts.map fun t => tval nv φ (genTerm gens t) * pval nv φ (piece pcs t)).sum
  | [], _ => by
    show (0 : R) - 0 = 0
    ring
  | t :: ts, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ht, hts⟩ := h
    have ih := sides_spec hG gens pcs ts hts
    change (Nat.beq (Nat.land (genTerm gens t).1 G) 0 && guards G (piece pcs t).pos &&
      guards G (piece pcs t).neg) = true at ht
    simp only [Bool.and_eq_true] at ht
    obtain ⟨⟨hk, hp⟩, hn⟩ := ht
    subst hG
    have sk : SmallKey nv (genTerm gens t).1 := smallKey_of_guard (Nat.eq_of_beq_eq_true hk)
    have sp : ∀ u ∈ (piece pcs t).pos, SmallKey nv u.1 := fun u hu => smallKey_of_guard (guards_spec hp u hu)
    have sn : ∀ u ∈ (piece pcs t).neg, SmallKey nv u.1 := fun u hu => smallKey_of_guard (guards_spec hn u hu)
    have e : sides gens pcs (t :: ts) = Int.rec (motive := fun _ => List NTerms × List NTerms)
        (fun c => (shift (genTerm gens t).1 c (piece pcs t).pos :: (sides gens pcs ts).1,
          shift (genTerm gens t).1 c (piece pcs t).neg :: (sides gens pcs ts).2))
        (fun c => (shift (genTerm gens t).1 (c + 1) (piece pcs t).neg :: (sides gens pcs ts).1,
          shift (genTerm gens t).1 (c + 1) (piece pcs t).pos :: (sides gens pcs ts).2))
        (genTerm gens t).2 := rfl
    rw [e, List.map_cons, List.sum_cons, ← ih]
    unfold tval pval
    cases hc : (genTerm gens t).2 with
    | ofNat c =>
      simp only [List.map_cons, List.sum_cons, den_shift nv φ c sk sp, den_shift nv φ c sk sn,
        Int.ofNat_eq_coe, Int.cast_natCast]
      ring
    | negSucc c =>
      simp only [List.map_cons, List.sum_cons, den_shift nv φ (c + 1) sk sp, den_shift nv φ (c + 1) sk sn,
        Int.cast_negSucc]
      push_cast
      ring

/-- **A bucket that passes its check is an identity**: the sum of its products is its part of `h`. -/
theorem bucket_sound {G F r : ℕ} (hG : G = guardMask nv) {gens : List Poly} {pcs : List (List Piece)}
    {ts : List ℕ} {hp : Piece} (h : bucketOK G F r gens pcs ts hp = true) :
    (ts.map fun t => tval nv φ (genTerm gens t) * pval nv φ (piece pcs t)).sum = pval nv φ hp := by
  unfold bucketOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hc, he⟩ := h
  have e := congrArg (den nv φ) (listEq_eq he)
  rw [den_mergeAll, den_mergeAll, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons] at e
  rw [← sides_spec nv φ hG gens pcs ts hc]
  unfold pval
  linear_combination e

/-- The sum over all codes is `Σᵢ gᵢ · cᵢ`, with `cᵢ` the sum of the pieces of cofactor `i`. -/
theorem sum_allCodes {gens : List Poly} {pcs : List (List Piece)} (hg : ∀ g ∈ gens, g.length ≤ 16)
    (hp : ∀ l ∈ pcs, l.length ≤ 2 ^ 20) :
    ((allCodes gens pcs).map fun t => tval nv φ (genTerm gens t) * pval nv φ (piece pcs t)).sum =
      ((List.range gens.length).map fun i => eval nv φ (nth [] gens i) *
        ((List.range (nth [] pcs i).length).map fun p => pval nv φ (nth ⟨[], []⟩ (nth [] pcs i) p)).sum).sum := by
  unfold allCodes
  rw [sum_map_flatMap]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  have hgi : (nth [] gens i).length ≤ 16 := hg _ (nth_mem (List.mem_range.mp hi))
  have hpi : (nth [] pcs i).length ≤ 2 ^ 20 := by
    rcases nth_mem_or pcs i with h | h
    · exact hp _ h
    · rw [h]
      norm_num
  rw [sum_map_flatMap, eval_eq_tval, ← sum_range_nth (0, 0) (tval nv φ) (nth [] gens i), ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj' : j < 16 := lt_of_lt_of_le (List.mem_range.mp hj) hgi
  rw [List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p hp' => ?_)
  have hp'' : p < 2 ^ 20 := lt_of_lt_of_le (List.mem_range.mp hp') hpi
  simp only [Function.comp, genTerm, piece, code_div hj' hp'', code_mid hj' hp'', code_mod hp'']

theorem eval_h_masses_k {h : Poly} (hm : h.all (fun t => decide (t.1 < 256 ^ 6)) = true) (n : ℕ) :
    eval (6 + n) φ h = eval 6 φ h := by
  simp only [List.all_eq_true, decide_eq_true_eq] at hm
  unfold eval
  congr 1
  refine List.map_congr_left fun t ht => ?_
  congr 1
  unfold monoEval
  rw [prod_range_add]
  have : ∏ i ∈ range n, φ (6 + i) ^ keyExp t.1 (6 + i) = 1 := by
    refine prod_eq_one fun i _ => ?_
    have hlt := hm t ht
    have : keyExp t.1 (6 + i) = 0 := by
      rw [keyExp_eq_div]
      have : t.1 / 256 ^ (6 + i) = 0 := by
        apply Nat.div_eq_of_lt
        calc t.1 < 256 ^ 6 := hlt
          _ ≤ 256 ^ (6 + i) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [this]
    rw [this, pow_zero]
  rw [this, mul_one]

end Values

theorem coverOK_spec {D : ℕ} {gens : List Poly} {pcs : List (List Piece)} {ts : List ℕ}
    (h : coverOK D gens pcs ts = true) :
    (∀ g ∈ gens, g.length ≤ 16) ∧ (∀ l ∈ pcs, l.length ≤ 2 ^ 20) ∧ ts.Perm (allCodes gens pcs) := by
  unfold coverOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.ble_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rw [← h3]
  exact (L6K.F1.msortR_perm D ts).symm

theorem coverIvl_spec {gens : List Poly} {pcs : List (List Piece)} {ts : List ℕ} {L : List (ℕ × ℕ)}
    (hh : coverHead gens pcs L = true) (hl : L.all (fun lh => L6K.F1.ivlCheck ts (allCodes gens pcs) lh.1 lh.2) = true) :
    (∀ g ∈ gens, g.length ≤ 16) ∧ (∀ l ∈ pcs, l.length ≤ 2 ^ 20) ∧ ts.Perm (allCodes gens pcs) := by
  unfold coverHead at hh
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.ble_eq] at hh
  obtain ⟨⟨h1, h2⟩, h3⟩ := hh
  exact ⟨h1, h2, (L6K.F1.nodup_perm_of_ivls h3 hl).2⟩

/-- The inverse of `termCode`. -/
def decodeTerm (CB n : ℕ) : ℕ × ℤ :=
  (n / 2 ^ (CB + 1), if n % 2 ^ (CB + 1) % 2 = 0 then ((n % 2 ^ (CB + 1) / 2 : ℕ) : ℤ)
    else Int.negSucc (n % 2 ^ (CB + 1) / 2))

theorem decodeTerm_termCode {CB k : ℕ} {c : ℤ} (hc : c.natAbs < 2 ^ CB) :
    decodeTerm CB (termCode CB k c) = (k, c) := by
  have hM : 0 < 2 ^ (CB + 1) := by positivity
  cases c with
  | ofNat n =>
    have hn : n < 2 ^ CB := by simpa using hc
    have hz : 2 * n < 2 ^ (CB + 1) := by rw [pow_succ]; omega
    have e : termCode CB k (Int.ofNat n) = 2 * n + k * 2 ^ (CB + 1) := by
      unfold termCode
      show k * 2 ^ (CB + 1) + 2 * n = _
      ring
    unfold decodeTerm
    rw [e, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hz, zero_add, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hz]
    simp
  | negSucc n =>
    have hn : n + 1 < 2 ^ CB := by simpa [Int.natAbs_negSucc] using hc
    have hz : 2 * n + 1 < 2 ^ (CB + 1) := by rw [pow_succ]; omega
    have e : termCode CB k (Int.negSucc n) = (2 * n + 1) + k * 2 ^ (CB + 1) := by
      unfold termCode
      show k * 2 ^ (CB + 1) + (2 * n + 1) = _
      ring
    unfold decodeTerm
    rw [e, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hz, zero_add, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hz]
    have h1 : (2 * n + 1) % 2 = 1 := by omega
    have h2 : (2 * n + 1) / 2 = n := by omega
    simp [h1, h2]

theorem hOK_perm {CB D : ℕ} {h : Poly} {parts : List Piece} (hh : hOK CB D h parts = true) :
    (parts.flatMap signed).Perm h := by
  unfold hOK at hh
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, beq_iff_eq] at hh
  obtain ⟨hb, he⟩ := hh
  have hp : ((parts.flatMap signed).map fun t => termCode CB t.1 t.2).Perm (h.map fun t => termCode CB t.1 t.2) := by
    refine (L6K.F1.msortR_perm D _).symm.trans ?_
    rw [he]
    exact L6K.F1.msortR_perm D _
  have e1 : parts.flatMap signed =
      ((parts.flatMap signed).map fun t => termCode CB t.1 t.2).map (decodeTerm CB) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id (parts.flatMap signed)]
    exact List.map_congr_left fun t ht =>
      (decodeTerm_termCode (hb t (List.mem_append_left _ ht))).symm
  have e2 : h = (h.map fun t => termCode CB t.1 t.2).map (decodeTerm CB) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id h]
    exact List.map_congr_left fun t ht => (decodeTerm_termCode (hb t (List.mem_append_right _ ht))).symm
  rw [e1, e2]
  exact hp.map _

/-- **Soundness of the kernel check of a certificate**, from the facts of the cover check. -/
theorem cert_sound_of {nvar D CB : ℕ} {fixed : ℤ} {gens : List Poly} {h : Poly} {pcs : List (List Piece)}
    {bks : List (ℕ × ℕ × List ℕ × Piece)}
    (hb : bks.all (fun b => bucketOK (guardMask (6 + nvar)) b.1 b.2.1 gens pcs b.2.2.1 b.2.2.2) = true)
    (hc : (∀ g ∈ gens, g.length ≤ 16) ∧ (∀ l ∈ pcs, l.length ≤ 2 ^ 20) ∧
      (bks.flatMap fun b => b.2.2.1).Perm (allCodes gens pcs))
    (hh : hOK CB D h (bks.map fun b => b.2.2.2) = true)
    (hm : h.all (fun t => decide (t.1 < 256 ^ 6)) = true)
    (hz : (evalAt 6 (hPoint fixed) h != 0) = true) :
    CertMeaning ⟨nvar, fixed, gens, [], h⟩ := by
  refine ⟨fun {R} _ φ hg => ?_, ?_⟩
  · show eval 6 φ h = 0
    obtain ⟨hg16, hp20, hperm⟩ := hc
    rw [← eval_h_masses_k φ hm nvar, ← eval_perm _ φ (hOK_perm hh), eval_flatMap_signed, List.map_map]
    have e1 : (bks.map ((pval (6 + nvar) φ) ∘ fun b => b.2.2.2)).sum =
        ((bks.flatMap fun b => b.2.2.1).map fun t =>
          tval (6 + nvar) φ (genTerm gens t) * pval (6 + nvar) φ (piece pcs t)).sum := by
      rw [sum_map_flatMap]
      refine congrArg List.sum (List.map_congr_left fun b hb' => ?_)
      exact (bucket_sound (6 + nvar) φ rfl (List.all_eq_true.mp hb b hb')).symm
    rw [e1, (hperm.map _).sum_eq, sum_allCodes (6 + nvar) φ hg16 hp20]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    show eval (6 + nvar) φ (nth [] gens i) * _ = 0
    rw [hg _ (nth_mem (List.mem_range.mp hi)), zero_mul]
  · show eval 6 (fun i => (hPoint fixed).getD i (0 : ℤ)) h ≠ 0
    rw [← evalAt_eq]
    exact bne_iff_ne.mp hz

/-- **Soundness of the kernel check of a certificate.** -/
theorem cert_sound {nvar D CB : ℕ} {fixed : ℤ} {gens : List Poly} {h : Poly} {pcs : List (List Piece)}
    {bks : List (ℕ × ℕ × List ℕ × Piece)}
    (hb : bks.all (fun b => bucketOK (guardMask (6 + nvar)) b.1 b.2.1 gens pcs b.2.2.1 b.2.2.2) = true)
    (hc : coverOK D gens pcs (bks.flatMap fun b => b.2.2.1) = true)
    (hh : hOK CB D h (bks.map fun b => b.2.2.2) = true)
    (hm : h.all (fun t => decide (t.1 < 256 ^ 6)) = true)
    (hz : (evalAt 6 (hPoint fixed) h != 0) = true) :
    CertMeaning ⟨nvar, fixed, gens, [], h⟩ :=
  cert_sound_of (D := D) hb (coverOK_spec hc) hh hm hz

/-- **Soundness of the kernel check of a certificate**, the cover compared by intervals. -/
theorem cert_sound_ivl {nvar D CB : ℕ} {fixed : ℤ} {gens : List Poly} {h : Poly} {pcs : List (List Piece)}
    {bks : List (ℕ × ℕ × List ℕ × Piece)} {L : List (ℕ × ℕ)}
    (hb : bks.all (fun b => bucketOK (guardMask (6 + nvar)) b.1 b.2.1 gens pcs b.2.2.1 b.2.2.2) = true)
    (hc : coverHead gens pcs L = true)
    (hl : L.all (fun lh => L6K.F1.ivlCheck (bks.flatMap fun b => b.2.2.1) (allCodes gens pcs) lh.1 lh.2) = true)
    (hh : hOK CB D h (bks.map fun b => b.2.2.2) = true)
    (hm : h.all (fun t => decide (t.1 < 256 ^ 6)) = true)
    (hz : (evalAt 6 (hPoint fixed) h != 0) = true) :
    CertMeaning ⟨nvar, fixed, gens, [], h⟩ :=
  cert_sound_of (D := D) hb (coverIvl_spec hc hl) hh hm hz

end L6K.F4
