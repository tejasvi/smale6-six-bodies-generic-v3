import CC6Compose.ClaimCore
import L6Sound.F34S.Meaning
import CC6Compose.CellsCore
import CC6Full.Germ.CellIds

/-!
# Bridge: the identities of the checks of Proposition 5.3 are the identities of the full formalization

The certificate project writes the identities of its checks of Proposition 5.3 as term lists (`L6.F34S.XId.terms`,
`L6F34S/Ids.lean`), "with the families, parameters, order of the terms and coefficients of the full formalization".
This file proves it: each identity, converted term by term (`toTerm`: the coefficient as a polynomial in the masses
and `E`, the points as `Pt 6`, the bodies as `Fin 6`), is the identity of `CC6Full` of the same family
(`xid_eq`: `xid I = I.terms.map toTerm`), so it holds at every germ (`xid_holds`).

* `fin6`, `finsetOf`, `toCoef`, `toPtPair`, `toFinPair`, `toTerm`, `xid` (`Identity.bodyZ`, `bodyW`, `potU`, `lagr`,
  `subsetSumZ`, `subsetSumW`, `torque`, `partialVirial`, `differenceZ`, `differenceW`, `potVirial`, `virialE`).
* The lists of bodies and pairs of the certificate project are those of `CC6Full` (`others_eq`, `bodiesIn_eq`,
  `bodiesOut_eq`, `crossOf_eq`, `pairsIn_eq`, `pairsAll_eq`).
* `expo_toTerm`: at a germ realizing the trees, the exponent of a converted term is the exponent `L6.F34S.texp` of
  the term at the converted trees with heights (`toExp`); `isArgmin_of_isArgminX`: an argmin set of the checks
  (`L6.F34S.IsArgminX`) is the argmin set of the identity at the germ (`Identity.IsArgmin`).
* `cval_toTerm_ne_zero`: the coefficients do not vanish at positive masses.
* **`single_false`** (Lemma 5.1): a good identity of the checks with a term of strictly least exponent at the
  converted trees of a germ with positive masses is impossible (`Identity.single`).
-/

namespace CC6Compose

open CC6Full Finset

/-! ## Conversions -/

/-- The body with a given number (`k mod 6`). -/
def fin6 (k : ℕ) : Fin 6 := ⟨k % 6, Nat.mod_lt _ (by norm_num)⟩

@[simp] theorem fin6_val (k : Fin 6) : fin6 k.val = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)

theorem fin6_val_of_lt {k : ℕ} (hk : k < 6) : (fin6 k).val = k := Nat.mod_eq_of_lt hk

theorem fin6_eq_mk {k : ℕ} (hk : k < 6) : fin6 k = ⟨k, hk⟩ := Fin.ext (fin6_val_of_lt hk)

@[simp] theorem ptOfN_val (k : Fin 6) : ptOfN k.val = some k := by
  simp [ptOfN, k.isLt]

@[simp] theorem ptOfN_O : ptOfN L6.F34S.O = none := rfl

theorem ptOfN_of_lt {k : ℕ} (hk : k < 6) : ptOfN k = some (fin6 k) := by
  rw [fin6_eq_mk hk]
  simp [ptOfN, hk]

/-- The set of bodies whose numbers are in the list `J`. -/
def finsetOf (J : List ℕ) : Finset (Fin 6) := univ.filter fun k => k.val ∈ J

theorem mem_finsetOf {J : List ℕ} {k : Fin 6} : k ∈ finsetOf J ↔ k.val ∈ J := by simp [finsetOf]

noncomputable section

/-- The coefficient `num / den · Π m_i · (Σ_k m_k)^[msum] · E^[e]` of a term of the checks, as a polynomial in the
masses and `E`. -/
def toCoef (c : L6.F34S.XCoef) : MvPolynomial (Fin 6 ⊕ Unit) ℚ :=
  MvPolynomial.C ((c.num : ℚ) / c.den) * (c.masses.map fun i => Identity.cm (fin6 i)).prod *
    (if c.msum then ∑ k, Identity.cm k else 1) * (if c.e then Identity.cE else 1)

/-- A factor `z_p − z_q` of the checks (points as numbers, `O = 6`) as a pair of points. -/
def toPtPair (pq : ℕ × ℕ) : Pt 6 × Pt 6 := (ptOfN pq.1, ptOfN pq.2)

/-- A factor `p_kl` of the checks as a pair of bodies. -/
def toFinPair (kl : ℕ × ℕ) : Fin 6 × Fin 6 := (fin6 kl.1, fin6 kl.2)

/-- A term of the checks as a term of the full formalization. -/
def toTerm (t : L6.F34S.XTerm) : Term 6 :=
  ⟨toCoef t.coef, t.zs.map toPtPair, t.ws.map toPtPair, t.ps.map toFinPair⟩

/-- The identity of the full formalization of the same family and parameters as an identity of the checks. -/
def xid : L6.F34S.XId → Identity 6
  | .bodyZ k => Identity.bodyZ (fin6 k)
  | .bodyW k => Identity.bodyW (fin6 k)
  | .potU => Identity.potU 6
  | .lagr => Identity.lagr 6
  | .subsetZ J => Identity.subsetSumZ (finsetOf J)
  | .subsetW J => Identity.subsetSumW (finsetOf J)
  | .torque J => Identity.torque (finsetOf J)
  | .virial J => Identity.partialVirial (finsetOf J)
  | .diffZ k l => Identity.differenceZ (fin6 k) (fin6 l)
  | .diffW k l => Identity.differenceW (fin6 k) (fin6 l)
  | .potVirial => Identity.potVirial 6
  | .virialE => Identity.virialE 6

/-- The identities hold at every germ. -/
theorem xid_holds (I : L6.F34S.XId) : (xid I).Holds := by
  cases I with
  | bodyZ k => exact Identity.bodyZ_holds _
  | bodyW k => exact Identity.bodyW_holds _
  | potU => exact Identity.potU_holds
  | lagr => exact Identity.lagr_holds
  | subsetZ J => exact Identity.subsetSumZ_holds _
  | subsetW J => exact Identity.subsetSumW_holds _
  | torque J => exact Identity.torque_holds _
  | virial J => exact Identity.partialVirial_holds _
  | diffZ k l => exact Identity.differenceZ_holds _ _
  | diffW k l => exact Identity.differenceW_holds _ _
  | potVirial => exact Identity.potVirial_holds
  | virialE => exact Identity.virialE_holds

end

/-! ## Lists of bodies and pairs -/

theorem range6_eq : List.range 6 = (List.finRange 6).map Fin.val := by decide

theorem others_eq (k : Fin 6) : L6.F34S.others k.val = ((List.finRange 6).filter fun l => l ≠ k).map Fin.val :=
  range_filter_ne k

theorem bodiesIn_eq (J : List ℕ) : L6.F34S.bodiesIn J = (Identity.bodiesIn (finsetOf J)).map Fin.val := by
  unfold L6.F34S.bodiesIn Identity.bodiesIn
  rw [range6_eq, List.filter_map]
  congr 1
  refine List.filter_congr fun k _ => ?_
  simp [mem_finsetOf]

theorem bodiesOut_eq (J : List ℕ) : L6.F34S.bodiesOut J = (Identity.bodiesIn (finsetOf J)ᶜ).map Fin.val := by
  unfold L6.F34S.bodiesOut Identity.bodiesIn
  rw [range6_eq, List.filter_map]
  congr 1
  refine List.filter_congr fun k _ => ?_
  simp [mem_finsetOf]

/-- A pair of bodies as a pair of numbers. -/
def valPair (kl : Fin 6 × Fin 6) : ℕ × ℕ := (kl.1.val, kl.2.val)

theorem crossOf_eq (J : List ℕ) : L6.F34S.crossOf J = (Identity.cross (finsetOf J)).map valPair := by
  unfold L6.F34S.crossOf Identity.cross
  rw [bodiesIn_eq, bodiesOut_eq, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun k _ => ?_
  rw [List.map_map, List.map_map]
  rfl

theorem pairsIn_eq (J : List ℕ) : L6.F34S.pairsIn J = (Identity.pairsIn (finsetOf J)).map valPair := by
  unfold L6.F34S.pairsIn Identity.pairsIn
  rw [bodiesIn_eq, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun k _ => ?_
  rw [List.filter_map, List.map_map, List.map_map]
  congr 1

theorem pairsAll_eq : L6.F34S.pairsAll = (Identity.pairs 6).map valPair := by decide

/-! ## The identities, term by term -/

section families

open L6.F34S (XId)

theorem xid_bodyZ (k : Fin 6) : xid (.bodyZ k.val) = (XId.bodyZ k.val).terms.map toTerm := by
  simp only [xid, fin6_val, Identity.bodyZ, XId.terms, List.map_cons, others_eq, List.map_map]
  congr 1
  · simp [toTerm, toCoef, toPtPair]
  · refine List.map_congr_left fun l _ => ?_
    simp [toTerm, toCoef, toPtPair, toFinPair, L6.F34S.p3]

theorem xid_bodyW (k : Fin 6) : xid (.bodyW k.val) = (XId.bodyW k.val).terms.map toTerm := by
  simp only [xid, fin6_val, Identity.bodyW, XId.terms, List.map_cons, others_eq, List.map_map]
  congr 1
  · simp [toTerm, toCoef, toPtPair]
  · refine List.map_congr_left fun l _ => ?_
    simp [toTerm, toCoef, toPtPair, toFinPair, L6.F34S.p3]

theorem xid_potU : xid .potU = XId.potU.terms.map toTerm := by
  simp only [xid, Identity.potU, XId.terms, List.map_append, pairsAll_eq, List.map_map, List.map_cons,
    List.map_nil]
  congr 1
  · refine List.map_congr_left fun kl _ => ?_
    simp [toTerm, toCoef, toFinPair, valPair]
  · simp [toTerm, toCoef]

theorem xid_lagr : xid .lagr = XId.lagr.terms.map toTerm := by
  simp only [xid, Identity.lagr, XId.terms, List.map_append, pairsAll_eq, List.map_map, List.map_cons,
    List.map_nil]
  congr 1
  · refine List.map_congr_left fun kl _ => ?_
    simp [toTerm, toCoef, toPtPair, valPair]
  · simp [toTerm, toCoef]

theorem xid_subsetZ (J : List ℕ) : xid (.subsetZ J) = (XId.subsetZ J).terms.map toTerm := by
  simp only [xid, Identity.subsetSumZ, XId.terms, List.map_append, bodiesIn_eq, crossOf_eq, List.map_map]
  congr 1
  · refine List.map_congr_left fun k _ => ?_
    simp [toTerm, toCoef, toPtPair]
  · refine List.map_congr_left fun kl _ => ?_
    simp [toTerm, toCoef, toPtPair, toFinPair, valPair, L6.F34S.p3]

theorem xid_subsetW (J : List ℕ) : xid (.subsetW J) = (XId.subsetW J).terms.map toTerm := by
  simp only [xid, Identity.subsetSumW, XId.terms, List.map_append, bodiesIn_eq, crossOf_eq, List.map_map]
  congr 1
  · refine List.map_congr_left fun k _ => ?_
    simp [toTerm, toCoef, toPtPair]
  · refine List.map_congr_left fun kl _ => ?_
    simp [toTerm, toCoef, toPtPair, toFinPair, valPair, L6.F34S.p3]

theorem xid_torque (J : List ℕ) : xid (.torque J) = (XId.torque J).terms.map toTerm := by
  simp only [xid, Identity.torque, XId.terms, crossOf_eq, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun kl _ => ?_
  simp [toTerm, toCoef, toPtPair, toFinPair, valPair, L6.F34S.p3]

theorem xid_virial (J : List ℕ) : xid (.virial J) = (XId.virial J).terms.map toTerm := by
  simp only [xid, Identity.partialVirial, XId.terms, List.map_append, bodiesIn_eq, pairsIn_eq, crossOf_eq,
    List.map_map, List.flatMap_map, List.map_flatMap]
  congr 1
  · congr 1
    · refine List.map_congr_left fun k _ => ?_
      simp [toTerm, toCoef, toPtPair]
    · refine List.map_congr_left fun kl _ => ?_
      simp [toTerm, toCoef, toFinPair, valPair]
  · refine List.flatMap_congr fun kl _ => ?_
    have h2 : (MvPolynomial.C (-1 / 2 : ℚ) : MvPolynomial (Fin 6 ⊕ Unit) ℚ) = -MvPolynomial.C 2⁻¹ := by
      rw [neg_div, one_div, map_neg]
    simp [toTerm, toCoef, toPtPair, toFinPair, valPair, L6.F34S.p3, h2]

theorem xid_diffZ (k l : Fin 6) : xid (.diffZ k.val l.val) = (XId.diffZ k.val l.val).terms.map toTerm := by
  simp only [xid, fin6_val, Identity.differenceZ, XId.terms, List.map_cons, List.map_append, others_eq,
    List.map_map]
  congr 1
  · simp [toTerm, toCoef, toPtPair]
  · congr 1
    · refine List.map_congr_left fun j _ => ?_
      simp [toTerm, toCoef, toPtPair, toFinPair, L6.F34S.p3]
    · refine List.map_congr_left fun j _ => ?_
      simp [toTerm, toCoef, toPtPair, toFinPair, L6.F34S.p3]

theorem xid_diffW (k l : Fin 6) : xid (.diffW k.val l.val) = (XId.diffW k.val l.val).terms.map toTerm := by
  simp only [xid, fin6_val, Identity.differenceW, XId.terms, List.map_cons, List.map_append, others_eq,
    List.map_map]
  congr 1
  · simp [toTerm, toCoef, toPtPair]
  · congr 1
    · refine List.map_congr_left fun j _ => ?_
      simp [toTerm, toCoef, toPtPair, toFinPair, L6.F34S.p3]
    · refine List.map_congr_left fun j _ => ?_
      simp [toTerm, toCoef, toPtPair, toFinPair, L6.F34S.p3]

theorem xid_potVirial : xid .potVirial = XId.potVirial.terms.map toTerm := by
  simp only [xid, Identity.potVirial, XId.terms, List.map_append, pairsAll_eq, range6_eq, List.map_map]
  congr 1
  · refine List.map_congr_left fun kl _ => ?_
    simp [toTerm, toCoef, toFinPair, valPair]
  · refine List.map_congr_left fun k _ => ?_
    simp [toTerm, toCoef, toPtPair]

theorem xid_virialE : xid .virialE = XId.virialE.terms.map toTerm := by
  simp only [xid, Identity.virialE, XId.terms, List.map_append, range6_eq, List.map_map, List.map_cons,
    List.map_nil]
  congr 1
  · refine List.map_congr_left fun k _ => ?_
    simp [toTerm, toCoef, toPtPair]
  · simp [toTerm, toCoef]

end families

/-- **The identities of the checks are those of the full formalization**: a valid identity of the checks, converted
term by term, is the identity `xid I` of `CC6Full` of the same family and parameters. -/
theorem xid_eq {I : L6.F34S.XId} (hI : I.valid = true) : xid I = I.terms.map toTerm := by
  cases I with
  | bodyZ k =>
    have hk : k < 6 := by simpa [L6.F34S.XId.valid] using hI
    exact xid_bodyZ ⟨k, hk⟩
  | bodyW k =>
    have hk : k < 6 := by simpa [L6.F34S.XId.valid] using hI
    exact xid_bodyW ⟨k, hk⟩
  | potU => exact xid_potU
  | lagr => exact xid_lagr
  | subsetZ J => exact xid_subsetZ J
  | subsetW J => exact xid_subsetW J
  | torque J => exact xid_torque J
  | virial J => exact xid_virial J
  | diffZ k l =>
    have hkl : k < l ∧ l < 6 := by simpa [L6.F34S.XId.valid] using hI
    exact xid_diffZ ⟨k, by omega⟩ ⟨l, hkl.2⟩
  | diffW k l =>
    have hkl : k < l ∧ l < 6 := by simpa [L6.F34S.XId.valid] using hI
    exact xid_diffW ⟨k, by omega⟩ ⟨l, hkl.2⟩
  | potVirial => exact xid_potVirial
  | virialE => exact xid_virialE

theorem xid_length {I : L6.F34S.XId} (hI : I.valid = true) : (xid I).length = I.terms.length := by
  rw [xid_eq hI, List.length_map]

theorem xid_getElem {I : L6.F34S.XId} (hI : I.valid = true) {i : ℕ} (hi : i < (xid I).length) :
    (xid I)[i] = toTerm (I.terms[i]'(by rwa [xid_length hI] at hi)) := by
  rw [List.getElem_of_eq (xid_eq hI) hi, List.getElem_map]

theorem valid_of_good {I : L6.F34S.XId} (hI : I.good = true) : I.valid = true := by
  unfold L6.F34S.XId.good at hI
  simp only [Bool.and_eq_true] at hI
  exact hI.1.1

theorem good_getElem {I : L6.F34S.XId} (hI : I.good = true) {k : ℕ} (hk : k < I.terms.length) :
    (I.terms[k]).good = true := by
  have := L6.F34S.good_get hI hk
  rwa [getElem!_pos I.terms k hk] at this

/-! ## Exponents at a germ -/

section expo

variable {m : Fin 6 → ℝ} {G : Germ 6 m} {Tz Tw : TreeShape 6} {htz htw : Finset (Pt 6) → ℚ}

theorem coe_sum_map {α : Type*} (L : List α) (f : α → ℚ) :
    (((L.map f).sum : ℚ) : WithTop ℚ) = (L.map fun a => ((f a : ℚ) : WithTop ℚ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, WithTop.coe_add]

/-- The exponent of a factor `pos_p − pos_q` at the converted tree with heights is that of the germ. -/
theorem sepExp_eq {T : TreeShape 6} {h : Pt 6 → Pt 6 → WithTop ℚ} {hts : Finset (Pt 6) → ℚ}
    (hR : T.Realizes h hts) {pq : ℕ × ℕ} (h1 : pq.1 < 7) (h2 : pq.2 < 7) :
    L6.F34S.sepExp (toExp T hts) pq = h (ptOfN pq.1) (ptOfN pq.2) := by
  obtain ⟨p, q⟩ := pq
  obtain ⟨a, rfl⟩ : ∃ a, ptN a = p := ⟨ptOfN p, ptN_ptOfN h1⟩
  obtain ⟨b, rfl⟩ : ∃ b, ptN b = q := ⟨ptOfN q, ptN_ptOfN h2⟩
  simp only [L6.F34S.sepExp, ptOfN_ptN, hR.eq_hgt, TreeShape.hgt]
  rw [toExp_T, toTS_sameLeaf]
  by_cases hs : T.SameLeaf a b
  · simp [hs]
  · simp [hs, toExp_e hR.wf]

theorem goodSep_lt {pq : ℕ × ℕ} (h : L6.F34S.goodSep pq = true) : pq.1 < 7 ∧ pq.2 < 7 := by
  unfold L6.F34S.goodSep at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨h1, h2 | ⟨h2, -⟩⟩ := h
  · exact ⟨by omega, by rw [h2]; decide⟩
  · exact ⟨by omega, by omega⟩

theorem goodP_spec {kl : ℕ × ℕ} (h : L6.F34S.goodP kl = true) : kl.1 < 6 ∧ kl.2 < 6 ∧ kl.1 ≠ kl.2 := by
  unfold L6.F34S.goodP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **The exponent of a converted term at a germ** realizing the trees is the exponent of the term of the checks at
the converted trees with heights. -/
theorem expo_toTerm (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {t : L6.F34S.XTerm}
    (ht : t.good = true) : (toTerm t).expo G = L6.F34S.texp (toExp Tz htz) (toExp Tw htw) t := by
  unfold L6.F34S.XTerm.good at ht
  simp only [Bool.and_eq_true, List.all_eq_true] at ht
  obtain ⟨⟨⟨⟨⟨hzs, hws⟩, hps⟩, -⟩, -⟩, -⟩ := ht
  unfold Term.expo L6.F34S.texp toTerm
  simp only [List.map_map]
  congr 1
  · congr 1
    · congr 1
      refine List.map_congr_left fun pq hpq => ?_
      have hlt := goodSep_lt (hzs pq hpq)
      exact (sepExp_eq hRz hlt.1 hlt.2).symm
    · congr 1
      refine List.map_congr_left fun pq hpq => ?_
      have hlt := goodSep_lt (hws pq hpq)
      exact (sepExp_eq hRw hlt.1 hlt.2).symm
  · rw [coe_sum_map]
    congr 1
    refine List.map_congr_left fun kl hkl => ?_
    obtain ⟨h1, h2, h12⟩ := goodP_spec (hps kl hkl)
    have hne : fin6 kl.1 ≠ fin6 kl.2 := fun e => h12 (by
      rw [← fin6_val_of_lt h1, ← fin6_val_of_lt h2, e])
    have hx := xkl_eq hRz hRw hne
    rw [fin6_val_of_lt h1, fin6_val_of_lt h2] at hx
    simp only [Function.comp_apply, toFinPair]
    rw [G.orderTop_p hne, hx]

/-- **An argmin set of the checks is the argmin set of the identity at the germ.** -/
theorem isArgmin_of_isArgminX (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {I : L6.F34S.XId}
    (hg : I.good = true) {S : List ℕ} (h : L6.F34S.IsArgminX I.terms (toExp Tz htz) (toExp Tw htw) S) :
    (xid I).IsArgmin G S.toFinset := by
  have hv := valid_of_good hg
  obtain ⟨-, -, e, hin, hout⟩ := h
  refine ⟨e, fun i hi => ?_, fun i hi => ?_⟩
  · have hi' : i.1 < I.terms.length := by rw [← xid_length hv]; exact i.2
    rw [xid_getElem hv i.2, expo_toTerm hRz hRw (good_getElem hg hi'), ← getElem!_pos I.terms i.1 hi']
    exact hin i.1 (List.mem_toFinset.mp hi)
  · have hi' : i.1 < I.terms.length := by rw [← xid_length hv]; exact i.2
    rw [xid_getElem hv i.2, expo_toTerm hRz hRw (good_getElem hg hi'), ← getElem!_pos I.terms i.1 hi']
    exact hout i.1 hi' fun hm => hi (List.mem_toFinset.mpr hm)

end expo

/-! ## Coefficients -/

section coef

variable {m : Fin 6 → ℝ}

/-- The value of a converted coefficient at a germ. -/
theorem cval_toCoef (G : Germ 6 m) (c : L6.F34S.XCoef) :
    G.cval (toCoef c) = (((c.num : ℚ) / c.den : ℚ) : ℂ) * (c.masses.map fun i => (m (fin6 i) : ℂ)).prod *
      (if c.msum then ∑ k, (m k : ℂ) else 1) * (if c.e then G.E else 1) := by
  unfold toCoef
  rw [Identity.cval_mul, Identity.cval_mul, Identity.cval_mul]
  congr 1
  · congr 1
    · congr 1
      · simp [Germ.cval]
      · rw [Germ.cval, map_list_prod, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp
    · split_ifs
      · rw [Identity.cval_sum]
        exact Finset.sum_congr rfl fun k _ => Identity.cval_cm G k
      · exact Identity.cval_one G
  · split_ifs
    · exact Identity.cval_cE G
    · exact Identity.cval_one G

/-- The coefficients of the terms do not vanish at positive masses (for a nonzero numerator). -/
theorem cval_toCoef_ne_zero (hm : ∀ k, 0 < m k) (G : Germ 6 m) {c : L6.F34S.XCoef} (hnum : c.num ≠ 0)
    (hden : c.den ≠ 0) : G.cval (toCoef c) ≠ 0 := by
  rw [cval_toCoef]
  have hm0 : ∀ k, (m k : ℂ) ≠ 0 := fun k => Complex.ofReal_ne_zero.mpr (hm k).ne'
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · have : ((c.num : ℚ) / c.den : ℚ) ≠ 0 :=
      div_ne_zero (Int.cast_ne_zero.mpr hnum) (Nat.cast_ne_zero.mpr hden)
    exact_mod_cast this
  · refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨i, -, hi⟩ := List.mem_map.mp h0
    exact hm0 _ hi
  · split_ifs
    · rw [← Complex.ofReal_sum, Complex.ofReal_ne_zero]
      exact (Finset.sum_pos (fun k _ => hm k) ⟨0, Finset.mem_univ _⟩).ne'
    · exact one_ne_zero
  · split_ifs
    · exact G.E_ne
    · exact one_ne_zero

/-- Every term of an identity of the checks has the numerator `1` or `-1`. -/
theorem terms_num (I : L6.F34S.XId) : ∀ t ∈ I.terms, t.coef.num ≠ 0 := by
  have h : (I.terms.all fun t => t.coef.num != 0) = true := by
    cases I <;> simp [L6.F34S.XId.terms, List.all_map, List.all_flatMap, List.all_append, Function.comp_def]
  simpa using h

theorem den_ne_zero {t : L6.F34S.XTerm} (ht : t.good = true) : t.coef.den ≠ 0 := by
  unfold L6.F34S.XTerm.good at ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht.1.1.2 with h | h <;> rw [h] <;> decide

end coef

/-! ## Lemma 5.1 at the converted trees -/

/-- **Lemma 5.1 for the single terms of the checks**: at the converted trees with heights of a germ with positive
masses, no good identity of the checks has a term of strictly least exponent (`L6.F34S.IsArgminX … [i]`). -/
theorem single_false {m : Fin 6 → ℝ} (hm : ∀ k, 0 < m k) {G : Germ 6 m} {Tz Tw : TreeShape 6}
    {htz htw : Finset (Pt 6) → ℚ} (hRz : Tz.Realizes G.hz htz) (hRw : Tw.Realizes G.hw htw) {I : L6.F34S.XId}
    (hg : I.good = true) {i : ℕ} (h : L6.F34S.IsArgminX I.terms (toExp Tz htz) (toExp Tw htw) [i]) : False := by
  have hv := valid_of_good hg
  have hi : i < I.terms.length := h.2.1 i List.mem_cons_self
  have hi' : i < (xid I).length := by rw [xid_length hv]; exact hi
  have hS := isArgmin_of_isArgminX hRz hRw hg h
  rw [show [i].toFinset = ({i} : Finset ℕ) by simp] at hS
  refine Identity.single (xid_holds I) G (i₀ := ⟨i, hi'⟩) ?_ hS
  rw [xid_getElem hv hi']
  exact cval_toCoef_ne_zero hm G (terms_num I _ (List.getElem_mem hi)) (den_ne_zero (good_getElem hg hi))

end CC6Compose
