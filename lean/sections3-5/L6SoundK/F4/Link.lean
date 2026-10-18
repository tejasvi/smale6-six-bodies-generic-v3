import L6SoundK.F4.Cert

/-!
# From the literal certificates to the texts

`meaning_of_link`: if a certificate text parses to a certificate with the generators, `h`, `nvar` and `fixed` of a
literal certificate `c₀` (a `native_decide` check of version 1, `L6CheckK.F4Link`), and `c₀` has its meaning (the
kernel theorem `L6CheckK.F4.C<H>.cert`), then the text parses to a certificate with its meaning: the conclusion of
lean6's `checkCert_meaning`.
-/

namespace L6K.F4

open L6.Poly

theorem meaning_of_link {s : String} {c0 : Cert}
    (hl : (parseCert s).map (fun c => (c.nvar, c.fixed, c.gens, c.h)) = some (c0.nvar, c0.fixed, c0.gens, c0.h))
    (hm : CertMeaning c0) : ∃ c, parseCert s = some c ∧ CertMeaning c := by
  cases hp : parseCert s with
  | none =>
    rw [hp] at hl
    exact absurd hl (by simp)
  | some c =>
    rw [hp] at hl
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨h1, h2, h3, h4⟩ := hl
    refine ⟨c, rfl, ?_⟩
    unfold CertMeaning at hm ⊢
    rw [h1, h2, h3, h4]
    exact hm

end L6K.F4
