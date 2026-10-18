import Lean6.Special.D88.Count.Final

/-! The axioms of the theorems of Lemma 6.19(b)'s bridge (`lake env lean gen/d88count/br_axioms.lean`). -/

open Lean6.Special.D88.Count

#print axioms DegRevLex.wellFoundedLT
#print axioms DegRevLex.toDegRevLex_monotone
#print axioms degRevLex_lt_iff'
#print axioms degRevLex_single_lt_iff
#print axioms grevGtStd_iff
#print axioms eval_toMv
#print axioms mem_span_of_good
#print axioms lead_toMv
#print axioms std_subset_of_border
#print axioms span_std
#print axioms finrank_le_of_border
#print axioms dimCheck_sound
#print axioms eval_s12InputsZ
#print axioms eval_kcInputsZ
#print axioms eval_reduceMod
#print axioms toMv_s12Input
#print axioms toMv_kcInput
#print axioms span_s12Inputs_le
#print axioms span_kcInputs_le
#print axioms count_KC_of
#print axioms count_S12_of
