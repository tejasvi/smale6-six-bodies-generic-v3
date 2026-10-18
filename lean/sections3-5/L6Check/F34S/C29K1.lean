import L6F34S.Check
import L6F2.Check
import L6Check.F2.Data.C29
import L6Check.F34.Data.Common
import L6Check.F34.Data.C29
import L6Check.Certs.C04976f6105d50ea4
import L6Check.Certs.C0caf283145283ffb
import L6Check.Certs.C18da9e9512937815
import L6Check.Certs.C1ad9c65c60547bbf
import L6Check.Certs.C28eee02a6830a945
import L6Check.Certs.C2d57c023f5dd4dde
import L6Check.Certs.C3114b5ca0817d4e7
import L6Check.Certs.C35f6c4c708ec33d1
import L6Check.Certs.C41cc2a0df9f68df1
import L6Check.Certs.C426793f245c4eb93
import L6Check.Certs.C4314ebe75f1994a9
import L6Check.Certs.C4a1d8a002c1e3294
import L6Check.Certs.C4bf2f3478894a671
import L6Check.Certs.C4c4f286f9223c675
import L6Check.Certs.C56053a1b4afdd71c
import L6Check.Certs.C59e0304641b0fd0e
import L6Check.Certs.C6ae09f8b25d10bd4
import L6Check.Certs.C6d2bce990d0e417f
import L6Check.Certs.C6dd7c8e608b7373e
import L6Check.Certs.C72c6ea6832ea0931
import L6Check.Certs.C740918de82ddeaf7
import L6Check.Certs.C7a03a79a20539158
import L6Check.Certs.C7b19a211af6bd364
import L6Check.Certs.C7c87c045697b6032
import L6Check.Certs.C80f756ffb4f0d8a2
import L6Check.Certs.C862b369431b75812
import L6Check.Certs.C88cf72b03b325106
import L6Check.Certs.C89ae6b12c4314316
import L6Check.Certs.C8ee387c2184c925d
import L6Check.Certs.C9029a0d174803d69
import L6Check.Certs.C914d344bf8d502cc
import L6Check.Certs.C972e9014b176196b
import L6Check.Certs.C9a088d4abe154ab9
import L6Check.Certs.Ca2d29dd6ead597c1
import L6Check.Certs.Ca5ce291fd63b43b1
import L6Check.Certs.Ca9a3399951913dfa
import L6Check.Certs.Cb328af070b6cb40b
import L6Check.Certs.Cb47055ae31c415c9
import L6Check.Certs.Cb69875f269beb5ca
import L6Check.Certs.Cc1ab002742763f83
import L6Check.Certs.Cc1ed1134280e5006
import L6Check.Certs.Cc2875bce501e2ff0
import L6Check.Certs.Cc69290e9c98d135e
import L6Check.Certs.Cd2661a3b40ddfcb1
import L6Check.Certs.Cd482324ed4adc671
import L6Check.Certs.Cd8330ca45abf11e0
import L6Check.Certs.Cd931ce135ab544e2
import L6Check.Certs.Cdb96fdb7be4f76bc
import L6Check.Certs.Cdd1283a6f1bca57e
import L6Check.Certs.Ce51c5452e0e8f4f9
import L6Check.Certs.Ce6181d77c8f32251
import L6Check.Certs.Ce68c15091cc784c6
import L6Check.Certs.Ce7b4061e97cfa0cb
import L6Check.Certs.Ce836f639badb985f
import L6Check.Certs.Ceca16cfa877cd561
import L6Check.Certs.Cf3b259d6d9a76ddf
import L6Check.Certs.Cfbb34b2ab0989e7b

/-! F3/F4 on the cells of the specification search (Proposition 5.3), class 29, cells 1500 ≤ cell < 1866 of
`data/cells/c29.jsonl`. -/

namespace L6.F34S.Checks

open L6.F34S L6.F34.Data

set_option maxHeartbeats 0 in
/-- Every cell `1500 ≤ cell < 1866` of class 29 is one of the 43 open cells, or its claim (single term or core) holds on
every cell of the specification search with its argmin part; with the counts { single := 84, core1 := 262, core2 := 20, opn := 0 }. -/
theorem F34S_c29_k1 : checkChunkS 29 (L6.F2.diagOf 29) L6.F2.Data.cells_c29 single_29 links_29 pass_29 open43
    [("04976f6105d50ea4", L6.Certs.C04976f6105d50ea4), ("0caf283145283ffb", L6.Certs.C0caf283145283ffb), ("18da9e9512937815", L6.Certs.C18da9e9512937815), ("1ad9c65c60547bbf", L6.Certs.C1ad9c65c60547bbf), ("28eee02a6830a945", L6.Certs.C28eee02a6830a945), ("2d57c023f5dd4dde", L6.Certs.C2d57c023f5dd4dde), ("3114b5ca0817d4e7", L6.Certs.C3114b5ca0817d4e7), ("35f6c4c708ec33d1", L6.Certs.C35f6c4c708ec33d1), ("41cc2a0df9f68df1", L6.Certs.C41cc2a0df9f68df1), ("426793f245c4eb93", L6.Certs.C426793f245c4eb93), ("4314ebe75f1994a9", L6.Certs.C4314ebe75f1994a9), ("4a1d8a002c1e3294", L6.Certs.C4a1d8a002c1e3294), ("4bf2f3478894a671", L6.Certs.C4bf2f3478894a671), ("4c4f286f9223c675", L6.Certs.C4c4f286f9223c675), ("56053a1b4afdd71c", L6.Certs.C56053a1b4afdd71c), ("59e0304641b0fd0e", L6.Certs.C59e0304641b0fd0e), ("6ae09f8b25d10bd4", L6.Certs.C6ae09f8b25d10bd4), ("6d2bce990d0e417f", L6.Certs.C6d2bce990d0e417f), ("6dd7c8e608b7373e", L6.Certs.C6dd7c8e608b7373e), ("72c6ea6832ea0931", L6.Certs.C72c6ea6832ea0931), ("740918de82ddeaf7", L6.Certs.C740918de82ddeaf7), ("7a03a79a20539158", L6.Certs.C7a03a79a20539158), ("7b19a211af6bd364", L6.Certs.C7b19a211af6bd364), ("7c87c045697b6032", L6.Certs.C7c87c045697b6032), ("80f756ffb4f0d8a2", L6.Certs.C80f756ffb4f0d8a2), ("862b369431b75812", L6.Certs.C862b369431b75812), ("88cf72b03b325106", L6.Certs.C88cf72b03b325106), ("89ae6b12c4314316", L6.Certs.C89ae6b12c4314316), ("8ee387c2184c925d", L6.Certs.C8ee387c2184c925d), ("9029a0d174803d69", L6.Certs.C9029a0d174803d69), ("914d344bf8d502cc", L6.Certs.C914d344bf8d502cc), ("972e9014b176196b", L6.Certs.C972e9014b176196b), ("9a088d4abe154ab9", L6.Certs.C9a088d4abe154ab9), ("a2d29dd6ead597c1", L6.Certs.Ca2d29dd6ead597c1), ("a5ce291fd63b43b1", L6.Certs.Ca5ce291fd63b43b1), ("a9a3399951913dfa", L6.Certs.Ca9a3399951913dfa), ("b328af070b6cb40b", L6.Certs.Cb328af070b6cb40b), ("b47055ae31c415c9", L6.Certs.Cb47055ae31c415c9), ("b69875f269beb5ca", L6.Certs.Cb69875f269beb5ca), ("c1ab002742763f83", L6.Certs.Cc1ab002742763f83), ("c1ed1134280e5006", L6.Certs.Cc1ed1134280e5006), ("c2875bce501e2ff0", L6.Certs.Cc2875bce501e2ff0), ("c69290e9c98d135e", L6.Certs.Cc69290e9c98d135e), ("d2661a3b40ddfcb1", L6.Certs.Cd2661a3b40ddfcb1), ("d482324ed4adc671", L6.Certs.Cd482324ed4adc671), ("d8330ca45abf11e0", L6.Certs.Cd8330ca45abf11e0), ("d931ce135ab544e2", L6.Certs.Cd931ce135ab544e2), ("db96fdb7be4f76bc", L6.Certs.Cdb96fdb7be4f76bc), ("dd1283a6f1bca57e", L6.Certs.Cdd1283a6f1bca57e), ("e51c5452e0e8f4f9", L6.Certs.Ce51c5452e0e8f4f9), ("e6181d77c8f32251", L6.Certs.Ce6181d77c8f32251), ("e68c15091cc784c6", L6.Certs.Ce68c15091cc784c6), ("e7b4061e97cfa0cb", L6.Certs.Ce7b4061e97cfa0cb), ("e836f639badb985f", L6.Certs.Ce836f639badb985f), ("eca16cfa877cd561", L6.Certs.Ceca16cfa877cd561), ("f3b259d6d9a76ddf", L6.Certs.Cf3b259d6d9a76ddf), ("fbb34b2ab0989e7b", L6.Certs.Cfbb34b2ab0989e7b)]
    1500 1866 { single := 84, core1 := 262, core2 := 20, opn := 0 } = true := by
  native_decide

end L6.F34S.Checks
