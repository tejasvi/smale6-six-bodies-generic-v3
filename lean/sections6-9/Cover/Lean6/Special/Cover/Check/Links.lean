import L6Check.F34.Data.C0
import L6Check.F34.Data.C3
import L6Check.F34.Data.C4
import L6Check.F34.Data.C8
import L6Check.F34.Data.C10
import L6Check.F34.Data.C12
import L6Check.F34.Data.C13
import L6Check.F34.Data.C14
import L6Check.F34.Data.C15
import L6Check.F34.Data.C16
import L6Check.F34.Data.C20
import L6Check.F34.Data.C22
import L6Check.F34.Data.C23
import L6Check.F34.Data.C24
import L6Check.F34.Data.C25
import L6Check.F34.Data.C28
import L6Check.F34.Data.C29
import L6Check.F34.Data.C30
import L6Check.F34.Data.C31
import L6Check.F34.Data.C34
import L6Check.F34.Data.C35
import L6Check.F34.Data.C40
import L6Check.F34.Data.C42
import L6Check.F34.Data.C44
import L6Check.F34.Data.C47
import L6Check.F34.Data.C53
import L6Check.F34.Data.C56
import L6Check.F34.Data.C57
import L6Check.F34.Data.C58
import L6Check.F34.Data.C62
import L6Check.F34.Data.C63
import L6Check.F34.Data.C64
import L6Check.F34.Data.C65
import L6Check.F34.Data.C66
import L6Check.F34.Data.C67
import L6Check.F34.Data.C69
import L6Check.F34.Data.C84
import L6Check.F34.Data.C110
import L6Check.F34.Data.C116
import L6Check.F34.Data.C117
import L6Check.F34.Data.C119
import L6Check.F34.Data.C120
import L6Check.F34.Data.C121
import L6Check.F34.Data.C122
import L6Check.F34.Data.C123
import L6Check.F34.Data.C124
import L6Check.F34.Data.C126
import L6Check.F34.Data.C128
import L6Check.F34.Data.C129
import L6Check.F34.Data.C130
import L6Check.F34.Data.C132
import L6Check.F34.Data.C133
import L6Check.F34.Data.C142
import L6Check.F34.Data.C143
import L6Check.F34.Data.C146
import L6Check.F34.Data.C147
import L6Check.F34.Data.C148
import L6Check.F34.Data.C149
import L6Check.F34.Data.C150
import L6Check.F34.Data.C167
import L6Check.F34.Data.C169
import L6Check.F34.Data.C170
import L6Check.F34.Data.C171
import L6Check.F34.Data.C172
import L6Check.F34.Data.C173
import L6Check.F34.Data.C183

/-!
# Proposition 9.23: the core links

The link files of the companion project `lean6` (`data/f4/links/c<N>.txt`, embedded in `L6Check.F34.Data`): for each
core cell of the class `N`, the names of the identities of its core. The 66 classes listed are those with core cells.
-/

namespace Lean6.Special.Cover

/-- The link files, `(class, text)`. -/
def coreLinks : List (Nat × String) :=
  [(0, L6.F34.Data.links_0), (3, L6.F34.Data.links_3), (4, L6.F34.Data.links_4), (8, L6.F34.Data.links_8), (10,
   L6.F34.Data.links_10), (12, L6.F34.Data.links_12), (13, L6.F34.Data.links_13), (14, L6.F34.Data.links_14), (15,
   L6.F34.Data.links_15), (16, L6.F34.Data.links_16), (20, L6.F34.Data.links_20), (22, L6.F34.Data.links_22), (23,
   L6.F34.Data.links_23), (24, L6.F34.Data.links_24), (25, L6.F34.Data.links_25), (28, L6.F34.Data.links_28), (29,
   L6.F34.Data.links_29), (30, L6.F34.Data.links_30), (31, L6.F34.Data.links_31), (34, L6.F34.Data.links_34), (35,
   L6.F34.Data.links_35), (40, L6.F34.Data.links_40), (42, L6.F34.Data.links_42), (44, L6.F34.Data.links_44), (47,
   L6.F34.Data.links_47), (53, L6.F34.Data.links_53), (56, L6.F34.Data.links_56), (57, L6.F34.Data.links_57), (58,
   L6.F34.Data.links_58), (62, L6.F34.Data.links_62), (63, L6.F34.Data.links_63), (64, L6.F34.Data.links_64), (65,
   L6.F34.Data.links_65), (66, L6.F34.Data.links_66), (67, L6.F34.Data.links_67), (69, L6.F34.Data.links_69), (84,
   L6.F34.Data.links_84), (110, L6.F34.Data.links_110), (116, L6.F34.Data.links_116), (117, L6.F34.Data.links_117),
   (119, L6.F34.Data.links_119), (120, L6.F34.Data.links_120), (121, L6.F34.Data.links_121), (122,
   L6.F34.Data.links_122), (123, L6.F34.Data.links_123), (124, L6.F34.Data.links_124), (126, L6.F34.Data.links_126),
   (128, L6.F34.Data.links_128), (129, L6.F34.Data.links_129), (130, L6.F34.Data.links_130), (132,
   L6.F34.Data.links_132), (133, L6.F34.Data.links_133), (142, L6.F34.Data.links_142), (143, L6.F34.Data.links_143),
   (146, L6.F34.Data.links_146), (147, L6.F34.Data.links_147), (148, L6.F34.Data.links_148), (149,
   L6.F34.Data.links_149), (150, L6.F34.Data.links_150), (167, L6.F34.Data.links_167), (169, L6.F34.Data.links_169),
   (170, L6.F34.Data.links_170), (171, L6.F34.Data.links_171), (172, L6.F34.Data.links_172), (173,
   L6.F34.Data.links_173), (183, L6.F34.Data.links_183)]

end Lean6.Special.Cover
