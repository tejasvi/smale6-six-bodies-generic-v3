import L6F34.Check
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
import L6Check.F34.Data.C55
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
import L6Check.F34.Data.C127
import L6Check.F34.Data.C128
import L6Check.F34.Data.C129
import L6Check.F34.Data.C130
import L6Check.F34.Data.C131
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

/-! F3/F4: the number of stored cells of each of the 191 classes (the chunks of each class cover them). -/

namespace L6.F34.Data

/-- Class 1 has no listed cell. -/
def cells_1 : String := include_str "../../data/cells/c1.jsonl"
/-- Class 2 has no listed cell. -/
def cells_2 : String := include_str "../../data/cells/c2.jsonl"
/-- Class 5 has no listed cell. -/
def cells_5 : String := include_str "../../data/cells/c5.jsonl"
/-- Class 6 has no listed cell. -/
def cells_6 : String := include_str "../../data/cells/c6.jsonl"
/-- Class 7 has no listed cell. -/
def cells_7 : String := include_str "../../data/cells/c7.jsonl"
/-- Class 9 has no listed cell. -/
def cells_9 : String := include_str "../../data/cells/c9.jsonl"
/-- Class 11 has no listed cell. -/
def cells_11 : String := include_str "../../data/cells/c11.jsonl"
/-- Class 17 has no listed cell. -/
def cells_17 : String := include_str "../../data/cells/c17.jsonl"
/-- Class 18 has no listed cell. -/
def cells_18 : String := include_str "../../data/cells/c18.jsonl"
/-- Class 19 has no listed cell. -/
def cells_19 : String := include_str "../../data/cells/c19.jsonl"
/-- Class 21 has no listed cell. -/
def cells_21 : String := include_str "../../data/cells/c21.jsonl"
/-- Class 26 has no listed cell. -/
def cells_26 : String := include_str "../../data/cells/c26.jsonl"
/-- Class 27 has no listed cell. -/
def cells_27 : String := include_str "../../data/cells/c27.jsonl"
/-- Class 32 has no listed cell. -/
def cells_32 : String := include_str "../../data/cells/c32.jsonl"
/-- Class 33 has no listed cell. -/
def cells_33 : String := include_str "../../data/cells/c33.jsonl"
/-- Class 36 has no listed cell. -/
def cells_36 : String := include_str "../../data/cells/c36.jsonl"
/-- Class 37 has no listed cell. -/
def cells_37 : String := include_str "../../data/cells/c37.jsonl"
/-- Class 38 has no listed cell. -/
def cells_38 : String := include_str "../../data/cells/c38.jsonl"
/-- Class 39 has no listed cell. -/
def cells_39 : String := include_str "../../data/cells/c39.jsonl"
/-- Class 41 has no listed cell. -/
def cells_41 : String := include_str "../../data/cells/c41.jsonl"
/-- Class 43 has no listed cell. -/
def cells_43 : String := include_str "../../data/cells/c43.jsonl"
/-- Class 45 has no listed cell. -/
def cells_45 : String := include_str "../../data/cells/c45.jsonl"
/-- Class 46 has no listed cell. -/
def cells_46 : String := include_str "../../data/cells/c46.jsonl"
/-- Class 48 has no listed cell. -/
def cells_48 : String := include_str "../../data/cells/c48.jsonl"
/-- Class 49 has no listed cell. -/
def cells_49 : String := include_str "../../data/cells/c49.jsonl"
/-- Class 50 has no listed cell. -/
def cells_50 : String := include_str "../../data/cells/c50.jsonl"
/-- Class 51 has no listed cell. -/
def cells_51 : String := include_str "../../data/cells/c51.jsonl"
/-- Class 52 has no listed cell. -/
def cells_52 : String := include_str "../../data/cells/c52.jsonl"
/-- Class 54 has no listed cell. -/
def cells_54 : String := include_str "../../data/cells/c54.jsonl"
/-- Class 59 has no listed cell. -/
def cells_59 : String := include_str "../../data/cells/c59.jsonl"
/-- Class 60 has no listed cell. -/
def cells_60 : String := include_str "../../data/cells/c60.jsonl"
/-- Class 61 has no listed cell. -/
def cells_61 : String := include_str "../../data/cells/c61.jsonl"
/-- Class 68 has no listed cell. -/
def cells_68 : String := include_str "../../data/cells/c68.jsonl"
/-- Class 70 has no listed cell. -/
def cells_70 : String := include_str "../../data/cells/c70.jsonl"
/-- Class 71 has no listed cell. -/
def cells_71 : String := include_str "../../data/cells/c71.jsonl"
/-- Class 72 has no listed cell. -/
def cells_72 : String := include_str "../../data/cells/c72.jsonl"
/-- Class 73 has no listed cell. -/
def cells_73 : String := include_str "../../data/cells/c73.jsonl"
/-- Class 74 has no listed cell. -/
def cells_74 : String := include_str "../../data/cells/c74.jsonl"
/-- Class 75 has no listed cell. -/
def cells_75 : String := include_str "../../data/cells/c75.jsonl"
/-- Class 76 has no listed cell. -/
def cells_76 : String := include_str "../../data/cells/c76.jsonl"
/-- Class 77 has no listed cell. -/
def cells_77 : String := include_str "../../data/cells/c77.jsonl"
/-- Class 78 has no listed cell. -/
def cells_78 : String := include_str "../../data/cells/c78.jsonl"
/-- Class 79 has no listed cell. -/
def cells_79 : String := include_str "../../data/cells/c79.jsonl"
/-- Class 80 has no listed cell. -/
def cells_80 : String := include_str "../../data/cells/c80.jsonl"
/-- Class 81 has no listed cell. -/
def cells_81 : String := include_str "../../data/cells/c81.jsonl"
/-- Class 82 has no listed cell. -/
def cells_82 : String := include_str "../../data/cells/c82.jsonl"
/-- Class 83 has no listed cell. -/
def cells_83 : String := include_str "../../data/cells/c83.jsonl"
/-- Class 85 has no listed cell. -/
def cells_85 : String := include_str "../../data/cells/c85.jsonl"
/-- Class 86 has no listed cell. -/
def cells_86 : String := include_str "../../data/cells/c86.jsonl"
/-- Class 87 has no listed cell. -/
def cells_87 : String := include_str "../../data/cells/c87.jsonl"
/-- Class 88 has no listed cell. -/
def cells_88 : String := include_str "../../data/cells/c88.jsonl"
/-- Class 89 has no listed cell. -/
def cells_89 : String := include_str "../../data/cells/c89.jsonl"
/-- Class 90 has no listed cell. -/
def cells_90 : String := include_str "../../data/cells/c90.jsonl"
/-- Class 91 has no listed cell. -/
def cells_91 : String := include_str "../../data/cells/c91.jsonl"
/-- Class 92 has no listed cell. -/
def cells_92 : String := include_str "../../data/cells/c92.jsonl"
/-- Class 93 has no listed cell. -/
def cells_93 : String := include_str "../../data/cells/c93.jsonl"
/-- Class 94 has no listed cell. -/
def cells_94 : String := include_str "../../data/cells/c94.jsonl"
/-- Class 95 has no listed cell. -/
def cells_95 : String := include_str "../../data/cells/c95.jsonl"
/-- Class 96 has no listed cell. -/
def cells_96 : String := include_str "../../data/cells/c96.jsonl"
/-- Class 97 has no listed cell. -/
def cells_97 : String := include_str "../../data/cells/c97.jsonl"
/-- Class 98 has no listed cell. -/
def cells_98 : String := include_str "../../data/cells/c98.jsonl"
/-- Class 99 has no listed cell. -/
def cells_99 : String := include_str "../../data/cells/c99.jsonl"
/-- Class 100 has no listed cell. -/
def cells_100 : String := include_str "../../data/cells/c100.jsonl"
/-- Class 101 has no listed cell. -/
def cells_101 : String := include_str "../../data/cells/c101.jsonl"
/-- Class 102 has no listed cell. -/
def cells_102 : String := include_str "../../data/cells/c102.jsonl"
/-- Class 103 has no listed cell. -/
def cells_103 : String := include_str "../../data/cells/c103.jsonl"
/-- Class 104 has no listed cell. -/
def cells_104 : String := include_str "../../data/cells/c104.jsonl"
/-- Class 105 has no listed cell. -/
def cells_105 : String := include_str "../../data/cells/c105.jsonl"
/-- Class 106 has no listed cell. -/
def cells_106 : String := include_str "../../data/cells/c106.jsonl"
/-- Class 107 has no listed cell. -/
def cells_107 : String := include_str "../../data/cells/c107.jsonl"
/-- Class 108 has no listed cell. -/
def cells_108 : String := include_str "../../data/cells/c108.jsonl"
/-- Class 109 has no listed cell. -/
def cells_109 : String := include_str "../../data/cells/c109.jsonl"
/-- Class 111 has no listed cell. -/
def cells_111 : String := include_str "../../data/cells/c111.jsonl"
/-- Class 112 has no listed cell. -/
def cells_112 : String := include_str "../../data/cells/c112.jsonl"
/-- Class 113 has no listed cell. -/
def cells_113 : String := include_str "../../data/cells/c113.jsonl"
/-- Class 114 has no listed cell. -/
def cells_114 : String := include_str "../../data/cells/c114.jsonl"
/-- Class 115 has no listed cell. -/
def cells_115 : String := include_str "../../data/cells/c115.jsonl"
/-- Class 118 has no listed cell. -/
def cells_118 : String := include_str "../../data/cells/c118.jsonl"
/-- Class 125 has no listed cell. -/
def cells_125 : String := include_str "../../data/cells/c125.jsonl"
/-- Class 134 has no listed cell. -/
def cells_134 : String := include_str "../../data/cells/c134.jsonl"
/-- Class 135 has no listed cell. -/
def cells_135 : String := include_str "../../data/cells/c135.jsonl"
/-- Class 136 has no listed cell. -/
def cells_136 : String := include_str "../../data/cells/c136.jsonl"
/-- Class 137 has no listed cell. -/
def cells_137 : String := include_str "../../data/cells/c137.jsonl"
/-- Class 138 has no listed cell. -/
def cells_138 : String := include_str "../../data/cells/c138.jsonl"
/-- Class 139 has no listed cell. -/
def cells_139 : String := include_str "../../data/cells/c139.jsonl"
/-- Class 140 has no listed cell. -/
def cells_140 : String := include_str "../../data/cells/c140.jsonl"
/-- Class 141 has no listed cell. -/
def cells_141 : String := include_str "../../data/cells/c141.jsonl"
/-- Class 144 has no listed cell. -/
def cells_144 : String := include_str "../../data/cells/c144.jsonl"
/-- Class 145 has no listed cell. -/
def cells_145 : String := include_str "../../data/cells/c145.jsonl"
/-- Class 151 has no listed cell. -/
def cells_151 : String := include_str "../../data/cells/c151.jsonl"
/-- Class 152 has no listed cell. -/
def cells_152 : String := include_str "../../data/cells/c152.jsonl"
/-- Class 153 has no listed cell. -/
def cells_153 : String := include_str "../../data/cells/c153.jsonl"
/-- Class 154 has no listed cell. -/
def cells_154 : String := include_str "../../data/cells/c154.jsonl"
/-- Class 155 has no listed cell. -/
def cells_155 : String := include_str "../../data/cells/c155.jsonl"
/-- Class 156 has no listed cell. -/
def cells_156 : String := include_str "../../data/cells/c156.jsonl"
/-- Class 157 has no listed cell. -/
def cells_157 : String := include_str "../../data/cells/c157.jsonl"
/-- Class 158 has no listed cell. -/
def cells_158 : String := include_str "../../data/cells/c158.jsonl"
/-- Class 159 has no listed cell. -/
def cells_159 : String := include_str "../../data/cells/c159.jsonl"
/-- Class 160 has no listed cell. -/
def cells_160 : String := include_str "../../data/cells/c160.jsonl"
/-- Class 161 has no listed cell. -/
def cells_161 : String := include_str "../../data/cells/c161.jsonl"
/-- Class 162 has no listed cell. -/
def cells_162 : String := include_str "../../data/cells/c162.jsonl"
/-- Class 163 has no listed cell. -/
def cells_163 : String := include_str "../../data/cells/c163.jsonl"
/-- Class 164 has no listed cell. -/
def cells_164 : String := include_str "../../data/cells/c164.jsonl"
/-- Class 165 has no listed cell. -/
def cells_165 : String := include_str "../../data/cells/c165.jsonl"
/-- Class 166 has no listed cell. -/
def cells_166 : String := include_str "../../data/cells/c166.jsonl"
/-- Class 168 has no listed cell. -/
def cells_168 : String := include_str "../../data/cells/c168.jsonl"
/-- Class 174 has no listed cell. -/
def cells_174 : String := include_str "../../data/cells/c174.jsonl"
/-- Class 175 has no listed cell. -/
def cells_175 : String := include_str "../../data/cells/c175.jsonl"
/-- Class 176 has no listed cell. -/
def cells_176 : String := include_str "../../data/cells/c176.jsonl"
/-- Class 177 has no listed cell. -/
def cells_177 : String := include_str "../../data/cells/c177.jsonl"
/-- Class 178 has no listed cell. -/
def cells_178 : String := include_str "../../data/cells/c178.jsonl"
/-- Class 179 has no listed cell. -/
def cells_179 : String := include_str "../../data/cells/c179.jsonl"
/-- Class 180 has no listed cell. -/
def cells_180 : String := include_str "../../data/cells/c180.jsonl"
/-- Class 181 has no listed cell. -/
def cells_181 : String := include_str "../../data/cells/c181.jsonl"
/-- Class 182 has no listed cell. -/
def cells_182 : String := include_str "../../data/cells/c182.jsonl"
/-- Class 184 has no listed cell. -/
def cells_184 : String := include_str "../../data/cells/c184.jsonl"
/-- Class 185 has no listed cell. -/
def cells_185 : String := include_str "../../data/cells/c185.jsonl"
/-- Class 186 has no listed cell. -/
def cells_186 : String := include_str "../../data/cells/c186.jsonl"
/-- Class 187 has no listed cell. -/
def cells_187 : String := include_str "../../data/cells/c187.jsonl"
/-- Class 188 has no listed cell. -/
def cells_188 : String := include_str "../../data/cells/c188.jsonl"
/-- Class 189 has no listed cell. -/
def cells_189 : String := include_str "../../data/cells/c189.jsonl"
/-- Class 190 has no listed cell. -/
def cells_190 : String := include_str "../../data/cells/c190.jsonl"

end L6.F34.Data

namespace L6.F34.Checks

open L6.F34 L6.F34.Data

set_option maxHeartbeats 0 in
/-- The numbers of cells of the classes `0, …, 190`. -/
theorem F34_cover : [numCells cells_0, numCells cells_1, numCells cells_2, numCells cells_3, numCells cells_4, numCells cells_5, numCells cells_6, numCells cells_7, numCells cells_8, numCells cells_9, numCells cells_10, numCells cells_11, numCells cells_12, numCells cells_13, numCells cells_14, numCells cells_15, numCells cells_16, numCells cells_17, numCells cells_18, numCells cells_19, numCells cells_20, numCells cells_21, numCells cells_22, numCells cells_23, numCells cells_24, numCells cells_25, numCells cells_26, numCells cells_27, numCells cells_28, numCells cells_29, numCells cells_30, numCells cells_31, numCells cells_32, numCells cells_33, numCells cells_34, numCells cells_35, numCells cells_36, numCells cells_37, numCells cells_38, numCells cells_39, numCells cells_40, numCells cells_41, numCells cells_42, numCells cells_43, numCells cells_44, numCells cells_45, numCells cells_46, numCells cells_47, numCells cells_48, numCells cells_49, numCells cells_50, numCells cells_51, numCells cells_52, numCells cells_53, numCells cells_54, numCells cells_55, numCells cells_56, numCells cells_57, numCells cells_58, numCells cells_59, numCells cells_60, numCells cells_61, numCells cells_62, numCells cells_63, numCells cells_64, numCells cells_65, numCells cells_66, numCells cells_67, numCells cells_68, numCells cells_69, numCells cells_70, numCells cells_71, numCells cells_72, numCells cells_73, numCells cells_74, numCells cells_75, numCells cells_76, numCells cells_77, numCells cells_78, numCells cells_79, numCells cells_80, numCells cells_81, numCells cells_82, numCells cells_83, numCells cells_84, numCells cells_85, numCells cells_86, numCells cells_87, numCells cells_88, numCells cells_89, numCells cells_90, numCells cells_91, numCells cells_92, numCells cells_93, numCells cells_94, numCells cells_95, numCells cells_96, numCells cells_97, numCells cells_98, numCells cells_99, numCells cells_100, numCells cells_101, numCells cells_102, numCells cells_103, numCells cells_104, numCells cells_105, numCells cells_106, numCells cells_107, numCells cells_108, numCells cells_109, numCells cells_110, numCells cells_111, numCells cells_112, numCells cells_113, numCells cells_114, numCells cells_115, numCells cells_116, numCells cells_117, numCells cells_118, numCells cells_119, numCells cells_120, numCells cells_121, numCells cells_122, numCells cells_123, numCells cells_124, numCells cells_125, numCells cells_126, numCells cells_127, numCells cells_128, numCells cells_129, numCells cells_130, numCells cells_131, numCells cells_132, numCells cells_133, numCells cells_134, numCells cells_135, numCells cells_136, numCells cells_137, numCells cells_138, numCells cells_139, numCells cells_140, numCells cells_141, numCells cells_142, numCells cells_143, numCells cells_144, numCells cells_145, numCells cells_146, numCells cells_147, numCells cells_148, numCells cells_149, numCells cells_150, numCells cells_151, numCells cells_152, numCells cells_153, numCells cells_154, numCells cells_155, numCells cells_156, numCells cells_157, numCells cells_158, numCells cells_159, numCells cells_160, numCells cells_161, numCells cells_162, numCells cells_163, numCells cells_164, numCells cells_165, numCells cells_166, numCells cells_167, numCells cells_168, numCells cells_169, numCells cells_170, numCells cells_171, numCells cells_172, numCells cells_173, numCells cells_174, numCells cells_175, numCells cells_176, numCells cells_177, numCells cells_178, numCells cells_179, numCells cells_180, numCells cells_181, numCells cells_182, numCells cells_183, numCells cells_184, numCells cells_185, numCells cells_186, numCells cells_187, numCells cells_188, numCells cells_189, numCells cells_190] =
    [17, 0, 0, 44247, 177, 0, 0, 0, 1, 0, 10, 0, 1, 1, 865, 42, 28, 0, 0, 0, 13, 0, 2, 239, 72, 88, 0, 0, 3, 1866, 273, 49, 0, 0, 1, 1, 0, 0, 0, 0, 394, 0, 20, 0, 154, 0, 0, 497, 0, 0, 0, 0, 0, 3, 0, 24, 37, 2, 2, 0, 0, 0, 14, 7, 162, 1, 1, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 21, 2, 0, 1, 2, 1, 10, 1, 143, 0, 27, 9, 32864, 1449, 630, 196, 147, 49, 0, 0, 0, 0, 0, 0, 0, 0, 297, 77, 0, 0, 81, 63, 4777, 756, 224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 18, 9, 19, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] := by
  native_decide

end L6.F34.Checks
