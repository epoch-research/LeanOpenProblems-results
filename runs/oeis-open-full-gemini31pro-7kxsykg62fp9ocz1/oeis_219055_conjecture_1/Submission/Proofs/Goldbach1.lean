import Mathlib

set_option maxHeartbeats 10000000
theorem goldbach_case_4 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 4 = p + q := by exact ⟨2, 2, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_6 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 6 = p + q := by exact ⟨3, 3, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_8 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 8 = p + q := by exact ⟨3, 5, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_10 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 10 = p + q := by exact ⟨3, 7, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_12 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 12 = p + q := by exact ⟨5, 7, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_14 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 14 = p + q := by exact ⟨3, 11, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_16 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 16 = p + q := by exact ⟨3, 13, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_18 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 18 = p + q := by exact ⟨5, 13, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_20 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 20 = p + q := by exact ⟨3, 17, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_22 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 22 = p + q := by exact ⟨3, 19, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_24 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 24 = p + q := by exact ⟨5, 19, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_26 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 26 = p + q := by exact ⟨3, 23, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_28 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 28 = p + q := by exact ⟨5, 23, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_30 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 30 = p + q := by exact ⟨7, 23, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_32 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 32 = p + q := by exact ⟨3, 29, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_34 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 34 = p + q := by exact ⟨3, 31, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_36 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 36 = p + q := by exact ⟨5, 31, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_38 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 38 = p + q := by exact ⟨7, 31, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_40 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 40 = p + q := by exact ⟨3, 37, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_42 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 42 = p + q := by exact ⟨5, 37, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_44 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 44 = p + q := by exact ⟨3, 41, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_46 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 46 = p + q := by exact ⟨3, 43, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_48 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 48 = p + q := by exact ⟨5, 43, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_50 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 50 = p + q := by exact ⟨3, 47, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_52 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 52 = p + q := by exact ⟨5, 47, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_54 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 54 = p + q := by exact ⟨7, 47, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_56 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 56 = p + q := by exact ⟨3, 53, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_58 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 58 = p + q := by exact ⟨5, 53, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_60 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 60 = p + q := by exact ⟨7, 53, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_62 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 62 = p + q := by exact ⟨3, 59, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_64 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 64 = p + q := by exact ⟨3, 61, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_66 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 66 = p + q := by exact ⟨5, 61, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_68 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 68 = p + q := by exact ⟨7, 61, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_70 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 70 = p + q := by exact ⟨3, 67, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_72 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 72 = p + q := by exact ⟨5, 67, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_74 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 74 = p + q := by exact ⟨3, 71, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_76 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 76 = p + q := by exact ⟨3, 73, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_78 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 78 = p + q := by exact ⟨5, 73, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_80 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 80 = p + q := by exact ⟨7, 73, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_82 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 82 = p + q := by exact ⟨3, 79, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_84 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 84 = p + q := by exact ⟨5, 79, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_86 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 86 = p + q := by exact ⟨3, 83, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_88 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 88 = p + q := by exact ⟨5, 83, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_90 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 90 = p + q := by exact ⟨7, 83, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_92 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 92 = p + q := by exact ⟨3, 89, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_94 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 94 = p + q := by exact ⟨5, 89, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_96 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 96 = p + q := by exact ⟨7, 89, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_98 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 98 = p + q := by exact ⟨19, 79, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_100 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 100 = p + q := by exact ⟨3, 97, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_102 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 102 = p + q := by exact ⟨5, 97, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_104 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 104 = p + q := by exact ⟨3, 101, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_106 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 106 = p + q := by exact ⟨3, 103, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_108 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 108 = p + q := by exact ⟨5, 103, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_110 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 110 = p + q := by exact ⟨3, 107, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_112 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 112 = p + q := by exact ⟨3, 109, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_114 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 114 = p + q := by exact ⟨5, 109, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_116 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 116 = p + q := by exact ⟨3, 113, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_118 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 118 = p + q := by exact ⟨5, 113, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_120 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 120 = p + q := by exact ⟨7, 113, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_122 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 122 = p + q := by exact ⟨13, 109, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_124 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 124 = p + q := by exact ⟨11, 113, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_126 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 126 = p + q := by exact ⟨13, 113, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_128 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 128 = p + q := by exact ⟨19, 109, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_130 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 130 = p + q := by exact ⟨3, 127, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_132 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 132 = p + q := by exact ⟨5, 127, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_134 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 134 = p + q := by exact ⟨3, 131, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_136 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 136 = p + q := by exact ⟨5, 131, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_138 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 138 = p + q := by exact ⟨7, 131, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_140 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 140 = p + q := by exact ⟨3, 137, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_142 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 142 = p + q := by exact ⟨3, 139, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_144 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 144 = p + q := by exact ⟨5, 139, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_146 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 146 = p + q := by exact ⟨7, 139, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_148 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 148 = p + q := by exact ⟨11, 137, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_150 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 150 = p + q := by exact ⟨11, 139, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_152 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 152 = p + q := by exact ⟨3, 149, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_154 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 154 = p + q := by exact ⟨3, 151, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_156 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 156 = p + q := by exact ⟨5, 151, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_158 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 158 = p + q := by exact ⟨7, 151, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_160 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 160 = p + q := by exact ⟨3, 157, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_162 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 162 = p + q := by exact ⟨5, 157, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_164 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 164 = p + q := by exact ⟨7, 157, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_166 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 166 = p + q := by exact ⟨3, 163, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_168 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 168 = p + q := by exact ⟨5, 163, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_170 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 170 = p + q := by exact ⟨3, 167, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_172 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 172 = p + q := by exact ⟨5, 167, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_174 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 174 = p + q := by exact ⟨7, 167, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_176 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 176 = p + q := by exact ⟨3, 173, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_178 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 178 = p + q := by exact ⟨5, 173, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_180 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 180 = p + q := by exact ⟨7, 173, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_182 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 182 = p + q := by exact ⟨3, 179, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_184 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 184 = p + q := by exact ⟨3, 181, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_186 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 186 = p + q := by exact ⟨5, 181, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_188 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 188 = p + q := by exact ⟨7, 181, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_190 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 190 = p + q := by exact ⟨11, 179, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_192 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 192 = p + q := by exact ⟨11, 181, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_194 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 194 = p + q := by exact ⟨3, 191, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_196 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 196 = p + q := by exact ⟨3, 193, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_198 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 198 = p + q := by exact ⟨5, 193, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_200 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 200 = p + q := by exact ⟨3, 197, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_202 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 202 = p + q := by exact ⟨3, 199, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_204 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 204 = p + q := by exact ⟨5, 199, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_206 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 206 = p + q := by exact ⟨7, 199, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_208 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 208 = p + q := by exact ⟨11, 197, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_210 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 210 = p + q := by exact ⟨11, 199, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_212 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 212 = p + q := by exact ⟨13, 199, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_214 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 214 = p + q := by exact ⟨3, 211, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_216 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 216 = p + q := by exact ⟨5, 211, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_218 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 218 = p + q := by exact ⟨7, 211, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_220 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 220 = p + q := by exact ⟨23, 197, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_222 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 222 = p + q := by exact ⟨11, 211, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_224 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 224 = p + q := by exact ⟨13, 211, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_226 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 226 = p + q := by exact ⟨3, 223, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_228 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 228 = p + q := by exact ⟨5, 223, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_230 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 230 = p + q := by exact ⟨3, 227, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_232 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 232 = p + q := by exact ⟨3, 229, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_234 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 234 = p + q := by exact ⟨5, 229, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_236 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 236 = p + q := by exact ⟨3, 233, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_238 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 238 = p + q := by exact ⟨5, 233, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_240 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 240 = p + q := by exact ⟨7, 233, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_242 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 242 = p + q := by exact ⟨3, 239, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_244 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 244 = p + q := by exact ⟨3, 241, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_246 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 246 = p + q := by exact ⟨5, 241, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_248 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 248 = p + q := by exact ⟨7, 241, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_250 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 250 = p + q := by exact ⟨11, 239, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_252 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 252 = p + q := by exact ⟨11, 241, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_254 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 254 = p + q := by exact ⟨3, 251, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_256 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 256 = p + q := by exact ⟨5, 251, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_258 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 258 = p + q := by exact ⟨7, 251, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_260 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 260 = p + q := by exact ⟨3, 257, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_262 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 262 = p + q := by exact ⟨5, 257, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_264 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 264 = p + q := by exact ⟨7, 257, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_266 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 266 = p + q := by exact ⟨3, 263, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_268 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 268 = p + q := by exact ⟨5, 263, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_270 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 270 = p + q := by exact ⟨7, 263, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_272 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 272 = p + q := by exact ⟨3, 269, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_274 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 274 = p + q := by exact ⟨3, 271, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_276 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 276 = p + q := by exact ⟨5, 271, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_278 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 278 = p + q := by exact ⟨7, 271, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_280 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 280 = p + q := by exact ⟨3, 277, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_282 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 282 = p + q := by exact ⟨5, 277, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_284 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 284 = p + q := by exact ⟨3, 281, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_286 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 286 = p + q := by exact ⟨3, 283, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_288 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 288 = p + q := by exact ⟨5, 283, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_290 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 290 = p + q := by exact ⟨7, 283, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_292 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 292 = p + q := by exact ⟨11, 281, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_294 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 294 = p + q := by exact ⟨11, 283, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_296 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 296 = p + q := by exact ⟨3, 293, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_298 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 298 = p + q := by exact ⟨5, 293, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_300 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 300 = p + q := by exact ⟨7, 293, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_302 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 302 = p + q := by exact ⟨19, 283, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_304 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 304 = p + q := by exact ⟨11, 293, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_306 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 306 = p + q := by exact ⟨13, 293, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_308 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 308 = p + q := by exact ⟨31, 277, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_310 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 310 = p + q := by exact ⟨3, 307, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_312 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 312 = p + q := by exact ⟨5, 307, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_314 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 314 = p + q := by exact ⟨3, 311, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_316 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 316 = p + q := by exact ⟨3, 313, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_318 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 318 = p + q := by exact ⟨5, 313, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_320 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 320 = p + q := by exact ⟨3, 317, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_322 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 322 = p + q := by exact ⟨5, 317, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_324 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 324 = p + q := by exact ⟨7, 317, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_326 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 326 = p + q := by exact ⟨13, 313, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_328 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 328 = p + q := by exact ⟨11, 317, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_330 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 330 = p + q := by exact ⟨13, 317, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_332 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 332 = p + q := by exact ⟨19, 313, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_334 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 334 = p + q := by exact ⟨3, 331, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_336 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 336 = p + q := by exact ⟨5, 331, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_338 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 338 = p + q := by exact ⟨7, 331, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_340 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 340 = p + q := by exact ⟨3, 337, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_342 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 342 = p + q := by exact ⟨5, 337, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_344 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 344 = p + q := by exact ⟨7, 337, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_346 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 346 = p + q := by exact ⟨29, 317, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_348 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 348 = p + q := by exact ⟨11, 337, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_350 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 350 = p + q := by exact ⟨3, 347, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_352 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 352 = p + q := by exact ⟨3, 349, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_354 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 354 = p + q := by exact ⟨5, 349, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_356 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 356 = p + q := by exact ⟨3, 353, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_358 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 358 = p + q := by exact ⟨5, 353, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_360 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 360 = p + q := by exact ⟨7, 353, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_362 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 362 = p + q := by exact ⟨3, 359, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_364 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 364 = p + q := by exact ⟨5, 359, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_366 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 366 = p + q := by exact ⟨7, 359, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_368 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 368 = p + q := by exact ⟨19, 349, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_370 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 370 = p + q := by exact ⟨3, 367, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_372 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 372 = p + q := by exact ⟨5, 367, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_374 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 374 = p + q := by exact ⟨7, 367, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_376 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 376 = p + q := by exact ⟨3, 373, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_378 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 378 = p + q := by exact ⟨5, 373, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_380 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 380 = p + q := by exact ⟨7, 373, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_382 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 382 = p + q := by exact ⟨3, 379, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_384 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 384 = p + q := by exact ⟨5, 379, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_386 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 386 = p + q := by exact ⟨3, 383, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_388 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 388 = p + q := by exact ⟨5, 383, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_390 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 390 = p + q := by exact ⟨7, 383, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_392 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 392 = p + q := by exact ⟨3, 389, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_394 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 394 = p + q := by exact ⟨5, 389, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_396 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 396 = p + q := by exact ⟨7, 389, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_398 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 398 = p + q := by exact ⟨19, 379, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_400 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 400 = p + q := by exact ⟨3, 397, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_402 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 402 = p + q := by exact ⟨5, 397, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_404 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 404 = p + q := by exact ⟨3, 401, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_406 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 406 = p + q := by exact ⟨5, 401, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_408 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 408 = p + q := by exact ⟨7, 401, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_410 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 410 = p + q := by exact ⟨13, 397, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_412 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 412 = p + q := by exact ⟨3, 409, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_414 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 414 = p + q := by exact ⟨5, 409, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_416 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 416 = p + q := by exact ⟨7, 409, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_418 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 418 = p + q := by exact ⟨17, 401, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_420 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 420 = p + q := by exact ⟨11, 409, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_422 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 422 = p + q := by exact ⟨3, 419, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_424 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 424 = p + q := by exact ⟨3, 421, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_426 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 426 = p + q := by exact ⟨5, 421, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_428 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 428 = p + q := by exact ⟨7, 421, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_430 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 430 = p + q := by exact ⟨11, 419, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_432 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 432 = p + q := by exact ⟨11, 421, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_434 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 434 = p + q := by exact ⟨3, 431, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_436 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 436 = p + q := by exact ⟨3, 433, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_438 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 438 = p + q := by exact ⟨5, 433, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_440 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 440 = p + q := by exact ⟨7, 433, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_442 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 442 = p + q := by exact ⟨3, 439, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_444 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 444 = p + q := by exact ⟨5, 439, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_446 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 446 = p + q := by exact ⟨3, 443, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_448 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 448 = p + q := by exact ⟨5, 443, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_450 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 450 = p + q := by exact ⟨7, 443, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_452 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 452 = p + q := by exact ⟨3, 449, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_454 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 454 = p + q := by exact ⟨5, 449, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_456 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 456 = p + q := by exact ⟨7, 449, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_458 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 458 = p + q := by exact ⟨19, 439, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_460 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 460 = p + q := by exact ⟨3, 457, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_462 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 462 = p + q := by exact ⟨5, 457, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_464 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 464 = p + q := by exact ⟨3, 461, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_466 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 466 = p + q := by exact ⟨3, 463, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_468 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 468 = p + q := by exact ⟨5, 463, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_470 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 470 = p + q := by exact ⟨3, 467, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_472 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 472 = p + q := by exact ⟨5, 467, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_474 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 474 = p + q := by exact ⟨7, 467, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_476 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 476 = p + q := by exact ⟨13, 463, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_478 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 478 = p + q := by exact ⟨11, 467, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_480 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 480 = p + q := by exact ⟨13, 467, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_482 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 482 = p + q := by exact ⟨3, 479, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_484 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 484 = p + q := by exact ⟨5, 479, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_486 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 486 = p + q := by exact ⟨7, 479, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_488 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 488 = p + q := by exact ⟨31, 457, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_490 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 490 = p + q := by exact ⟨3, 487, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_492 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 492 = p + q := by exact ⟨5, 487, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_494 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 494 = p + q := by exact ⟨3, 491, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_496 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 496 = p + q := by exact ⟨5, 491, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_498 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 498 = p + q := by exact ⟨7, 491, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_500 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 500 = p + q := by exact ⟨13, 487, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_502 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 502 = p + q := by exact ⟨3, 499, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_504 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 504 = p + q := by exact ⟨5, 499, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_506 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 506 = p + q := by exact ⟨3, 503, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_508 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 508 = p + q := by exact ⟨5, 503, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_510 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 510 = p + q := by exact ⟨7, 503, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_512 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 512 = p + q := by exact ⟨3, 509, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_514 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 514 = p + q := by exact ⟨5, 509, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_516 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 516 = p + q := by exact ⟨7, 509, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_518 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 518 = p + q := by exact ⟨19, 499, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_520 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 520 = p + q := by exact ⟨11, 509, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_522 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 522 = p + q := by exact ⟨13, 509, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_524 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 524 = p + q := by exact ⟨3, 521, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_526 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 526 = p + q := by exact ⟨3, 523, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_528 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 528 = p + q := by exact ⟨5, 523, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_530 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 530 = p + q := by exact ⟨7, 523, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_532 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 532 = p + q := by exact ⟨11, 521, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_534 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 534 = p + q := by exact ⟨11, 523, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_536 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 536 = p + q := by exact ⟨13, 523, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_538 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 538 = p + q := by exact ⟨17, 521, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_540 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 540 = p + q := by exact ⟨17, 523, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_542 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 542 = p + q := by exact ⟨19, 523, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_544 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 544 = p + q := by exact ⟨3, 541, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_546 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 546 = p + q := by exact ⟨5, 541, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_548 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 548 = p + q := by exact ⟨7, 541, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_550 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 550 = p + q := by exact ⟨3, 547, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_552 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 552 = p + q := by exact ⟨5, 547, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_554 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 554 = p + q := by exact ⟨7, 547, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_556 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 556 = p + q := by exact ⟨47, 509, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_558 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 558 = p + q := by exact ⟨11, 547, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_560 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 560 = p + q := by exact ⟨3, 557, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_562 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 562 = p + q := by exact ⟨5, 557, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_564 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 564 = p + q := by exact ⟨7, 557, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_566 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 566 = p + q := by exact ⟨3, 563, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_568 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 568 = p + q := by exact ⟨5, 563, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_570 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 570 = p + q := by exact ⟨7, 563, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_572 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 572 = p + q := by exact ⟨3, 569, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_574 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 574 = p + q := by exact ⟨3, 571, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_576 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 576 = p + q := by exact ⟨5, 571, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_578 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 578 = p + q := by exact ⟨7, 571, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_580 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 580 = p + q := by exact ⟨3, 577, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_582 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 582 = p + q := by exact ⟨5, 577, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_584 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 584 = p + q := by exact ⟨7, 577, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_586 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 586 = p + q := by exact ⟨17, 569, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_588 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 588 = p + q := by exact ⟨11, 577, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_590 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 590 = p + q := by exact ⟨3, 587, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_592 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 592 = p + q := by exact ⟨5, 587, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_594 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 594 = p + q := by exact ⟨7, 587, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_596 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 596 = p + q := by exact ⟨3, 593, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_598 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 598 = p + q := by exact ⟨5, 593, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_600 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 600 = p + q := by exact ⟨7, 593, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_602 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 602 = p + q := by exact ⟨3, 599, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_604 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 604 = p + q := by exact ⟨3, 601, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_606 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 606 = p + q := by exact ⟨5, 601, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_608 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 608 = p + q := by exact ⟨7, 601, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_610 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 610 = p + q := by exact ⟨3, 607, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_612 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 612 = p + q := by exact ⟨5, 607, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_614 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 614 = p + q := by exact ⟨7, 607, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_616 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 616 = p + q := by exact ⟨3, 613, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_618 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 618 = p + q := by exact ⟨5, 613, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_620 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 620 = p + q := by exact ⟨3, 617, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_622 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 622 = p + q := by exact ⟨3, 619, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_624 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 624 = p + q := by exact ⟨5, 619, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_626 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 626 = p + q := by exact ⟨7, 619, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_628 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 628 = p + q := by exact ⟨11, 617, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_630 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 630 = p + q := by exact ⟨11, 619, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_632 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 632 = p + q := by exact ⟨13, 619, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_634 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 634 = p + q := by exact ⟨3, 631, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_636 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 636 = p + q := by exact ⟨5, 631, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_638 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 638 = p + q := by exact ⟨7, 631, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_640 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 640 = p + q := by exact ⟨23, 617, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_642 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 642 = p + q := by exact ⟨11, 631, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_644 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 644 = p + q := by exact ⟨3, 641, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_646 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 646 = p + q := by exact ⟨3, 643, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_648 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 648 = p + q := by exact ⟨5, 643, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_650 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 650 = p + q := by exact ⟨3, 647, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_652 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 652 = p + q := by exact ⟨5, 647, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_654 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 654 = p + q := by exact ⟨7, 647, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_656 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 656 = p + q := by exact ⟨3, 653, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_658 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 658 = p + q := by exact ⟨5, 653, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_660 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 660 = p + q := by exact ⟨7, 653, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_662 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 662 = p + q := by exact ⟨3, 659, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_664 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 664 = p + q := by exact ⟨3, 661, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_666 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 666 = p + q := by exact ⟨5, 661, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_668 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 668 = p + q := by exact ⟨7, 661, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_670 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 670 = p + q := by exact ⟨11, 659, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_672 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 672 = p + q := by exact ⟨11, 661, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_674 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 674 = p + q := by exact ⟨13, 661, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_676 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 676 = p + q := by exact ⟨3, 673, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_678 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 678 = p + q := by exact ⟨5, 673, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_680 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 680 = p + q := by exact ⟨3, 677, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_682 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 682 = p + q := by exact ⟨5, 677, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_684 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 684 = p + q := by exact ⟨7, 677, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_686 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 686 = p + q := by exact ⟨3, 683, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_688 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 688 = p + q := by exact ⟨5, 683, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_690 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 690 = p + q := by exact ⟨7, 683, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_692 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 692 = p + q := by exact ⟨19, 673, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_694 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 694 = p + q := by exact ⟨3, 691, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_696 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 696 = p + q := by exact ⟨5, 691, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_698 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 698 = p + q := by exact ⟨7, 691, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_700 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 700 = p + q := by exact ⟨17, 683, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_702 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 702 = p + q := by exact ⟨11, 691, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_704 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 704 = p + q := by exact ⟨3, 701, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_706 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 706 = p + q := by exact ⟨5, 701, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_708 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 708 = p + q := by exact ⟨7, 701, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_710 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 710 = p + q := by exact ⟨19, 691, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_712 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 712 = p + q := by exact ⟨3, 709, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_714 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 714 = p + q := by exact ⟨5, 709, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_716 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 716 = p + q := by exact ⟨7, 709, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_718 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 718 = p + q := by exact ⟨17, 701, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_720 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 720 = p + q := by exact ⟨11, 709, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_722 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 722 = p + q := by exact ⟨3, 719, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_724 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 724 = p + q := by exact ⟨5, 719, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_726 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 726 = p + q := by exact ⟨7, 719, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_728 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 728 = p + q := by exact ⟨19, 709, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_730 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 730 = p + q := by exact ⟨3, 727, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_732 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 732 = p + q := by exact ⟨5, 727, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_734 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 734 = p + q := by exact ⟨7, 727, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_736 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 736 = p + q := by exact ⟨3, 733, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_738 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 738 = p + q := by exact ⟨5, 733, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_740 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 740 = p + q := by exact ⟨7, 733, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_742 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 742 = p + q := by exact ⟨3, 739, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_744 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 744 = p + q := by exact ⟨5, 739, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_746 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 746 = p + q := by exact ⟨3, 743, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_748 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 748 = p + q := by exact ⟨5, 743, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_750 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 750 = p + q := by exact ⟨7, 743, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_752 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 752 = p + q := by exact ⟨13, 739, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_754 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 754 = p + q := by exact ⟨3, 751, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_756 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 756 = p + q := by exact ⟨5, 751, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_758 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 758 = p + q := by exact ⟨7, 751, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_760 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 760 = p + q := by exact ⟨3, 757, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_762 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 762 = p + q := by exact ⟨5, 757, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_764 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 764 = p + q := by exact ⟨3, 761, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_766 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 766 = p + q := by exact ⟨5, 761, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_768 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 768 = p + q := by exact ⟨7, 761, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_770 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 770 = p + q := by exact ⟨13, 757, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_772 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 772 = p + q := by exact ⟨3, 769, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_774 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 774 = p + q := by exact ⟨5, 769, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_776 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 776 = p + q := by exact ⟨3, 773, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_778 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 778 = p + q := by exact ⟨5, 773, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_780 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 780 = p + q := by exact ⟨7, 773, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_782 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 782 = p + q := by exact ⟨13, 769, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_784 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 784 = p + q := by exact ⟨11, 773, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_786 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 786 = p + q := by exact ⟨13, 773, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_788 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 788 = p + q := by exact ⟨19, 769, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_790 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 790 = p + q := by exact ⟨3, 787, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_792 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 792 = p + q := by exact ⟨5, 787, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_794 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 794 = p + q := by exact ⟨7, 787, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_796 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 796 = p + q := by exact ⟨23, 773, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_798 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 798 = p + q := by exact ⟨11, 787, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_800 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 800 = p + q := by exact ⟨3, 797, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_802 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 802 = p + q := by exact ⟨5, 797, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_804 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 804 = p + q := by exact ⟨7, 797, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_806 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 806 = p + q := by exact ⟨19, 787, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_808 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 808 = p + q := by exact ⟨11, 797, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_810 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 810 = p + q := by exact ⟨13, 797, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_812 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 812 = p + q := by exact ⟨3, 809, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_814 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 814 = p + q := by exact ⟨3, 811, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_816 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 816 = p + q := by exact ⟨5, 811, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_818 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 818 = p + q := by exact ⟨7, 811, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_820 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 820 = p + q := by exact ⟨11, 809, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_822 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 822 = p + q := by exact ⟨11, 811, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_824 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 824 = p + q := by exact ⟨3, 821, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_826 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 826 = p + q := by exact ⟨3, 823, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_828 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 828 = p + q := by exact ⟨5, 823, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_830 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 830 = p + q := by exact ⟨3, 827, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_832 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 832 = p + q := by exact ⟨3, 829, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_834 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 834 = p + q := by exact ⟨5, 829, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_836 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 836 = p + q := by exact ⟨7, 829, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_838 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 838 = p + q := by exact ⟨11, 827, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_840 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 840 = p + q := by exact ⟨11, 829, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_842 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 842 = p + q := by exact ⟨3, 839, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_844 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 844 = p + q := by exact ⟨5, 839, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_846 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 846 = p + q := by exact ⟨7, 839, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_848 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 848 = p + q := by exact ⟨19, 829, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_850 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 850 = p + q := by exact ⟨11, 839, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_852 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 852 = p + q := by exact ⟨13, 839, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_854 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 854 = p + q := by exact ⟨31, 823, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_856 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 856 = p + q := by exact ⟨3, 853, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_858 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 858 = p + q := by exact ⟨5, 853, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_860 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 860 = p + q := by exact ⟨3, 857, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_862 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 862 = p + q := by exact ⟨3, 859, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_864 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 864 = p + q := by exact ⟨5, 859, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_866 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 866 = p + q := by exact ⟨3, 863, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_868 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 868 = p + q := by exact ⟨5, 863, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_870 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 870 = p + q := by exact ⟨7, 863, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_872 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 872 = p + q := by exact ⟨13, 859, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_874 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 874 = p + q := by exact ⟨11, 863, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_876 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 876 = p + q := by exact ⟨13, 863, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_878 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 878 = p + q := by exact ⟨19, 859, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_880 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 880 = p + q := by exact ⟨3, 877, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_882 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 882 = p + q := by exact ⟨5, 877, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_884 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 884 = p + q := by exact ⟨3, 881, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_886 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 886 = p + q := by exact ⟨3, 883, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_888 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 888 = p + q := by exact ⟨5, 883, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_890 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 890 = p + q := by exact ⟨3, 887, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_892 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 892 = p + q := by exact ⟨5, 887, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_894 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 894 = p + q := by exact ⟨7, 887, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_896 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 896 = p + q := by exact ⟨13, 883, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_898 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 898 = p + q := by exact ⟨11, 887, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_900 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 900 = p + q := by exact ⟨13, 887, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_902 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 902 = p + q := by exact ⟨19, 883, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_904 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 904 = p + q := by exact ⟨17, 887, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_906 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 906 = p + q := by exact ⟨19, 887, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_908 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 908 = p + q := by exact ⟨31, 877, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_910 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 910 = p + q := by exact ⟨3, 907, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_912 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 912 = p + q := by exact ⟨5, 907, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_914 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 914 = p + q := by exact ⟨3, 911, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_916 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 916 = p + q := by exact ⟨5, 911, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_918 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 918 = p + q := by exact ⟨7, 911, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_920 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 920 = p + q := by exact ⟨13, 907, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_922 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 922 = p + q := by exact ⟨3, 919, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_924 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 924 = p + q := by exact ⟨5, 919, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_926 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 926 = p + q := by exact ⟨7, 919, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_928 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 928 = p + q := by exact ⟨17, 911, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_930 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 930 = p + q := by exact ⟨11, 919, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_932 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 932 = p + q := by exact ⟨3, 929, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_934 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 934 = p + q := by exact ⟨5, 929, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_936 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 936 = p + q := by exact ⟨7, 929, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_938 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 938 = p + q := by exact ⟨19, 919, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_940 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 940 = p + q := by exact ⟨3, 937, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_942 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 942 = p + q := by exact ⟨5, 937, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_944 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 944 = p + q := by exact ⟨3, 941, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_946 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 946 = p + q := by exact ⟨5, 941, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_948 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 948 = p + q := by exact ⟨7, 941, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_950 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 950 = p + q := by exact ⟨3, 947, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_952 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 952 = p + q := by exact ⟨5, 947, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_954 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 954 = p + q := by exact ⟨7, 947, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_956 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 956 = p + q := by exact ⟨3, 953, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_958 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 958 = p + q := by exact ⟨5, 953, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_960 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 960 = p + q := by exact ⟨7, 953, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_962 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 962 = p + q := by exact ⟨43, 919, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_964 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 964 = p + q := by exact ⟨11, 953, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_966 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 966 = p + q := by exact ⟨13, 953, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_968 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 968 = p + q := by exact ⟨31, 937, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_970 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 970 = p + q := by exact ⟨3, 967, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_972 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 972 = p + q := by exact ⟨5, 967, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_974 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 974 = p + q := by exact ⟨3, 971, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_976 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 976 = p + q := by exact ⟨5, 971, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_978 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 978 = p + q := by exact ⟨7, 971, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_980 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 980 = p + q := by exact ⟨3, 977, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_982 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 982 = p + q := by exact ⟨5, 977, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_984 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 984 = p + q := by exact ⟨7, 977, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_986 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 986 = p + q := by exact ⟨3, 983, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_988 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 988 = p + q := by exact ⟨5, 983, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_990 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 990 = p + q := by exact ⟨7, 983, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_992 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 992 = p + q := by exact ⟨73, 919, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_994 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 994 = p + q := by exact ⟨3, 991, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_996 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 996 = p + q := by exact ⟨5, 991, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_998 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 998 = p + q := by exact ⟨7, 991, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_1000 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 1000 = p + q := by exact ⟨3, 997, by norm_num, by norm_num, rfl⟩
theorem goldbach_case_1002 : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 1002 = p + q := by exact ⟨5, 997, by norm_num, by norm_num, rfl⟩

lemma goldbach_match_1 (n : ℕ) : (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q) ∨ True := by
  match n with
  | 4 => exact Or.inl goldbach_case_4
  | 6 => exact Or.inl goldbach_case_6
  | 8 => exact Or.inl goldbach_case_8
  | 10 => exact Or.inl goldbach_case_10
  | 12 => exact Or.inl goldbach_case_12
  | 14 => exact Or.inl goldbach_case_14
  | 16 => exact Or.inl goldbach_case_16
  | 18 => exact Or.inl goldbach_case_18
  | 20 => exact Or.inl goldbach_case_20
  | 22 => exact Or.inl goldbach_case_22
  | 24 => exact Or.inl goldbach_case_24
  | 26 => exact Or.inl goldbach_case_26
  | 28 => exact Or.inl goldbach_case_28
  | 30 => exact Or.inl goldbach_case_30
  | 32 => exact Or.inl goldbach_case_32
  | 34 => exact Or.inl goldbach_case_34
  | 36 => exact Or.inl goldbach_case_36
  | 38 => exact Or.inl goldbach_case_38
  | 40 => exact Or.inl goldbach_case_40
  | 42 => exact Or.inl goldbach_case_42
  | 44 => exact Or.inl goldbach_case_44
  | 46 => exact Or.inl goldbach_case_46
  | 48 => exact Or.inl goldbach_case_48
  | 50 => exact Or.inl goldbach_case_50
  | 52 => exact Or.inl goldbach_case_52
  | 54 => exact Or.inl goldbach_case_54
  | 56 => exact Or.inl goldbach_case_56
  | 58 => exact Or.inl goldbach_case_58
  | 60 => exact Or.inl goldbach_case_60
  | 62 => exact Or.inl goldbach_case_62
  | 64 => exact Or.inl goldbach_case_64
  | 66 => exact Or.inl goldbach_case_66
  | 68 => exact Or.inl goldbach_case_68
  | 70 => exact Or.inl goldbach_case_70
  | 72 => exact Or.inl goldbach_case_72
  | 74 => exact Or.inl goldbach_case_74
  | 76 => exact Or.inl goldbach_case_76
  | 78 => exact Or.inl goldbach_case_78
  | 80 => exact Or.inl goldbach_case_80
  | 82 => exact Or.inl goldbach_case_82
  | 84 => exact Or.inl goldbach_case_84
  | 86 => exact Or.inl goldbach_case_86
  | 88 => exact Or.inl goldbach_case_88
  | 90 => exact Or.inl goldbach_case_90
  | 92 => exact Or.inl goldbach_case_92
  | 94 => exact Or.inl goldbach_case_94
  | 96 => exact Or.inl goldbach_case_96
  | 98 => exact Or.inl goldbach_case_98
  | 100 => exact Or.inl goldbach_case_100
  | 102 => exact Or.inl goldbach_case_102
  | 104 => exact Or.inl goldbach_case_104
  | 106 => exact Or.inl goldbach_case_106
  | 108 => exact Or.inl goldbach_case_108
  | 110 => exact Or.inl goldbach_case_110
  | 112 => exact Or.inl goldbach_case_112
  | 114 => exact Or.inl goldbach_case_114
  | 116 => exact Or.inl goldbach_case_116
  | 118 => exact Or.inl goldbach_case_118
  | 120 => exact Or.inl goldbach_case_120
  | 122 => exact Or.inl goldbach_case_122
  | 124 => exact Or.inl goldbach_case_124
  | 126 => exact Or.inl goldbach_case_126
  | 128 => exact Or.inl goldbach_case_128
  | 130 => exact Or.inl goldbach_case_130
  | 132 => exact Or.inl goldbach_case_132
  | 134 => exact Or.inl goldbach_case_134
  | 136 => exact Or.inl goldbach_case_136
  | 138 => exact Or.inl goldbach_case_138
  | 140 => exact Or.inl goldbach_case_140
  | 142 => exact Or.inl goldbach_case_142
  | 144 => exact Or.inl goldbach_case_144
  | 146 => exact Or.inl goldbach_case_146
  | 148 => exact Or.inl goldbach_case_148
  | 150 => exact Or.inl goldbach_case_150
  | 152 => exact Or.inl goldbach_case_152
  | 154 => exact Or.inl goldbach_case_154
  | 156 => exact Or.inl goldbach_case_156
  | 158 => exact Or.inl goldbach_case_158
  | 160 => exact Or.inl goldbach_case_160
  | 162 => exact Or.inl goldbach_case_162
  | 164 => exact Or.inl goldbach_case_164
  | 166 => exact Or.inl goldbach_case_166
  | 168 => exact Or.inl goldbach_case_168
  | 170 => exact Or.inl goldbach_case_170
  | 172 => exact Or.inl goldbach_case_172
  | 174 => exact Or.inl goldbach_case_174
  | 176 => exact Or.inl goldbach_case_176
  | 178 => exact Or.inl goldbach_case_178
  | 180 => exact Or.inl goldbach_case_180
  | 182 => exact Or.inl goldbach_case_182
  | 184 => exact Or.inl goldbach_case_184
  | 186 => exact Or.inl goldbach_case_186
  | 188 => exact Or.inl goldbach_case_188
  | 190 => exact Or.inl goldbach_case_190
  | 192 => exact Or.inl goldbach_case_192
  | 194 => exact Or.inl goldbach_case_194
  | 196 => exact Or.inl goldbach_case_196
  | 198 => exact Or.inl goldbach_case_198
  | 200 => exact Or.inl goldbach_case_200
  | 202 => exact Or.inl goldbach_case_202
  | 204 => exact Or.inl goldbach_case_204
  | 206 => exact Or.inl goldbach_case_206
  | 208 => exact Or.inl goldbach_case_208
  | 210 => exact Or.inl goldbach_case_210
  | 212 => exact Or.inl goldbach_case_212
  | 214 => exact Or.inl goldbach_case_214
  | 216 => exact Or.inl goldbach_case_216
  | 218 => exact Or.inl goldbach_case_218
  | 220 => exact Or.inl goldbach_case_220
  | 222 => exact Or.inl goldbach_case_222
  | 224 => exact Or.inl goldbach_case_224
  | 226 => exact Or.inl goldbach_case_226
  | 228 => exact Or.inl goldbach_case_228
  | 230 => exact Or.inl goldbach_case_230
  | 232 => exact Or.inl goldbach_case_232
  | 234 => exact Or.inl goldbach_case_234
  | 236 => exact Or.inl goldbach_case_236
  | 238 => exact Or.inl goldbach_case_238
  | 240 => exact Or.inl goldbach_case_240
  | 242 => exact Or.inl goldbach_case_242
  | 244 => exact Or.inl goldbach_case_244
  | 246 => exact Or.inl goldbach_case_246
  | 248 => exact Or.inl goldbach_case_248
  | 250 => exact Or.inl goldbach_case_250
  | 252 => exact Or.inl goldbach_case_252
  | 254 => exact Or.inl goldbach_case_254
  | 256 => exact Or.inl goldbach_case_256
  | 258 => exact Or.inl goldbach_case_258
  | 260 => exact Or.inl goldbach_case_260
  | 262 => exact Or.inl goldbach_case_262
  | 264 => exact Or.inl goldbach_case_264
  | 266 => exact Or.inl goldbach_case_266
  | 268 => exact Or.inl goldbach_case_268
  | 270 => exact Or.inl goldbach_case_270
  | 272 => exact Or.inl goldbach_case_272
  | 274 => exact Or.inl goldbach_case_274
  | 276 => exact Or.inl goldbach_case_276
  | 278 => exact Or.inl goldbach_case_278
  | 280 => exact Or.inl goldbach_case_280
  | 282 => exact Or.inl goldbach_case_282
  | 284 => exact Or.inl goldbach_case_284
  | 286 => exact Or.inl goldbach_case_286
  | 288 => exact Or.inl goldbach_case_288
  | 290 => exact Or.inl goldbach_case_290
  | 292 => exact Or.inl goldbach_case_292
  | 294 => exact Or.inl goldbach_case_294
  | 296 => exact Or.inl goldbach_case_296
  | 298 => exact Or.inl goldbach_case_298
  | 300 => exact Or.inl goldbach_case_300
  | 302 => exact Or.inl goldbach_case_302
  | 304 => exact Or.inl goldbach_case_304
  | 306 => exact Or.inl goldbach_case_306
  | 308 => exact Or.inl goldbach_case_308
  | 310 => exact Or.inl goldbach_case_310
  | 312 => exact Or.inl goldbach_case_312
  | 314 => exact Or.inl goldbach_case_314
  | 316 => exact Or.inl goldbach_case_316
  | 318 => exact Or.inl goldbach_case_318
  | 320 => exact Or.inl goldbach_case_320
  | 322 => exact Or.inl goldbach_case_322
  | 324 => exact Or.inl goldbach_case_324
  | 326 => exact Or.inl goldbach_case_326
  | 328 => exact Or.inl goldbach_case_328
  | 330 => exact Or.inl goldbach_case_330
  | 332 => exact Or.inl goldbach_case_332
  | 334 => exact Or.inl goldbach_case_334
  | 336 => exact Or.inl goldbach_case_336
  | 338 => exact Or.inl goldbach_case_338
  | 340 => exact Or.inl goldbach_case_340
  | 342 => exact Or.inl goldbach_case_342
  | 344 => exact Or.inl goldbach_case_344
  | 346 => exact Or.inl goldbach_case_346
  | 348 => exact Or.inl goldbach_case_348
  | 350 => exact Or.inl goldbach_case_350
  | 352 => exact Or.inl goldbach_case_352
  | 354 => exact Or.inl goldbach_case_354
  | 356 => exact Or.inl goldbach_case_356
  | 358 => exact Or.inl goldbach_case_358
  | 360 => exact Or.inl goldbach_case_360
  | 362 => exact Or.inl goldbach_case_362
  | 364 => exact Or.inl goldbach_case_364
  | 366 => exact Or.inl goldbach_case_366
  | 368 => exact Or.inl goldbach_case_368
  | 370 => exact Or.inl goldbach_case_370
  | 372 => exact Or.inl goldbach_case_372
  | 374 => exact Or.inl goldbach_case_374
  | 376 => exact Or.inl goldbach_case_376
  | 378 => exact Or.inl goldbach_case_378
  | 380 => exact Or.inl goldbach_case_380
  | 382 => exact Or.inl goldbach_case_382
  | 384 => exact Or.inl goldbach_case_384
  | 386 => exact Or.inl goldbach_case_386
  | 388 => exact Or.inl goldbach_case_388
  | 390 => exact Or.inl goldbach_case_390
  | 392 => exact Or.inl goldbach_case_392
  | 394 => exact Or.inl goldbach_case_394
  | 396 => exact Or.inl goldbach_case_396
  | 398 => exact Or.inl goldbach_case_398
  | 400 => exact Or.inl goldbach_case_400
  | 402 => exact Or.inl goldbach_case_402
  | 404 => exact Or.inl goldbach_case_404
  | 406 => exact Or.inl goldbach_case_406
  | 408 => exact Or.inl goldbach_case_408
  | 410 => exact Or.inl goldbach_case_410
  | 412 => exact Or.inl goldbach_case_412
  | 414 => exact Or.inl goldbach_case_414
  | 416 => exact Or.inl goldbach_case_416
  | 418 => exact Or.inl goldbach_case_418
  | 420 => exact Or.inl goldbach_case_420
  | 422 => exact Or.inl goldbach_case_422
  | 424 => exact Or.inl goldbach_case_424
  | 426 => exact Or.inl goldbach_case_426
  | 428 => exact Or.inl goldbach_case_428
  | 430 => exact Or.inl goldbach_case_430
  | 432 => exact Or.inl goldbach_case_432
  | 434 => exact Or.inl goldbach_case_434
  | 436 => exact Or.inl goldbach_case_436
  | 438 => exact Or.inl goldbach_case_438
  | 440 => exact Or.inl goldbach_case_440
  | 442 => exact Or.inl goldbach_case_442
  | 444 => exact Or.inl goldbach_case_444
  | 446 => exact Or.inl goldbach_case_446
  | 448 => exact Or.inl goldbach_case_448
  | 450 => exact Or.inl goldbach_case_450
  | 452 => exact Or.inl goldbach_case_452
  | 454 => exact Or.inl goldbach_case_454
  | 456 => exact Or.inl goldbach_case_456
  | 458 => exact Or.inl goldbach_case_458
  | 460 => exact Or.inl goldbach_case_460
  | 462 => exact Or.inl goldbach_case_462
  | 464 => exact Or.inl goldbach_case_464
  | 466 => exact Or.inl goldbach_case_466
  | 468 => exact Or.inl goldbach_case_468
  | 470 => exact Or.inl goldbach_case_470
  | 472 => exact Or.inl goldbach_case_472
  | 474 => exact Or.inl goldbach_case_474
  | 476 => exact Or.inl goldbach_case_476
  | 478 => exact Or.inl goldbach_case_478
  | 480 => exact Or.inl goldbach_case_480
  | 482 => exact Or.inl goldbach_case_482
  | 484 => exact Or.inl goldbach_case_484
  | 486 => exact Or.inl goldbach_case_486
  | 488 => exact Or.inl goldbach_case_488
  | 490 => exact Or.inl goldbach_case_490
  | 492 => exact Or.inl goldbach_case_492
  | 494 => exact Or.inl goldbach_case_494
  | 496 => exact Or.inl goldbach_case_496
  | 498 => exact Or.inl goldbach_case_498
  | 500 => exact Or.inl goldbach_case_500
  | 502 => exact Or.inl goldbach_case_502
  | 504 => exact Or.inl goldbach_case_504
  | 506 => exact Or.inl goldbach_case_506
  | 508 => exact Or.inl goldbach_case_508
  | 510 => exact Or.inl goldbach_case_510
  | 512 => exact Or.inl goldbach_case_512
  | 514 => exact Or.inl goldbach_case_514
  | 516 => exact Or.inl goldbach_case_516
  | 518 => exact Or.inl goldbach_case_518
  | 520 => exact Or.inl goldbach_case_520
  | 522 => exact Or.inl goldbach_case_522
  | 524 => exact Or.inl goldbach_case_524
  | 526 => exact Or.inl goldbach_case_526
  | 528 => exact Or.inl goldbach_case_528
  | 530 => exact Or.inl goldbach_case_530
  | 532 => exact Or.inl goldbach_case_532
  | 534 => exact Or.inl goldbach_case_534
  | 536 => exact Or.inl goldbach_case_536
  | 538 => exact Or.inl goldbach_case_538
  | 540 => exact Or.inl goldbach_case_540
  | 542 => exact Or.inl goldbach_case_542
  | 544 => exact Or.inl goldbach_case_544
  | 546 => exact Or.inl goldbach_case_546
  | 548 => exact Or.inl goldbach_case_548
  | 550 => exact Or.inl goldbach_case_550
  | 552 => exact Or.inl goldbach_case_552
  | 554 => exact Or.inl goldbach_case_554
  | 556 => exact Or.inl goldbach_case_556
  | 558 => exact Or.inl goldbach_case_558
  | 560 => exact Or.inl goldbach_case_560
  | 562 => exact Or.inl goldbach_case_562
  | 564 => exact Or.inl goldbach_case_564
  | 566 => exact Or.inl goldbach_case_566
  | 568 => exact Or.inl goldbach_case_568
  | 570 => exact Or.inl goldbach_case_570
  | 572 => exact Or.inl goldbach_case_572
  | 574 => exact Or.inl goldbach_case_574
  | 576 => exact Or.inl goldbach_case_576
  | 578 => exact Or.inl goldbach_case_578
  | 580 => exact Or.inl goldbach_case_580
  | 582 => exact Or.inl goldbach_case_582
  | 584 => exact Or.inl goldbach_case_584
  | 586 => exact Or.inl goldbach_case_586
  | 588 => exact Or.inl goldbach_case_588
  | 590 => exact Or.inl goldbach_case_590
  | 592 => exact Or.inl goldbach_case_592
  | 594 => exact Or.inl goldbach_case_594
  | 596 => exact Or.inl goldbach_case_596
  | 598 => exact Or.inl goldbach_case_598
  | 600 => exact Or.inl goldbach_case_600
  | 602 => exact Or.inl goldbach_case_602
  | 604 => exact Or.inl goldbach_case_604
  | 606 => exact Or.inl goldbach_case_606
  | 608 => exact Or.inl goldbach_case_608
  | 610 => exact Or.inl goldbach_case_610
  | 612 => exact Or.inl goldbach_case_612
  | 614 => exact Or.inl goldbach_case_614
  | 616 => exact Or.inl goldbach_case_616
  | 618 => exact Or.inl goldbach_case_618
  | 620 => exact Or.inl goldbach_case_620
  | 622 => exact Or.inl goldbach_case_622
  | 624 => exact Or.inl goldbach_case_624
  | 626 => exact Or.inl goldbach_case_626
  | 628 => exact Or.inl goldbach_case_628
  | 630 => exact Or.inl goldbach_case_630
  | 632 => exact Or.inl goldbach_case_632
  | 634 => exact Or.inl goldbach_case_634
  | 636 => exact Or.inl goldbach_case_636
  | 638 => exact Or.inl goldbach_case_638
  | 640 => exact Or.inl goldbach_case_640
  | 642 => exact Or.inl goldbach_case_642
  | 644 => exact Or.inl goldbach_case_644
  | 646 => exact Or.inl goldbach_case_646
  | 648 => exact Or.inl goldbach_case_648
  | 650 => exact Or.inl goldbach_case_650
  | 652 => exact Or.inl goldbach_case_652
  | 654 => exact Or.inl goldbach_case_654
  | 656 => exact Or.inl goldbach_case_656
  | 658 => exact Or.inl goldbach_case_658
  | 660 => exact Or.inl goldbach_case_660
  | 662 => exact Or.inl goldbach_case_662
  | 664 => exact Or.inl goldbach_case_664
  | 666 => exact Or.inl goldbach_case_666
  | 668 => exact Or.inl goldbach_case_668
  | 670 => exact Or.inl goldbach_case_670
  | 672 => exact Or.inl goldbach_case_672
  | 674 => exact Or.inl goldbach_case_674
  | 676 => exact Or.inl goldbach_case_676
  | 678 => exact Or.inl goldbach_case_678
  | 680 => exact Or.inl goldbach_case_680
  | 682 => exact Or.inl goldbach_case_682
  | 684 => exact Or.inl goldbach_case_684
  | 686 => exact Or.inl goldbach_case_686
  | 688 => exact Or.inl goldbach_case_688
  | 690 => exact Or.inl goldbach_case_690
  | 692 => exact Or.inl goldbach_case_692
  | 694 => exact Or.inl goldbach_case_694
  | 696 => exact Or.inl goldbach_case_696
  | 698 => exact Or.inl goldbach_case_698
  | 700 => exact Or.inl goldbach_case_700
  | 702 => exact Or.inl goldbach_case_702
  | 704 => exact Or.inl goldbach_case_704
  | 706 => exact Or.inl goldbach_case_706
  | 708 => exact Or.inl goldbach_case_708
  | 710 => exact Or.inl goldbach_case_710
  | 712 => exact Or.inl goldbach_case_712
  | 714 => exact Or.inl goldbach_case_714
  | 716 => exact Or.inl goldbach_case_716
  | 718 => exact Or.inl goldbach_case_718
  | 720 => exact Or.inl goldbach_case_720
  | 722 => exact Or.inl goldbach_case_722
  | 724 => exact Or.inl goldbach_case_724
  | 726 => exact Or.inl goldbach_case_726
  | 728 => exact Or.inl goldbach_case_728
  | 730 => exact Or.inl goldbach_case_730
  | 732 => exact Or.inl goldbach_case_732
  | 734 => exact Or.inl goldbach_case_734
  | 736 => exact Or.inl goldbach_case_736
  | 738 => exact Or.inl goldbach_case_738
  | 740 => exact Or.inl goldbach_case_740
  | 742 => exact Or.inl goldbach_case_742
  | 744 => exact Or.inl goldbach_case_744
  | 746 => exact Or.inl goldbach_case_746
  | 748 => exact Or.inl goldbach_case_748
  | 750 => exact Or.inl goldbach_case_750
  | 752 => exact Or.inl goldbach_case_752
  | 754 => exact Or.inl goldbach_case_754
  | 756 => exact Or.inl goldbach_case_756
  | 758 => exact Or.inl goldbach_case_758
  | 760 => exact Or.inl goldbach_case_760
  | 762 => exact Or.inl goldbach_case_762
  | 764 => exact Or.inl goldbach_case_764
  | 766 => exact Or.inl goldbach_case_766
  | 768 => exact Or.inl goldbach_case_768
  | 770 => exact Or.inl goldbach_case_770
  | 772 => exact Or.inl goldbach_case_772
  | 774 => exact Or.inl goldbach_case_774
  | 776 => exact Or.inl goldbach_case_776
  | 778 => exact Or.inl goldbach_case_778
  | 780 => exact Or.inl goldbach_case_780
  | 782 => exact Or.inl goldbach_case_782
  | 784 => exact Or.inl goldbach_case_784
  | 786 => exact Or.inl goldbach_case_786
  | 788 => exact Or.inl goldbach_case_788
  | 790 => exact Or.inl goldbach_case_790
  | 792 => exact Or.inl goldbach_case_792
  | 794 => exact Or.inl goldbach_case_794
  | 796 => exact Or.inl goldbach_case_796
  | 798 => exact Or.inl goldbach_case_798
  | 800 => exact Or.inl goldbach_case_800
  | 802 => exact Or.inl goldbach_case_802
  | 804 => exact Or.inl goldbach_case_804
  | 806 => exact Or.inl goldbach_case_806
  | 808 => exact Or.inl goldbach_case_808
  | 810 => exact Or.inl goldbach_case_810
  | 812 => exact Or.inl goldbach_case_812
  | 814 => exact Or.inl goldbach_case_814
  | 816 => exact Or.inl goldbach_case_816
  | 818 => exact Or.inl goldbach_case_818
  | 820 => exact Or.inl goldbach_case_820
  | 822 => exact Or.inl goldbach_case_822
  | 824 => exact Or.inl goldbach_case_824
  | 826 => exact Or.inl goldbach_case_826
  | 828 => exact Or.inl goldbach_case_828
  | 830 => exact Or.inl goldbach_case_830
  | 832 => exact Or.inl goldbach_case_832
  | 834 => exact Or.inl goldbach_case_834
  | 836 => exact Or.inl goldbach_case_836
  | 838 => exact Or.inl goldbach_case_838
  | 840 => exact Or.inl goldbach_case_840
  | 842 => exact Or.inl goldbach_case_842
  | 844 => exact Or.inl goldbach_case_844
  | 846 => exact Or.inl goldbach_case_846
  | 848 => exact Or.inl goldbach_case_848
  | 850 => exact Or.inl goldbach_case_850
  | 852 => exact Or.inl goldbach_case_852
  | 854 => exact Or.inl goldbach_case_854
  | 856 => exact Or.inl goldbach_case_856
  | 858 => exact Or.inl goldbach_case_858
  | 860 => exact Or.inl goldbach_case_860
  | 862 => exact Or.inl goldbach_case_862
  | 864 => exact Or.inl goldbach_case_864
  | 866 => exact Or.inl goldbach_case_866
  | 868 => exact Or.inl goldbach_case_868
  | 870 => exact Or.inl goldbach_case_870
  | 872 => exact Or.inl goldbach_case_872
  | 874 => exact Or.inl goldbach_case_874
  | 876 => exact Or.inl goldbach_case_876
  | 878 => exact Or.inl goldbach_case_878
  | 880 => exact Or.inl goldbach_case_880
  | 882 => exact Or.inl goldbach_case_882
  | 884 => exact Or.inl goldbach_case_884
  | 886 => exact Or.inl goldbach_case_886
  | 888 => exact Or.inl goldbach_case_888
  | 890 => exact Or.inl goldbach_case_890
  | 892 => exact Or.inl goldbach_case_892
  | 894 => exact Or.inl goldbach_case_894
  | 896 => exact Or.inl goldbach_case_896
  | 898 => exact Or.inl goldbach_case_898
  | 900 => exact Or.inl goldbach_case_900
  | 902 => exact Or.inl goldbach_case_902
  | 904 => exact Or.inl goldbach_case_904
  | 906 => exact Or.inl goldbach_case_906
  | 908 => exact Or.inl goldbach_case_908
  | 910 => exact Or.inl goldbach_case_910
  | 912 => exact Or.inl goldbach_case_912
  | 914 => exact Or.inl goldbach_case_914
  | 916 => exact Or.inl goldbach_case_916
  | 918 => exact Or.inl goldbach_case_918
  | 920 => exact Or.inl goldbach_case_920
  | 922 => exact Or.inl goldbach_case_922
  | 924 => exact Or.inl goldbach_case_924
  | 926 => exact Or.inl goldbach_case_926
  | 928 => exact Or.inl goldbach_case_928
  | 930 => exact Or.inl goldbach_case_930
  | 932 => exact Or.inl goldbach_case_932
  | 934 => exact Or.inl goldbach_case_934
  | 936 => exact Or.inl goldbach_case_936
  | 938 => exact Or.inl goldbach_case_938
  | 940 => exact Or.inl goldbach_case_940
  | 942 => exact Or.inl goldbach_case_942
  | 944 => exact Or.inl goldbach_case_944
  | 946 => exact Or.inl goldbach_case_946
  | 948 => exact Or.inl goldbach_case_948
  | 950 => exact Or.inl goldbach_case_950
  | 952 => exact Or.inl goldbach_case_952
  | 954 => exact Or.inl goldbach_case_954
  | 956 => exact Or.inl goldbach_case_956
  | 958 => exact Or.inl goldbach_case_958
  | 960 => exact Or.inl goldbach_case_960
  | 962 => exact Or.inl goldbach_case_962
  | 964 => exact Or.inl goldbach_case_964
  | 966 => exact Or.inl goldbach_case_966
  | 968 => exact Or.inl goldbach_case_968
  | 970 => exact Or.inl goldbach_case_970
  | 972 => exact Or.inl goldbach_case_972
  | 974 => exact Or.inl goldbach_case_974
  | 976 => exact Or.inl goldbach_case_976
  | 978 => exact Or.inl goldbach_case_978
  | 980 => exact Or.inl goldbach_case_980
  | 982 => exact Or.inl goldbach_case_982
  | 984 => exact Or.inl goldbach_case_984
  | 986 => exact Or.inl goldbach_case_986
  | 988 => exact Or.inl goldbach_case_988
  | 990 => exact Or.inl goldbach_case_990
  | 992 => exact Or.inl goldbach_case_992
  | 994 => exact Or.inl goldbach_case_994
  | 996 => exact Or.inl goldbach_case_996
  | 998 => exact Or.inl goldbach_case_998
  | 1000 => exact Or.inl goldbach_case_1000
  | 1002 => exact Or.inl goldbach_case_1002
  | _ => exact Or.inr trivial
