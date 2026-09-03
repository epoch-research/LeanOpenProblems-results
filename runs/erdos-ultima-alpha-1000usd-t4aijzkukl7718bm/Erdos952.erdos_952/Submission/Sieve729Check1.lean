import Submission.Sieve729Data
import Submission.Sieve729Masks

/-! Kernel-checked closure identities for a block of barrier rows. -/
namespace Erdos952Investigation.Sieve729
open BitsetBarrier
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

lemma row_checked_100 :
    (dilate period (rowNeighbors rows 100) &&& bits 100) ||| rows 100 = rows 100 := by
  decide +kernel

lemma row_checked_101 :
    (dilate period (rowNeighbors rows 101) &&& bits 101) ||| rows 101 = rows 101 := by
  decide +kernel

lemma row_checked_102 :
    (dilate period (rowNeighbors rows 102) &&& bits 102) ||| rows 102 = rows 102 := by
  decide +kernel

lemma row_checked_103 :
    (dilate period (rowNeighbors rows 103) &&& bits 103) ||| rows 103 = rows 103 := by
  decide +kernel

lemma row_checked_104 :
    (dilate period (rowNeighbors rows 104) &&& bits 104) ||| rows 104 = rows 104 := by
  decide +kernel

lemma row_checked_105 :
    (dilate period (rowNeighbors rows 105) &&& bits 105) ||| rows 105 = rows 105 := by
  decide +kernel

lemma row_checked_106 :
    (dilate period (rowNeighbors rows 106) &&& bits 106) ||| rows 106 = rows 106 := by
  decide +kernel

lemma row_checked_107 :
    (dilate period (rowNeighbors rows 107) &&& bits 107) ||| rows 107 = rows 107 := by
  decide +kernel

lemma row_checked_108 :
    (dilate period (rowNeighbors rows 108) &&& bits 108) ||| rows 108 = rows 108 := by
  decide +kernel

lemma row_checked_109 :
    (dilate period (rowNeighbors rows 109) &&& bits 109) ||| rows 109 = rows 109 := by
  decide +kernel

lemma row_checked_110 :
    (dilate period (rowNeighbors rows 110) &&& bits 110) ||| rows 110 = rows 110 := by
  decide +kernel

lemma row_checked_111 :
    (dilate period (rowNeighbors rows 111) &&& bits 111) ||| rows 111 = rows 111 := by
  decide +kernel

lemma row_checked_112 :
    (dilate period (rowNeighbors rows 112) &&& bits 112) ||| rows 112 = rows 112 := by
  decide +kernel

lemma row_checked_113 :
    (dilate period (rowNeighbors rows 113) &&& bits 113) ||| rows 113 = rows 113 := by
  decide +kernel

lemma row_checked_114 :
    (dilate period (rowNeighbors rows 114) &&& bits 114) ||| rows 114 = rows 114 := by
  decide +kernel

lemma row_checked_115 :
    (dilate period (rowNeighbors rows 115) &&& bits 115) ||| rows 115 = rows 115 := by
  decide +kernel

lemma row_checked_116 :
    (dilate period (rowNeighbors rows 116) &&& bits 116) ||| rows 116 = rows 116 := by
  decide +kernel

lemma row_checked_117 :
    (dilate period (rowNeighbors rows 117) &&& bits 117) ||| rows 117 = rows 117 := by
  decide +kernel

lemma row_checked_118 :
    (dilate period (rowNeighbors rows 118) &&& bits 118) ||| rows 118 = rows 118 := by
  decide +kernel

lemma row_checked_119 :
    (dilate period (rowNeighbors rows 119) &&& bits 119) ||| rows 119 = rows 119 := by
  decide +kernel

lemma row_checked_120 :
    (dilate period (rowNeighbors rows 120) &&& bits 120) ||| rows 120 = rows 120 := by
  decide +kernel

lemma row_checked_121 :
    (dilate period (rowNeighbors rows 121) &&& bits 121) ||| rows 121 = rows 121 := by
  decide +kernel

lemma row_checked_122 :
    (dilate period (rowNeighbors rows 122) &&& bits 122) ||| rows 122 = rows 122 := by
  decide +kernel

lemma row_checked_123 :
    (dilate period (rowNeighbors rows 123) &&& bits 123) ||| rows 123 = rows 123 := by
  decide +kernel

lemma row_checked_124 :
    (dilate period (rowNeighbors rows 124) &&& bits 124) ||| rows 124 = rows 124 := by
  decide +kernel

lemma row_checked_125 :
    (dilate period (rowNeighbors rows 125) &&& bits 125) ||| rows 125 = rows 125 := by
  decide +kernel

lemma row_checked_126 :
    (dilate period (rowNeighbors rows 126) &&& bits 126) ||| rows 126 = rows 126 := by
  decide +kernel

lemma row_checked_127 :
    (dilate period (rowNeighbors rows 127) &&& bits 127) ||| rows 127 = rows 127 := by
  decide +kernel

lemma row_checked_128 :
    (dilate period (rowNeighbors rows 128) &&& bits 128) ||| rows 128 = rows 128 := by
  decide +kernel

lemma row_checked_129 :
    (dilate period (rowNeighbors rows 129) &&& bits 129) ||| rows 129 = rows 129 := by
  decide +kernel

lemma row_checked_130 :
    (dilate period (rowNeighbors rows 130) &&& bits 130) ||| rows 130 = rows 130 := by
  decide +kernel

lemma row_checked_131 :
    (dilate period (rowNeighbors rows 131) &&& bits 131) ||| rows 131 = rows 131 := by
  decide +kernel

lemma row_checked_132 :
    (dilate period (rowNeighbors rows 132) &&& bits 132) ||| rows 132 = rows 132 := by
  decide +kernel

lemma row_checked_133 :
    (dilate period (rowNeighbors rows 133) &&& bits 133) ||| rows 133 = rows 133 := by
  decide +kernel

lemma row_checked_134 :
    (dilate period (rowNeighbors rows 134) &&& bits 134) ||| rows 134 = rows 134 := by
  decide +kernel

lemma row_checked_135 :
    (dilate period (rowNeighbors rows 135) &&& bits 135) ||| rows 135 = rows 135 := by
  decide +kernel

lemma row_checked_136 :
    (dilate period (rowNeighbors rows 136) &&& bits 136) ||| rows 136 = rows 136 := by
  decide +kernel

lemma row_checked_137 :
    (dilate period (rowNeighbors rows 137) &&& bits 137) ||| rows 137 = rows 137 := by
  decide +kernel

lemma row_checked_138 :
    (dilate period (rowNeighbors rows 138) &&& bits 138) ||| rows 138 = rows 138 := by
  decide +kernel

lemma row_checked_139 :
    (dilate period (rowNeighbors rows 139) &&& bits 139) ||| rows 139 = rows 139 := by
  decide +kernel

lemma row_checked_140 :
    (dilate period (rowNeighbors rows 140) &&& bits 140) ||| rows 140 = rows 140 := by
  decide +kernel

lemma row_checked_141 :
    (dilate period (rowNeighbors rows 141) &&& bits 141) ||| rows 141 = rows 141 := by
  decide +kernel

lemma row_checked_142 :
    (dilate period (rowNeighbors rows 142) &&& bits 142) ||| rows 142 = rows 142 := by
  decide +kernel

lemma row_checked_143 :
    (dilate period (rowNeighbors rows 143) &&& bits 143) ||| rows 143 = rows 143 := by
  decide +kernel

lemma row_checked_144 :
    (dilate period (rowNeighbors rows 144) &&& bits 144) ||| rows 144 = rows 144 := by
  decide +kernel

lemma row_checked_145 :
    (dilate period (rowNeighbors rows 145) &&& bits 145) ||| rows 145 = rows 145 := by
  decide +kernel

lemma row_checked_146 :
    (dilate period (rowNeighbors rows 146) &&& bits 146) ||| rows 146 = rows 146 := by
  decide +kernel

lemma row_checked_147 :
    (dilate period (rowNeighbors rows 147) &&& bits 147) ||| rows 147 = rows 147 := by
  decide +kernel

lemma row_checked_148 :
    (dilate period (rowNeighbors rows 148) &&& bits 148) ||| rows 148 = rows 148 := by
  decide +kernel

lemma row_checked_149 :
    (dilate period (rowNeighbors rows 149) &&& bits 149) ||| rows 149 = rows 149 := by
  decide +kernel

lemma row_checked_150 :
    (dilate period (rowNeighbors rows 150) &&& bits 150) ||| rows 150 = rows 150 := by
  decide +kernel

lemma row_checked_151 :
    (dilate period (rowNeighbors rows 151) &&& bits 151) ||| rows 151 = rows 151 := by
  decide +kernel

lemma row_checked_152 :
    (dilate period (rowNeighbors rows 152) &&& bits 152) ||| rows 152 = rows 152 := by
  decide +kernel

lemma row_checked_153 :
    (dilate period (rowNeighbors rows 153) &&& bits 153) ||| rows 153 = rows 153 := by
  decide +kernel

lemma row_checked_154 :
    (dilate period (rowNeighbors rows 154) &&& bits 154) ||| rows 154 = rows 154 := by
  decide +kernel

lemma row_checked_155 :
    (dilate period (rowNeighbors rows 155) &&& bits 155) ||| rows 155 = rows 155 := by
  decide +kernel

lemma row_checked_156 :
    (dilate period (rowNeighbors rows 156) &&& bits 156) ||| rows 156 = rows 156 := by
  decide +kernel

lemma row_checked_157 :
    (dilate period (rowNeighbors rows 157) &&& bits 157) ||| rows 157 = rows 157 := by
  decide +kernel

lemma row_checked_158 :
    (dilate period (rowNeighbors rows 158) &&& bits 158) ||| rows 158 = rows 158 := by
  decide +kernel

lemma row_checked_159 :
    (dilate period (rowNeighbors rows 159) &&& bits 159) ||| rows 159 = rows 159 := by
  decide +kernel

lemma row_checked_160 :
    (dilate period (rowNeighbors rows 160) &&& bits 160) ||| rows 160 = rows 160 := by
  decide +kernel

lemma row_checked_161 :
    (dilate period (rowNeighbors rows 161) &&& bits 161) ||| rows 161 = rows 161 := by
  decide +kernel

lemma row_checked_162 :
    (dilate period (rowNeighbors rows 162) &&& bits 162) ||| rows 162 = rows 162 := by
  decide +kernel

lemma row_checked_163 :
    (dilate period (rowNeighbors rows 163) &&& bits 163) ||| rows 163 = rows 163 := by
  decide +kernel

lemma row_checked_164 :
    (dilate period (rowNeighbors rows 164) &&& bits 164) ||| rows 164 = rows 164 := by
  decide +kernel

lemma row_checked_165 :
    (dilate period (rowNeighbors rows 165) &&& bits 165) ||| rows 165 = rows 165 := by
  decide +kernel

lemma row_checked_166 :
    (dilate period (rowNeighbors rows 166) &&& bits 166) ||| rows 166 = rows 166 := by
  decide +kernel

lemma row_checked_167 :
    (dilate period (rowNeighbors rows 167) &&& bits 167) ||| rows 167 = rows 167 := by
  decide +kernel

lemma row_checked_168 :
    (dilate period (rowNeighbors rows 168) &&& bits 168) ||| rows 168 = rows 168 := by
  decide +kernel

lemma row_checked_169 :
    (dilate period (rowNeighbors rows 169) &&& bits 169) ||| rows 169 = rows 169 := by
  decide +kernel

lemma row_checked_170 :
    (dilate period (rowNeighbors rows 170) &&& bits 170) ||| rows 170 = rows 170 := by
  decide +kernel

lemma row_checked_171 :
    (dilate period (rowNeighbors rows 171) &&& bits 171) ||| rows 171 = rows 171 := by
  decide +kernel

lemma row_checked_172 :
    (dilate period (rowNeighbors rows 172) &&& bits 172) ||| rows 172 = rows 172 := by
  decide +kernel

lemma row_checked_173 :
    (dilate period (rowNeighbors rows 173) &&& bits 173) ||| rows 173 = rows 173 := by
  decide +kernel

lemma row_checked_174 :
    (dilate period (rowNeighbors rows 174) &&& bits 174) ||| rows 174 = rows 174 := by
  decide +kernel

lemma row_checked_175 :
    (dilate period (rowNeighbors rows 175) &&& bits 175) ||| rows 175 = rows 175 := by
  decide +kernel

lemma row_checked_176 :
    (dilate period (rowNeighbors rows 176) &&& bits 176) ||| rows 176 = rows 176 := by
  decide +kernel

lemma row_checked_177 :
    (dilate period (rowNeighbors rows 177) &&& bits 177) ||| rows 177 = rows 177 := by
  decide +kernel

lemma row_checked_178 :
    (dilate period (rowNeighbors rows 178) &&& bits 178) ||| rows 178 = rows 178 := by
  decide +kernel

lemma row_checked_179 :
    (dilate period (rowNeighbors rows 179) &&& bits 179) ||| rows 179 = rows 179 := by
  decide +kernel

lemma row_checked_180 :
    (dilate period (rowNeighbors rows 180) &&& bits 180) ||| rows 180 = rows 180 := by
  decide +kernel

lemma row_checked_181 :
    (dilate period (rowNeighbors rows 181) &&& bits 181) ||| rows 181 = rows 181 := by
  decide +kernel

lemma row_checked_182 :
    (dilate period (rowNeighbors rows 182) &&& bits 182) ||| rows 182 = rows 182 := by
  decide +kernel

lemma row_checked_183 :
    (dilate period (rowNeighbors rows 183) &&& bits 183) ||| rows 183 = rows 183 := by
  decide +kernel

lemma row_checked_184 :
    (dilate period (rowNeighbors rows 184) &&& bits 184) ||| rows 184 = rows 184 := by
  decide +kernel

lemma row_checked_185 :
    (dilate period (rowNeighbors rows 185) &&& bits 185) ||| rows 185 = rows 185 := by
  decide +kernel

lemma row_checked_186 :
    (dilate period (rowNeighbors rows 186) &&& bits 186) ||| rows 186 = rows 186 := by
  decide +kernel

lemma row_checked_187 :
    (dilate period (rowNeighbors rows 187) &&& bits 187) ||| rows 187 = rows 187 := by
  decide +kernel

lemma row_checked_188 :
    (dilate period (rowNeighbors rows 188) &&& bits 188) ||| rows 188 = rows 188 := by
  decide +kernel

lemma row_checked_189 :
    (dilate period (rowNeighbors rows 189) &&& bits 189) ||| rows 189 = rows 189 := by
  decide +kernel

lemma row_checked_190 :
    (dilate period (rowNeighbors rows 190) &&& bits 190) ||| rows 190 = rows 190 := by
  decide +kernel

lemma row_checked_191 :
    (dilate period (rowNeighbors rows 191) &&& bits 191) ||| rows 191 = rows 191 := by
  decide +kernel

lemma row_checked_192 :
    (dilate period (rowNeighbors rows 192) &&& bits 192) ||| rows 192 = rows 192 := by
  decide +kernel

lemma row_checked_193 :
    (dilate period (rowNeighbors rows 193) &&& bits 193) ||| rows 193 = rows 193 := by
  decide +kernel

lemma row_checked_194 :
    (dilate period (rowNeighbors rows 194) &&& bits 194) ||| rows 194 = rows 194 := by
  decide +kernel

lemma row_checked_195 :
    (dilate period (rowNeighbors rows 195) &&& bits 195) ||| rows 195 = rows 195 := by
  decide +kernel

lemma row_checked_196 :
    (dilate period (rowNeighbors rows 196) &&& bits 196) ||| rows 196 = rows 196 := by
  decide +kernel

lemma row_checked_197 :
    (dilate period (rowNeighbors rows 197) &&& bits 197) ||| rows 197 = rows 197 := by
  decide +kernel

lemma row_checked_198 :
    (dilate period (rowNeighbors rows 198) &&& bits 198) ||| rows 198 = rows 198 := by
  decide +kernel

lemma row_checked_199 :
    (dilate period (rowNeighbors rows 199) &&& bits 199) ||| rows 199 = rows 199 := by
  decide +kernel

lemma block_checked_1 (i : Fin 100) :
    (dilate period (rowNeighbors rows (100 + i.val)) &&& bits (100 + i.val)) |||
      rows (100 + i.val) = rows (100 + i.val) := by
  fin_cases i
  · exact row_checked_100
  · exact row_checked_101
  · exact row_checked_102
  · exact row_checked_103
  · exact row_checked_104
  · exact row_checked_105
  · exact row_checked_106
  · exact row_checked_107
  · exact row_checked_108
  · exact row_checked_109
  · exact row_checked_110
  · exact row_checked_111
  · exact row_checked_112
  · exact row_checked_113
  · exact row_checked_114
  · exact row_checked_115
  · exact row_checked_116
  · exact row_checked_117
  · exact row_checked_118
  · exact row_checked_119
  · exact row_checked_120
  · exact row_checked_121
  · exact row_checked_122
  · exact row_checked_123
  · exact row_checked_124
  · exact row_checked_125
  · exact row_checked_126
  · exact row_checked_127
  · exact row_checked_128
  · exact row_checked_129
  · exact row_checked_130
  · exact row_checked_131
  · exact row_checked_132
  · exact row_checked_133
  · exact row_checked_134
  · exact row_checked_135
  · exact row_checked_136
  · exact row_checked_137
  · exact row_checked_138
  · exact row_checked_139
  · exact row_checked_140
  · exact row_checked_141
  · exact row_checked_142
  · exact row_checked_143
  · exact row_checked_144
  · exact row_checked_145
  · exact row_checked_146
  · exact row_checked_147
  · exact row_checked_148
  · exact row_checked_149
  · exact row_checked_150
  · exact row_checked_151
  · exact row_checked_152
  · exact row_checked_153
  · exact row_checked_154
  · exact row_checked_155
  · exact row_checked_156
  · exact row_checked_157
  · exact row_checked_158
  · exact row_checked_159
  · exact row_checked_160
  · exact row_checked_161
  · exact row_checked_162
  · exact row_checked_163
  · exact row_checked_164
  · exact row_checked_165
  · exact row_checked_166
  · exact row_checked_167
  · exact row_checked_168
  · exact row_checked_169
  · exact row_checked_170
  · exact row_checked_171
  · exact row_checked_172
  · exact row_checked_173
  · exact row_checked_174
  · exact row_checked_175
  · exact row_checked_176
  · exact row_checked_177
  · exact row_checked_178
  · exact row_checked_179
  · exact row_checked_180
  · exact row_checked_181
  · exact row_checked_182
  · exact row_checked_183
  · exact row_checked_184
  · exact row_checked_185
  · exact row_checked_186
  · exact row_checked_187
  · exact row_checked_188
  · exact row_checked_189
  · exact row_checked_190
  · exact row_checked_191
  · exact row_checked_192
  · exact row_checked_193
  · exact row_checked_194
  · exact row_checked_195
  · exact row_checked_196
  · exact row_checked_197
  · exact row_checked_198
  · exact row_checked_199

#print axioms row_checked_199

end Erdos952Investigation.Sieve729
