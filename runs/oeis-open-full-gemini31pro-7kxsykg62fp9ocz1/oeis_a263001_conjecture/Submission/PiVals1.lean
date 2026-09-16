import Submission.PrimeProof
import Submission.Diffs.Diff0
import Submission.Diffs.Diff1
import Submission.Diffs.Diff2
import Submission.Diffs.Diff3
import Submission.Diffs.Diff4
import Submission.Diffs.Diff5
import Submission.Diffs.Diff6
import Submission.Diffs.Diff7
import Submission.Diffs.Diff8
import Submission.Diffs.Diff9
import Submission.Diffs.Diff10
import Submission.Diffs.Diff11
import Submission.Diffs.Diff12
import Submission.Diffs.Diff13
import Submission.Diffs.Diff14
import Submission.Diffs.Diff15
import Submission.Diffs.Diff16
import Submission.Diffs.Diff17
import Submission.Diffs.Diff18
import Submission.Diffs.Diff19
import Submission.Diffs.Diff20
import Submission.Diffs.Diff21
import Submission.Diffs.Diff22
import Submission.Diffs.Diff23
import Submission.Diffs.Diff24
import Submission.Diffs.Diff25
import Submission.Diffs.Diff26
import Submission.Diffs.Diff27
import Submission.Diffs.Diff28
import Submission.Diffs.Diff29
import Submission.Diffs.Diff30
import Submission.Diffs.Diff31
import Submission.PiVals0

lemma pi_7310 : my_pi 7310 = 932 :=
  pi_step 7310 7140 170 914 18 rfl pi_7140 diff_100

lemma pi_7482 : my_pi 7482 = 947 :=
  pi_step 7482 7310 172 932 15 rfl pi_7310 diff_101

lemma pi_7656 : my_pi 7656 = 971 :=
  pi_step 7656 7482 174 947 24 rfl pi_7482 diff_102

lemma pi_7832 : my_pi 7832 = 990 :=
  pi_step 7832 7656 176 971 19 rfl pi_7656 diff_103

lemma pi_7875 : my_pi 7875 = 994 :=
  pi_step 7875 7832 43 990 4 rfl pi_7832 diff_104

lemma pi_8001 : my_pi 8001 = 1007 :=
  pi_step 8001 7875 126 994 13 rfl pi_7875 diff_105

lemma pi_8010 : my_pi 8010 = 1008 :=
  pi_step 8010 8001 9 1007 1 rfl pi_8001 diff_106

lemma pi_8190 : my_pi 8190 = 1027 :=
  pi_step 8190 8010 180 1008 19 rfl pi_8010 diff_107

lemma pi_8372 : my_pi 8372 = 1048 :=
  pi_step 8372 8190 182 1027 21 rfl pi_8190 diff_108

lemma pi_8556 : my_pi 8556 = 1066 :=
  pi_step 8556 8372 184 1048 18 rfl pi_8372 diff_109

lemma pi_8742 : my_pi 8742 = 1090 :=
  pi_step 8742 8556 186 1066 24 rfl pi_8556 diff_110

lemma pi_8930 : my_pi 8930 = 1110 :=
  pi_step 8930 8742 188 1090 20 rfl pi_8742 diff_111

lemma pi_9045 : my_pi 9045 = 1124 :=
  pi_step 9045 8930 115 1110 14 rfl pi_8930 diff_112

lemma pi_9120 : my_pi 9120 = 1130 :=
  pi_step 9120 9045 75 1124 6 rfl pi_9045 diff_113

lemma pi_9180 : my_pi 9180 = 1137 :=
  pi_step 9180 9120 60 1130 7 rfl pi_9120 diff_114

lemma pi_9312 : my_pi 9312 = 1152 :=
  pi_step 9312 9180 132 1137 15 rfl pi_9180 diff_115

lemma pi_9506 : my_pi 9506 = 1177 :=
  pi_step 9506 9312 194 1152 25 rfl pi_9312 diff_116

lemma pi_9702 : my_pi 9702 = 1197 :=
  pi_step 9702 9506 196 1177 20 rfl pi_9506 diff_117

lemma pi_9900 : my_pi 9900 = 1220 :=
  pi_step 9900 9702 198 1197 23 rfl pi_9702 diff_118

lemma pi_10011 : my_pi 10011 = 1231 :=
  pi_step 10011 9900 111 1220 11 rfl pi_9900 diff_119

lemma pi_10100 : my_pi 10100 = 1240 :=
  pi_step 10100 10011 89 1231 9 rfl pi_10011 diff_120

lemma pi_10153 : my_pi 10153 = 1246 :=
  pi_step 10153 10100 53 1240 6 rfl pi_10100 diff_121

lemma pi_10302 : my_pi 10302 = 1263 :=
  pi_step 10302 10153 149 1246 17 rfl pi_10153 diff_122

lemma pi_10506 : my_pi 10506 = 1285 :=
  pi_step 10506 10302 204 1263 22 rfl pi_10302 diff_123

lemma pi_10712 : my_pi 10712 = 1306 :=
  pi_step 10712 10506 206 1285 21 rfl pi_10506 diff_124

lemma pi_10920 : my_pi 10920 = 1327 :=
  pi_step 10920 10712 208 1306 21 rfl pi_10712 diff_125

lemma pi_11130 : my_pi 11130 = 1348 :=
  pi_step 11130 10920 210 1327 21 rfl pi_10920 diff_126

lemma pi_11175 : my_pi 11175 = 1354 :=
  pi_step 11175 11130 45 1348 6 rfl pi_11130 diff_127

lemma pi_11325 : my_pi 11325 = 1369 :=
  pi_step 11325 11175 150 1354 15 rfl pi_11175 diff_128

lemma pi_11342 : my_pi 11342 = 1370 :=
  pi_step 11342 11325 17 1369 1 rfl pi_11325 diff_129

lemma pi_11556 : my_pi 11556 = 1392 :=
  pi_step 11556 11342 214 1370 22 rfl pi_11342 diff_130

lemma pi_11772 : my_pi 11772 = 1409 :=
  pi_step 11772 11556 216 1392 17 rfl pi_11556 diff_131

lemma pi_11990 : my_pi 11990 = 1438 :=
  pi_step 11990 11772 218 1409 29 rfl pi_11772 diff_132

lemma pi_12210 : my_pi 12210 = 1459 :=
  pi_step 12210 11990 220 1438 21 rfl pi_11990 diff_133

lemma pi_12403 : my_pi 12403 = 1480 :=
  pi_step 12403 12210 193 1459 21 rfl pi_12210 diff_134

lemma pi_12432 : my_pi 12432 = 1483 :=
  pi_step 12432 12403 29 1480 3 rfl pi_12403 diff_135

lemma pi_12561 : my_pi 12561 = 1500 :=
  pi_step 12561 12432 129 1483 17 rfl pi_12432 diff_136

lemma pi_12656 : my_pi 12656 = 1512 :=
  pi_step 12656 12561 95 1500 12 rfl pi_12561 diff_137

lemma pi_12882 : my_pi 12882 = 1532 :=
  pi_step 12882 12656 226 1512 20 rfl pi_12656 diff_138

lemma pi_13110 : my_pi 13110 = 1560 :=
  pi_step 13110 12882 228 1532 28 rfl pi_12882 diff_139

lemma pi_13340 : my_pi 13340 = 1585 :=
  pi_step 13340 13110 230 1560 25 rfl pi_13110 diff_140

lemma pi_13366 : my_pi 13366 = 1585 :=
  pi_step 13366 13340 26 1585 0 rfl pi_13340 diff_141

lemma pi_13530 : my_pi 13530 = 1602 :=
  pi_step 13530 13366 164 1585 17 rfl pi_13366 diff_142

lemma pi_13572 : my_pi 13572 = 1605 :=
  pi_step 13572 13530 42 1602 3 rfl pi_13530 diff_143

lemma pi_13806 : my_pi 13806 = 1632 :=
  pi_step 13806 13572 234 1605 27 rfl pi_13572 diff_144

lemma pi_14042 : my_pi 14042 = 1656 :=
  pi_step 14042 13806 236 1632 24 rfl pi_13806 diff_145

lemma pi_14280 : my_pi 14280 = 1675 :=
  pi_step 14280 14042 238 1656 19 rfl pi_14042 diff_146

lemma pi_14520 : my_pi 14520 = 1700 :=
  pi_step 14520 14280 240 1675 25 rfl pi_14280 diff_147

lemma pi_14535 : my_pi 14535 = 1701 :=
  pi_step 14535 14520 15 1700 1 rfl pi_14520 diff_148

lemma pi_14706 : my_pi 14706 = 1720 :=
  pi_step 14706 14535 171 1701 19 rfl pi_14535 diff_149

lemma pi_14762 : my_pi 14762 = 1729 :=
  pi_step 14762 14706 56 1720 9 rfl pi_14706 diff_150

lemma pi_15006 : my_pi 15006 = 1754 :=
  pi_step 15006 14762 244 1729 25 rfl pi_14762 diff_151

lemma pi_15252 : my_pi 15252 = 1779 :=
  pi_step 15252 15006 246 1754 25 rfl pi_15006 diff_152

lemma pi_15500 : my_pi 15500 = 1810 :=
  pi_step 15500 15252 248 1779 31 rfl pi_15252 diff_153

lemma pi_15576 : my_pi 15576 = 1816 :=
  pi_step 15576 15500 76 1810 6 rfl pi_15500 diff_154

lemma pi_15750 : my_pi 15750 = 1837 :=
  pi_step 15750 15576 174 1816 21 rfl pi_15576 diff_155

lemma pi_15753 : my_pi 15753 = 1837 :=
  pi_step 15753 15750 3 1837 0 rfl pi_15750 diff_156

lemma pi_16002 : my_pi 16002 = 1863 :=
  pi_step 16002 15753 249 1837 26 rfl pi_15753 diff_157

lemma pi_16256 : my_pi 16256 = 1889 :=
  pi_step 16256 16002 254 1863 26 rfl pi_16002 diff_158

lemma pi_16512 : my_pi 16512 = 1912 :=
  pi_step 16512 16256 256 1889 23 rfl pi_16256 diff_159

lemma pi_16770 : my_pi 16770 = 1938 :=
  pi_step 16770 16512 258 1912 26 rfl pi_16512 diff_160

lemma pi_16836 : my_pi 16836 = 1943 :=
  pi_step 16836 16770 66 1938 5 rfl pi_16770 diff_161

lemma pi_17020 : my_pi 17020 = 1961 :=
  pi_step 17020 16836 184 1943 18 rfl pi_16836 diff_162

lemma pi_17030 : my_pi 17030 = 1964 :=
  pi_step 17030 17020 10 1961 3 rfl pi_17020 diff_163

lemma pi_17292 : my_pi 17292 = 1987 :=
  pi_step 17292 17030 262 1964 23 rfl pi_17030 diff_164

lemma pi_17556 : my_pi 17556 = 2018 :=
  pi_step 17556 17292 264 1987 31 rfl pi_17292 diff_165

lemma pi_17822 : my_pi 17822 = 2043 :=
  pi_step 17822 17556 266 2018 25 rfl pi_17556 diff_166

lemma pi_17955 : my_pi 17955 = 2057 :=
  pi_step 17955 17822 133 2043 14 rfl pi_17822 diff_167

lemma pi_18090 : my_pi 18090 = 2073 :=
  pi_step 18090 17955 135 2057 16 rfl pi_17955 diff_168

lemma pi_18145 : my_pi 18145 = 2080 :=
  pi_step 18145 18090 55 2073 7 rfl pi_18090 diff_169

lemma pi_18360 : my_pi 18360 = 2103 :=
  pi_step 18360 18145 215 2080 23 rfl pi_18145 diff_170

lemma pi_18632 : my_pi 18632 = 2129 :=
  pi_step 18632 18360 272 2103 26 rfl pi_18360 diff_171

lemma pi_18906 : my_pi 18906 = 2150 :=
  pi_step 18906 18632 274 2129 21 rfl pi_18632 diff_172

lemma pi_19110 : my_pi 19110 = 2169 :=
  pi_step 19110 18906 204 2150 19 rfl pi_18906 diff_173

lemma pi_19182 : my_pi 19182 = 2175 :=
  pi_step 19182 19110 72 2169 6 rfl pi_19110 diff_174

lemma pi_19306 : my_pi 19306 = 2188 :=
  pi_step 19306 19182 124 2175 13 rfl pi_19182 diff_175

lemma pi_19460 : my_pi 19460 = 2206 :=
  pi_step 19460 19306 154 2188 18 rfl pi_19306 diff_176

lemma pi_19740 : my_pi 19740 = 2234 :=
  pi_step 19740 19460 280 2206 28 rfl pi_19460 diff_177

lemma pi_20022 : my_pi 20022 = 2264 :=
  pi_step 20022 19740 282 2234 30 rfl pi_19740 diff_178

lemma pi_20301 : my_pi 20301 = 2293 :=
  pi_step 20301 20022 279 2264 29 rfl pi_20022 diff_179

lemma pi_20306 : my_pi 20306 = 2293 :=
  pi_step 20306 20301 5 2293 0 rfl pi_20301 diff_180

lemma pi_20503 : my_pi 20503 = 2313 :=
  pi_step 20503 20306 197 2293 20 rfl pi_20306 diff_181

lemma pi_20592 : my_pi 20592 = 2321 :=
  pi_step 20592 20503 89 2313 8 rfl pi_20503 diff_182

lemma pi_20880 : my_pi 20880 = 2348 :=
  pi_step 20880 20592 288 2321 27 rfl pi_20592 diff_183

lemma pi_21170 : my_pi 21170 = 2380 :=
  pi_step 21170 20880 290 2348 32 rfl pi_20880 diff_184

lemma pi_21321 : my_pi 21321 = 2394 :=
  pi_step 21321 21170 151 2380 14 rfl pi_21170 diff_185

lemma pi_21462 : my_pi 21462 = 2406 :=
  pi_step 21462 21321 141 2394 12 rfl pi_21321 diff_186

lemma pi_21528 : my_pi 21528 = 2416 :=
  pi_step 21528 21462 66 2406 10 rfl pi_21462 diff_187

lemma pi_21756 : my_pi 21756 = 2440 :=
  pi_step 21756 21528 228 2416 24 rfl pi_21528 diff_188

lemma pi_22052 : my_pi 22052 = 2471 :=
  pi_step 22052 21756 296 2440 31 rfl pi_21756 diff_189

lemma pi_22350 : my_pi 22350 = 2502 :=
  pi_step 22350 22052 298 2471 31 rfl pi_22052 diff_190

lemma pi_22578 : my_pi 22578 = 2524 :=
  pi_step 22578 22350 228 2502 22 rfl pi_22350 diff_191

lemma pi_22650 : my_pi 22650 = 2530 :=
  pi_step 22650 22578 72 2524 6 rfl pi_22578 diff_192

lemma pi_22791 : my_pi 22791 = 2547 :=
  pi_step 22791 22650 141 2530 17 rfl pi_22650 diff_193

lemma pi_22952 : my_pi 22952 = 2560 :=
  pi_step 22952 22791 161 2547 13 rfl pi_22791 diff_194

lemma pi_23256 : my_pi 23256 = 2593 :=
  pi_step 23256 22952 304 2560 33 rfl pi_22952 diff_195

lemma pi_23562 : my_pi 23562 = 2620 :=
  pi_step 23562 23256 306 2593 27 rfl pi_23256 diff_196

lemma pi_23870 : my_pi 23870 = 2654 :=
  pi_step 23870 23562 308 2620 34 rfl pi_23562 diff_197

lemma pi_23871 : my_pi 23871 = 2654 :=
  pi_step 23871 23870 1 2654 0 rfl pi_23870 diff_198

lemma pi_24090 : my_pi 24090 = 2679 :=
  pi_step 24090 23871 219 2654 25 rfl pi_23871 diff_199

lemma pi_24180 : my_pi 24180 = 2691 :=
  pi_step 24180 24090 90 2679 12 rfl pi_24090 diff_200

