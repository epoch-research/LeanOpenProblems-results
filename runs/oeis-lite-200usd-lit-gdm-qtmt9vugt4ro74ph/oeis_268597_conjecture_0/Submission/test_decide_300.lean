import Mathlib

set_option maxRecDepth 50000
set_option maxHeartbeats 0

open Nat

def witness_0 (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 4
  | 2 => 9
  | 3 => 8
  | 4 => 25
  | 5 => 18
  | 6 => 15
  | 7 => 16
  | 8 => 21
  | 9 => 50
  | 10 => 35
  | 11 => 36
  | 12 => 33
  | 13 => 98
  | 14 => 39
  | 15 => 32
  | 16 => 65
  | 17 => 54
  | 18 => 51
  | 19 => 100
  | 20 => 45
  | 21 => 70
  | 22 => 95
  | 23 => 72
  | 24 => 69
  | 25 => 338
  | 26 => 63
  | 27 => 196
  | 28 => 161
  | 29 => 110
  | 30 => 87
  | 31 => 64
  | 32 => 93
  | 33 => 130
  | 34 => 75
  | 35 => 108
  | 36 => 217
  | 37 => 182
  | 38 => 99
  | 39 => 200
  | 40 => 185
  | 41 => 170
  | 42 => 123
  | 43 => 140
  | 44 => 117
  | 45 => 190
  | 46 => 215
  | 47 => 144
  | 48 => 141
  | 49 => 250
  | 50 => 235
  | 51 => 676
  | 52 => 329
  | 53 => 162
  | 54 => 159
  | 55 => 392
  | 56 => 153
  | 57 => 322
  | 58 => 371
  | 59 => 220
  | 60 => 177
  | 61 => 494
  | 62 => 135
  | 63 => 128
  | 64 => 305
  | 65 => 290
  | 66 => 427
  | 67 => 260
  | 68 => 201
  | 69 => 310
  | 70 => 335
  | 71 => 216
  | 72 => 213
  | 73 => 434
  | 74 => 207
  | 75 => 364
  | 76 => 245
  | 77 => 638
  | 78 => 511
  | 79 => 400
  | 80 => 189
  | 81 => 370
  | 82 => 395
  | 83 => 340
  | 84 => 249
  | 85 => 518
  | 86 => 415
  | 87 => 280
  | 88 => 581
  | 89 => 410
  | 90 => 267
  | 91 => 380
  | 92 => 261
  | 93 => 430
  | 94 => 623
  | 95 => 288
  | 96 => 1501
  | 97 => 602
  | 98 => 279
  | 99 => 500
  | 100 => 485
  | 101 => 462
  | 102 => 303
  | 103 => 1352
  | 104 => 225
  | 105 => 658
  | 106 => 515
  | 107 => 324
  | 108 => 321
  | 109 => 350
  | 110 => 231
  | 111 => 784
  | 112 => 545
  | 113 => 530
  | 114 => 339
  | 115 => 644
  | 116 => 297
  | 117 => 742
  | 118 => 539
  | 119 => 440
  | 120 => 1331
  | 121 => 1634
  | 122 => 1243
  | 123 => 988
  | 124 => 625
  | 125 => 510
  | 126 => 255
  | 127 => 256
  | 128 => 273
  | 129 => 610
  | 130 => 635
  | 131 => 580
  | 132 => 393
  | 133 => 854
  | 134 => 351
  | 135 => 520
  | 136 => 917
  | 137 => 570
  | 138 => 411
  | 139 => 620
  | 140 => 285
  | 141 => 670
  | 142 => 363
  | 143 => 432
  | 144 => 385
  | 145 => 938
  | 146 => 423
  | 147 => 868
  | 148 => 1529
  | 149 => 550
  | 150 => 447
  | 151 => 728
  | 152 => 453
  | 153 => 490
  | 154 => 755
  | 155 => 1276
  | 156 => 1057
  | 157 => 1022
  | 158 => 471
  | 159 => 800
  | 160 => 785
  | 161 => 486
  | 162 => 1099
  | 163 => 740
  | 164 => 357
  | 165 => 790
  | 166 => 455
  | 167 => 680
  | 168 => 345
  | 169 => 650
  | 170 => 459
  | 171 => 1036
  | 172 => 1169
  | 173 => 830
  | 174 => 375
  | 175 => 560
  | 176 => 865
  | 177 => 1162
  | 178 => 1211
  | 179 => 820
  | 180 => 537
  | 181 => 2054
  | 182 => 399
  | 183 => 760
  | 184 => 905
  | 185 => 890
  | 186 => 847
  | 187 => 860
  | 188 => 405
  | 189 => 1246
  | 190 => 1991
  | 191 => 576
  | 192 => 573
  | 193 => 3002
  | 194 => 507
  | 195 => 1204
  | 196 => 965
  | 197 => 870
  | 198 => 591
  | 199 => 1000
  | 200 => 597
  | 201 => 970
  | 202 => 995
  | 203 => 924
  | 204 => 925
  | 205 => 1358
  | 206 => 603
  | 207 => 2704
  | 208 => 2189
  | 209 => 850
  | 210 => 435
  | 211 => 1316
  | 212 => 633
  | 213 => 1030
  | 214 => 1055
  | 215 => 648
  | 216 => 1477
  | 217 => 1442
  | 218 => 483
  | 219 => 700
  | 220 => 845
  | 221 => 1070
  | 222 => 2743
  | 223 => 1568
  | 224 => 465
  | 225 => 1090
  | 226 => 1115
  | 227 => 1060
  | 228 => 681
  | 229 => 950
  | 230 => 687
  | 231 => 1288
  | 232 => 665
  | 233 => 1130
  | 234 => 699
  | 235 => 1484
  | 236 => 1165
  | 237 => 1078
  | 238 => 1631
  | 239 => 880
  | 240 => 561
  | 241 => 2662
  | 242 => 567
  | 243 => 3268
  | 244 => 1205
  | 245 => 1110
  | 246 => 1183
  | 247 => 1976
  | 248 => 1785
  | 249 => 1250
  | 250 => 2651
  | 251 => 1020
  | 252 => 753
  | 253 => 4142
  | 254 => 747
  | 255 => 512
  | 256 => 1757
  | 257 => 1554
  | 258 => 771
  | 259 => 1220
  | 260 => 1285
  | 261 => 1270
  | 262 => 1799
  | 263 => 1160
  | 264 => 789
  | 265 => 1274
  | 266 => 555
  | 267 => 1708
  | 268 => 1841
  | 269 => 1150
  | 270 => 807
  | 271 => 1040
  | 272 => 609
  | 273 => 1834
  | 274 => 875
  | 275 => 1140
  | 276 => 805
  | 277 => 3302
  | 278 => 663
  | 279 => 1240
  | 280 => 1001
  | 281 => 1290
  | 282 => 843
  | 283 => 1340
  | 284 => 849
  | 285 => 1390
  | 286 => 1415
  | 287 => 864
  | 288 => 1981
  | 289 => 1946
  | 290 => 651
  | 291 => 1876
  | 292 => 3113
  | 293 => 1806
  | 294 => 615
  | 295 => 1736
  | 296 => 837
  | 297 => 3058
  | 298 => 1859
  | 299 => 1100
  | _ => 1

lemma witness_pos_and_mod_0 (n : ℕ) (h2 : n < 300) : witness_0 n > 0 ∧ (witness_0 n - 1) % Nat.totient (witness_0 n) = n := by
  by_cases h_mid : n < 150
  · by_cases h_mid : n < 75
    · by_cases h_mid : n < 38
      · by_cases h_mid : n < 19
        · by_cases h_mid : n < 10
          · by_cases h_mid : n < 5
            · by_cases h_mid : n < 3
              · by_cases h_mid : n < 2
                · by_cases h_mid : n < 1
                  · have : n = 0 := by omega
                    subst this
                    decide
                  · have : n = 1 := by omega
                    subst this
                    decide
                · have : n = 2 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 4
                · have : n = 3 := by omega
                  subst this
                  decide
                · have : n = 4 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 8
              · by_cases h_mid : n < 7
                · by_cases h_mid : n < 6
                  · have : n = 5 := by omega
                    subst this
                    decide
                  · have : n = 6 := by omega
                    subst this
                    decide
                · have : n = 7 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 9
                · have : n = 8 := by omega
                  subst this
                  decide
                · have : n = 9 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 15
            · by_cases h_mid : n < 13
              · by_cases h_mid : n < 12
                · by_cases h_mid : n < 11
                  · have : n = 10 := by omega
                    subst this
                    decide
                  · have : n = 11 := by omega
                    subst this
                    decide
                · have : n = 12 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 14
                · have : n = 13 := by omega
                  subst this
                  decide
                · have : n = 14 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 17
              · by_cases h_mid : n < 16
                · have : n = 15 := by omega
                  subst this
                  decide
                · have : n = 16 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 18
                · have : n = 17 := by omega
                  subst this
                  decide
                · have : n = 18 := by omega
                  subst this
                  decide
        · by_cases h_mid : n < 29
          · by_cases h_mid : n < 24
            · by_cases h_mid : n < 22
              · by_cases h_mid : n < 21
                · by_cases h_mid : n < 20
                  · have : n = 19 := by omega
                    subst this
                    decide
                  · have : n = 20 := by omega
                    subst this
                    decide
                · have : n = 21 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 23
                · have : n = 22 := by omega
                  subst this
                  decide
                · have : n = 23 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 27
              · by_cases h_mid : n < 26
                · by_cases h_mid : n < 25
                  · have : n = 24 := by omega
                    subst this
                    decide
                  · have : n = 25 := by omega
                    subst this
                    decide
                · have : n = 26 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 28
                · have : n = 27 := by omega
                  subst this
                  decide
                · have : n = 28 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 34
            · by_cases h_mid : n < 32
              · by_cases h_mid : n < 31
                · by_cases h_mid : n < 30
                  · have : n = 29 := by omega
                    subst this
                    decide
                  · have : n = 30 := by omega
                    subst this
                    decide
                · have : n = 31 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 33
                · have : n = 32 := by omega
                  subst this
                  decide
                · have : n = 33 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 36
              · by_cases h_mid : n < 35
                · have : n = 34 := by omega
                  subst this
                  decide
                · have : n = 35 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 37
                · have : n = 36 := by omega
                  subst this
                  decide
                · have : n = 37 := by omega
                  subst this
                  decide
      · by_cases h_mid : n < 57
        · by_cases h_mid : n < 48
          · by_cases h_mid : n < 43
            · by_cases h_mid : n < 41
              · by_cases h_mid : n < 40
                · by_cases h_mid : n < 39
                  · have : n = 38 := by omega
                    subst this
                    decide
                  · have : n = 39 := by omega
                    subst this
                    decide
                · have : n = 40 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 42
                · have : n = 41 := by omega
                  subst this
                  decide
                · have : n = 42 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 46
              · by_cases h_mid : n < 45
                · by_cases h_mid : n < 44
                  · have : n = 43 := by omega
                    subst this
                    decide
                  · have : n = 44 := by omega
                    subst this
                    decide
                · have : n = 45 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 47
                · have : n = 46 := by omega
                  subst this
                  decide
                · have : n = 47 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 53
            · by_cases h_mid : n < 51
              · by_cases h_mid : n < 50
                · by_cases h_mid : n < 49
                  · have : n = 48 := by omega
                    subst this
                    decide
                  · have : n = 49 := by omega
                    subst this
                    decide
                · have : n = 50 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 52
                · have : n = 51 := by omega
                  subst this
                  decide
                · have : n = 52 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 55
              · by_cases h_mid : n < 54
                · have : n = 53 := by omega
                  subst this
                  decide
                · have : n = 54 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 56
                · have : n = 55 := by omega
                  subst this
                  decide
                · have : n = 56 := by omega
                  subst this
                  decide
        · by_cases h_mid : n < 66
          · by_cases h_mid : n < 62
            · by_cases h_mid : n < 60
              · by_cases h_mid : n < 59
                · by_cases h_mid : n < 58
                  · have : n = 57 := by omega
                    subst this
                    decide
                  · have : n = 58 := by omega
                    subst this
                    decide
                · have : n = 59 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 61
                · have : n = 60 := by omega
                  subst this
                  decide
                · have : n = 61 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 64
              · by_cases h_mid : n < 63
                · have : n = 62 := by omega
                  subst this
                  decide
                · have : n = 63 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 65
                · have : n = 64 := by omega
                  subst this
                  decide
                · have : n = 65 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 71
            · by_cases h_mid : n < 69
              · by_cases h_mid : n < 68
                · by_cases h_mid : n < 67
                  · have : n = 66 := by omega
                    subst this
                    decide
                  · have : n = 67 := by omega
                    subst this
                    decide
                · have : n = 68 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 70
                · have : n = 69 := by omega
                  subst this
                  decide
                · have : n = 70 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 73
              · by_cases h_mid : n < 72
                · have : n = 71 := by omega
                  subst this
                  decide
                · have : n = 72 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 74
                · have : n = 73 := by omega
                  subst this
                  decide
                · have : n = 74 := by omega
                  subst this
                  decide
    · by_cases h_mid : n < 113
      · by_cases h_mid : n < 94
        · by_cases h_mid : n < 85
          · by_cases h_mid : n < 80
            · by_cases h_mid : n < 78
              · by_cases h_mid : n < 77
                · by_cases h_mid : n < 76
                  · have : n = 75 := by omega
                    subst this
                    decide
                  · have : n = 76 := by omega
                    subst this
                    decide
                · have : n = 77 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 79
                · have : n = 78 := by omega
                  subst this
                  decide
                · have : n = 79 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 83
              · by_cases h_mid : n < 82
                · by_cases h_mid : n < 81
                  · have : n = 80 := by omega
                    subst this
                    decide
                  · have : n = 81 := by omega
                    subst this
                    decide
                · have : n = 82 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 84
                · have : n = 83 := by omega
                  subst this
                  decide
                · have : n = 84 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 90
            · by_cases h_mid : n < 88
              · by_cases h_mid : n < 87
                · by_cases h_mid : n < 86
                  · have : n = 85 := by omega
                    subst this
                    decide
                  · have : n = 86 := by omega
                    subst this
                    decide
                · have : n = 87 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 89
                · have : n = 88 := by omega
                  subst this
                  decide
                · have : n = 89 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 92
              · by_cases h_mid : n < 91
                · have : n = 90 := by omega
                  subst this
                  decide
                · have : n = 91 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 93
                · have : n = 92 := by omega
                  subst this
                  decide
                · have : n = 93 := by omega
                  subst this
                  decide
        · by_cases h_mid : n < 104
          · by_cases h_mid : n < 99
            · by_cases h_mid : n < 97
              · by_cases h_mid : n < 96
                · by_cases h_mid : n < 95
                  · have : n = 94 := by omega
                    subst this
                    decide
                  · have : n = 95 := by omega
                    subst this
                    decide
                · have : n = 96 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 98
                · have : n = 97 := by omega
                  subst this
                  decide
                · have : n = 98 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 102
              · by_cases h_mid : n < 101
                · by_cases h_mid : n < 100
                  · have : n = 99 := by omega
                    subst this
                    decide
                  · have : n = 100 := by omega
                    subst this
                    decide
                · have : n = 101 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 103
                · have : n = 102 := by omega
                  subst this
                  decide
                · have : n = 103 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 109
            · by_cases h_mid : n < 107
              · by_cases h_mid : n < 106
                · by_cases h_mid : n < 105
                  · have : n = 104 := by omega
                    subst this
                    decide
                  · have : n = 105 := by omega
                    subst this
                    decide
                · have : n = 106 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 108
                · have : n = 107 := by omega
                  subst this
                  decide
                · have : n = 108 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 111
              · by_cases h_mid : n < 110
                · have : n = 109 := by omega
                  subst this
                  decide
                · have : n = 110 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 112
                · have : n = 111 := by omega
                  subst this
                  decide
                · have : n = 112 := by omega
                  subst this
                  decide
      · by_cases h_mid : n < 132
        · by_cases h_mid : n < 123
          · by_cases h_mid : n < 118
            · by_cases h_mid : n < 116
              · by_cases h_mid : n < 115
                · by_cases h_mid : n < 114
                  · have : n = 113 := by omega
                    subst this
                    decide
                  · have : n = 114 := by omega
                    subst this
                    decide
                · have : n = 115 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 117
                · have : n = 116 := by omega
                  subst this
                  decide
                · have : n = 117 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 121
              · by_cases h_mid : n < 120
                · by_cases h_mid : n < 119
                  · have : n = 118 := by omega
                    subst this
                    decide
                  · have : n = 119 := by omega
                    subst this
                    decide
                · have : n = 120 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 122
                · have : n = 121 := by omega
                  subst this
                  decide
                · have : n = 122 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 128
            · by_cases h_mid : n < 126
              · by_cases h_mid : n < 125
                · by_cases h_mid : n < 124
                  · have : n = 123 := by omega
                    subst this
                    decide
                  · have : n = 124 := by omega
                    subst this
                    decide
                · have : n = 125 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 127
                · have : n = 126 := by omega
                  subst this
                  decide
                · have : n = 127 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 130
              · by_cases h_mid : n < 129
                · have : n = 128 := by omega
                  subst this
                  decide
                · have : n = 129 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 131
                · have : n = 130 := by omega
                  subst this
                  decide
                · have : n = 131 := by omega
                  subst this
                  decide
        · by_cases h_mid : n < 141
          · by_cases h_mid : n < 137
            · by_cases h_mid : n < 135
              · by_cases h_mid : n < 134
                · by_cases h_mid : n < 133
                  · have : n = 132 := by omega
                    subst this
                    decide
                  · have : n = 133 := by omega
                    subst this
                    decide
                · have : n = 134 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 136
                · have : n = 135 := by omega
                  subst this
                  decide
                · have : n = 136 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 139
              · by_cases h_mid : n < 138
                · have : n = 137 := by omega
                  subst this
                  decide
                · have : n = 138 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 140
                · have : n = 139 := by omega
                  subst this
                  decide
                · have : n = 140 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 146
            · by_cases h_mid : n < 144
              · by_cases h_mid : n < 143
                · by_cases h_mid : n < 142
                  · have : n = 141 := by omega
                    subst this
                    decide
                  · have : n = 142 := by omega
                    subst this
                    decide
                · have : n = 143 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 145
                · have : n = 144 := by omega
                  subst this
                  decide
                · have : n = 145 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 148
              · by_cases h_mid : n < 147
                · have : n = 146 := by omega
                  subst this
                  decide
                · have : n = 147 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 149
                · have : n = 148 := by omega
                  subst this
                  decide
                · have : n = 149 := by omega
                  subst this
                  decide
  · by_cases h_mid : n < 225
    · by_cases h_mid : n < 188
      · by_cases h_mid : n < 169
        · by_cases h_mid : n < 160
          · by_cases h_mid : n < 155
            · by_cases h_mid : n < 153
              · by_cases h_mid : n < 152
                · by_cases h_mid : n < 151
                  · have : n = 150 := by omega
                    subst this
                    decide
                  · have : n = 151 := by omega
                    subst this
                    decide
                · have : n = 152 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 154
                · have : n = 153 := by omega
                  subst this
                  decide
                · have : n = 154 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 158
              · by_cases h_mid : n < 157
                · by_cases h_mid : n < 156
                  · have : n = 155 := by omega
                    subst this
                    decide
                  · have : n = 156 := by omega
                    subst this
                    decide
                · have : n = 157 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 159
                · have : n = 158 := by omega
                  subst this
                  decide
                · have : n = 159 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 165
            · by_cases h_mid : n < 163
              · by_cases h_mid : n < 162
                · by_cases h_mid : n < 161
                  · have : n = 160 := by omega
                    subst this
                    decide
                  · have : n = 161 := by omega
                    subst this
                    decide
                · have : n = 162 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 164
                · have : n = 163 := by omega
                  subst this
                  decide
                · have : n = 164 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 167
              · by_cases h_mid : n < 166
                · have : n = 165 := by omega
                  subst this
                  decide
                · have : n = 166 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 168
                · have : n = 167 := by omega
                  subst this
                  decide
                · have : n = 168 := by omega
                  subst this
                  decide
        · by_cases h_mid : n < 179
          · by_cases h_mid : n < 174
            · by_cases h_mid : n < 172
              · by_cases h_mid : n < 171
                · by_cases h_mid : n < 170
                  · have : n = 169 := by omega
                    subst this
                    decide
                  · have : n = 170 := by omega
                    subst this
                    decide
                · have : n = 171 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 173
                · have : n = 172 := by omega
                  subst this
                  decide
                · have : n = 173 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 177
              · by_cases h_mid : n < 176
                · by_cases h_mid : n < 175
                  · have : n = 174 := by omega
                    subst this
                    decide
                  · have : n = 175 := by omega
                    subst this
                    decide
                · have : n = 176 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 178
                · have : n = 177 := by omega
                  subst this
                  decide
                · have : n = 178 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 184
            · by_cases h_mid : n < 182
              · by_cases h_mid : n < 181
                · by_cases h_mid : n < 180
                  · have : n = 179 := by omega
                    subst this
                    decide
                  · have : n = 180 := by omega
                    subst this
                    decide
                · have : n = 181 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 183
                · have : n = 182 := by omega
                  subst this
                  decide
                · have : n = 183 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 186
              · by_cases h_mid : n < 185
                · have : n = 184 := by omega
                  subst this
                  decide
                · have : n = 185 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 187
                · have : n = 186 := by omega
                  subst this
                  decide
                · have : n = 187 := by omega
                  subst this
                  decide
      · by_cases h_mid : n < 207
        · by_cases h_mid : n < 198
          · by_cases h_mid : n < 193
            · by_cases h_mid : n < 191
              · by_cases h_mid : n < 190
                · by_cases h_mid : n < 189
                  · have : n = 188 := by omega
                    subst this
                    decide
                  · have : n = 189 := by omega
                    subst this
                    decide
                · have : n = 190 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 192
                · have : n = 191 := by omega
                  subst this
                  decide
                · have : n = 192 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 196
              · by_cases h_mid : n < 195
                · by_cases h_mid : n < 194
                  · have : n = 193 := by omega
                    subst this
                    decide
                  · have : n = 194 := by omega
                    subst this
                    decide
                · have : n = 195 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 197
                · have : n = 196 := by omega
                  subst this
                  decide
                · have : n = 197 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 203
            · by_cases h_mid : n < 201
              · by_cases h_mid : n < 200
                · by_cases h_mid : n < 199
                  · have : n = 198 := by omega
                    subst this
                    decide
                  · have : n = 199 := by omega
                    subst this
                    decide
                · have : n = 200 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 202
                · have : n = 201 := by omega
                  subst this
                  decide
                · have : n = 202 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 205
              · by_cases h_mid : n < 204
                · have : n = 203 := by omega
                  subst this
                  decide
                · have : n = 204 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 206
                · have : n = 205 := by omega
                  subst this
                  decide
                · have : n = 206 := by omega
                  subst this
                  decide
        · by_cases h_mid : n < 216
          · by_cases h_mid : n < 212
            · by_cases h_mid : n < 210
              · by_cases h_mid : n < 209
                · by_cases h_mid : n < 208
                  · have : n = 207 := by omega
                    subst this
                    decide
                  · have : n = 208 := by omega
                    subst this
                    decide
                · have : n = 209 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 211
                · have : n = 210 := by omega
                  subst this
                  decide
                · have : n = 211 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 214
              · by_cases h_mid : n < 213
                · have : n = 212 := by omega
                  subst this
                  decide
                · have : n = 213 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 215
                · have : n = 214 := by omega
                  subst this
                  decide
                · have : n = 215 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 221
            · by_cases h_mid : n < 219
              · by_cases h_mid : n < 218
                · by_cases h_mid : n < 217
                  · have : n = 216 := by omega
                    subst this
                    decide
                  · have : n = 217 := by omega
                    subst this
                    decide
                · have : n = 218 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 220
                · have : n = 219 := by omega
                  subst this
                  decide
                · have : n = 220 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 223
              · by_cases h_mid : n < 222
                · have : n = 221 := by omega
                  subst this
                  decide
                · have : n = 222 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 224
                · have : n = 223 := by omega
                  subst this
                  decide
                · have : n = 224 := by omega
                  subst this
                  decide
    · by_cases h_mid : n < 263
      · by_cases h_mid : n < 244
        · by_cases h_mid : n < 235
          · by_cases h_mid : n < 230
            · by_cases h_mid : n < 228
              · by_cases h_mid : n < 227
                · by_cases h_mid : n < 226
                  · have : n = 225 := by omega
                    subst this
                    decide
                  · have : n = 226 := by omega
                    subst this
                    decide
                · have : n = 227 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 229
                · have : n = 228 := by omega
                  subst this
                  decide
                · have : n = 229 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 233
              · by_cases h_mid : n < 232
                · by_cases h_mid : n < 231
                  · have : n = 230 := by omega
                    subst this
                    decide
                  · have : n = 231 := by omega
                    subst this
                    decide
                · have : n = 232 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 234
                · have : n = 233 := by omega
                  subst this
                  decide
                · have : n = 234 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 240
            · by_cases h_mid : n < 238
              · by_cases h_mid : n < 237
                · by_cases h_mid : n < 236
                  · have : n = 235 := by omega
                    subst this
                    decide
                  · have : n = 236 := by omega
                    subst this
                    decide
                · have : n = 237 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 239
                · have : n = 238 := by omega
                  subst this
                  decide
                · have : n = 239 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 242
              · by_cases h_mid : n < 241
                · have : n = 240 := by omega
                  subst this
                  decide
                · have : n = 241 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 243
                · have : n = 242 := by omega
                  subst this
                  decide
                · have : n = 243 := by omega
                  subst this
                  decide
        · by_cases h_mid : n < 254
          · by_cases h_mid : n < 249
            · by_cases h_mid : n < 247
              · by_cases h_mid : n < 246
                · by_cases h_mid : n < 245
                  · have : n = 244 := by omega
                    subst this
                    decide
                  · have : n = 245 := by omega
                    subst this
                    decide
                · have : n = 246 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 248
                · have : n = 247 := by omega
                  subst this
                  decide
                · have : n = 248 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 252
              · by_cases h_mid : n < 251
                · by_cases h_mid : n < 250
                  · have : n = 249 := by omega
                    subst this
                    decide
                  · have : n = 250 := by omega
                    subst this
                    decide
                · have : n = 251 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 253
                · have : n = 252 := by omega
                  subst this
                  decide
                · have : n = 253 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 259
            · by_cases h_mid : n < 257
              · by_cases h_mid : n < 256
                · by_cases h_mid : n < 255
                  · have : n = 254 := by omega
                    subst this
                    decide
                  · have : n = 255 := by omega
                    subst this
                    decide
                · have : n = 256 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 258
                · have : n = 257 := by omega
                  subst this
                  decide
                · have : n = 258 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 261
              · by_cases h_mid : n < 260
                · have : n = 259 := by omega
                  subst this
                  decide
                · have : n = 260 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 262
                · have : n = 261 := by omega
                  subst this
                  decide
                · have : n = 262 := by omega
                  subst this
                  decide
      · by_cases h_mid : n < 282
        · by_cases h_mid : n < 273
          · by_cases h_mid : n < 268
            · by_cases h_mid : n < 266
              · by_cases h_mid : n < 265
                · by_cases h_mid : n < 264
                  · have : n = 263 := by omega
                    subst this
                    decide
                  · have : n = 264 := by omega
                    subst this
                    decide
                · have : n = 265 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 267
                · have : n = 266 := by omega
                  subst this
                  decide
                · have : n = 267 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 271
              · by_cases h_mid : n < 270
                · by_cases h_mid : n < 269
                  · have : n = 268 := by omega
                    subst this
                    decide
                  · have : n = 269 := by omega
                    subst this
                    decide
                · have : n = 270 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 272
                · have : n = 271 := by omega
                  subst this
                  decide
                · have : n = 272 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 278
            · by_cases h_mid : n < 276
              · by_cases h_mid : n < 275
                · by_cases h_mid : n < 274
                  · have : n = 273 := by omega
                    subst this
                    decide
                  · have : n = 274 := by omega
                    subst this
                    decide
                · have : n = 275 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 277
                · have : n = 276 := by omega
                  subst this
                  decide
                · have : n = 277 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 280
              · by_cases h_mid : n < 279
                · have : n = 278 := by omega
                  subst this
                  decide
                · have : n = 279 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 281
                · have : n = 280 := by omega
                  subst this
                  decide
                · have : n = 281 := by omega
                  subst this
                  decide
        · by_cases h_mid : n < 291
          · by_cases h_mid : n < 287
            · by_cases h_mid : n < 285
              · by_cases h_mid : n < 284
                · by_cases h_mid : n < 283
                  · have : n = 282 := by omega
                    subst this
                    decide
                  · have : n = 283 := by omega
                    subst this
                    decide
                · have : n = 284 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 286
                · have : n = 285 := by omega
                  subst this
                  decide
                · have : n = 286 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 289
              · by_cases h_mid : n < 288
                · have : n = 287 := by omega
                  subst this
                  decide
                · have : n = 288 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 290
                · have : n = 289 := by omega
                  subst this
                  decide
                · have : n = 290 := by omega
                  subst this
                  decide
          · by_cases h_mid : n < 296
            · by_cases h_mid : n < 294
              · by_cases h_mid : n < 293
                · by_cases h_mid : n < 292
                  · have : n = 291 := by omega
                    subst this
                    decide
                  · have : n = 292 := by omega
                    subst this
                    decide
                · have : n = 293 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 295
                · have : n = 294 := by omega
                  subst this
                  decide
                · have : n = 295 := by omega
                  subst this
                  decide
            · by_cases h_mid : n < 298
              · by_cases h_mid : n < 297
                · have : n = 296 := by omega
                  subst this
                  decide
                · have : n = 297 := by omega
                  subst this
                  decide
              · by_cases h_mid : n < 299
                · have : n = 298 := by omega
                  subst this
                  decide
                · have : n = 299 := by omega
                  subst this
                  decide
