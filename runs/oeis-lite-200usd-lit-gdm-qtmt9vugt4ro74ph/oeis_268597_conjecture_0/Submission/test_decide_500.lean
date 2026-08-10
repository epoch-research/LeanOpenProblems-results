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
  | _ => 1

def witness_1 (n : ℕ) : ℕ :=
  match n with
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
  | _ => 1

def witness_2 (n : ℕ) : ℕ :=
  match n with
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

def witness_3 (n : ℕ) : ℕ :=
  match n with
  | 300 => 1813
  | 301 => 3614
  | 302 => 2415
  | 303 => 1456
  | 304 => 3809
  | 305 => 1386
  | 306 => 8587
  | 307 => 980
  | 308 => 645
  | 309 => 1510
  | 310 => 1535
  | 311 => 2552
  | 312 => 933
  | 313 => 2114
  | 314 => 675
  | 315 => 2044
  | 316 => 1565
  | 317 => 1974
  | 318 => 759
  | 319 => 1600
  | 320 => 1585
  | 321 => 1570
  | 322 => 867
  | 323 => 972
  | 324 => 1045
  | 325 => 2198
  | 326 => 963
  | 327 => 1480
  | 328 => 2009
  | 329 => 1210
  | 330 => 5947
  | 331 => 1580
  | 332 => 693
  | 333 => 1630
  | 334 => 1655
  | 335 => 1360
  | 336 => 705
  | 337 => 2282
  | 338 => 1011
  | 339 => 1300
  | 340 => 1685
  | 341 => 1590
  | 342 => 1015
  | 343 => 2072
  | 344 => 777
  | 345 => 2338
  | 346 => 3707
  | 347 => 1660
  | 348 => 1041
  | 349 => 1550
  | 350 => 891
  | 351 => 1120
  | 352 => 1745
  | 353 => 1730
  | 354 => 1059
  | 355 => 2324
  | 356 => 1445
  | 357 => 2422
  | 358 => 2471
  | 359 => 1640
  | 360 => 1077
  | 361 => 6194
  | 362 => 1795
  | 363 => 4108
  | 364 => 1085
  | 365 => 1790
  | 366 => 6631
  | 367 => 1520
  | 368 => 897
  | 369 => 1810
  | 370 => 1235
  | 371 => 1780
  | 372 => 2569
  | 373 => 1694
  | 374 => 1119
  | 375 => 1720
  | 376 => 1865
  | 377 => 1530
  | 378 => 795
  | 379 => 2492
  | 380 => 765
  | 381 => 3982
  | 382 => 1463
  | 383 => 1152
  | 384 => 1149
  | 385 => 4706
  | 386 => 819
  | 387 => 6004
  | 388 => 2681
  | 389 => 1830
  | 390 => 1167
  | 391 => 2408
  | 392 => 969
  | 393 => 1930
  | 394 => 1547
  | 395 => 1740
  | 396 => 957
  | 397 => 2702
  | 398 => 903
  | 399 => 2000
  | _ => 1

def witness_4 (n : ℕ) : ℕ :=
  match n with
  | 400 => 1985
  | 401 => 1970
  | 402 => 1203
  | 403 => 1940
  | 404 => 1053
  | 405 => 1990
  | 406 => 2807
  | 407 => 1848
  | 408 => 5161
  | 409 => 1850
  | 410 => 1227
  | 411 => 2716
  | 412 => 2045
  | 413 => 1710
  | 414 => 1975
  | 415 => 5408
  | 416 => 1233
  | 417 => 4378
  | 418 => 4499
  | 419 => 1700
  | 420 => 885
  | 421 => 5174
  | 422 => 855
  | 423 => 2632
  | 424 => 1625
  | 425 => 2010
  | 426 => 2947
  | 427 => 2060
  | 428 => 1089
  | 429 => 2110
  | 430 => 1295
  | 431 => 1296
  | 432 => 1293
  | 433 => 2954
  | 434 => 915
  | 435 => 2884
  | 436 => 1805
  | 437 => 2814
  | 438 => 1495
  | 439 => 1400
  | 440 => 1029
  | 441 => 1690
  | 442 => 2195
  | 443 => 2140
  | 444 => 1329
  | 445 => 5486
  | 446 => 2215
  | 447 => 3136
  | 448 => 3101
  | 449 => 2050
  | 450 => 1347
  | 451 => 2180
  | 452 => 1341
  | 453 => 2230
  | 454 => 2891
  | 455 => 2120
  | 456 => 8341
  | 457 => 3122
  | 458 => 1131
  | 459 => 1900
  | 460 => 2285
  | 461 => 2190
  | 462 => 1383
  | 463 => 2576
  | 464 => 1389
  | 465 => 2290
  | 466 => 2315
  | 467 => 2260
  | 468 => 1173
  | 469 => 1430
  | 470 => 2335
  | 471 => 2968
  | 472 => 3269
  | 473 => 2330
  | 474 => 1435
  | 475 => 2156
  | 476 => 1005
  | 477 => 3262
  | 478 => 6071
  | 479 => 1760
  | 480 => 1437
  | 481 => 5954
  | 482 => 2395
  | 483 => 5324
  | 484 => 3353
  | 485 => 1458
  | 486 => 14167
  | 487 => 6536
  | 488 => 1113
  | 489 => 2410
  | 490 => 2435
  | 491 => 2220
  | 492 => 1473
  | 493 => 2366
  | 494 => 1071
  | 495 => 3952
  | 496 => 1505
  | 497 => 2370
  | 498 => 6331
  | 499 => 2500
  | _ => 1

lemma witness_pos_and_mod_0 (n : ℕ) (h2 : n < 100) : witness_0 n > 0 ∧ (witness_0 n - 1) % Nat.totient (witness_0 n) = n := by
  by_cases h_mid : n < 50
  · by_cases h_mid : n < 25
    · by_cases h_mid : n < 13
      · by_cases h_mid : n < 7
        · by_cases h_mid : n < 4
          · by_cases h_mid : n < 2
            · by_cases h_mid : n < 1
              · have : n = 0 := by omega
                subst this
                decide
              · have : n = 1 := by omega
                subst this
                decide
            · by_cases h_mid : n < 3
              · have : n = 2 := by omega
                subst this
                decide
              · have : n = 3 := by omega
                subst this
                decide
          · by_cases h_mid : n < 6
            · by_cases h_mid : n < 5
              · have : n = 4 := by omega
                subst this
                decide
              · have : n = 5 := by omega
                subst this
                decide
            · have : n = 6 := by omega
              subst this
              decide
        · by_cases h_mid : n < 10
          · by_cases h_mid : n < 9
            · by_cases h_mid : n < 8
              · have : n = 7 := by omega
                subst this
                decide
              · have : n = 8 := by omega
                subst this
                decide
            · have : n = 9 := by omega
              subst this
              decide
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
      · by_cases h_mid : n < 19
        · by_cases h_mid : n < 16
          · by_cases h_mid : n < 15
            · by_cases h_mid : n < 14
              · have : n = 13 := by omega
                subst this
                decide
              · have : n = 14 := by omega
                subst this
                decide
            · have : n = 15 := by omega
              subst this
              decide
          · by_cases h_mid : n < 18
            · by_cases h_mid : n < 17
              · have : n = 16 := by omega
                subst this
                decide
              · have : n = 17 := by omega
                subst this
                decide
            · have : n = 18 := by omega
              subst this
              decide
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
          · by_cases h_mid : n < 24
            · by_cases h_mid : n < 23
              · have : n = 22 := by omega
                subst this
                decide
              · have : n = 23 := by omega
                subst this
                decide
            · have : n = 24 := by omega
              subst this
              decide
    · by_cases h_mid : n < 38
      · by_cases h_mid : n < 32
        · by_cases h_mid : n < 29
          · by_cases h_mid : n < 27
            · by_cases h_mid : n < 26
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
        · by_cases h_mid : n < 35
          · by_cases h_mid : n < 34
            · by_cases h_mid : n < 33
              · have : n = 32 := by omega
                subst this
                decide
              · have : n = 33 := by omega
                subst this
                decide
            · have : n = 34 := by omega
              subst this
              decide
          · by_cases h_mid : n < 37
            · by_cases h_mid : n < 36
              · have : n = 35 := by omega
                subst this
                decide
              · have : n = 36 := by omega
                subst this
                decide
            · have : n = 37 := by omega
              subst this
              decide
      · by_cases h_mid : n < 44
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
          · by_cases h_mid : n < 43
            · by_cases h_mid : n < 42
              · have : n = 41 := by omega
                subst this
                decide
              · have : n = 42 := by omega
                subst this
                decide
            · have : n = 43 := by omega
              subst this
              decide
        · by_cases h_mid : n < 47
          · by_cases h_mid : n < 46
            · by_cases h_mid : n < 45
              · have : n = 44 := by omega
                subst this
                decide
              · have : n = 45 := by omega
                subst this
                decide
            · have : n = 46 := by omega
              subst this
              decide
          · by_cases h_mid : n < 49
            · by_cases h_mid : n < 48
              · have : n = 47 := by omega
                subst this
                decide
              · have : n = 48 := by omega
                subst this
                decide
            · have : n = 49 := by omega
              subst this
              decide
  · by_cases h_mid : n < 75
    · by_cases h_mid : n < 63
      · by_cases h_mid : n < 57
        · by_cases h_mid : n < 54
          · by_cases h_mid : n < 52
            · by_cases h_mid : n < 51
              · have : n = 50 := by omega
                subst this
                decide
              · have : n = 51 := by omega
                subst this
                decide
            · by_cases h_mid : n < 53
              · have : n = 52 := by omega
                subst this
                decide
              · have : n = 53 := by omega
                subst this
                decide
          · by_cases h_mid : n < 56
            · by_cases h_mid : n < 55
              · have : n = 54 := by omega
                subst this
                decide
              · have : n = 55 := by omega
                subst this
                decide
            · have : n = 56 := by omega
              subst this
              decide
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
          · by_cases h_mid : n < 62
            · by_cases h_mid : n < 61
              · have : n = 60 := by omega
                subst this
                decide
              · have : n = 61 := by omega
                subst this
                decide
            · have : n = 62 := by omega
              subst this
              decide
      · by_cases h_mid : n < 69
        · by_cases h_mid : n < 66
          · by_cases h_mid : n < 65
            · by_cases h_mid : n < 64
              · have : n = 63 := by omega
                subst this
                decide
              · have : n = 64 := by omega
                subst this
                decide
            · have : n = 65 := by omega
              subst this
              decide
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
        · by_cases h_mid : n < 72
          · by_cases h_mid : n < 71
            · by_cases h_mid : n < 70
              · have : n = 69 := by omega
                subst this
                decide
              · have : n = 70 := by omega
                subst this
                decide
            · have : n = 71 := by omega
              subst this
              decide
          · by_cases h_mid : n < 74
            · by_cases h_mid : n < 73
              · have : n = 72 := by omega
                subst this
                decide
              · have : n = 73 := by omega
                subst this
                decide
            · have : n = 74 := by omega
              subst this
              decide
    · by_cases h_mid : n < 88
      · by_cases h_mid : n < 82
        · by_cases h_mid : n < 79
          · by_cases h_mid : n < 77
            · by_cases h_mid : n < 76
              · have : n = 75 := by omega
                subst this
                decide
              · have : n = 76 := by omega
                subst this
                decide
            · by_cases h_mid : n < 78
              · have : n = 77 := by omega
                subst this
                decide
              · have : n = 78 := by omega
                subst this
                decide
          · by_cases h_mid : n < 81
            · by_cases h_mid : n < 80
              · have : n = 79 := by omega
                subst this
                decide
              · have : n = 80 := by omega
                subst this
                decide
            · have : n = 81 := by omega
              subst this
              decide
        · by_cases h_mid : n < 85
          · by_cases h_mid : n < 84
            · by_cases h_mid : n < 83
              · have : n = 82 := by omega
                subst this
                decide
              · have : n = 83 := by omega
                subst this
                decide
            · have : n = 84 := by omega
              subst this
              decide
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
      · by_cases h_mid : n < 94
        · by_cases h_mid : n < 91
          · by_cases h_mid : n < 90
            · by_cases h_mid : n < 89
              · have : n = 88 := by omega
                subst this
                decide
              · have : n = 89 := by omega
                subst this
                decide
            · have : n = 90 := by omega
              subst this
              decide
          · by_cases h_mid : n < 93
            · by_cases h_mid : n < 92
              · have : n = 91 := by omega
                subst this
                decide
              · have : n = 92 := by omega
                subst this
                decide
            · have : n = 93 := by omega
              subst this
              decide
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
          · by_cases h_mid : n < 99
            · by_cases h_mid : n < 98
              · have : n = 97 := by omega
                subst this
                decide
              · have : n = 98 := by omega
                subst this
                decide
            · have : n = 99 := by omega
              subst this
              decide

lemma witness_pos_and_mod_1 (n : ℕ) (h1 : 100 ≤ n) (h2 : n < 200) : witness_1 n > 0 ∧ (witness_1 n - 1) % Nat.totient (witness_1 n) = n := by
  by_cases h_mid : n < 150
  · by_cases h_mid : n < 125
    · by_cases h_mid : n < 113
      · by_cases h_mid : n < 107
        · by_cases h_mid : n < 104
          · by_cases h_mid : n < 102
            · by_cases h_mid : n < 101
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
        · by_cases h_mid : n < 110
          · by_cases h_mid : n < 109
            · by_cases h_mid : n < 108
              · have : n = 107 := by omega
                subst this
                decide
              · have : n = 108 := by omega
                subst this
                decide
            · have : n = 109 := by omega
              subst this
              decide
          · by_cases h_mid : n < 112
            · by_cases h_mid : n < 111
              · have : n = 110 := by omega
                subst this
                decide
              · have : n = 111 := by omega
                subst this
                decide
            · have : n = 112 := by omega
              subst this
              decide
      · by_cases h_mid : n < 119
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
          · by_cases h_mid : n < 118
            · by_cases h_mid : n < 117
              · have : n = 116 := by omega
                subst this
                decide
              · have : n = 117 := by omega
                subst this
                decide
            · have : n = 118 := by omega
              subst this
              decide
        · by_cases h_mid : n < 122
          · by_cases h_mid : n < 121
            · by_cases h_mid : n < 120
              · have : n = 119 := by omega
                subst this
                decide
              · have : n = 120 := by omega
                subst this
                decide
            · have : n = 121 := by omega
              subst this
              decide
          · by_cases h_mid : n < 124
            · by_cases h_mid : n < 123
              · have : n = 122 := by omega
                subst this
                decide
              · have : n = 123 := by omega
                subst this
                decide
            · have : n = 124 := by omega
              subst this
              decide
    · by_cases h_mid : n < 138
      · by_cases h_mid : n < 132
        · by_cases h_mid : n < 129
          · by_cases h_mid : n < 127
            · by_cases h_mid : n < 126
              · have : n = 125 := by omega
                subst this
                decide
              · have : n = 126 := by omega
                subst this
                decide
            · by_cases h_mid : n < 128
              · have : n = 127 := by omega
                subst this
                decide
              · have : n = 128 := by omega
                subst this
                decide
          · by_cases h_mid : n < 131
            · by_cases h_mid : n < 130
              · have : n = 129 := by omega
                subst this
                decide
              · have : n = 130 := by omega
                subst this
                decide
            · have : n = 131 := by omega
              subst this
              decide
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
          · by_cases h_mid : n < 137
            · by_cases h_mid : n < 136
              · have : n = 135 := by omega
                subst this
                decide
              · have : n = 136 := by omega
                subst this
                decide
            · have : n = 137 := by omega
              subst this
              decide
      · by_cases h_mid : n < 144
        · by_cases h_mid : n < 141
          · by_cases h_mid : n < 140
            · by_cases h_mid : n < 139
              · have : n = 138 := by omega
                subst this
                decide
              · have : n = 139 := by omega
                subst this
                decide
            · have : n = 140 := by omega
              subst this
              decide
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
        · by_cases h_mid : n < 147
          · by_cases h_mid : n < 146
            · by_cases h_mid : n < 145
              · have : n = 144 := by omega
                subst this
                decide
              · have : n = 145 := by omega
                subst this
                decide
            · have : n = 146 := by omega
              subst this
              decide
          · by_cases h_mid : n < 149
            · by_cases h_mid : n < 148
              · have : n = 147 := by omega
                subst this
                decide
              · have : n = 148 := by omega
                subst this
                decide
            · have : n = 149 := by omega
              subst this
              decide
  · by_cases h_mid : n < 175
    · by_cases h_mid : n < 163
      · by_cases h_mid : n < 157
        · by_cases h_mid : n < 154
          · by_cases h_mid : n < 152
            · by_cases h_mid : n < 151
              · have : n = 150 := by omega
                subst this
                decide
              · have : n = 151 := by omega
                subst this
                decide
            · by_cases h_mid : n < 153
              · have : n = 152 := by omega
                subst this
                decide
              · have : n = 153 := by omega
                subst this
                decide
          · by_cases h_mid : n < 156
            · by_cases h_mid : n < 155
              · have : n = 154 := by omega
                subst this
                decide
              · have : n = 155 := by omega
                subst this
                decide
            · have : n = 156 := by omega
              subst this
              decide
        · by_cases h_mid : n < 160
          · by_cases h_mid : n < 159
            · by_cases h_mid : n < 158
              · have : n = 157 := by omega
                subst this
                decide
              · have : n = 158 := by omega
                subst this
                decide
            · have : n = 159 := by omega
              subst this
              decide
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
      · by_cases h_mid : n < 169
        · by_cases h_mid : n < 166
          · by_cases h_mid : n < 165
            · by_cases h_mid : n < 164
              · have : n = 163 := by omega
                subst this
                decide
              · have : n = 164 := by omega
                subst this
                decide
            · have : n = 165 := by omega
              subst this
              decide
          · by_cases h_mid : n < 168
            · by_cases h_mid : n < 167
              · have : n = 166 := by omega
                subst this
                decide
              · have : n = 167 := by omega
                subst this
                decide
            · have : n = 168 := by omega
              subst this
              decide
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
          · by_cases h_mid : n < 174
            · by_cases h_mid : n < 173
              · have : n = 172 := by omega
                subst this
                decide
              · have : n = 173 := by omega
                subst this
                decide
            · have : n = 174 := by omega
              subst this
              decide
    · by_cases h_mid : n < 188
      · by_cases h_mid : n < 182
        · by_cases h_mid : n < 179
          · by_cases h_mid : n < 177
            · by_cases h_mid : n < 176
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
        · by_cases h_mid : n < 185
          · by_cases h_mid : n < 184
            · by_cases h_mid : n < 183
              · have : n = 182 := by omega
                subst this
                decide
              · have : n = 183 := by omega
                subst this
                decide
            · have : n = 184 := by omega
              subst this
              decide
          · by_cases h_mid : n < 187
            · by_cases h_mid : n < 186
              · have : n = 185 := by omega
                subst this
                decide
              · have : n = 186 := by omega
                subst this
                decide
            · have : n = 187 := by omega
              subst this
              decide
      · by_cases h_mid : n < 194
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
          · by_cases h_mid : n < 193
            · by_cases h_mid : n < 192
              · have : n = 191 := by omega
                subst this
                decide
              · have : n = 192 := by omega
                subst this
                decide
            · have : n = 193 := by omega
              subst this
              decide
        · by_cases h_mid : n < 197
          · by_cases h_mid : n < 196
            · by_cases h_mid : n < 195
              · have : n = 194 := by omega
                subst this
                decide
              · have : n = 195 := by omega
                subst this
                decide
            · have : n = 196 := by omega
              subst this
              decide
          · by_cases h_mid : n < 199
            · by_cases h_mid : n < 198
              · have : n = 197 := by omega
                subst this
                decide
              · have : n = 198 := by omega
                subst this
                decide
            · have : n = 199 := by omega
              subst this
              decide

lemma witness_pos_and_mod_2 (n : ℕ) (h1 : 200 ≤ n) (h2 : n < 300) : witness_2 n > 0 ∧ (witness_2 n - 1) % Nat.totient (witness_2 n) = n := by
  by_cases h_mid : n < 250
  · by_cases h_mid : n < 225
    · by_cases h_mid : n < 213
      · by_cases h_mid : n < 207
        · by_cases h_mid : n < 204
          · by_cases h_mid : n < 202
            · by_cases h_mid : n < 201
              · have : n = 200 := by omega
                subst this
                decide
              · have : n = 201 := by omega
                subst this
                decide
            · by_cases h_mid : n < 203
              · have : n = 202 := by omega
                subst this
                decide
              · have : n = 203 := by omega
                subst this
                decide
          · by_cases h_mid : n < 206
            · by_cases h_mid : n < 205
              · have : n = 204 := by omega
                subst this
                decide
              · have : n = 205 := by omega
                subst this
                decide
            · have : n = 206 := by omega
              subst this
              decide
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
          · by_cases h_mid : n < 212
            · by_cases h_mid : n < 211
              · have : n = 210 := by omega
                subst this
                decide
              · have : n = 211 := by omega
                subst this
                decide
            · have : n = 212 := by omega
              subst this
              decide
      · by_cases h_mid : n < 219
        · by_cases h_mid : n < 216
          · by_cases h_mid : n < 215
            · by_cases h_mid : n < 214
              · have : n = 213 := by omega
                subst this
                decide
              · have : n = 214 := by omega
                subst this
                decide
            · have : n = 215 := by omega
              subst this
              decide
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
        · by_cases h_mid : n < 222
          · by_cases h_mid : n < 221
            · by_cases h_mid : n < 220
              · have : n = 219 := by omega
                subst this
                decide
              · have : n = 220 := by omega
                subst this
                decide
            · have : n = 221 := by omega
              subst this
              decide
          · by_cases h_mid : n < 224
            · by_cases h_mid : n < 223
              · have : n = 222 := by omega
                subst this
                decide
              · have : n = 223 := by omega
                subst this
                decide
            · have : n = 224 := by omega
              subst this
              decide
    · by_cases h_mid : n < 238
      · by_cases h_mid : n < 232
        · by_cases h_mid : n < 229
          · by_cases h_mid : n < 227
            · by_cases h_mid : n < 226
              · have : n = 225 := by omega
                subst this
                decide
              · have : n = 226 := by omega
                subst this
                decide
            · by_cases h_mid : n < 228
              · have : n = 227 := by omega
                subst this
                decide
              · have : n = 228 := by omega
                subst this
                decide
          · by_cases h_mid : n < 231
            · by_cases h_mid : n < 230
              · have : n = 229 := by omega
                subst this
                decide
              · have : n = 230 := by omega
                subst this
                decide
            · have : n = 231 := by omega
              subst this
              decide
        · by_cases h_mid : n < 235
          · by_cases h_mid : n < 234
            · by_cases h_mid : n < 233
              · have : n = 232 := by omega
                subst this
                decide
              · have : n = 233 := by omega
                subst this
                decide
            · have : n = 234 := by omega
              subst this
              decide
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
      · by_cases h_mid : n < 244
        · by_cases h_mid : n < 241
          · by_cases h_mid : n < 240
            · by_cases h_mid : n < 239
              · have : n = 238 := by omega
                subst this
                decide
              · have : n = 239 := by omega
                subst this
                decide
            · have : n = 240 := by omega
              subst this
              decide
          · by_cases h_mid : n < 243
            · by_cases h_mid : n < 242
              · have : n = 241 := by omega
                subst this
                decide
              · have : n = 242 := by omega
                subst this
                decide
            · have : n = 243 := by omega
              subst this
              decide
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
          · by_cases h_mid : n < 249
            · by_cases h_mid : n < 248
              · have : n = 247 := by omega
                subst this
                decide
              · have : n = 248 := by omega
                subst this
                decide
            · have : n = 249 := by omega
              subst this
              decide
  · by_cases h_mid : n < 275
    · by_cases h_mid : n < 263
      · by_cases h_mid : n < 257
        · by_cases h_mid : n < 254
          · by_cases h_mid : n < 252
            · by_cases h_mid : n < 251
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
        · by_cases h_mid : n < 260
          · by_cases h_mid : n < 259
            · by_cases h_mid : n < 258
              · have : n = 257 := by omega
                subst this
                decide
              · have : n = 258 := by omega
                subst this
                decide
            · have : n = 259 := by omega
              subst this
              decide
          · by_cases h_mid : n < 262
            · by_cases h_mid : n < 261
              · have : n = 260 := by omega
                subst this
                decide
              · have : n = 261 := by omega
                subst this
                decide
            · have : n = 262 := by omega
              subst this
              decide
      · by_cases h_mid : n < 269
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
          · by_cases h_mid : n < 268
            · by_cases h_mid : n < 267
              · have : n = 266 := by omega
                subst this
                decide
              · have : n = 267 := by omega
                subst this
                decide
            · have : n = 268 := by omega
              subst this
              decide
        · by_cases h_mid : n < 272
          · by_cases h_mid : n < 271
            · by_cases h_mid : n < 270
              · have : n = 269 := by omega
                subst this
                decide
              · have : n = 270 := by omega
                subst this
                decide
            · have : n = 271 := by omega
              subst this
              decide
          · by_cases h_mid : n < 274
            · by_cases h_mid : n < 273
              · have : n = 272 := by omega
                subst this
                decide
              · have : n = 273 := by omega
                subst this
                decide
            · have : n = 274 := by omega
              subst this
              decide
    · by_cases h_mid : n < 288
      · by_cases h_mid : n < 282
        · by_cases h_mid : n < 279
          · by_cases h_mid : n < 277
            · by_cases h_mid : n < 276
              · have : n = 275 := by omega
                subst this
                decide
              · have : n = 276 := by omega
                subst this
                decide
            · by_cases h_mid : n < 278
              · have : n = 277 := by omega
                subst this
                decide
              · have : n = 278 := by omega
                subst this
                decide
          · by_cases h_mid : n < 281
            · by_cases h_mid : n < 280
              · have : n = 279 := by omega
                subst this
                decide
              · have : n = 280 := by omega
                subst this
                decide
            · have : n = 281 := by omega
              subst this
              decide
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
          · by_cases h_mid : n < 287
            · by_cases h_mid : n < 286
              · have : n = 285 := by omega
                subst this
                decide
              · have : n = 286 := by omega
                subst this
                decide
            · have : n = 287 := by omega
              subst this
              decide
      · by_cases h_mid : n < 294
        · by_cases h_mid : n < 291
          · by_cases h_mid : n < 290
            · by_cases h_mid : n < 289
              · have : n = 288 := by omega
                subst this
                decide
              · have : n = 289 := by omega
                subst this
                decide
            · have : n = 290 := by omega
              subst this
              decide
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
        · by_cases h_mid : n < 297
          · by_cases h_mid : n < 296
            · by_cases h_mid : n < 295
              · have : n = 294 := by omega
                subst this
                decide
              · have : n = 295 := by omega
                subst this
                decide
            · have : n = 296 := by omega
              subst this
              decide
          · by_cases h_mid : n < 299
            · by_cases h_mid : n < 298
              · have : n = 297 := by omega
                subst this
                decide
              · have : n = 298 := by omega
                subst this
                decide
            · have : n = 299 := by omega
              subst this
              decide

lemma witness_pos_and_mod_3 (n : ℕ) (h1 : 300 ≤ n) (h2 : n < 400) : witness_3 n > 0 ∧ (witness_3 n - 1) % Nat.totient (witness_3 n) = n := by
  by_cases h_mid : n < 350
  · by_cases h_mid : n < 325
    · by_cases h_mid : n < 313
      · by_cases h_mid : n < 307
        · by_cases h_mid : n < 304
          · by_cases h_mid : n < 302
            · by_cases h_mid : n < 301
              · have : n = 300 := by omega
                subst this
                decide
              · have : n = 301 := by omega
                subst this
                decide
            · by_cases h_mid : n < 303
              · have : n = 302 := by omega
                subst this
                decide
              · have : n = 303 := by omega
                subst this
                decide
          · by_cases h_mid : n < 306
            · by_cases h_mid : n < 305
              · have : n = 304 := by omega
                subst this
                decide
              · have : n = 305 := by omega
                subst this
                decide
            · have : n = 306 := by omega
              subst this
              decide
        · by_cases h_mid : n < 310
          · by_cases h_mid : n < 309
            · by_cases h_mid : n < 308
              · have : n = 307 := by omega
                subst this
                decide
              · have : n = 308 := by omega
                subst this
                decide
            · have : n = 309 := by omega
              subst this
              decide
          · by_cases h_mid : n < 312
            · by_cases h_mid : n < 311
              · have : n = 310 := by omega
                subst this
                decide
              · have : n = 311 := by omega
                subst this
                decide
            · have : n = 312 := by omega
              subst this
              decide
      · by_cases h_mid : n < 319
        · by_cases h_mid : n < 316
          · by_cases h_mid : n < 315
            · by_cases h_mid : n < 314
              · have : n = 313 := by omega
                subst this
                decide
              · have : n = 314 := by omega
                subst this
                decide
            · have : n = 315 := by omega
              subst this
              decide
          · by_cases h_mid : n < 318
            · by_cases h_mid : n < 317
              · have : n = 316 := by omega
                subst this
                decide
              · have : n = 317 := by omega
                subst this
                decide
            · have : n = 318 := by omega
              subst this
              decide
        · by_cases h_mid : n < 322
          · by_cases h_mid : n < 321
            · by_cases h_mid : n < 320
              · have : n = 319 := by omega
                subst this
                decide
              · have : n = 320 := by omega
                subst this
                decide
            · have : n = 321 := by omega
              subst this
              decide
          · by_cases h_mid : n < 324
            · by_cases h_mid : n < 323
              · have : n = 322 := by omega
                subst this
                decide
              · have : n = 323 := by omega
                subst this
                decide
            · have : n = 324 := by omega
              subst this
              decide
    · by_cases h_mid : n < 338
      · by_cases h_mid : n < 332
        · by_cases h_mid : n < 329
          · by_cases h_mid : n < 327
            · by_cases h_mid : n < 326
              · have : n = 325 := by omega
                subst this
                decide
              · have : n = 326 := by omega
                subst this
                decide
            · by_cases h_mid : n < 328
              · have : n = 327 := by omega
                subst this
                decide
              · have : n = 328 := by omega
                subst this
                decide
          · by_cases h_mid : n < 331
            · by_cases h_mid : n < 330
              · have : n = 329 := by omega
                subst this
                decide
              · have : n = 330 := by omega
                subst this
                decide
            · have : n = 331 := by omega
              subst this
              decide
        · by_cases h_mid : n < 335
          · by_cases h_mid : n < 334
            · by_cases h_mid : n < 333
              · have : n = 332 := by omega
                subst this
                decide
              · have : n = 333 := by omega
                subst this
                decide
            · have : n = 334 := by omega
              subst this
              decide
          · by_cases h_mid : n < 337
            · by_cases h_mid : n < 336
              · have : n = 335 := by omega
                subst this
                decide
              · have : n = 336 := by omega
                subst this
                decide
            · have : n = 337 := by omega
              subst this
              decide
      · by_cases h_mid : n < 344
        · by_cases h_mid : n < 341
          · by_cases h_mid : n < 340
            · by_cases h_mid : n < 339
              · have : n = 338 := by omega
                subst this
                decide
              · have : n = 339 := by omega
                subst this
                decide
            · have : n = 340 := by omega
              subst this
              decide
          · by_cases h_mid : n < 343
            · by_cases h_mid : n < 342
              · have : n = 341 := by omega
                subst this
                decide
              · have : n = 342 := by omega
                subst this
                decide
            · have : n = 343 := by omega
              subst this
              decide
        · by_cases h_mid : n < 347
          · by_cases h_mid : n < 346
            · by_cases h_mid : n < 345
              · have : n = 344 := by omega
                subst this
                decide
              · have : n = 345 := by omega
                subst this
                decide
            · have : n = 346 := by omega
              subst this
              decide
          · by_cases h_mid : n < 349
            · by_cases h_mid : n < 348
              · have : n = 347 := by omega
                subst this
                decide
              · have : n = 348 := by omega
                subst this
                decide
            · have : n = 349 := by omega
              subst this
              decide
  · by_cases h_mid : n < 375
    · by_cases h_mid : n < 363
      · by_cases h_mid : n < 357
        · by_cases h_mid : n < 354
          · by_cases h_mid : n < 352
            · by_cases h_mid : n < 351
              · have : n = 350 := by omega
                subst this
                decide
              · have : n = 351 := by omega
                subst this
                decide
            · by_cases h_mid : n < 353
              · have : n = 352 := by omega
                subst this
                decide
              · have : n = 353 := by omega
                subst this
                decide
          · by_cases h_mid : n < 356
            · by_cases h_mid : n < 355
              · have : n = 354 := by omega
                subst this
                decide
              · have : n = 355 := by omega
                subst this
                decide
            · have : n = 356 := by omega
              subst this
              decide
        · by_cases h_mid : n < 360
          · by_cases h_mid : n < 359
            · by_cases h_mid : n < 358
              · have : n = 357 := by omega
                subst this
                decide
              · have : n = 358 := by omega
                subst this
                decide
            · have : n = 359 := by omega
              subst this
              decide
          · by_cases h_mid : n < 362
            · by_cases h_mid : n < 361
              · have : n = 360 := by omega
                subst this
                decide
              · have : n = 361 := by omega
                subst this
                decide
            · have : n = 362 := by omega
              subst this
              decide
      · by_cases h_mid : n < 369
        · by_cases h_mid : n < 366
          · by_cases h_mid : n < 365
            · by_cases h_mid : n < 364
              · have : n = 363 := by omega
                subst this
                decide
              · have : n = 364 := by omega
                subst this
                decide
            · have : n = 365 := by omega
              subst this
              decide
          · by_cases h_mid : n < 368
            · by_cases h_mid : n < 367
              · have : n = 366 := by omega
                subst this
                decide
              · have : n = 367 := by omega
                subst this
                decide
            · have : n = 368 := by omega
              subst this
              decide
        · by_cases h_mid : n < 372
          · by_cases h_mid : n < 371
            · by_cases h_mid : n < 370
              · have : n = 369 := by omega
                subst this
                decide
              · have : n = 370 := by omega
                subst this
                decide
            · have : n = 371 := by omega
              subst this
              decide
          · by_cases h_mid : n < 374
            · by_cases h_mid : n < 373
              · have : n = 372 := by omega
                subst this
                decide
              · have : n = 373 := by omega
                subst this
                decide
            · have : n = 374 := by omega
              subst this
              decide
    · by_cases h_mid : n < 388
      · by_cases h_mid : n < 382
        · by_cases h_mid : n < 379
          · by_cases h_mid : n < 377
            · by_cases h_mid : n < 376
              · have : n = 375 := by omega
                subst this
                decide
              · have : n = 376 := by omega
                subst this
                decide
            · by_cases h_mid : n < 378
              · have : n = 377 := by omega
                subst this
                decide
              · have : n = 378 := by omega
                subst this
                decide
          · by_cases h_mid : n < 381
            · by_cases h_mid : n < 380
              · have : n = 379 := by omega
                subst this
                decide
              · have : n = 380 := by omega
                subst this
                decide
            · have : n = 381 := by omega
              subst this
              decide
        · by_cases h_mid : n < 385
          · by_cases h_mid : n < 384
            · by_cases h_mid : n < 383
              · have : n = 382 := by omega
                subst this
                decide
              · have : n = 383 := by omega
                subst this
                decide
            · have : n = 384 := by omega
              subst this
              decide
          · by_cases h_mid : n < 387
            · by_cases h_mid : n < 386
              · have : n = 385 := by omega
                subst this
                decide
              · have : n = 386 := by omega
                subst this
                decide
            · have : n = 387 := by omega
              subst this
              decide
      · by_cases h_mid : n < 394
        · by_cases h_mid : n < 391
          · by_cases h_mid : n < 390
            · by_cases h_mid : n < 389
              · have : n = 388 := by omega
                subst this
                decide
              · have : n = 389 := by omega
                subst this
                decide
            · have : n = 390 := by omega
              subst this
              decide
          · by_cases h_mid : n < 393
            · by_cases h_mid : n < 392
              · have : n = 391 := by omega
                subst this
                decide
              · have : n = 392 := by omega
                subst this
                decide
            · have : n = 393 := by omega
              subst this
              decide
        · by_cases h_mid : n < 397
          · by_cases h_mid : n < 396
            · by_cases h_mid : n < 395
              · have : n = 394 := by omega
                subst this
                decide
              · have : n = 395 := by omega
                subst this
                decide
            · have : n = 396 := by omega
              subst this
              decide
          · by_cases h_mid : n < 399
            · by_cases h_mid : n < 398
              · have : n = 397 := by omega
                subst this
                decide
              · have : n = 398 := by omega
                subst this
                decide
            · have : n = 399 := by omega
              subst this
              decide

lemma witness_pos_and_mod_4 (n : ℕ) (h1 : 400 ≤ n) (h2 : n < 500) : witness_4 n > 0 ∧ (witness_4 n - 1) % Nat.totient (witness_4 n) = n := by
  by_cases h_mid : n < 450
  · by_cases h_mid : n < 425
    · by_cases h_mid : n < 413
      · by_cases h_mid : n < 407
        · by_cases h_mid : n < 404
          · by_cases h_mid : n < 402
            · by_cases h_mid : n < 401
              · have : n = 400 := by omega
                subst this
                decide
              · have : n = 401 := by omega
                subst this
                decide
            · by_cases h_mid : n < 403
              · have : n = 402 := by omega
                subst this
                decide
              · have : n = 403 := by omega
                subst this
                decide
          · by_cases h_mid : n < 406
            · by_cases h_mid : n < 405
              · have : n = 404 := by omega
                subst this
                decide
              · have : n = 405 := by omega
                subst this
                decide
            · have : n = 406 := by omega
              subst this
              decide
        · by_cases h_mid : n < 410
          · by_cases h_mid : n < 409
            · by_cases h_mid : n < 408
              · have : n = 407 := by omega
                subst this
                decide
              · have : n = 408 := by omega
                subst this
                decide
            · have : n = 409 := by omega
              subst this
              decide
          · by_cases h_mid : n < 412
            · by_cases h_mid : n < 411
              · have : n = 410 := by omega
                subst this
                decide
              · have : n = 411 := by omega
                subst this
                decide
            · have : n = 412 := by omega
              subst this
              decide
      · by_cases h_mid : n < 419
        · by_cases h_mid : n < 416
          · by_cases h_mid : n < 415
            · by_cases h_mid : n < 414
              · have : n = 413 := by omega
                subst this
                decide
              · have : n = 414 := by omega
                subst this
                decide
            · have : n = 415 := by omega
              subst this
              decide
          · by_cases h_mid : n < 418
            · by_cases h_mid : n < 417
              · have : n = 416 := by omega
                subst this
                decide
              · have : n = 417 := by omega
                subst this
                decide
            · have : n = 418 := by omega
              subst this
              decide
        · by_cases h_mid : n < 422
          · by_cases h_mid : n < 421
            · by_cases h_mid : n < 420
              · have : n = 419 := by omega
                subst this
                decide
              · have : n = 420 := by omega
                subst this
                decide
            · have : n = 421 := by omega
              subst this
              decide
          · by_cases h_mid : n < 424
            · by_cases h_mid : n < 423
              · have : n = 422 := by omega
                subst this
                decide
              · have : n = 423 := by omega
                subst this
                decide
            · have : n = 424 := by omega
              subst this
              decide
    · by_cases h_mid : n < 438
      · by_cases h_mid : n < 432
        · by_cases h_mid : n < 429
          · by_cases h_mid : n < 427
            · by_cases h_mid : n < 426
              · have : n = 425 := by omega
                subst this
                decide
              · have : n = 426 := by omega
                subst this
                decide
            · by_cases h_mid : n < 428
              · have : n = 427 := by omega
                subst this
                decide
              · have : n = 428 := by omega
                subst this
                decide
          · by_cases h_mid : n < 431
            · by_cases h_mid : n < 430
              · have : n = 429 := by omega
                subst this
                decide
              · have : n = 430 := by omega
                subst this
                decide
            · have : n = 431 := by omega
              subst this
              decide
        · by_cases h_mid : n < 435
          · by_cases h_mid : n < 434
            · by_cases h_mid : n < 433
              · have : n = 432 := by omega
                subst this
                decide
              · have : n = 433 := by omega
                subst this
                decide
            · have : n = 434 := by omega
              subst this
              decide
          · by_cases h_mid : n < 437
            · by_cases h_mid : n < 436
              · have : n = 435 := by omega
                subst this
                decide
              · have : n = 436 := by omega
                subst this
                decide
            · have : n = 437 := by omega
              subst this
              decide
      · by_cases h_mid : n < 444
        · by_cases h_mid : n < 441
          · by_cases h_mid : n < 440
            · by_cases h_mid : n < 439
              · have : n = 438 := by omega
                subst this
                decide
              · have : n = 439 := by omega
                subst this
                decide
            · have : n = 440 := by omega
              subst this
              decide
          · by_cases h_mid : n < 443
            · by_cases h_mid : n < 442
              · have : n = 441 := by omega
                subst this
                decide
              · have : n = 442 := by omega
                subst this
                decide
            · have : n = 443 := by omega
              subst this
              decide
        · by_cases h_mid : n < 447
          · by_cases h_mid : n < 446
            · by_cases h_mid : n < 445
              · have : n = 444 := by omega
                subst this
                decide
              · have : n = 445 := by omega
                subst this
                decide
            · have : n = 446 := by omega
              subst this
              decide
          · by_cases h_mid : n < 449
            · by_cases h_mid : n < 448
              · have : n = 447 := by omega
                subst this
                decide
              · have : n = 448 := by omega
                subst this
                decide
            · have : n = 449 := by omega
              subst this
              decide
  · by_cases h_mid : n < 475
    · by_cases h_mid : n < 463
      · by_cases h_mid : n < 457
        · by_cases h_mid : n < 454
          · by_cases h_mid : n < 452
            · by_cases h_mid : n < 451
              · have : n = 450 := by omega
                subst this
                decide
              · have : n = 451 := by omega
                subst this
                decide
            · by_cases h_mid : n < 453
              · have : n = 452 := by omega
                subst this
                decide
              · have : n = 453 := by omega
                subst this
                decide
          · by_cases h_mid : n < 456
            · by_cases h_mid : n < 455
              · have : n = 454 := by omega
                subst this
                decide
              · have : n = 455 := by omega
                subst this
                decide
            · have : n = 456 := by omega
              subst this
              decide
        · by_cases h_mid : n < 460
          · by_cases h_mid : n < 459
            · by_cases h_mid : n < 458
              · have : n = 457 := by omega
                subst this
                decide
              · have : n = 458 := by omega
                subst this
                decide
            · have : n = 459 := by omega
              subst this
              decide
          · by_cases h_mid : n < 462
            · by_cases h_mid : n < 461
              · have : n = 460 := by omega
                subst this
                decide
              · have : n = 461 := by omega
                subst this
                decide
            · have : n = 462 := by omega
              subst this
              decide
      · by_cases h_mid : n < 469
        · by_cases h_mid : n < 466
          · by_cases h_mid : n < 465
            · by_cases h_mid : n < 464
              · have : n = 463 := by omega
                subst this
                decide
              · have : n = 464 := by omega
                subst this
                decide
            · have : n = 465 := by omega
              subst this
              decide
          · by_cases h_mid : n < 468
            · by_cases h_mid : n < 467
              · have : n = 466 := by omega
                subst this
                decide
              · have : n = 467 := by omega
                subst this
                decide
            · have : n = 468 := by omega
              subst this
              decide
        · by_cases h_mid : n < 472
          · by_cases h_mid : n < 471
            · by_cases h_mid : n < 470
              · have : n = 469 := by omega
                subst this
                decide
              · have : n = 470 := by omega
                subst this
                decide
            · have : n = 471 := by omega
              subst this
              decide
          · by_cases h_mid : n < 474
            · by_cases h_mid : n < 473
              · have : n = 472 := by omega
                subst this
                decide
              · have : n = 473 := by omega
                subst this
                decide
            · have : n = 474 := by omega
              subst this
              decide
    · by_cases h_mid : n < 488
      · by_cases h_mid : n < 482
        · by_cases h_mid : n < 479
          · by_cases h_mid : n < 477
            · by_cases h_mid : n < 476
              · have : n = 475 := by omega
                subst this
                decide
              · have : n = 476 := by omega
                subst this
                decide
            · by_cases h_mid : n < 478
              · have : n = 477 := by omega
                subst this
                decide
              · have : n = 478 := by omega
                subst this
                decide
          · by_cases h_mid : n < 481
            · by_cases h_mid : n < 480
              · have : n = 479 := by omega
                subst this
                decide
              · have : n = 480 := by omega
                subst this
                decide
            · have : n = 481 := by omega
              subst this
              decide
        · by_cases h_mid : n < 485
          · by_cases h_mid : n < 484
            · by_cases h_mid : n < 483
              · have : n = 482 := by omega
                subst this
                decide
              · have : n = 483 := by omega
                subst this
                decide
            · have : n = 484 := by omega
              subst this
              decide
          · by_cases h_mid : n < 487
            · by_cases h_mid : n < 486
              · have : n = 485 := by omega
                subst this
                decide
              · have : n = 486 := by omega
                subst this
                decide
            · have : n = 487 := by omega
              subst this
              decide
      · by_cases h_mid : n < 494
        · by_cases h_mid : n < 491
          · by_cases h_mid : n < 490
            · by_cases h_mid : n < 489
              · have : n = 488 := by omega
                subst this
                decide
              · have : n = 489 := by omega
                subst this
                decide
            · have : n = 490 := by omega
              subst this
              decide
          · by_cases h_mid : n < 493
            · by_cases h_mid : n < 492
              · have : n = 491 := by omega
                subst this
                decide
              · have : n = 492 := by omega
                subst this
                decide
            · have : n = 493 := by omega
              subst this
              decide
        · by_cases h_mid : n < 497
          · by_cases h_mid : n < 496
            · by_cases h_mid : n < 495
              · have : n = 494 := by omega
                subst this
                decide
              · have : n = 495 := by omega
                subst this
                decide
            · have : n = 496 := by omega
              subst this
              decide
          · by_cases h_mid : n < 499
            · by_cases h_mid : n < 498
              · have : n = 497 := by omega
                subst this
                decide
              · have : n = 498 := by omega
                subst this
                decide
            · have : n = 499 := by omega
              subst this
              decide

