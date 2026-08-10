import Mathlib

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
