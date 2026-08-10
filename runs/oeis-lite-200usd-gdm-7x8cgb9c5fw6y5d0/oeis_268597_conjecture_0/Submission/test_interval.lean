import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 300000
set_option maxHeartbeats 30000000

open Nat Set

noncomputable def A268597 (n : ℕ) : ℕ := 
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

lemma solve_concrete (n : ℕ) (x : ℕ) (hx_pos : x > 0) (hx_eq : (x - 1) % x.totient = n) :
  A268597 n > 0 := by
  change sInf { x : ℕ | x > 0 ∧ (x - 1) % x.totient = n } > 0
  have h : ∃ y, y > 0 ∧ (y - 1) % y.totient = n := ⟨x, hx_pos, hx_eq⟩
  rcases h with ⟨y, hy_pos, hy_eq⟩
  have h_nonempty : { y : ℕ | y > 0 ∧ (y - 1) % y.totient = n }.Nonempty := ⟨y, hy_pos, hy_eq⟩
  have h_mem := Nat.sInf_mem h_nonempty
  exact h_mem.1


lemma solve_interval_0_99 (n : ℕ) (h1 : n ≥ 0) (h2 : n < 100) : A268597 n > 0 := by
  have h : n - 0 < 100 := by omega
  generalize h_k : n - 0 = k
  rw [h_k] at h
  by_cases h_tree_k_50 : k < 50
  · by_cases h_tree_k_25 : k < 25
    · by_cases h_tree_k_13 : k < 13
      · by_cases h_tree_k_7 : k < 7
        · by_cases h_tree_k_4 : k < 4
          · by_cases h_tree_k_2 : k < 2
            · by_cases h_tree_k_1 : k < 1
              · · have hn : n = 0 + 0 := by omega
                  subst hn
                  exact solve_concrete 0 1 (by decide) (by rfl)
              · · have hn : n = 0 + 1 := by omega
                  subst hn
                  exact solve_concrete 1 4 (by decide) (by rfl)
            · by_cases h_tree_k_3 : k < 3
              · · have hn : n = 0 + 2 := by omega
                  subst hn
                  exact solve_concrete 2 9 (by decide) (by rfl)
              · · have hn : n = 0 + 3 := by omega
                  subst hn
                  exact solve_concrete 3 8 (by decide) (by rfl)
          · by_cases h_tree_k_6 : k < 6
            · by_cases h_tree_k_5 : k < 5
              · · have hn : n = 0 + 4 := by omega
                  subst hn
                  exact solve_concrete 4 25 (by decide) (by rfl)
              · · have hn : n = 0 + 5 := by omega
                  subst hn
                  exact solve_concrete 5 18 (by decide) (by rfl)
            · · have hn : n = 0 + 6 := by omega
                subst hn
                exact solve_concrete 6 15 (by decide) (by rfl)
        · by_cases h_tree_k_10 : k < 10
          · by_cases h_tree_k_9 : k < 9
            · by_cases h_tree_k_8 : k < 8
              · · have hn : n = 0 + 7 := by omega
                  subst hn
                  exact solve_concrete 7 16 (by decide) (by rfl)
              · · have hn : n = 0 + 8 := by omega
                  subst hn
                  exact solve_concrete 8 21 (by decide) (by rfl)
            · · have hn : n = 0 + 9 := by omega
                subst hn
                exact solve_concrete 9 50 (by decide) (by rfl)
          · by_cases h_tree_k_12 : k < 12
            · by_cases h_tree_k_11 : k < 11
              · · have hn : n = 0 + 10 := by omega
                  subst hn
                  exact solve_concrete 10 35 (by decide) (by rfl)
              · · have hn : n = 0 + 11 := by omega
                  subst hn
                  exact solve_concrete 11 36 (by decide) (by rfl)
            · · have hn : n = 0 + 12 := by omega
                subst hn
                exact solve_concrete 12 33 (by decide) (by rfl)
      · by_cases h_tree_k_19 : k < 19
        · by_cases h_tree_k_16 : k < 16
          · by_cases h_tree_k_15 : k < 15
            · by_cases h_tree_k_14 : k < 14
              · · have hn : n = 0 + 13 := by omega
                  subst hn
                  exact solve_concrete 13 98 (by decide) (by rfl)
              · · have hn : n = 0 + 14 := by omega
                  subst hn
                  exact solve_concrete 14 39 (by decide) (by rfl)
            · · have hn : n = 0 + 15 := by omega
                subst hn
                exact solve_concrete 15 32 (by decide) (by rfl)
          · by_cases h_tree_k_18 : k < 18
            · by_cases h_tree_k_17 : k < 17
              · · have hn : n = 0 + 16 := by omega
                  subst hn
                  exact solve_concrete 16 65 (by decide) (by rfl)
              · · have hn : n = 0 + 17 := by omega
                  subst hn
                  exact solve_concrete 17 54 (by decide) (by rfl)
            · · have hn : n = 0 + 18 := by omega
                subst hn
                exact solve_concrete 18 51 (by decide) (by rfl)
        · by_cases h_tree_k_22 : k < 22
          · by_cases h_tree_k_21 : k < 21
            · by_cases h_tree_k_20 : k < 20
              · · have hn : n = 0 + 19 := by omega
                  subst hn
                  exact solve_concrete 19 100 (by decide) (by rfl)
              · · have hn : n = 0 + 20 := by omega
                  subst hn
                  exact solve_concrete 20 45 (by decide) (by rfl)
            · · have hn : n = 0 + 21 := by omega
                subst hn
                exact solve_concrete 21 70 (by decide) (by rfl)
          · by_cases h_tree_k_24 : k < 24
            · by_cases h_tree_k_23 : k < 23
              · · have hn : n = 0 + 22 := by omega
                  subst hn
                  exact solve_concrete 22 95 (by decide) (by rfl)
              · · have hn : n = 0 + 23 := by omega
                  subst hn
                  exact solve_concrete 23 72 (by decide) (by rfl)
            · · have hn : n = 0 + 24 := by omega
                subst hn
                exact solve_concrete 24 69 (by decide) (by rfl)
    · by_cases h_tree_k_38 : k < 38
      · by_cases h_tree_k_32 : k < 32
        · by_cases h_tree_k_29 : k < 29
          · by_cases h_tree_k_27 : k < 27
            · by_cases h_tree_k_26 : k < 26
              · · have hn : n = 0 + 25 := by omega
                  subst hn
                  exact solve_concrete 25 338 (by decide) (by rfl)
              · · have hn : n = 0 + 26 := by omega
                  subst hn
                  exact solve_concrete 26 63 (by decide) (by rfl)
            · by_cases h_tree_k_28 : k < 28
              · · have hn : n = 0 + 27 := by omega
                  subst hn
                  exact solve_concrete 27 196 (by decide) (by rfl)
              · · have hn : n = 0 + 28 := by omega
                  subst hn
                  exact solve_concrete 28 161 (by decide) (by rfl)
          · by_cases h_tree_k_31 : k < 31
            · by_cases h_tree_k_30 : k < 30
              · · have hn : n = 0 + 29 := by omega
                  subst hn
                  exact solve_concrete 29 110 (by decide) (by rfl)
              · · have hn : n = 0 + 30 := by omega
                  subst hn
                  exact solve_concrete 30 87 (by decide) (by rfl)
            · · have hn : n = 0 + 31 := by omega
                subst hn
                exact solve_concrete 31 64 (by decide) (by rfl)
        · by_cases h_tree_k_35 : k < 35
          · by_cases h_tree_k_34 : k < 34
            · by_cases h_tree_k_33 : k < 33
              · · have hn : n = 0 + 32 := by omega
                  subst hn
                  exact solve_concrete 32 93 (by decide) (by rfl)
              · · have hn : n = 0 + 33 := by omega
                  subst hn
                  exact solve_concrete 33 130 (by decide) (by rfl)
            · · have hn : n = 0 + 34 := by omega
                subst hn
                exact solve_concrete 34 75 (by decide) (by rfl)
          · by_cases h_tree_k_37 : k < 37
            · by_cases h_tree_k_36 : k < 36
              · · have hn : n = 0 + 35 := by omega
                  subst hn
                  exact solve_concrete 35 108 (by decide) (by rfl)
              · · have hn : n = 0 + 36 := by omega
                  subst hn
                  exact solve_concrete 36 217 (by decide) (by rfl)
            · · have hn : n = 0 + 37 := by omega
                subst hn
                exact solve_concrete 37 182 (by decide) (by rfl)
      · by_cases h_tree_k_44 : k < 44
        · by_cases h_tree_k_41 : k < 41
          · by_cases h_tree_k_40 : k < 40
            · by_cases h_tree_k_39 : k < 39
              · · have hn : n = 0 + 38 := by omega
                  subst hn
                  exact solve_concrete 38 99 (by decide) (by rfl)
              · · have hn : n = 0 + 39 := by omega
                  subst hn
                  exact solve_concrete 39 200 (by decide) (by rfl)
            · · have hn : n = 0 + 40 := by omega
                subst hn
                exact solve_concrete 40 185 (by decide) (by rfl)
          · by_cases h_tree_k_43 : k < 43
            · by_cases h_tree_k_42 : k < 42
              · · have hn : n = 0 + 41 := by omega
                  subst hn
                  exact solve_concrete 41 170 (by decide) (by rfl)
              · · have hn : n = 0 + 42 := by omega
                  subst hn
                  exact solve_concrete 42 123 (by decide) (by rfl)
            · · have hn : n = 0 + 43 := by omega
                subst hn
                exact solve_concrete 43 140 (by decide) (by rfl)
        · by_cases h_tree_k_47 : k < 47
          · by_cases h_tree_k_46 : k < 46
            · by_cases h_tree_k_45 : k < 45
              · · have hn : n = 0 + 44 := by omega
                  subst hn
                  exact solve_concrete 44 117 (by decide) (by rfl)
              · · have hn : n = 0 + 45 := by omega
                  subst hn
                  exact solve_concrete 45 190 (by decide) (by rfl)
            · · have hn : n = 0 + 46 := by omega
                subst hn
                exact solve_concrete 46 215 (by decide) (by rfl)
          · by_cases h_tree_k_49 : k < 49
            · by_cases h_tree_k_48 : k < 48
              · · have hn : n = 0 + 47 := by omega
                  subst hn
                  exact solve_concrete 47 144 (by decide) (by rfl)
              · · have hn : n = 0 + 48 := by omega
                  subst hn
                  exact solve_concrete 48 141 (by decide) (by rfl)
            · · have hn : n = 0 + 49 := by omega
                subst hn
                exact solve_concrete 49 250 (by decide) (by rfl)
  · by_cases h_tree_k_75 : k < 75
    · by_cases h_tree_k_63 : k < 63
      · by_cases h_tree_k_57 : k < 57
        · by_cases h_tree_k_54 : k < 54
          · by_cases h_tree_k_52 : k < 52
            · by_cases h_tree_k_51 : k < 51
              · · have hn : n = 0 + 50 := by omega
                  subst hn
                  exact solve_concrete 50 235 (by decide) (by rfl)
              · · have hn : n = 0 + 51 := by omega
                  subst hn
                  exact solve_concrete 51 676 (by decide) (by rfl)
            · by_cases h_tree_k_53 : k < 53
              · · have hn : n = 0 + 52 := by omega
                  subst hn
                  exact solve_concrete 52 329 (by decide) (by rfl)
              · · have hn : n = 0 + 53 := by omega
                  subst hn
                  exact solve_concrete 53 162 (by decide) (by rfl)
          · by_cases h_tree_k_56 : k < 56
            · by_cases h_tree_k_55 : k < 55
              · · have hn : n = 0 + 54 := by omega
                  subst hn
                  exact solve_concrete 54 159 (by decide) (by rfl)
              · · have hn : n = 0 + 55 := by omega
                  subst hn
                  exact solve_concrete 55 392 (by decide) (by rfl)
            · · have hn : n = 0 + 56 := by omega
                subst hn
                exact solve_concrete 56 153 (by decide) (by rfl)
        · by_cases h_tree_k_60 : k < 60
          · by_cases h_tree_k_59 : k < 59
            · by_cases h_tree_k_58 : k < 58
              · · have hn : n = 0 + 57 := by omega
                  subst hn
                  exact solve_concrete 57 322 (by decide) (by rfl)
              · · have hn : n = 0 + 58 := by omega
                  subst hn
                  exact solve_concrete 58 371 (by decide) (by rfl)
            · · have hn : n = 0 + 59 := by omega
                subst hn
                exact solve_concrete 59 220 (by decide) (by rfl)
          · by_cases h_tree_k_62 : k < 62
            · by_cases h_tree_k_61 : k < 61
              · · have hn : n = 0 + 60 := by omega
                  subst hn
                  exact solve_concrete 60 177 (by decide) (by rfl)
              · · have hn : n = 0 + 61 := by omega
                  subst hn
                  exact solve_concrete 61 494 (by decide) (by rfl)
            · · have hn : n = 0 + 62 := by omega
                subst hn
                exact solve_concrete 62 135 (by decide) (by rfl)
      · by_cases h_tree_k_69 : k < 69
        · by_cases h_tree_k_66 : k < 66
          · by_cases h_tree_k_65 : k < 65
            · by_cases h_tree_k_64 : k < 64
              · · have hn : n = 0 + 63 := by omega
                  subst hn
                  exact solve_concrete 63 128 (by decide) (by rfl)
              · · have hn : n = 0 + 64 := by omega
                  subst hn
                  exact solve_concrete 64 305 (by decide) (by rfl)
            · · have hn : n = 0 + 65 := by omega
                subst hn
                exact solve_concrete 65 290 (by decide) (by rfl)
          · by_cases h_tree_k_68 : k < 68
            · by_cases h_tree_k_67 : k < 67
              · · have hn : n = 0 + 66 := by omega
                  subst hn
                  exact solve_concrete 66 427 (by decide) (by rfl)
              · · have hn : n = 0 + 67 := by omega
                  subst hn
                  exact solve_concrete 67 260 (by decide) (by rfl)
            · · have hn : n = 0 + 68 := by omega
                subst hn
                exact solve_concrete 68 201 (by decide) (by rfl)
        · by_cases h_tree_k_72 : k < 72
          · by_cases h_tree_k_71 : k < 71
            · by_cases h_tree_k_70 : k < 70
              · · have hn : n = 0 + 69 := by omega
                  subst hn
                  exact solve_concrete 69 310 (by decide) (by rfl)
              · · have hn : n = 0 + 70 := by omega
                  subst hn
                  exact solve_concrete 70 335 (by decide) (by rfl)
            · · have hn : n = 0 + 71 := by omega
                subst hn
                exact solve_concrete 71 216 (by decide) (by rfl)
          · by_cases h_tree_k_74 : k < 74
            · by_cases h_tree_k_73 : k < 73
              · · have hn : n = 0 + 72 := by omega
                  subst hn
                  exact solve_concrete 72 213 (by decide) (by rfl)
              · · have hn : n = 0 + 73 := by omega
                  subst hn
                  exact solve_concrete 73 434 (by decide) (by rfl)
            · · have hn : n = 0 + 74 := by omega
                subst hn
                exact solve_concrete 74 207 (by decide) (by rfl)
    · by_cases h_tree_k_88 : k < 88
      · by_cases h_tree_k_82 : k < 82
        · by_cases h_tree_k_79 : k < 79
          · by_cases h_tree_k_77 : k < 77
            · by_cases h_tree_k_76 : k < 76
              · · have hn : n = 0 + 75 := by omega
                  subst hn
                  exact solve_concrete 75 364 (by decide) (by rfl)
              · · have hn : n = 0 + 76 := by omega
                  subst hn
                  exact solve_concrete 76 245 (by decide) (by rfl)
            · by_cases h_tree_k_78 : k < 78
              · · have hn : n = 0 + 77 := by omega
                  subst hn
                  exact solve_concrete 77 638 (by decide) (by rfl)
              · · have hn : n = 0 + 78 := by omega
                  subst hn
                  exact solve_concrete 78 511 (by decide) (by rfl)
          · by_cases h_tree_k_81 : k < 81
            · by_cases h_tree_k_80 : k < 80
              · · have hn : n = 0 + 79 := by omega
                  subst hn
                  exact solve_concrete 79 400 (by decide) (by rfl)
              · · have hn : n = 0 + 80 := by omega
                  subst hn
                  exact solve_concrete 80 189 (by decide) (by rfl)
            · · have hn : n = 0 + 81 := by omega
                subst hn
                exact solve_concrete 81 370 (by decide) (by rfl)
        · by_cases h_tree_k_85 : k < 85
          · by_cases h_tree_k_84 : k < 84
            · by_cases h_tree_k_83 : k < 83
              · · have hn : n = 0 + 82 := by omega
                  subst hn
                  exact solve_concrete 82 395 (by decide) (by rfl)
              · · have hn : n = 0 + 83 := by omega
                  subst hn
                  exact solve_concrete 83 340 (by decide) (by rfl)
            · · have hn : n = 0 + 84 := by omega
                subst hn
                exact solve_concrete 84 249 (by decide) (by rfl)
          · by_cases h_tree_k_87 : k < 87
            · by_cases h_tree_k_86 : k < 86
              · · have hn : n = 0 + 85 := by omega
                  subst hn
                  exact solve_concrete 85 518 (by decide) (by rfl)
              · · have hn : n = 0 + 86 := by omega
                  subst hn
                  exact solve_concrete 86 415 (by decide) (by rfl)
            · · have hn : n = 0 + 87 := by omega
                subst hn
                exact solve_concrete 87 280 (by decide) (by rfl)
      · by_cases h_tree_k_94 : k < 94
        · by_cases h_tree_k_91 : k < 91
          · by_cases h_tree_k_90 : k < 90
            · by_cases h_tree_k_89 : k < 89
              · · have hn : n = 0 + 88 := by omega
                  subst hn
                  exact solve_concrete 88 581 (by decide) (by rfl)
              · · have hn : n = 0 + 89 := by omega
                  subst hn
                  exact solve_concrete 89 410 (by decide) (by rfl)
            · · have hn : n = 0 + 90 := by omega
                subst hn
                exact solve_concrete 90 267 (by decide) (by rfl)
          · by_cases h_tree_k_93 : k < 93
            · by_cases h_tree_k_92 : k < 92
              · · have hn : n = 0 + 91 := by omega
                  subst hn
                  exact solve_concrete 91 380 (by decide) (by rfl)
              · · have hn : n = 0 + 92 := by omega
                  subst hn
                  exact solve_concrete 92 261 (by decide) (by rfl)
            · · have hn : n = 0 + 93 := by omega
                subst hn
                exact solve_concrete 93 430 (by decide) (by rfl)
        · by_cases h_tree_k_97 : k < 97
          · by_cases h_tree_k_96 : k < 96
            · by_cases h_tree_k_95 : k < 95
              · · have hn : n = 0 + 94 := by omega
                  subst hn
                  exact solve_concrete 94 623 (by decide) (by rfl)
              · · have hn : n = 0 + 95 := by omega
                  subst hn
                  exact solve_concrete 95 288 (by decide) (by rfl)
            · · have hn : n = 0 + 96 := by omega
                subst hn
                exact solve_concrete 96 1501 (by decide) (by rfl)
          · by_cases h_tree_k_99 : k < 99
            · by_cases h_tree_k_98 : k < 98
              · · have hn : n = 0 + 97 := by omega
                  subst hn
                  exact solve_concrete 97 602 (by decide) (by rfl)
              · · have hn : n = 0 + 98 := by omega
                  subst hn
                  exact solve_concrete 98 279 (by decide) (by rfl)
            · · have hn : n = 0 + 99 := by omega
                subst hn
                exact solve_concrete 99 500 (by decide) (by rfl)



lemma solve_interval_100_199 (n : ℕ) (h1 : n ≥ 100) (h2 : n < 200) : A268597 n > 0 := by
  have h : n - 100 < 100 := by omega
  generalize h_k : n - 100 = k
  rw [h_k] at h
  by_cases h_tree_k_50 : k < 50
  · by_cases h_tree_k_25 : k < 25
    · by_cases h_tree_k_13 : k < 13
      · by_cases h_tree_k_7 : k < 7
        · by_cases h_tree_k_4 : k < 4
          · by_cases h_tree_k_2 : k < 2
            · by_cases h_tree_k_1 : k < 1
              · · have hn : n = 100 + 0 := by omega
                  subst hn
                  exact solve_concrete 100 485 (by decide) (by rfl)
              · · have hn : n = 100 + 1 := by omega
                  subst hn
                  exact solve_concrete 101 462 (by decide) (by rfl)
            · by_cases h_tree_k_3 : k < 3
              · · have hn : n = 100 + 2 := by omega
                  subst hn
                  exact solve_concrete 102 303 (by decide) (by rfl)
              · · have hn : n = 100 + 3 := by omega
                  subst hn
                  exact solve_concrete 103 1352 (by decide) (by rfl)
          · by_cases h_tree_k_6 : k < 6
            · by_cases h_tree_k_5 : k < 5
              · · have hn : n = 100 + 4 := by omega
                  subst hn
                  exact solve_concrete 104 225 (by decide) (by rfl)
              · · have hn : n = 100 + 5 := by omega
                  subst hn
                  exact solve_concrete 105 658 (by decide) (by rfl)
            · · have hn : n = 100 + 6 := by omega
                subst hn
                exact solve_concrete 106 515 (by decide) (by rfl)
        · by_cases h_tree_k_10 : k < 10
          · by_cases h_tree_k_9 : k < 9
            · by_cases h_tree_k_8 : k < 8
              · · have hn : n = 100 + 7 := by omega
                  subst hn
                  exact solve_concrete 107 324 (by decide) (by rfl)
              · · have hn : n = 100 + 8 := by omega
                  subst hn
                  exact solve_concrete 108 321 (by decide) (by rfl)
            · · have hn : n = 100 + 9 := by omega
                subst hn
                exact solve_concrete 109 350 (by decide) (by rfl)
          · by_cases h_tree_k_12 : k < 12
            · by_cases h_tree_k_11 : k < 11
              · · have hn : n = 100 + 10 := by omega
                  subst hn
                  exact solve_concrete 110 231 (by decide) (by rfl)
              · · have hn : n = 100 + 11 := by omega
                  subst hn
                  exact solve_concrete 111 784 (by decide) (by rfl)
            · · have hn : n = 100 + 12 := by omega
                subst hn
                exact solve_concrete 112 545 (by decide) (by rfl)
      · by_cases h_tree_k_19 : k < 19
        · by_cases h_tree_k_16 : k < 16
          · by_cases h_tree_k_15 : k < 15
            · by_cases h_tree_k_14 : k < 14
              · · have hn : n = 100 + 13 := by omega
                  subst hn
                  exact solve_concrete 113 530 (by decide) (by rfl)
              · · have hn : n = 100 + 14 := by omega
                  subst hn
                  exact solve_concrete 114 339 (by decide) (by rfl)
            · · have hn : n = 100 + 15 := by omega
                subst hn
                exact solve_concrete 115 644 (by decide) (by rfl)
          · by_cases h_tree_k_18 : k < 18
            · by_cases h_tree_k_17 : k < 17
              · · have hn : n = 100 + 16 := by omega
                  subst hn
                  exact solve_concrete 116 297 (by decide) (by rfl)
              · · have hn : n = 100 + 17 := by omega
                  subst hn
                  exact solve_concrete 117 742 (by decide) (by rfl)
            · · have hn : n = 100 + 18 := by omega
                subst hn
                exact solve_concrete 118 539 (by decide) (by rfl)
        · by_cases h_tree_k_22 : k < 22
          · by_cases h_tree_k_21 : k < 21
            · by_cases h_tree_k_20 : k < 20
              · · have hn : n = 100 + 19 := by omega
                  subst hn
                  exact solve_concrete 119 440 (by decide) (by rfl)
              · · have hn : n = 100 + 20 := by omega
                  subst hn
                  exact solve_concrete 120 1331 (by decide) (by rfl)
            · · have hn : n = 100 + 21 := by omega
                subst hn
                exact solve_concrete 121 1634 (by decide) (by rfl)
          · by_cases h_tree_k_24 : k < 24
            · by_cases h_tree_k_23 : k < 23
              · · have hn : n = 100 + 22 := by omega
                  subst hn
                  exact solve_concrete 122 1243 (by decide) (by rfl)
              · · have hn : n = 100 + 23 := by omega
                  subst hn
                  exact solve_concrete 123 988 (by decide) (by rfl)
            · · have hn : n = 100 + 24 := by omega
                subst hn
                exact solve_concrete 124 625 (by decide) (by rfl)
    · by_cases h_tree_k_38 : k < 38
      · by_cases h_tree_k_32 : k < 32
        · by_cases h_tree_k_29 : k < 29
          · by_cases h_tree_k_27 : k < 27
            · by_cases h_tree_k_26 : k < 26
              · · have hn : n = 100 + 25 := by omega
                  subst hn
                  exact solve_concrete 125 510 (by decide) (by rfl)
              · · have hn : n = 100 + 26 := by omega
                  subst hn
                  exact solve_concrete 126 255 (by decide) (by rfl)
            · by_cases h_tree_k_28 : k < 28
              · · have hn : n = 100 + 27 := by omega
                  subst hn
                  exact solve_concrete 127 256 (by decide) (by rfl)
              · · have hn : n = 100 + 28 := by omega
                  subst hn
                  exact solve_concrete 128 273 (by decide) (by rfl)
          · by_cases h_tree_k_31 : k < 31
            · by_cases h_tree_k_30 : k < 30
              · · have hn : n = 100 + 29 := by omega
                  subst hn
                  exact solve_concrete 129 610 (by decide) (by rfl)
              · · have hn : n = 100 + 30 := by omega
                  subst hn
                  exact solve_concrete 130 635 (by decide) (by rfl)
            · · have hn : n = 100 + 31 := by omega
                subst hn
                exact solve_concrete 131 580 (by decide) (by rfl)
        · by_cases h_tree_k_35 : k < 35
          · by_cases h_tree_k_34 : k < 34
            · by_cases h_tree_k_33 : k < 33
              · · have hn : n = 100 + 32 := by omega
                  subst hn
                  exact solve_concrete 132 393 (by decide) (by rfl)
              · · have hn : n = 100 + 33 := by omega
                  subst hn
                  exact solve_concrete 133 854 (by decide) (by rfl)
            · · have hn : n = 100 + 34 := by omega
                subst hn
                exact solve_concrete 134 351 (by decide) (by rfl)
          · by_cases h_tree_k_37 : k < 37
            · by_cases h_tree_k_36 : k < 36
              · · have hn : n = 100 + 35 := by omega
                  subst hn
                  exact solve_concrete 135 520 (by decide) (by rfl)
              · · have hn : n = 100 + 36 := by omega
                  subst hn
                  exact solve_concrete 136 917 (by decide) (by rfl)
            · · have hn : n = 100 + 37 := by omega
                subst hn
                exact solve_concrete 137 570 (by decide) (by rfl)
      · by_cases h_tree_k_44 : k < 44
        · by_cases h_tree_k_41 : k < 41
          · by_cases h_tree_k_40 : k < 40
            · by_cases h_tree_k_39 : k < 39
              · · have hn : n = 100 + 38 := by omega
                  subst hn
                  exact solve_concrete 138 411 (by decide) (by rfl)
              · · have hn : n = 100 + 39 := by omega
                  subst hn
                  exact solve_concrete 139 620 (by decide) (by rfl)
            · · have hn : n = 100 + 40 := by omega
                subst hn
                exact solve_concrete 140 285 (by decide) (by rfl)
          · by_cases h_tree_k_43 : k < 43
            · by_cases h_tree_k_42 : k < 42
              · · have hn : n = 100 + 41 := by omega
                  subst hn
                  exact solve_concrete 141 670 (by decide) (by rfl)
              · · have hn : n = 100 + 42 := by omega
                  subst hn
                  exact solve_concrete 142 363 (by decide) (by rfl)
            · · have hn : n = 100 + 43 := by omega
                subst hn
                exact solve_concrete 143 432 (by decide) (by rfl)
        · by_cases h_tree_k_47 : k < 47
          · by_cases h_tree_k_46 : k < 46
            · by_cases h_tree_k_45 : k < 45
              · · have hn : n = 100 + 44 := by omega
                  subst hn
                  exact solve_concrete 144 385 (by decide) (by rfl)
              · · have hn : n = 100 + 45 := by omega
                  subst hn
                  exact solve_concrete 145 938 (by decide) (by rfl)
            · · have hn : n = 100 + 46 := by omega
                subst hn
                exact solve_concrete 146 423 (by decide) (by rfl)
          · by_cases h_tree_k_49 : k < 49
            · by_cases h_tree_k_48 : k < 48
              · · have hn : n = 100 + 47 := by omega
                  subst hn
                  exact solve_concrete 147 868 (by decide) (by rfl)
              · · have hn : n = 100 + 48 := by omega
                  subst hn
                  exact solve_concrete 148 1529 (by decide) (by rfl)
            · · have hn : n = 100 + 49 := by omega
                subst hn
                exact solve_concrete 149 550 (by decide) (by rfl)
  · by_cases h_tree_k_75 : k < 75
    · by_cases h_tree_k_63 : k < 63
      · by_cases h_tree_k_57 : k < 57
        · by_cases h_tree_k_54 : k < 54
          · by_cases h_tree_k_52 : k < 52
            · by_cases h_tree_k_51 : k < 51
              · · have hn : n = 100 + 50 := by omega
                  subst hn
                  exact solve_concrete 150 447 (by decide) (by rfl)
              · · have hn : n = 100 + 51 := by omega
                  subst hn
                  exact solve_concrete 151 728 (by decide) (by rfl)
            · by_cases h_tree_k_53 : k < 53
              · · have hn : n = 100 + 52 := by omega
                  subst hn
                  exact solve_concrete 152 453 (by decide) (by rfl)
              · · have hn : n = 100 + 53 := by omega
                  subst hn
                  exact solve_concrete 153 490 (by decide) (by rfl)
          · by_cases h_tree_k_56 : k < 56
            · by_cases h_tree_k_55 : k < 55
              · · have hn : n = 100 + 54 := by omega
                  subst hn
                  exact solve_concrete 154 755 (by decide) (by rfl)
              · · have hn : n = 100 + 55 := by omega
                  subst hn
                  exact solve_concrete 155 1276 (by decide) (by rfl)
            · · have hn : n = 100 + 56 := by omega
                subst hn
                exact solve_concrete 156 1057 (by decide) (by rfl)
        · by_cases h_tree_k_60 : k < 60
          · by_cases h_tree_k_59 : k < 59
            · by_cases h_tree_k_58 : k < 58
              · · have hn : n = 100 + 57 := by omega
                  subst hn
                  exact solve_concrete 157 1022 (by decide) (by rfl)
              · · have hn : n = 100 + 58 := by omega
                  subst hn
                  exact solve_concrete 158 471 (by decide) (by rfl)
            · · have hn : n = 100 + 59 := by omega
                subst hn
                exact solve_concrete 159 800 (by decide) (by rfl)
          · by_cases h_tree_k_62 : k < 62
            · by_cases h_tree_k_61 : k < 61
              · · have hn : n = 100 + 60 := by omega
                  subst hn
                  exact solve_concrete 160 785 (by decide) (by rfl)
              · · have hn : n = 100 + 61 := by omega
                  subst hn
                  exact solve_concrete 161 486 (by decide) (by rfl)
            · · have hn : n = 100 + 62 := by omega
                subst hn
                exact solve_concrete 162 1099 (by decide) (by rfl)
      · by_cases h_tree_k_69 : k < 69
        · by_cases h_tree_k_66 : k < 66
          · by_cases h_tree_k_65 : k < 65
            · by_cases h_tree_k_64 : k < 64
              · · have hn : n = 100 + 63 := by omega
                  subst hn
                  exact solve_concrete 163 740 (by decide) (by rfl)
              · · have hn : n = 100 + 64 := by omega
                  subst hn
                  exact solve_concrete 164 357 (by decide) (by rfl)
            · · have hn : n = 100 + 65 := by omega
                subst hn
                exact solve_concrete 165 790 (by decide) (by rfl)
          · by_cases h_tree_k_68 : k < 68
            · by_cases h_tree_k_67 : k < 67
              · · have hn : n = 100 + 66 := by omega
                  subst hn
                  exact solve_concrete 166 455 (by decide) (by rfl)
              · · have hn : n = 100 + 67 := by omega
                  subst hn
                  exact solve_concrete 167 680 (by decide) (by rfl)
            · · have hn : n = 100 + 68 := by omega
                subst hn
                exact solve_concrete 168 345 (by decide) (by rfl)
        · by_cases h_tree_k_72 : k < 72
          · by_cases h_tree_k_71 : k < 71
            · by_cases h_tree_k_70 : k < 70
              · · have hn : n = 100 + 69 := by omega
                  subst hn
                  exact solve_concrete 169 650 (by decide) (by rfl)
              · · have hn : n = 100 + 70 := by omega
                  subst hn
                  exact solve_concrete 170 459 (by decide) (by rfl)
            · · have hn : n = 100 + 71 := by omega
                subst hn
                exact solve_concrete 171 1036 (by decide) (by rfl)
          · by_cases h_tree_k_74 : k < 74
            · by_cases h_tree_k_73 : k < 73
              · · have hn : n = 100 + 72 := by omega
                  subst hn
                  exact solve_concrete 172 1169 (by decide) (by rfl)
              · · have hn : n = 100 + 73 := by omega
                  subst hn
                  exact solve_concrete 173 830 (by decide) (by rfl)
            · · have hn : n = 100 + 74 := by omega
                subst hn
                exact solve_concrete 174 375 (by decide) (by rfl)
    · by_cases h_tree_k_88 : k < 88
      · by_cases h_tree_k_82 : k < 82
        · by_cases h_tree_k_79 : k < 79
          · by_cases h_tree_k_77 : k < 77
            · by_cases h_tree_k_76 : k < 76
              · · have hn : n = 100 + 75 := by omega
                  subst hn
                  exact solve_concrete 175 560 (by decide) (by rfl)
              · · have hn : n = 100 + 76 := by omega
                  subst hn
                  exact solve_concrete 176 865 (by decide) (by rfl)
            · by_cases h_tree_k_78 : k < 78
              · · have hn : n = 100 + 77 := by omega
                  subst hn
                  exact solve_concrete 177 1162 (by decide) (by rfl)
              · · have hn : n = 100 + 78 := by omega
                  subst hn
                  exact solve_concrete 178 1211 (by decide) (by rfl)
          · by_cases h_tree_k_81 : k < 81
            · by_cases h_tree_k_80 : k < 80
              · · have hn : n = 100 + 79 := by omega
                  subst hn
                  exact solve_concrete 179 820 (by decide) (by rfl)
              · · have hn : n = 100 + 80 := by omega
                  subst hn
                  exact solve_concrete 180 537 (by decide) (by rfl)
            · · have hn : n = 100 + 81 := by omega
                subst hn
                exact solve_concrete 181 2054 (by decide) (by rfl)
        · by_cases h_tree_k_85 : k < 85
          · by_cases h_tree_k_84 : k < 84
            · by_cases h_tree_k_83 : k < 83
              · · have hn : n = 100 + 82 := by omega
                  subst hn
                  exact solve_concrete 182 399 (by decide) (by rfl)
              · · have hn : n = 100 + 83 := by omega
                  subst hn
                  exact solve_concrete 183 760 (by decide) (by rfl)
            · · have hn : n = 100 + 84 := by omega
                subst hn
                exact solve_concrete 184 905 (by decide) (by rfl)
          · by_cases h_tree_k_87 : k < 87
            · by_cases h_tree_k_86 : k < 86
              · · have hn : n = 100 + 85 := by omega
                  subst hn
                  exact solve_concrete 185 890 (by decide) (by rfl)
              · · have hn : n = 100 + 86 := by omega
                  subst hn
                  exact solve_concrete 186 847 (by decide) (by rfl)
            · · have hn : n = 100 + 87 := by omega
                subst hn
                exact solve_concrete 187 860 (by decide) (by rfl)
      · by_cases h_tree_k_94 : k < 94
        · by_cases h_tree_k_91 : k < 91
          · by_cases h_tree_k_90 : k < 90
            · by_cases h_tree_k_89 : k < 89
              · · have hn : n = 100 + 88 := by omega
                  subst hn
                  exact solve_concrete 188 405 (by decide) (by rfl)
              · · have hn : n = 100 + 89 := by omega
                  subst hn
                  exact solve_concrete 189 1246 (by decide) (by rfl)
            · · have hn : n = 100 + 90 := by omega
                subst hn
                exact solve_concrete 190 1991 (by decide) (by rfl)
          · by_cases h_tree_k_93 : k < 93
            · by_cases h_tree_k_92 : k < 92
              · · have hn : n = 100 + 91 := by omega
                  subst hn
                  exact solve_concrete 191 576 (by decide) (by rfl)
              · · have hn : n = 100 + 92 := by omega
                  subst hn
                  exact solve_concrete 192 573 (by decide) (by rfl)
            · · have hn : n = 100 + 93 := by omega
                subst hn
                exact solve_concrete 193 3002 (by decide) (by rfl)
        · by_cases h_tree_k_97 : k < 97
          · by_cases h_tree_k_96 : k < 96
            · by_cases h_tree_k_95 : k < 95
              · · have hn : n = 100 + 94 := by omega
                  subst hn
                  exact solve_concrete 194 507 (by decide) (by rfl)
              · · have hn : n = 100 + 95 := by omega
                  subst hn
                  exact solve_concrete 195 1204 (by decide) (by rfl)
            · · have hn : n = 100 + 96 := by omega
                subst hn
                exact solve_concrete 196 965 (by decide) (by rfl)
          · by_cases h_tree_k_99 : k < 99
            · by_cases h_tree_k_98 : k < 98
              · · have hn : n = 100 + 97 := by omega
                  subst hn
                  exact solve_concrete 197 870 (by decide) (by rfl)
              · · have hn : n = 100 + 98 := by omega
                  subst hn
                  exact solve_concrete 198 591 (by decide) (by rfl)
            · · have hn : n = 100 + 99 := by omega
                subst hn
                exact solve_concrete 199 1000 (by decide) (by rfl)



lemma solve_interval_200_299 (n : ℕ) (h1 : n ≥ 200) (h2 : n < 300) : A268597 n > 0 := by
  have h : n - 200 < 100 := by omega
  generalize h_k : n - 200 = k
  rw [h_k] at h
  by_cases h_tree_k_50 : k < 50
  · by_cases h_tree_k_25 : k < 25
    · by_cases h_tree_k_13 : k < 13
      · by_cases h_tree_k_7 : k < 7
        · by_cases h_tree_k_4 : k < 4
          · by_cases h_tree_k_2 : k < 2
            · by_cases h_tree_k_1 : k < 1
              · · have hn : n = 200 + 0 := by omega
                  subst hn
                  exact solve_concrete 200 597 (by decide) (by rfl)
              · · have hn : n = 200 + 1 := by omega
                  subst hn
                  exact solve_concrete 201 970 (by decide) (by rfl)
            · by_cases h_tree_k_3 : k < 3
              · · have hn : n = 200 + 2 := by omega
                  subst hn
                  exact solve_concrete 202 995 (by decide) (by rfl)
              · · have hn : n = 200 + 3 := by omega
                  subst hn
                  exact solve_concrete 203 924 (by decide) (by rfl)
          · by_cases h_tree_k_6 : k < 6
            · by_cases h_tree_k_5 : k < 5
              · · have hn : n = 200 + 4 := by omega
                  subst hn
                  exact solve_concrete 204 925 (by decide) (by rfl)
              · · have hn : n = 200 + 5 := by omega
                  subst hn
                  exact solve_concrete 205 1358 (by decide) (by rfl)
            · · have hn : n = 200 + 6 := by omega
                subst hn
                exact solve_concrete 206 603 (by decide) (by rfl)
        · by_cases h_tree_k_10 : k < 10
          · by_cases h_tree_k_9 : k < 9
            · by_cases h_tree_k_8 : k < 8
              · · have hn : n = 200 + 7 := by omega
                  subst hn
                  exact solve_concrete 207 2704 (by decide) (by rfl)
              · · have hn : n = 200 + 8 := by omega
                  subst hn
                  exact solve_concrete 208 2189 (by decide) (by rfl)
            · · have hn : n = 200 + 9 := by omega
                subst hn
                exact solve_concrete 209 850 (by decide) (by rfl)
          · by_cases h_tree_k_12 : k < 12
            · by_cases h_tree_k_11 : k < 11
              · · have hn : n = 200 + 10 := by omega
                  subst hn
                  exact solve_concrete 210 435 (by decide) (by rfl)
              · · have hn : n = 200 + 11 := by omega
                  subst hn
                  exact solve_concrete 211 1316 (by decide) (by rfl)
            · · have hn : n = 200 + 12 := by omega
                subst hn
                exact solve_concrete 212 633 (by decide) (by rfl)
      · by_cases h_tree_k_19 : k < 19
        · by_cases h_tree_k_16 : k < 16
          · by_cases h_tree_k_15 : k < 15
            · by_cases h_tree_k_14 : k < 14
              · · have hn : n = 200 + 13 := by omega
                  subst hn
                  exact solve_concrete 213 1030 (by decide) (by rfl)
              · · have hn : n = 200 + 14 := by omega
                  subst hn
                  exact solve_concrete 214 1055 (by decide) (by rfl)
            · · have hn : n = 200 + 15 := by omega
                subst hn
                exact solve_concrete 215 648 (by decide) (by rfl)
          · by_cases h_tree_k_18 : k < 18
            · by_cases h_tree_k_17 : k < 17
              · · have hn : n = 200 + 16 := by omega
                  subst hn
                  exact solve_concrete 216 1477 (by decide) (by rfl)
              · · have hn : n = 200 + 17 := by omega
                  subst hn
                  exact solve_concrete 217 1442 (by decide) (by rfl)
            · · have hn : n = 200 + 18 := by omega
                subst hn
                exact solve_concrete 218 483 (by decide) (by rfl)
        · by_cases h_tree_k_22 : k < 22
          · by_cases h_tree_k_21 : k < 21
            · by_cases h_tree_k_20 : k < 20
              · · have hn : n = 200 + 19 := by omega
                  subst hn
                  exact solve_concrete 219 700 (by decide) (by rfl)
              · · have hn : n = 200 + 20 := by omega
                  subst hn
                  exact solve_concrete 220 845 (by decide) (by rfl)
            · · have hn : n = 200 + 21 := by omega
                subst hn
                exact solve_concrete 221 1070 (by decide) (by rfl)
          · by_cases h_tree_k_24 : k < 24
            · by_cases h_tree_k_23 : k < 23
              · · have hn : n = 200 + 22 := by omega
                  subst hn
                  exact solve_concrete 222 2743 (by decide) (by rfl)
              · · have hn : n = 200 + 23 := by omega
                  subst hn
                  exact solve_concrete 223 1568 (by decide) (by rfl)
            · · have hn : n = 200 + 24 := by omega
                subst hn
                exact solve_concrete 224 465 (by decide) (by rfl)
    · by_cases h_tree_k_38 : k < 38
      · by_cases h_tree_k_32 : k < 32
        · by_cases h_tree_k_29 : k < 29
          · by_cases h_tree_k_27 : k < 27
            · by_cases h_tree_k_26 : k < 26
              · · have hn : n = 200 + 25 := by omega
                  subst hn
                  exact solve_concrete 225 1090 (by decide) (by rfl)
              · · have hn : n = 200 + 26 := by omega
                  subst hn
                  exact solve_concrete 226 1115 (by decide) (by rfl)
            · by_cases h_tree_k_28 : k < 28
              · · have hn : n = 200 + 27 := by omega
                  subst hn
                  exact solve_concrete 227 1060 (by decide) (by rfl)
              · · have hn : n = 200 + 28 := by omega
                  subst hn
                  exact solve_concrete 228 681 (by decide) (by rfl)
          · by_cases h_tree_k_31 : k < 31
            · by_cases h_tree_k_30 : k < 30
              · · have hn : n = 200 + 29 := by omega
                  subst hn
                  exact solve_concrete 229 950 (by decide) (by rfl)
              · · have hn : n = 200 + 30 := by omega
                  subst hn
                  exact solve_concrete 230 687 (by decide) (by rfl)
            · · have hn : n = 200 + 31 := by omega
                subst hn
                exact solve_concrete 231 1288 (by decide) (by rfl)
        · by_cases h_tree_k_35 : k < 35
          · by_cases h_tree_k_34 : k < 34
            · by_cases h_tree_k_33 : k < 33
              · · have hn : n = 200 + 32 := by omega
                  subst hn
                  exact solve_concrete 232 665 (by decide) (by rfl)
              · · have hn : n = 200 + 33 := by omega
                  subst hn
                  exact solve_concrete 233 1130 (by decide) (by rfl)
            · · have hn : n = 200 + 34 := by omega
                subst hn
                exact solve_concrete 234 699 (by decide) (by rfl)
          · by_cases h_tree_k_37 : k < 37
            · by_cases h_tree_k_36 : k < 36
              · · have hn : n = 200 + 35 := by omega
                  subst hn
                  exact solve_concrete 235 1484 (by decide) (by rfl)
              · · have hn : n = 200 + 36 := by omega
                  subst hn
                  exact solve_concrete 236 1165 (by decide) (by rfl)
            · · have hn : n = 200 + 37 := by omega
                subst hn
                exact solve_concrete 237 1078 (by decide) (by rfl)
      · by_cases h_tree_k_44 : k < 44
        · by_cases h_tree_k_41 : k < 41
          · by_cases h_tree_k_40 : k < 40
            · by_cases h_tree_k_39 : k < 39
              · · have hn : n = 200 + 38 := by omega
                  subst hn
                  exact solve_concrete 238 1631 (by decide) (by rfl)
              · · have hn : n = 200 + 39 := by omega
                  subst hn
                  exact solve_concrete 239 880 (by decide) (by rfl)
            · · have hn : n = 200 + 40 := by omega
                subst hn
                exact solve_concrete 240 561 (by decide) (by rfl)
          · by_cases h_tree_k_43 : k < 43
            · by_cases h_tree_k_42 : k < 42
              · · have hn : n = 200 + 41 := by omega
                  subst hn
                  exact solve_concrete 241 2662 (by decide) (by rfl)
              · · have hn : n = 200 + 42 := by omega
                  subst hn
                  exact solve_concrete 242 567 (by decide) (by rfl)
            · · have hn : n = 200 + 43 := by omega
                subst hn
                exact solve_concrete 243 3268 (by decide) (by rfl)
        · by_cases h_tree_k_47 : k < 47
          · by_cases h_tree_k_46 : k < 46
            · by_cases h_tree_k_45 : k < 45
              · · have hn : n = 200 + 44 := by omega
                  subst hn
                  exact solve_concrete 244 1205 (by decide) (by rfl)
              · · have hn : n = 200 + 45 := by omega
                  subst hn
                  exact solve_concrete 245 1110 (by decide) (by rfl)
            · · have hn : n = 200 + 46 := by omega
                subst hn
                exact solve_concrete 246 1183 (by decide) (by rfl)
          · by_cases h_tree_k_49 : k < 49
            · by_cases h_tree_k_48 : k < 48
              · · have hn : n = 200 + 47 := by omega
                  subst hn
                  exact solve_concrete 247 1976 (by decide) (by rfl)
              · · have hn : n = 200 + 48 := by omega
                  subst hn
                  exact solve_concrete 248 1785 (by decide) (by rfl)
            · · have hn : n = 200 + 49 := by omega
                subst hn
                exact solve_concrete 249 1250 (by decide) (by rfl)
  · by_cases h_tree_k_75 : k < 75
    · by_cases h_tree_k_63 : k < 63
      · by_cases h_tree_k_57 : k < 57
        · by_cases h_tree_k_54 : k < 54
          · by_cases h_tree_k_52 : k < 52
            · by_cases h_tree_k_51 : k < 51
              · · have hn : n = 200 + 50 := by omega
                  subst hn
                  exact solve_concrete 250 2651 (by decide) (by rfl)
              · · have hn : n = 200 + 51 := by omega
                  subst hn
                  exact solve_concrete 251 1020 (by decide) (by rfl)
            · by_cases h_tree_k_53 : k < 53
              · · have hn : n = 200 + 52 := by omega
                  subst hn
                  exact solve_concrete 252 753 (by decide) (by rfl)
              · · have hn : n = 200 + 53 := by omega
                  subst hn
                  exact solve_concrete 253 4142 (by decide) (by rfl)
          · by_cases h_tree_k_56 : k < 56
            · by_cases h_tree_k_55 : k < 55
              · · have hn : n = 200 + 54 := by omega
                  subst hn
                  exact solve_concrete 254 747 (by decide) (by rfl)
              · · have hn : n = 200 + 55 := by omega
                  subst hn
                  exact solve_concrete 255 512 (by decide) (by rfl)
            · · have hn : n = 200 + 56 := by omega
                subst hn
                exact solve_concrete 256 1757 (by decide) (by rfl)
        · by_cases h_tree_k_60 : k < 60
          · by_cases h_tree_k_59 : k < 59
            · by_cases h_tree_k_58 : k < 58
              · · have hn : n = 200 + 57 := by omega
                  subst hn
                  exact solve_concrete 257 1554 (by decide) (by rfl)
              · · have hn : n = 200 + 58 := by omega
                  subst hn
                  exact solve_concrete 258 771 (by decide) (by rfl)
            · · have hn : n = 200 + 59 := by omega
                subst hn
                exact solve_concrete 259 1220 (by decide) (by rfl)
          · by_cases h_tree_k_62 : k < 62
            · by_cases h_tree_k_61 : k < 61
              · · have hn : n = 200 + 60 := by omega
                  subst hn
                  exact solve_concrete 260 1285 (by decide) (by rfl)
              · · have hn : n = 200 + 61 := by omega
                  subst hn
                  exact solve_concrete 261 1270 (by decide) (by rfl)
            · · have hn : n = 200 + 62 := by omega
                subst hn
                exact solve_concrete 262 1799 (by decide) (by rfl)
      · by_cases h_tree_k_69 : k < 69
        · by_cases h_tree_k_66 : k < 66
          · by_cases h_tree_k_65 : k < 65
            · by_cases h_tree_k_64 : k < 64
              · · have hn : n = 200 + 63 := by omega
                  subst hn
                  exact solve_concrete 263 1160 (by decide) (by rfl)
              · · have hn : n = 200 + 64 := by omega
                  subst hn
                  exact solve_concrete 264 789 (by decide) (by rfl)
            · · have hn : n = 200 + 65 := by omega
                subst hn
                exact solve_concrete 265 1274 (by decide) (by rfl)
          · by_cases h_tree_k_68 : k < 68
            · by_cases h_tree_k_67 : k < 67
              · · have hn : n = 200 + 66 := by omega
                  subst hn
                  exact solve_concrete 266 555 (by decide) (by rfl)
              · · have hn : n = 200 + 67 := by omega
                  subst hn
                  exact solve_concrete 267 1708 (by decide) (by rfl)
            · · have hn : n = 200 + 68 := by omega
                subst hn
                exact solve_concrete 268 1841 (by decide) (by rfl)
        · by_cases h_tree_k_72 : k < 72
          · by_cases h_tree_k_71 : k < 71
            · by_cases h_tree_k_70 : k < 70
              · · have hn : n = 200 + 69 := by omega
                  subst hn
                  exact solve_concrete 269 1150 (by decide) (by rfl)
              · · have hn : n = 200 + 70 := by omega
                  subst hn
                  exact solve_concrete 270 807 (by decide) (by rfl)
            · · have hn : n = 200 + 71 := by omega
                subst hn
                exact solve_concrete 271 1040 (by decide) (by rfl)
          · by_cases h_tree_k_74 : k < 74
            · by_cases h_tree_k_73 : k < 73
              · · have hn : n = 200 + 72 := by omega
                  subst hn
                  exact solve_concrete 272 609 (by decide) (by rfl)
              · · have hn : n = 200 + 73 := by omega
                  subst hn
                  exact solve_concrete 273 1834 (by decide) (by rfl)
            · · have hn : n = 200 + 74 := by omega
                subst hn
                exact solve_concrete 274 875 (by decide) (by rfl)
    · by_cases h_tree_k_88 : k < 88
      · by_cases h_tree_k_82 : k < 82
        · by_cases h_tree_k_79 : k < 79
          · by_cases h_tree_k_77 : k < 77
            · by_cases h_tree_k_76 : k < 76
              · · have hn : n = 200 + 75 := by omega
                  subst hn
                  exact solve_concrete 275 1140 (by decide) (by rfl)
              · · have hn : n = 200 + 76 := by omega
                  subst hn
                  exact solve_concrete 276 805 (by decide) (by rfl)
            · by_cases h_tree_k_78 : k < 78
              · · have hn : n = 200 + 77 := by omega
                  subst hn
                  exact solve_concrete 277 3302 (by decide) (by rfl)
              · · have hn : n = 200 + 78 := by omega
                  subst hn
                  exact solve_concrete 278 663 (by decide) (by rfl)
          · by_cases h_tree_k_81 : k < 81
            · by_cases h_tree_k_80 : k < 80
              · · have hn : n = 200 + 79 := by omega
                  subst hn
                  exact solve_concrete 279 1240 (by decide) (by rfl)
              · · have hn : n = 200 + 80 := by omega
                  subst hn
                  exact solve_concrete 280 1001 (by decide) (by rfl)
            · · have hn : n = 200 + 81 := by omega
                subst hn
                exact solve_concrete 281 1290 (by decide) (by rfl)
        · by_cases h_tree_k_85 : k < 85
          · by_cases h_tree_k_84 : k < 84
            · by_cases h_tree_k_83 : k < 83
              · · have hn : n = 200 + 82 := by omega
                  subst hn
                  exact solve_concrete 282 843 (by decide) (by rfl)
              · · have hn : n = 200 + 83 := by omega
                  subst hn
                  exact solve_concrete 283 1340 (by decide) (by rfl)
            · · have hn : n = 200 + 84 := by omega
                subst hn
                exact solve_concrete 284 849 (by decide) (by rfl)
          · by_cases h_tree_k_87 : k < 87
            · by_cases h_tree_k_86 : k < 86
              · · have hn : n = 200 + 85 := by omega
                  subst hn
                  exact solve_concrete 285 1390 (by decide) (by rfl)
              · · have hn : n = 200 + 86 := by omega
                  subst hn
                  exact solve_concrete 286 1415 (by decide) (by rfl)
            · · have hn : n = 200 + 87 := by omega
                subst hn
                exact solve_concrete 287 864 (by decide) (by rfl)
      · by_cases h_tree_k_94 : k < 94
        · by_cases h_tree_k_91 : k < 91
          · by_cases h_tree_k_90 : k < 90
            · by_cases h_tree_k_89 : k < 89
              · · have hn : n = 200 + 88 := by omega
                  subst hn
                  exact solve_concrete 288 1981 (by decide) (by rfl)
              · · have hn : n = 200 + 89 := by omega
                  subst hn
                  exact solve_concrete 289 1946 (by decide) (by rfl)
            · · have hn : n = 200 + 90 := by omega
                subst hn
                exact solve_concrete 290 651 (by decide) (by rfl)
          · by_cases h_tree_k_93 : k < 93
            · by_cases h_tree_k_92 : k < 92
              · · have hn : n = 200 + 91 := by omega
                  subst hn
                  exact solve_concrete 291 1876 (by decide) (by rfl)
              · · have hn : n = 200 + 92 := by omega
                  subst hn
                  exact solve_concrete 292 3113 (by decide) (by rfl)
            · · have hn : n = 200 + 93 := by omega
                subst hn
                exact solve_concrete 293 1806 (by decide) (by rfl)
        · by_cases h_tree_k_97 : k < 97
          · by_cases h_tree_k_96 : k < 96
            · by_cases h_tree_k_95 : k < 95
              · · have hn : n = 200 + 94 := by omega
                  subst hn
                  exact solve_concrete 294 615 (by decide) (by rfl)
              · · have hn : n = 200 + 95 := by omega
                  subst hn
                  exact solve_concrete 295 1736 (by decide) (by rfl)
            · · have hn : n = 200 + 96 := by omega
                subst hn
                exact solve_concrete 296 837 (by decide) (by rfl)
          · by_cases h_tree_k_99 : k < 99
            · by_cases h_tree_k_98 : k < 98
              · · have hn : n = 200 + 97 := by omega
                  subst hn
                  exact solve_concrete 297 3058 (by decide) (by rfl)
              · · have hn : n = 200 + 98 := by omega
                  subst hn
                  exact solve_concrete 298 1859 (by decide) (by rfl)
            · · have hn : n = 200 + 99 := by omega
                subst hn
                exact solve_concrete 299 1100 (by decide) (by rfl)



lemma solve_interval_300_399 (n : ℕ) (h1 : n ≥ 300) (h2 : n < 400) : A268597 n > 0 := by
  have h : n - 300 < 100 := by omega
  generalize h_k : n - 300 = k
  rw [h_k] at h
  by_cases h_tree_k_50 : k < 50
  · by_cases h_tree_k_25 : k < 25
    · by_cases h_tree_k_13 : k < 13
      · by_cases h_tree_k_7 : k < 7
        · by_cases h_tree_k_4 : k < 4
          · by_cases h_tree_k_2 : k < 2
            · by_cases h_tree_k_1 : k < 1
              · · have hn : n = 300 + 0 := by omega
                  subst hn
                  exact solve_concrete 300 1813 (by decide) (by rfl)
              · · have hn : n = 300 + 1 := by omega
                  subst hn
                  exact solve_concrete 301 3614 (by decide) (by rfl)
            · by_cases h_tree_k_3 : k < 3
              · · have hn : n = 300 + 2 := by omega
                  subst hn
                  exact solve_concrete 302 2415 (by decide) (by rfl)
              · · have hn : n = 300 + 3 := by omega
                  subst hn
                  exact solve_concrete 303 1456 (by decide) (by rfl)
          · by_cases h_tree_k_6 : k < 6
            · by_cases h_tree_k_5 : k < 5
              · · have hn : n = 300 + 4 := by omega
                  subst hn
                  exact solve_concrete 304 3809 (by decide) (by rfl)
              · · have hn : n = 300 + 5 := by omega
                  subst hn
                  exact solve_concrete 305 1386 (by decide) (by rfl)
            · · have hn : n = 300 + 6 := by omega
                subst hn
                exact solve_concrete 306 8587 (by decide) (by rfl)
        · by_cases h_tree_k_10 : k < 10
          · by_cases h_tree_k_9 : k < 9
            · by_cases h_tree_k_8 : k < 8
              · · have hn : n = 300 + 7 := by omega
                  subst hn
                  exact solve_concrete 307 980 (by decide) (by rfl)
              · · have hn : n = 300 + 8 := by omega
                  subst hn
                  exact solve_concrete 308 645 (by decide) (by rfl)
            · · have hn : n = 300 + 9 := by omega
                subst hn
                exact solve_concrete 309 1510 (by decide) (by rfl)
          · by_cases h_tree_k_12 : k < 12
            · by_cases h_tree_k_11 : k < 11
              · · have hn : n = 300 + 10 := by omega
                  subst hn
                  exact solve_concrete 310 1535 (by decide) (by rfl)
              · · have hn : n = 300 + 11 := by omega
                  subst hn
                  exact solve_concrete 311 2552 (by decide) (by rfl)
            · · have hn : n = 300 + 12 := by omega
                subst hn
                exact solve_concrete 312 933 (by decide) (by rfl)
      · by_cases h_tree_k_19 : k < 19
        · by_cases h_tree_k_16 : k < 16
          · by_cases h_tree_k_15 : k < 15
            · by_cases h_tree_k_14 : k < 14
              · · have hn : n = 300 + 13 := by omega
                  subst hn
                  exact solve_concrete 313 2114 (by decide) (by rfl)
              · · have hn : n = 300 + 14 := by omega
                  subst hn
                  exact solve_concrete 314 675 (by decide) (by rfl)
            · · have hn : n = 300 + 15 := by omega
                subst hn
                exact solve_concrete 315 2044 (by decide) (by rfl)
          · by_cases h_tree_k_18 : k < 18
            · by_cases h_tree_k_17 : k < 17
              · · have hn : n = 300 + 16 := by omega
                  subst hn
                  exact solve_concrete 316 1565 (by decide) (by rfl)
              · · have hn : n = 300 + 17 := by omega
                  subst hn
                  exact solve_concrete 317 1974 (by decide) (by rfl)
            · · have hn : n = 300 + 18 := by omega
                subst hn
                exact solve_concrete 318 759 (by decide) (by rfl)
        · by_cases h_tree_k_22 : k < 22
          · by_cases h_tree_k_21 : k < 21
            · by_cases h_tree_k_20 : k < 20
              · · have hn : n = 300 + 19 := by omega
                  subst hn
                  exact solve_concrete 319 1600 (by decide) (by rfl)
              · · have hn : n = 300 + 20 := by omega
                  subst hn
                  exact solve_concrete 320 1585 (by decide) (by rfl)
            · · have hn : n = 300 + 21 := by omega
                subst hn
                exact solve_concrete 321 1570 (by decide) (by rfl)
          · by_cases h_tree_k_24 : k < 24
            · by_cases h_tree_k_23 : k < 23
              · · have hn : n = 300 + 22 := by omega
                  subst hn
                  exact solve_concrete 322 867 (by decide) (by rfl)
              · · have hn : n = 300 + 23 := by omega
                  subst hn
                  exact solve_concrete 323 972 (by decide) (by rfl)
            · · have hn : n = 300 + 24 := by omega
                subst hn
                exact solve_concrete 324 1045 (by decide) (by rfl)
    · by_cases h_tree_k_38 : k < 38
      · by_cases h_tree_k_32 : k < 32
        · by_cases h_tree_k_29 : k < 29
          · by_cases h_tree_k_27 : k < 27
            · by_cases h_tree_k_26 : k < 26
              · · have hn : n = 300 + 25 := by omega
                  subst hn
                  exact solve_concrete 325 2198 (by decide) (by rfl)
              · · have hn : n = 300 + 26 := by omega
                  subst hn
                  exact solve_concrete 326 963 (by decide) (by rfl)
            · by_cases h_tree_k_28 : k < 28
              · · have hn : n = 300 + 27 := by omega
                  subst hn
                  exact solve_concrete 327 1480 (by decide) (by rfl)
              · · have hn : n = 300 + 28 := by omega
                  subst hn
                  exact solve_concrete 328 2009 (by decide) (by rfl)
          · by_cases h_tree_k_31 : k < 31
            · by_cases h_tree_k_30 : k < 30
              · · have hn : n = 300 + 29 := by omega
                  subst hn
                  exact solve_concrete 329 1210 (by decide) (by rfl)
              · · have hn : n = 300 + 30 := by omega
                  subst hn
                  exact solve_concrete 330 5947 (by decide) (by rfl)
            · · have hn : n = 300 + 31 := by omega
                subst hn
                exact solve_concrete 331 1580 (by decide) (by rfl)
        · by_cases h_tree_k_35 : k < 35
          · by_cases h_tree_k_34 : k < 34
            · by_cases h_tree_k_33 : k < 33
              · · have hn : n = 300 + 32 := by omega
                  subst hn
                  exact solve_concrete 332 693 (by decide) (by rfl)
              · · have hn : n = 300 + 33 := by omega
                  subst hn
                  exact solve_concrete 333 1630 (by decide) (by rfl)
            · · have hn : n = 300 + 34 := by omega
                subst hn
                exact solve_concrete 334 1655 (by decide) (by rfl)
          · by_cases h_tree_k_37 : k < 37
            · by_cases h_tree_k_36 : k < 36
              · · have hn : n = 300 + 35 := by omega
                  subst hn
                  exact solve_concrete 335 1360 (by decide) (by rfl)
              · · have hn : n = 300 + 36 := by omega
                  subst hn
                  exact solve_concrete 336 705 (by decide) (by rfl)
            · · have hn : n = 300 + 37 := by omega
                subst hn
                exact solve_concrete 337 2282 (by decide) (by rfl)
      · by_cases h_tree_k_44 : k < 44
        · by_cases h_tree_k_41 : k < 41
          · by_cases h_tree_k_40 : k < 40
            · by_cases h_tree_k_39 : k < 39
              · · have hn : n = 300 + 38 := by omega
                  subst hn
                  exact solve_concrete 338 1011 (by decide) (by rfl)
              · · have hn : n = 300 + 39 := by omega
                  subst hn
                  exact solve_concrete 339 1300 (by decide) (by rfl)
            · · have hn : n = 300 + 40 := by omega
                subst hn
                exact solve_concrete 340 1685 (by decide) (by rfl)
          · by_cases h_tree_k_43 : k < 43
            · by_cases h_tree_k_42 : k < 42
              · · have hn : n = 300 + 41 := by omega
                  subst hn
                  exact solve_concrete 341 1590 (by decide) (by rfl)
              · · have hn : n = 300 + 42 := by omega
                  subst hn
                  exact solve_concrete 342 1015 (by decide) (by rfl)
            · · have hn : n = 300 + 43 := by omega
                subst hn
                exact solve_concrete 343 2072 (by decide) (by rfl)
        · by_cases h_tree_k_47 : k < 47
          · by_cases h_tree_k_46 : k < 46
            · by_cases h_tree_k_45 : k < 45
              · · have hn : n = 300 + 44 := by omega
                  subst hn
                  exact solve_concrete 344 777 (by decide) (by rfl)
              · · have hn : n = 300 + 45 := by omega
                  subst hn
                  exact solve_concrete 345 2338 (by decide) (by rfl)
            · · have hn : n = 300 + 46 := by omega
                subst hn
                exact solve_concrete 346 3707 (by decide) (by rfl)
          · by_cases h_tree_k_49 : k < 49
            · by_cases h_tree_k_48 : k < 48
              · · have hn : n = 300 + 47 := by omega
                  subst hn
                  exact solve_concrete 347 1660 (by decide) (by rfl)
              · · have hn : n = 300 + 48 := by omega
                  subst hn
                  exact solve_concrete 348 1041 (by decide) (by rfl)
            · · have hn : n = 300 + 49 := by omega
                subst hn
                exact solve_concrete 349 1550 (by decide) (by rfl)
  · by_cases h_tree_k_75 : k < 75
    · by_cases h_tree_k_63 : k < 63
      · by_cases h_tree_k_57 : k < 57
        · by_cases h_tree_k_54 : k < 54
          · by_cases h_tree_k_52 : k < 52
            · by_cases h_tree_k_51 : k < 51
              · · have hn : n = 300 + 50 := by omega
                  subst hn
                  exact solve_concrete 350 891 (by decide) (by rfl)
              · · have hn : n = 300 + 51 := by omega
                  subst hn
                  exact solve_concrete 351 1120 (by decide) (by rfl)
            · by_cases h_tree_k_53 : k < 53
              · · have hn : n = 300 + 52 := by omega
                  subst hn
                  exact solve_concrete 352 1745 (by decide) (by rfl)
              · · have hn : n = 300 + 53 := by omega
                  subst hn
                  exact solve_concrete 353 1730 (by decide) (by rfl)
          · by_cases h_tree_k_56 : k < 56
            · by_cases h_tree_k_55 : k < 55
              · · have hn : n = 300 + 54 := by omega
                  subst hn
                  exact solve_concrete 354 1059 (by decide) (by rfl)
              · · have hn : n = 300 + 55 := by omega
                  subst hn
                  exact solve_concrete 355 2324 (by decide) (by rfl)
            · · have hn : n = 300 + 56 := by omega
                subst hn
                exact solve_concrete 356 1445 (by decide) (by rfl)
        · by_cases h_tree_k_60 : k < 60
          · by_cases h_tree_k_59 : k < 59
            · by_cases h_tree_k_58 : k < 58
              · · have hn : n = 300 + 57 := by omega
                  subst hn
                  exact solve_concrete 357 2422 (by decide) (by rfl)
              · · have hn : n = 300 + 58 := by omega
                  subst hn
                  exact solve_concrete 358 2471 (by decide) (by rfl)
            · · have hn : n = 300 + 59 := by omega
                subst hn
                exact solve_concrete 359 1640 (by decide) (by rfl)
          · by_cases h_tree_k_62 : k < 62
            · by_cases h_tree_k_61 : k < 61
              · · have hn : n = 300 + 60 := by omega
                  subst hn
                  exact solve_concrete 360 1077 (by decide) (by rfl)
              · · have hn : n = 300 + 61 := by omega
                  subst hn
                  exact solve_concrete 361 6194 (by decide) (by rfl)
            · · have hn : n = 300 + 62 := by omega
                subst hn
                exact solve_concrete 362 1795 (by decide) (by rfl)
      · by_cases h_tree_k_69 : k < 69
        · by_cases h_tree_k_66 : k < 66
          · by_cases h_tree_k_65 : k < 65
            · by_cases h_tree_k_64 : k < 64
              · · have hn : n = 300 + 63 := by omega
                  subst hn
                  exact solve_concrete 363 4108 (by decide) (by rfl)
              · · have hn : n = 300 + 64 := by omega
                  subst hn
                  exact solve_concrete 364 1085 (by decide) (by rfl)
            · · have hn : n = 300 + 65 := by omega
                subst hn
                exact solve_concrete 365 1790 (by decide) (by rfl)
          · by_cases h_tree_k_68 : k < 68
            · by_cases h_tree_k_67 : k < 67
              · · have hn : n = 300 + 66 := by omega
                  subst hn
                  exact solve_concrete 366 6631 (by decide) (by rfl)
              · · have hn : n = 300 + 67 := by omega
                  subst hn
                  exact solve_concrete 367 1520 (by decide) (by rfl)
            · · have hn : n = 300 + 68 := by omega
                subst hn
                exact solve_concrete 368 897 (by decide) (by rfl)
        · by_cases h_tree_k_72 : k < 72
          · by_cases h_tree_k_71 : k < 71
            · by_cases h_tree_k_70 : k < 70
              · · have hn : n = 300 + 69 := by omega
                  subst hn
                  exact solve_concrete 369 1810 (by decide) (by rfl)
              · · have hn : n = 300 + 70 := by omega
                  subst hn
                  exact solve_concrete 370 1235 (by decide) (by rfl)
            · · have hn : n = 300 + 71 := by omega
                subst hn
                exact solve_concrete 371 1780 (by decide) (by rfl)
          · by_cases h_tree_k_74 : k < 74
            · by_cases h_tree_k_73 : k < 73
              · · have hn : n = 300 + 72 := by omega
                  subst hn
                  exact solve_concrete 372 2569 (by decide) (by rfl)
              · · have hn : n = 300 + 73 := by omega
                  subst hn
                  exact solve_concrete 373 1694 (by decide) (by rfl)
            · · have hn : n = 300 + 74 := by omega
                subst hn
                exact solve_concrete 374 1119 (by decide) (by rfl)
    · by_cases h_tree_k_88 : k < 88
      · by_cases h_tree_k_82 : k < 82
        · by_cases h_tree_k_79 : k < 79
          · by_cases h_tree_k_77 : k < 77
            · by_cases h_tree_k_76 : k < 76
              · · have hn : n = 300 + 75 := by omega
                  subst hn
                  exact solve_concrete 375 1720 (by decide) (by rfl)
              · · have hn : n = 300 + 76 := by omega
                  subst hn
                  exact solve_concrete 376 1865 (by decide) (by rfl)
            · by_cases h_tree_k_78 : k < 78
              · · have hn : n = 300 + 77 := by omega
                  subst hn
                  exact solve_concrete 377 1530 (by decide) (by rfl)
              · · have hn : n = 300 + 78 := by omega
                  subst hn
                  exact solve_concrete 378 795 (by decide) (by rfl)
          · by_cases h_tree_k_81 : k < 81
            · by_cases h_tree_k_80 : k < 80
              · · have hn : n = 300 + 79 := by omega
                  subst hn
                  exact solve_concrete 379 2492 (by decide) (by rfl)
              · · have hn : n = 300 + 80 := by omega
                  subst hn
                  exact solve_concrete 380 765 (by decide) (by rfl)
            · · have hn : n = 300 + 81 := by omega
                subst hn
                exact solve_concrete 381 3982 (by decide) (by rfl)
        · by_cases h_tree_k_85 : k < 85
          · by_cases h_tree_k_84 : k < 84
            · by_cases h_tree_k_83 : k < 83
              · · have hn : n = 300 + 82 := by omega
                  subst hn
                  exact solve_concrete 382 1463 (by decide) (by rfl)
              · · have hn : n = 300 + 83 := by omega
                  subst hn
                  exact solve_concrete 383 1152 (by decide) (by rfl)
            · · have hn : n = 300 + 84 := by omega
                subst hn
                exact solve_concrete 384 1149 (by decide) (by rfl)
          · by_cases h_tree_k_87 : k < 87
            · by_cases h_tree_k_86 : k < 86
              · · have hn : n = 300 + 85 := by omega
                  subst hn
                  exact solve_concrete 385 4706 (by decide) (by rfl)
              · · have hn : n = 300 + 86 := by omega
                  subst hn
                  exact solve_concrete 386 819 (by decide) (by rfl)
            · · have hn : n = 300 + 87 := by omega
                subst hn
                exact solve_concrete 387 6004 (by decide) (by rfl)
      · by_cases h_tree_k_94 : k < 94
        · by_cases h_tree_k_91 : k < 91
          · by_cases h_tree_k_90 : k < 90
            · by_cases h_tree_k_89 : k < 89
              · · have hn : n = 300 + 88 := by omega
                  subst hn
                  exact solve_concrete 388 2681 (by decide) (by rfl)
              · · have hn : n = 300 + 89 := by omega
                  subst hn
                  exact solve_concrete 389 1830 (by decide) (by rfl)
            · · have hn : n = 300 + 90 := by omega
                subst hn
                exact solve_concrete 390 1167 (by decide) (by rfl)
          · by_cases h_tree_k_93 : k < 93
            · by_cases h_tree_k_92 : k < 92
              · · have hn : n = 300 + 91 := by omega
                  subst hn
                  exact solve_concrete 391 2408 (by decide) (by rfl)
              · · have hn : n = 300 + 92 := by omega
                  subst hn
                  exact solve_concrete 392 969 (by decide) (by rfl)
            · · have hn : n = 300 + 93 := by omega
                subst hn
                exact solve_concrete 393 1930 (by decide) (by rfl)
        · by_cases h_tree_k_97 : k < 97
          · by_cases h_tree_k_96 : k < 96
            · by_cases h_tree_k_95 : k < 95
              · · have hn : n = 300 + 94 := by omega
                  subst hn
                  exact solve_concrete 394 1547 (by decide) (by rfl)
              · · have hn : n = 300 + 95 := by omega
                  subst hn
                  exact solve_concrete 395 1740 (by decide) (by rfl)
            · · have hn : n = 300 + 96 := by omega
                subst hn
                exact solve_concrete 396 957 (by decide) (by rfl)
          · by_cases h_tree_k_99 : k < 99
            · by_cases h_tree_k_98 : k < 98
              · · have hn : n = 300 + 97 := by omega
                  subst hn
                  exact solve_concrete 397 2702 (by decide) (by rfl)
              · · have hn : n = 300 + 98 := by omega
                  subst hn
                  exact solve_concrete 398 903 (by decide) (by rfl)
            · · have hn : n = 300 + 99 := by omega
                subst hn
                exact solve_concrete 399 2000 (by decide) (by rfl)

lemma solve_interval_400_499 (n : ℕ) (h1 : n ≥ 400) (h2 : n < 500) : A268597 n > 0 := by
  have h : n - 400 < 100 := by omega
  generalize h_k : n - 400 = k
  rw [h_k] at h
  by_cases h_tree_k_50 : k < 50
  · by_cases h_tree_k_25 : k < 25
    · by_cases h_tree_k_13 : k < 13
      · by_cases h_tree_k_7 : k < 7
        · by_cases h_tree_k_4 : k < 4
          · by_cases h_tree_k_2 : k < 2
            · by_cases h_tree_k_1 : k < 1
              · · have hn : n = 400 + 0 := by omega
                  subst hn
                  exact solve_concrete 400 1985 (by decide) (by rfl)
              · · have hn : n = 400 + 1 := by omega
                  subst hn
                  exact solve_concrete 401 1970 (by decide) (by rfl)
            · by_cases h_tree_k_3 : k < 3
              · · have hn : n = 400 + 2 := by omega
                  subst hn
                  exact solve_concrete 402 1203 (by decide) (by rfl)
              · · have hn : n = 400 + 3 := by omega
                  subst hn
                  exact solve_concrete 403 1940 (by decide) (by rfl)
          · by_cases h_tree_k_6 : k < 6
            · by_cases h_tree_k_5 : k < 5
              · · have hn : n = 400 + 4 := by omega
                  subst hn
                  exact solve_concrete 404 1053 (by decide) (by rfl)
              · · have hn : n = 400 + 5 := by omega
                  subst hn
                  exact solve_concrete 405 1990 (by decide) (by rfl)
            · · have hn : n = 400 + 6 := by omega
                subst hn
                exact solve_concrete 406 2807 (by decide) (by rfl)
        · by_cases h_tree_k_10 : k < 10
          · by_cases h_tree_k_9 : k < 9
            · by_cases h_tree_k_8 : k < 8
              · · have hn : n = 400 + 7 := by omega
                  subst hn
                  exact solve_concrete 407 1848 (by decide) (by rfl)
              · · have hn : n = 400 + 8 := by omega
                  subst hn
                  exact solve_concrete 408 5161 (by decide) (by rfl)
            · · have hn : n = 400 + 9 := by omega
                subst hn
                exact solve_concrete 409 1850 (by decide) (by rfl)
          · by_cases h_tree_k_12 : k < 12
            · by_cases h_tree_k_11 : k < 11
              · · have hn : n = 400 + 10 := by omega
                  subst hn
                  exact solve_concrete 410 1227 (by decide) (by rfl)
              · · have hn : n = 400 + 11 := by omega
                  subst hn
                  exact solve_concrete 411 2716 (by decide) (by rfl)
            · · have hn : n = 400 + 12 := by omega
                subst hn
                exact solve_concrete 412 2045 (by decide) (by rfl)
      · by_cases h_tree_k_19 : k < 19
        · by_cases h_tree_k_16 : k < 16
          · by_cases h_tree_k_15 : k < 15
            · by_cases h_tree_k_14 : k < 14
              · · have hn : n = 400 + 13 := by omega
                  subst hn
                  exact solve_concrete 413 1710 (by decide) (by rfl)
              · · have hn : n = 400 + 14 := by omega
                  subst hn
                  exact solve_concrete 414 1975 (by decide) (by rfl)
            · · have hn : n = 400 + 15 := by omega
                subst hn
                exact solve_concrete 415 5408 (by decide) (by rfl)
          · by_cases h_tree_k_18 : k < 18
            · by_cases h_tree_k_17 : k < 17
              · · have hn : n = 400 + 16 := by omega
                  subst hn
                  exact solve_concrete 416 1233 (by decide) (by rfl)
              · · have hn : n = 400 + 17 := by omega
                  subst hn
                  exact solve_concrete 417 4378 (by decide) (by rfl)
            · · have hn : n = 400 + 18 := by omega
                subst hn
                exact solve_concrete 418 4499 (by decide) (by rfl)
        · by_cases h_tree_k_22 : k < 22
          · by_cases h_tree_k_21 : k < 21
            · by_cases h_tree_k_20 : k < 20
              · · have hn : n = 400 + 19 := by omega
                  subst hn
                  exact solve_concrete 419 1700 (by decide) (by rfl)
              · · have hn : n = 400 + 20 := by omega
                  subst hn
                  exact solve_concrete 420 885 (by decide) (by rfl)
            · · have hn : n = 400 + 21 := by omega
                subst hn
                exact solve_concrete 421 5174 (by decide) (by rfl)
          · by_cases h_tree_k_24 : k < 24
            · by_cases h_tree_k_23 : k < 23
              · · have hn : n = 400 + 22 := by omega
                  subst hn
                  exact solve_concrete 422 855 (by decide) (by rfl)
              · · have hn : n = 400 + 23 := by omega
                  subst hn
                  exact solve_concrete 423 2632 (by decide) (by rfl)
            · · have hn : n = 400 + 24 := by omega
                subst hn
                exact solve_concrete 424 1625 (by decide) (by rfl)
    · by_cases h_tree_k_38 : k < 38
      · by_cases h_tree_k_32 : k < 32
        · by_cases h_tree_k_29 : k < 29
          · by_cases h_tree_k_27 : k < 27
            · by_cases h_tree_k_26 : k < 26
              · · have hn : n = 400 + 25 := by omega
                  subst hn
                  exact solve_concrete 425 2010 (by decide) (by rfl)
              · · have hn : n = 400 + 26 := by omega
                  subst hn
                  exact solve_concrete 426 2947 (by decide) (by rfl)
            · by_cases h_tree_k_28 : k < 28
              · · have hn : n = 400 + 27 := by omega
                  subst hn
                  exact solve_concrete 427 2060 (by decide) (by rfl)
              · · have hn : n = 400 + 28 := by omega
                  subst hn
                  exact solve_concrete 428 1089 (by decide) (by rfl)
          · by_cases h_tree_k_31 : k < 31
            · by_cases h_tree_k_30 : k < 30
              · · have hn : n = 400 + 29 := by omega
                  subst hn
                  exact solve_concrete 429 2110 (by decide) (by rfl)
              · · have hn : n = 400 + 30 := by omega
                  subst hn
                  exact solve_concrete 430 1295 (by decide) (by rfl)
            · · have hn : n = 400 + 31 := by omega
                subst hn
                exact solve_concrete 431 1296 (by decide) (by rfl)
        · by_cases h_tree_k_35 : k < 35
          · by_cases h_tree_k_34 : k < 34
            · by_cases h_tree_k_33 : k < 33
              · · have hn : n = 400 + 32 := by omega
                  subst hn
                  exact solve_concrete 432 1293 (by decide) (by rfl)
              · · have hn : n = 400 + 33 := by omega
                  subst hn
                  exact solve_concrete 433 2954 (by decide) (by rfl)
            · · have hn : n = 400 + 34 := by omega
                subst hn
                exact solve_concrete 434 915 (by decide) (by rfl)
          · by_cases h_tree_k_37 : k < 37
            · by_cases h_tree_k_36 : k < 36
              · · have hn : n = 400 + 35 := by omega
                  subst hn
                  exact solve_concrete 435 2884 (by decide) (by rfl)
              · · have hn : n = 400 + 36 := by omega
                  subst hn
                  exact solve_concrete 436 1805 (by decide) (by rfl)
            · · have hn : n = 400 + 37 := by omega
                subst hn
                exact solve_concrete 437 2814 (by decide) (by rfl)
      · by_cases h_tree_k_44 : k < 44
        · by_cases h_tree_k_41 : k < 41
          · by_cases h_tree_k_40 : k < 40
            · by_cases h_tree_k_39 : k < 39
              · · have hn : n = 400 + 38 := by omega
                  subst hn
                  exact solve_concrete 438 1495 (by decide) (by rfl)
              · · have hn : n = 400 + 39 := by omega
                  subst hn
                  exact solve_concrete 439 1400 (by decide) (by rfl)
            · · have hn : n = 400 + 40 := by omega
                subst hn
                exact solve_concrete 440 1029 (by decide) (by rfl)
          · by_cases h_tree_k_43 : k < 43
            · by_cases h_tree_k_42 : k < 42
              · · have hn : n = 400 + 41 := by omega
                  subst hn
                  exact solve_concrete 441 1690 (by decide) (by rfl)
              · · have hn : n = 400 + 42 := by omega
                  subst hn
                  exact solve_concrete 442 2195 (by decide) (by rfl)
            · · have hn : n = 400 + 43 := by omega
                subst hn
                exact solve_concrete 443 2140 (by decide) (by rfl)
        · by_cases h_tree_k_47 : k < 47
          · by_cases h_tree_k_46 : k < 46
            · by_cases h_tree_k_45 : k < 45
              · · have hn : n = 400 + 44 := by omega
                  subst hn
                  exact solve_concrete 444 1329 (by decide) (by rfl)
              · · have hn : n = 400 + 45 := by omega
                  subst hn
                  exact solve_concrete 445 5486 (by decide) (by rfl)
            · · have hn : n = 400 + 46 := by omega
                subst hn
                exact solve_concrete 446 2215 (by decide) (by rfl)
          · by_cases h_tree_k_49 : k < 49
            · by_cases h_tree_k_48 : k < 48
              · · have hn : n = 400 + 47 := by omega
                  subst hn
                  exact solve_concrete 447 3136 (by decide) (by rfl)
              · · have hn : n = 400 + 48 := by omega
                  subst hn
                  exact solve_concrete 448 3101 (by decide) (by rfl)
            · · have hn : n = 400 + 49 := by omega
                subst hn
                exact solve_concrete 449 2050 (by decide) (by rfl)
  · by_cases h_tree_k_75 : k < 75
    · by_cases h_tree_k_63 : k < 63
      · by_cases h_tree_k_57 : k < 57
        · by_cases h_tree_k_54 : k < 54
          · by_cases h_tree_k_52 : k < 52
            · by_cases h_tree_k_51 : k < 51
              · · have hn : n = 400 + 50 := by omega
                  subst hn
                  exact solve_concrete 450 1347 (by decide) (by rfl)
              · · have hn : n = 400 + 51 := by omega
                  subst hn
                  exact solve_concrete 451 2180 (by decide) (by rfl)
            · by_cases h_tree_k_53 : k < 53
              · · have hn : n = 400 + 52 := by omega
                  subst hn
                  exact solve_concrete 452 1341 (by decide) (by rfl)
              · · have hn : n = 400 + 53 := by omega
                  subst hn
                  exact solve_concrete 453 2230 (by decide) (by rfl)
          · by_cases h_tree_k_56 : k < 56
            · by_cases h_tree_k_55 : k < 55
              · · have hn : n = 400 + 54 := by omega
                  subst hn
                  exact solve_concrete 454 2891 (by decide) (by rfl)
              · · have hn : n = 400 + 55 := by omega
                  subst hn
                  exact solve_concrete 455 2120 (by decide) (by rfl)
            · · have hn : n = 400 + 56 := by omega
                subst hn
                exact solve_concrete 456 8341 (by decide) (by rfl)
        · by_cases h_tree_k_60 : k < 60
          · by_cases h_tree_k_59 : k < 59
            · by_cases h_tree_k_58 : k < 58
              · · have hn : n = 400 + 57 := by omega
                  subst hn
                  exact solve_concrete 457 3122 (by decide) (by rfl)
              · · have hn : n = 400 + 58 := by omega
                  subst hn
                  exact solve_concrete 458 1131 (by decide) (by rfl)
            · · have hn : n = 400 + 59 := by omega
                subst hn
                exact solve_concrete 459 1900 (by decide) (by rfl)
          · by_cases h_tree_k_62 : k < 62
            · by_cases h_tree_k_61 : k < 61
              · · have hn : n = 400 + 60 := by omega
                  subst hn
                  exact solve_concrete 460 2285 (by decide) (by rfl)
              · · have hn : n = 400 + 61 := by omega
                  subst hn
                  exact solve_concrete 461 2190 (by decide) (by rfl)
            · · have hn : n = 400 + 62 := by omega
                subst hn
                exact solve_concrete 462 1383 (by decide) (by rfl)
      · by_cases h_tree_k_69 : k < 69
        · by_cases h_tree_k_66 : k < 66
          · by_cases h_tree_k_65 : k < 65
            · by_cases h_tree_k_64 : k < 64
              · · have hn : n = 400 + 63 := by omega
                  subst hn
                  exact solve_concrete 463 2576 (by decide) (by rfl)
              · · have hn : n = 400 + 64 := by omega
                  subst hn
                  exact solve_concrete 464 1389 (by decide) (by rfl)
            · · have hn : n = 400 + 65 := by omega
                subst hn
                exact solve_concrete 465 2290 (by decide) (by rfl)
          · by_cases h_tree_k_68 : k < 68
            · by_cases h_tree_k_67 : k < 67
              · · have hn : n = 400 + 66 := by omega
                  subst hn
                  exact solve_concrete 466 2315 (by decide) (by rfl)
              · · have hn : n = 400 + 67 := by omega
                  subst hn
                  exact solve_concrete 467 2260 (by decide) (by rfl)
            · · have hn : n = 400 + 68 := by omega
                subst hn
                exact solve_concrete 468 1173 (by decide) (by rfl)
        · by_cases h_tree_k_72 : k < 72
          · by_cases h_tree_k_71 : k < 71
            · by_cases h_tree_k_70 : k < 70
              · · have hn : n = 400 + 69 := by omega
                  subst hn
                  exact solve_concrete 469 1430 (by decide) (by rfl)
              · · have hn : n = 400 + 70 := by omega
                  subst hn
                  exact solve_concrete 470 2335 (by decide) (by rfl)
            · · have hn : n = 400 + 71 := by omega
                subst hn
                exact solve_concrete 471 2968 (by decide) (by rfl)
          · by_cases h_tree_k_74 : k < 74
            · by_cases h_tree_k_73 : k < 73
              · · have hn : n = 400 + 72 := by omega
                  subst hn
                  exact solve_concrete 472 3269 (by decide) (by rfl)
              · · have hn : n = 400 + 73 := by omega
                  subst hn
                  exact solve_concrete 473 2330 (by decide) (by rfl)
            · · have hn : n = 400 + 74 := by omega
                subst hn
                exact solve_concrete 474 1435 (by decide) (by rfl)
    · by_cases h_tree_k_88 : k < 88
      · by_cases h_tree_k_82 : k < 82
        · by_cases h_tree_k_79 : k < 79
          · by_cases h_tree_k_77 : k < 77
            · by_cases h_tree_k_76 : k < 76
              · · have hn : n = 400 + 75 := by omega
                  subst hn
                  exact solve_concrete 475 2156 (by decide) (by rfl)
              · · have hn : n = 400 + 76 := by omega
                  subst hn
                  exact solve_concrete 476 1005 (by decide) (by rfl)
            · by_cases h_tree_k_78 : k < 78
              · · have hn : n = 400 + 77 := by omega
                  subst hn
                  exact solve_concrete 477 3262 (by decide) (by rfl)
              · · have hn : n = 400 + 78 := by omega
                  subst hn
                  exact solve_concrete 478 6071 (by decide) (by rfl)
          · by_cases h_tree_k_81 : k < 81
            · by_cases h_tree_k_80 : k < 80
              · · have hn : n = 400 + 79 := by omega
                  subst hn
                  exact solve_concrete 479 1760 (by decide) (by rfl)
              · · have hn : n = 400 + 80 := by omega
                  subst hn
                  exact solve_concrete 480 1437 (by decide) (by rfl)
            · · have hn : n = 400 + 81 := by omega
                subst hn
                exact solve_concrete 481 5954 (by decide) (by rfl)
        · by_cases h_tree_k_85 : k < 85
          · by_cases h_tree_k_84 : k < 84
            · by_cases h_tree_k_83 : k < 83
              · · have hn : n = 400 + 82 := by omega
                  subst hn
                  exact solve_concrete 482 2395 (by decide) (by rfl)
              · · have hn : n = 400 + 83 := by omega
                  subst hn
                  exact solve_concrete 483 5324 (by decide) (by rfl)
            · · have hn : n = 400 + 84 := by omega
                subst hn
                exact solve_concrete 484 3353 (by decide) (by rfl)
          · by_cases h_tree_k_87 : k < 87
            · by_cases h_tree_k_86 : k < 86
              · · have hn : n = 400 + 85 := by omega
                  subst hn
                  exact solve_concrete 485 1458 (by decide) (by rfl)
              · · have hn : n = 400 + 86 := by omega
                  subst hn
                  exact solve_concrete 486 14167 (by decide) (by rfl)
            · · have hn : n = 400 + 87 := by omega
                subst hn
                exact solve_concrete 487 6536 (by decide) (by rfl)
      · by_cases h_tree_k_94 : k < 94
        · by_cases h_tree_k_91 : k < 91
          · by_cases h_tree_k_90 : k < 90
            · by_cases h_tree_k_89 : k < 89
              · · have hn : n = 400 + 88 := by omega
                  subst hn
                  exact solve_concrete 488 1113 (by decide) (by rfl)
              · · have hn : n = 400 + 89 := by omega
                  subst hn
                  exact solve_concrete 489 2410 (by decide) (by rfl)
            · · have hn : n = 400 + 90 := by omega
                subst hn
                exact solve_concrete 490 2435 (by decide) (by rfl)
          · by_cases h_tree_k_93 : k < 93
            · by_cases h_tree_k_92 : k < 92
              · · have hn : n = 400 + 91 := by omega
                  subst hn
                  exact solve_concrete 491 2220 (by decide) (by rfl)
              · · have hn : n = 400 + 92 := by omega
                  subst hn
                  exact solve_concrete 492 1473 (by decide) (by rfl)
            · · have hn : n = 400 + 93 := by omega
                subst hn
                exact solve_concrete 493 2366 (by decide) (by rfl)
        · by_cases h_tree_k_97 : k < 97
          · by_cases h_tree_k_96 : k < 96
            · by_cases h_tree_k_95 : k < 95
              · · have hn : n = 400 + 94 := by omega
                  subst hn
                  exact solve_concrete 494 1071 (by decide) (by rfl)
              · · have hn : n = 400 + 95 := by omega
                  subst hn
                  exact solve_concrete 495 3952 (by decide) (by rfl)
            · · have hn : n = 400 + 96 := by omega
                subst hn
                exact solve_concrete 496 1505 (by decide) (by rfl)
          · by_cases h_tree_k_99 : k < 99
            · by_cases h_tree_k_98 : k < 98
              · · have hn : n = 400 + 97 := by omega
                  subst hn
                  exact solve_concrete 497 2370 (by decide) (by rfl)
              · · have hn : n = 400 + 98 := by omega
                  subst hn
                  exact solve_concrete 498 6331 (by decide) (by rfl)
            · · have hn : n = 400 + 99 := by omega
                subst hn
                exact solve_concrete 499 2500 (by decide) (by rfl)

