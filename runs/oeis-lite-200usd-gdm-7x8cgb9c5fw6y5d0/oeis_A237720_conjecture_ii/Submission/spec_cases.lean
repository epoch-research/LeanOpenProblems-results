      by_cases hS12 : S ≤ 12
      · interval_cases S
        · -- S = 2
          have h_S_prime : (2 - 1).Prime := hS_prime
          norm_num at h_S_prime
        · -- S = 3
          interval_cases p
          · -- p = 2
            use 2
            have h_n : n + 1 + 2 = 9 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 3
            use 2
            have h_n : n + 1 + 2 = 8 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 4
            norm_num at hp_prime
          · -- p = 5
            use 2
            have h_n : n + 1 + 2 = 6 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
        · -- S = 4
          interval_cases p
          · -- p = 2
            use 11
            have h_n : n + 1 + 11 = 25 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 3
            use 2
            have h_n : n + 1 + 2 = 15 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 4
            norm_num at hp_prime
          · -- p = 5
            use 2
            have h_n : n + 1 + 2 = 13 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 6
            norm_num at hp_prime
          · -- p = 7
            use 2
            have h_n : n + 1 + 2 = 11 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 8
            norm_num at hp_prime
          · -- p = 9
            norm_num at hp_prime
          · -- p = 10
            norm_num at hp_prime
          · -- p = 11
            use 2
            have h_n : n + 1 + 2 = 7 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 12
            norm_num at hp_prime
        · -- S = 5
          have h_S_prime : (5 - 1).Prime := hS_prime
          norm_num at h_S_prime
        · -- S = 6
          interval_cases p
          · -- p = 2
            use 17
            have h_n : n + 1 + 17 = 51 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 3
            use 2
            have h_n : n + 1 + 2 = 35 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 4
            norm_num at hp_prime
          · -- p = 5
            use 2
            have h_n : n + 1 + 2 = 33 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 6
            norm_num at hp_prime
          · -- p = 7
            use 2
            have h_n : n + 1 + 2 = 31 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 8
            norm_num at hp_prime
          · -- p = 9
            norm_num at hp_prime
          · -- p = 10
            norm_num at hp_prime
          · -- p = 11
            use 2
            have h_n : n + 1 + 2 = 27 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 12
            norm_num at hp_prime
          · -- p = 13
            use 2
            have h_n : n + 1 + 2 = 25 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 14
            norm_num at hp_prime
          · -- p = 15
            norm_num at hp_prime
          · -- p = 16
            norm_num at hp_prime
          · -- p = 17
            use 7
            have h_n : n + 1 + 7 = 26 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 18
            norm_num at hp_prime
          · -- p = 19
            use 11
            have h_n : n + 1 + 11 = 28 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 20
            norm_num at hp_prime
          · -- p = 21
            norm_num at hp_prime
          · -- p = 22
            norm_num at hp_prime
          · -- p = 23
            use 2
            have h_n : n + 1 + 2 = 15 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 24
            norm_num at hp_prime
          · -- p = 25
            norm_num at hp_prime
          · -- p = 26
            norm_num at hp_prime
          · -- p = 27
            norm_num at hp_prime
          · -- p = 28
            norm_num at hp_prime
          · -- p = 29
            use 2
            have h_n : n + 1 + 2 = 9 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 30
            norm_num at hp_prime
          · -- p = 31
            use 2
            have h_n : n + 1 + 2 = 7 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 32
            norm_num at hp_prime
        · -- S = 7
          have h_S_prime : (7 - 1).Prime := hS_prime
          norm_num at h_S_prime
        · -- S = 8
          interval_cases p
          · -- p = 2
            use 59
            have h_n : n + 1 + 59 = 121 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 3
            use 2
            have h_n : n + 1 + 2 = 63 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 4
            norm_num at hp_prime
          · -- p = 5
            use 2
            have h_n : n + 1 + 2 = 61 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 6
            norm_num at hp_prime
          · -- p = 7
            use 2
            have h_n : n + 1 + 2 = 59 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 8
            norm_num at hp_prime
          · -- p = 9
            norm_num at hp_prime
          · -- p = 10
            norm_num at hp_prime
          · -- p = 11
            use 2
            have h_n : n + 1 + 2 = 55 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 12
            norm_num at hp_prime
          · -- p = 13
            use 2
            have h_n : n + 1 + 2 = 53 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 14
            norm_num at hp_prime
          · -- p = 15
            norm_num at hp_prime
          · -- p = 16
            norm_num at hp_prime
          · -- p = 17
            use 2
            have h_n : n + 1 + 2 = 49 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 18
            norm_num at hp_prime
          · -- p = 19
            use 5
            have h_n : n + 1 + 5 = 50 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 20
            norm_num at hp_prime
          · -- p = 21
            norm_num at hp_prime
          · -- p = 22
            norm_num at hp_prime
          · -- p = 23
            use 11
            have h_n : n + 1 + 11 = 52 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 24
            norm_num at hp_prime
          · -- p = 25
            norm_num at hp_prime
          · -- p = 26
            norm_num at hp_prime
          · -- p = 27
            norm_num at hp_prime
          · -- p = 28
            norm_num at hp_prime
          · -- p = 29
            use 17
            have h_n : n + 1 + 17 = 52 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 30
            norm_num at hp_prime
          · -- p = 31
            use 2
            have h_n : n + 1 + 2 = 35 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 32
            norm_num at hp_prime
          · -- p = 33
            norm_num at hp_prime
          · -- p = 34
            norm_num at hp_prime
          · -- p = 35
            norm_num at hp_prime
          · -- p = 36
            norm_num at hp_prime
          · -- p = 37
            use 2
            have h_n : n + 1 + 2 = 29 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 38
            norm_num at hp_prime
          · -- p = 39
            norm_num at hp_prime
          · -- p = 40
            norm_num at hp_prime
          · -- p = 41
            use 2
            have h_n : n + 1 + 2 = 25 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 42
            norm_num at hp_prime
          · -- p = 43
            use 5
            have h_n : n + 1 + 5 = 26 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 44
            norm_num at hp_prime
          · -- p = 45
            norm_num at hp_prime
          · -- p = 46
            norm_num at hp_prime
          · -- p = 47
            use 11
            have h_n : n + 1 + 11 = 28 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 48
            norm_num at hp_prime
          · -- p = 49
            norm_num at hp_prime
          · -- p = 50
            norm_num at hp_prime
          · -- p = 51
            norm_num at hp_prime
          · -- p = 52
            norm_num at hp_prime
          · -- p = 53
            use 2
            have h_n : n + 1 + 2 = 13 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 54
            norm_num at hp_prime
          · -- p = 55
            norm_num at hp_prime
          · -- p = 56
            norm_num at hp_prime
          · -- p = 57
            norm_num at hp_prime
          · -- p = 58
            norm_num at hp_prime
          · -- p = 59
            use 2
            have h_n : n + 1 + 2 = 7 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 60
            norm_num at hp_prime
        · -- S = 9
          have h_S_prime : (9 - 1).Prime := hS_prime
          norm_num at h_S_prime
        · -- S = 10
          have h_S_prime : (10 - 1).Prime := hS_prime
          norm_num at h_S_prime
        · -- S = 11
          have h_S_prime : (11 - 1).Prime := hS_prime
          norm_num at h_S_prime
        · -- S = 12
          interval_cases p
          · -- p = 2
            use 29
            have h_n : n + 1 + 29 = 171 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 3
            use 29
            have h_n : n + 1 + 29 = 170 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 4
            norm_num at hp_prime
          · -- p = 5
            use 3
            have h_n : n + 1 + 3 = 142 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 6
            norm_num at hp_prime
          · -- p = 7
            use 3
            have h_n : n + 1 + 3 = 140 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 8
            norm_num at hp_prime
          · -- p = 9
            norm_num at hp_prime
          · -- p = 10
            norm_num at hp_prime
          · -- p = 11
            use 3
            have h_n : n + 1 + 3 = 136 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 12
            norm_num at hp_prime
          · -- p = 13
            use 3
            have h_n : n + 1 + 3 = 134 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 14
            norm_num at hp_prime
          · -- p = 15
            norm_num at hp_prime
          · -- p = 16
            norm_num at hp_prime
          · -- p = 17
            use 3
            have h_n : n + 1 + 3 = 130 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 18
            norm_num at hp_prime
          · -- p = 19
            use 3
            have h_n : n + 1 + 3 = 128 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 20
            norm_num at hp_prime
          · -- p = 21
            norm_num at hp_prime
          · -- p = 22
            norm_num at hp_prime
          · -- p = 23
            use 3
            have h_n : n + 1 + 3 = 124 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 24
            norm_num at hp_prime
          · -- p = 25
            norm_num at hp_prime
          · -- p = 26
            norm_num at hp_prime
          · -- p = 27
            norm_num at hp_prime
          · -- p = 28
            norm_num at hp_prime
          · -- p = 29
            use 7
            have h_n : n + 1 + 7 = 122 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 30
            norm_num at hp_prime
          · -- p = 31
            use 11
            have h_n : n + 1 + 11 = 124 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 32
            norm_num at hp_prime
          · -- p = 33
            norm_num at hp_prime
          · -- p = 34
            norm_num at hp_prime
          · -- p = 35
            norm_num at hp_prime
          · -- p = 36
            norm_num at hp_prime
          · -- p = 37
            use 17
            have h_n : n + 1 + 17 = 124 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 38
            norm_num at hp_prime
          · -- p = 39
            norm_num at hp_prime
          · -- p = 40
            norm_num at hp_prime
          · -- p = 41
            use 19
            have h_n : n + 1 + 19 = 122 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 42
            norm_num at hp_prime
          · -- p = 43
            use 23
            have h_n : n + 1 + 23 = 124 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 44
            norm_num at hp_prime
          · -- p = 45
            norm_num at hp_prime
          · -- p = 46
            norm_num at hp_prime
          · -- p = 47
            use 29
            have h_n : n + 1 + 29 = 126 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 48
            norm_num at hp_prime
          · -- p = 49
            norm_num at hp_prime
          · -- p = 50
            norm_num at hp_prime
          · -- p = 51
            norm_num at hp_prime
          · -- p = 52
            norm_num at hp_prime
          · -- p = 53
            use 31
            have h_n : n + 1 + 31 = 122 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 54
            norm_num at hp_prime
          · -- p = 55
            norm_num at hp_prime
          · -- p = 56
            norm_num at hp_prime
          · -- p = 57
            norm_num at hp_prime
          · -- p = 58
            norm_num at hp_prime
          · -- p = 59
            use 37
            have h_n : n + 1 + 37 = 122 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 60
            norm_num at hp_prime
          · -- p = 61
            use 41
            have h_n : n + 1 + 41 = 124 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 62
            norm_num at hp_prime
          · -- p = 63
            norm_num at hp_prime
          · -- p = 64
            norm_num at hp_prime
          · -- p = 65
            norm_num at hp_prime
          · -- p = 66
            norm_num at hp_prime
          · -- p = 67
            use 47
            have h_n : n + 1 + 47 = 124 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 68
            norm_num at hp_prime
          · -- p = 69
            norm_num at hp_prime
          · -- p = 70
            norm_num at hp_prime
          · -- p = 71
            use 53
            have h_n : n + 1 + 53 = 126 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 72
            norm_num at hp_prime
          · -- p = 73
            use 53
            have h_n : n + 1 + 53 = 124 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 74
            norm_num at hp_prime
          · -- p = 75
            norm_num at hp_prime
          · -- p = 76
            norm_num at hp_prime
          · -- p = 77
            norm_num at hp_prime
          · -- p = 78
            norm_num at hp_prime
          · -- p = 79
            use 59
            have h_n : n + 1 + 59 = 124 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 80
            norm_num at hp_prime
          · -- p = 81
            norm_num at hp_prime
          · -- p = 82
            norm_num at hp_prime
          · -- p = 83
            use 2
            have h_n : n + 1 + 2 = 63 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 84
            norm_num at hp_prime
          · -- p = 85
            norm_num at hp_prime
          · -- p = 86
            norm_num at hp_prime
          · -- p = 87
            norm_num at hp_prime
          · -- p = 88
            norm_num at hp_prime
          · -- p = 89
            use 2
            have h_n : n + 1 + 2 = 57 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 90
            norm_num at hp_prime
          · -- p = 91
            norm_num at hp_prime
          · -- p = 92
            norm_num at hp_prime
          · -- p = 93
            norm_num at hp_prime
          · -- p = 94
            norm_num at hp_prime
          · -- p = 95
            norm_num at hp_prime
          · -- p = 96
            norm_num at hp_prime
          · -- p = 97
            use 2
            have h_n : n + 1 + 2 = 49 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 98
            norm_num at hp_prime
          · -- p = 99
            norm_num at hp_prime
          · -- p = 100
            norm_num at hp_prime
          · -- p = 101
            use 7
            have h_n : n + 1 + 7 = 50 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 102
            norm_num at hp_prime
          · -- p = 103
            use 11
            have h_n : n + 1 + 11 = 52 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 104
            norm_num at hp_prime
          · -- p = 105
            norm_num at hp_prime
          · -- p = 106
            norm_num at hp_prime
          · -- p = 107
            use 13
            have h_n : n + 1 + 13 = 50 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 108
            norm_num at hp_prime
          · -- p = 109
            use 17
            have h_n : n + 1 + 17 = 52 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 110
            norm_num at hp_prime
          · -- p = 111
            norm_num at hp_prime
          · -- p = 112
            norm_num at hp_prime
          · -- p = 113
            use 2
            have h_n : n + 1 + 2 = 33 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 114
            norm_num at hp_prime
          · -- p = 115
            norm_num at hp_prime
          · -- p = 116
            norm_num at hp_prime
          · -- p = 117
            norm_num at hp_prime
          · -- p = 118
            norm_num at hp_prime
          · -- p = 119
            norm_num at hp_prime
          · -- p = 120
            norm_num at hp_prime
          · -- p = 121
            norm_num at hp_prime
          · -- p = 122
            norm_num at hp_prime
          · -- p = 123
            norm_num at hp_prime
          · -- p = 124
            norm_num at hp_prime
          · -- p = 125
            norm_num at hp_prime
          · -- p = 126
            norm_num at hp_prime
          · -- p = 127
            use 11
            have h_n : n + 1 + 11 = 28 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 128
            norm_num at hp_prime
          · -- p = 129
            norm_num at hp_prime
          · -- p = 130
            norm_num at hp_prime
          · -- p = 131
            use 2
            have h_n : n + 1 + 2 = 15 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 132
            norm_num at hp_prime
          · -- p = 133
            norm_num at hp_prime
          · -- p = 134
            norm_num at hp_prime
          · -- p = 135
            norm_num at hp_prime
          · -- p = 136
            norm_num at hp_prime
          · -- p = 137
            use 2
            have h_n : n + 1 + 2 = 9 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 138
            norm_num at hp_prime
          · -- p = 139
            use 2
            have h_n : n + 1 + 2 = 7 := by omega
            refine ⟨by norm_num, by omega, ?_, ?_, ?_, ?_⟩
            · rw [h_n]; norm_num
            · rw [h_n]; norm_num
            · intro hc; omega
            · intro hc; rw [h_n] at hc; norm_num at hc; exact hc
          · -- p = 140
            norm_num at hp_prime