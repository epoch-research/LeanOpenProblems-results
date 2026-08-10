import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 20000
set_option linter.unnecessarySeqFocus false

open Nat Set

noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)
noncomputable def S (i : ℕ) : ℕ := P i + P (i + 1)

noncomputable def A167918 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sInf { k : ℕ | k > n ∧ S n ∣ S k }

noncomputable def A167918_ratio (n : ℕ) : ℕ :=
  if n = 0 then 0
  else S (A167918 n) / S n

theorem next_prime {i : ℕ} {p q : ℕ} (hi : i ≥ 1) (hP : P i = p) (hq : Nat.Prime q) (h_gt : p < q) (h_none : ∀ x, p < x → x < q → ¬ Nat.Prime x) : P (i + 1) = q := by
  have h_inf := Nat.infinite_setOf_prime
  dsimp [P] at hP ⊢
  have h_lt_nth : nth Nat.Prime (i - 1) < nth Nat.Prime i := by
    rw [nth_lt_nth h_inf]
    omega
  rw [hP] at h_lt_nth
  by_contra h_neq
  have h_cases : nth Nat.Prime i < q ∨ q < nth Nat.Prime i := by omega
  rcases h_cases with h_lt | h_gt'
  · have h_prime : Nat.Prime (nth Nat.Prime i) := nth_mem_of_infinite h_inf i
    have h_false := h_none (nth Nat.Prime i) h_lt_nth h_lt
    contradiction
  · have h_gt'' : q < nth Nat.Prime (i - 1 + 1) := by rwa [Nat.sub_add_cancel hi]
    have h_le := le_nth_of_lt_nth_succ h_gt'' hq
    rw [hP] at h_le
    omega

theorem P_eq (i : ℕ) (p : ℕ) (hp : Nat.Prime p) (hc : Nat.count Nat.Prime p = i - 1) : P i = p := by
  dsimp [P]
  have h3 := Nat.nth_count hp
  rw [hc] at h3
  exact h3

-- Let's define the base primes up to P_57 from Spec.lean
theorem P_1 : P 1 = 2 := P_eq 1 2 (by decide) rfl
theorem P_2 : P 2 = 3 := P_eq 2 3 (by decide) rfl
theorem P_3 : P 3 = 5 := P_eq 3 5 (by decide) rfl
theorem P_4 : P 4 = 7 := P_eq 4 7 (by decide) rfl
theorem P_5 : P 5 = 11 := P_eq 5 11 (by decide) rfl
theorem P_6 : P 6 = 13 := P_eq 6 13 (by decide) rfl
theorem P_7 : P 7 = 17 := P_eq 7 17 (by decide) rfl
theorem P_8 : P 8 = 19 := P_eq 8 19 (by decide) rfl
theorem P_9 : P 9 = 23 := P_eq 9 23 (by decide) rfl
theorem P_10 : P 10 = 29 := P_eq 10 29 (by decide) rfl
theorem P_11 : P 11 = 31 := P_eq 11 31 (by decide) rfl
theorem P_12 : P 12 = 37 := P_eq 12 37 (by decide) rfl
theorem P_13 : P 13 = 41 := P_eq 13 41 (by decide) rfl
theorem P_14 : P 14 = 43 := P_eq 14 43 (by decide) rfl
theorem P_15 : P 15 = 47 := P_eq 15 47 (by decide) rfl
theorem P_16 : P 16 = 53 := P_eq 16 53 (by decide) rfl
theorem P_17 : P 17 = 59 := P_eq 17 59 (by decide) rfl
theorem P_18 : P 18 = 61 := P_eq 18 61 (by decide) rfl
theorem P_19 : P 19 = 67 := P_eq 19 67 (by decide) rfl
theorem P_20 : P 20 = 71 := P_eq 20 71 (by decide) rfl
theorem P_21 : P 21 = 73 := P_eq 21 73 (by decide) rfl
theorem P_22 : P 22 = 79 := P_eq 22 79 (by decide) rfl
theorem P_23 : P 23 = 83 := P_eq 23 83 (by decide) rfl
theorem P_24 : P 24 = 89 := P_eq 24 89 (by decide) rfl
theorem P_25 : P 25 = 97 := P_eq 25 97 (by decide) rfl
theorem P_26 : P 26 = 101 := P_eq 26 101 (by decide) rfl
theorem P_27 : P 27 = 103 := P_eq 27 103 (by decide) rfl
theorem P_28 : P 28 = 107 := P_eq 28 107 (by decide) rfl
theorem P_29 : P 29 = 109 := P_eq 29 109 (by decide) rfl
theorem P_30 : P 30 = 113 := P_eq 30 113 (by decide) rfl
theorem P_31 : P 31 = 127 := P_eq 31 127 (by decide) rfl
theorem P_32 : P 32 = 131 := P_eq 32 131 (by decide) rfl
theorem P_33 : P 33 = 137 := P_eq 33 137 (by decide) rfl
theorem P_34 : P 34 = 139 := P_eq 34 139 (by decide) rfl
theorem P_35 : P 35 = 149 := P_eq 35 149 (by decide) rfl
theorem P_36 : P 36 = 151 := P_eq 36 151 (by decide) rfl
theorem P_37 : P 37 = 157 := P_eq 37 157 (by decide) rfl
theorem P_38 : P 38 = 163 := P_eq 38 163 (by decide) rfl
theorem P_39 : P 39 = 167 := P_eq 39 167 (by decide) rfl
theorem P_40 : P 40 = 173 := P_eq 40 173 (by decide) rfl
theorem P_41 : P 41 = 179 := P_eq 41 179 (by decide) rfl
theorem P_42 : P 42 = 181 := P_eq 42 181 (by decide) rfl
theorem P_43 : P 43 = 191 := P_eq 43 191 (by decide) rfl
theorem P_44 : P 44 = 193 := P_eq 44 193 (by decide) rfl
theorem P_45 : P 45 = 197 := P_eq 45 197 (by decide) rfl
theorem P_46 : P 46 = 199 := P_eq 46 199 (by decide) rfl
theorem P_47 : P 47 = 211 := P_eq 47 211 (by decide) rfl
theorem P_48 : P 48 = 223 := P_eq 48 223 (by decide) rfl
theorem P_49 : P 49 = 227 := P_eq 49 227 (by decide) rfl
theorem P_50 : P 50 = 229 := P_eq 50 229 (by decide) rfl
theorem P_51 : P 51 = 233 := P_eq 51 233 (by decide) rfl
theorem P_52 : P 52 = 239 := P_eq 52 239 (by decide) rfl
theorem P_53 : P 53 = 241 := P_eq 53 241 (by decide) rfl
theorem P_54 : P 54 = 251 := P_eq 54 251 (by decide) rfl
theorem P_55 : P 55 = 257 := P_eq 55 257 (by decide) rfl
theorem P_56 : P 56 = 263 := P_eq 56 263 (by decide) rfl
theorem P_57 : P 57 = 269 := P_eq 57 269 (by decide) rfl
theorem S_1 : S 1 = 5 := by dsimp [S]; rw [P_1, P_2]
theorem S_2 : S 2 = 8 := by dsimp [S]; rw [P_2, P_3]
theorem S_3 : S 3 = 12 := by dsimp [S]; rw [P_3, P_4]
theorem S_4 : S 4 = 18 := by dsimp [S]; rw [P_4, P_5]
theorem S_5 : S 5 = 24 := by dsimp [S]; rw [P_5, P_6]
theorem S_6 : S 6 = 30 := by dsimp [S]; rw [P_6, P_7]
theorem S_7 : S 7 = 36 := by dsimp [S]; rw [P_7, P_8]
theorem S_8 : S 8 = 42 := by dsimp [S]; rw [P_8, P_9]
theorem S_9 : S 9 = 52 := by dsimp [S]; rw [P_9, P_10]
theorem S_10 : S 10 = 60 := by dsimp [S]; rw [P_10, P_11]
theorem S_11 : S 11 = 68 := by dsimp [S]; rw [P_11, P_12]
theorem S_12 : S 12 = 78 := by dsimp [S]; rw [P_12, P_13]
theorem S_13 : S 13 = 84 := by dsimp [S]; rw [P_13, P_14]
theorem S_14 : S 14 = 90 := by dsimp [S]; rw [P_14, P_15]
theorem S_15 : S 15 = 100 := by dsimp [S]; rw [P_15, P_16]
theorem S_16 : S 16 = 112 := by dsimp [S]; rw [P_16, P_17]
theorem S_17 : S 17 = 120 := by dsimp [S]; rw [P_17, P_18]
theorem S_18 : S 18 = 128 := by dsimp [S]; rw [P_18, P_19]
theorem S_19 : S 19 = 138 := by dsimp [S]; rw [P_19, P_20]
theorem S_20 : S 20 = 144 := by dsimp [S]; rw [P_20, P_21]
theorem S_21 : S 21 = 152 := by dsimp [S]; rw [P_21, P_22]
theorem S_22 : S 22 = 162 := by dsimp [S]; rw [P_22, P_23]
theorem S_23 : S 23 = 172 := by dsimp [S]; rw [P_23, P_24]
theorem S_24 : S 24 = 186 := by dsimp [S]; rw [P_24, P_25]
theorem S_25 : S 25 = 198 := by dsimp [S]; rw [P_25, P_26]
theorem S_26 : S 26 = 204 := by dsimp [S]; rw [P_26, P_27]
theorem S_27 : S 27 = 210 := by dsimp [S]; rw [P_27, P_28]
theorem S_28 : S 28 = 216 := by dsimp [S]; rw [P_28, P_29]
theorem S_29 : S 29 = 222 := by dsimp [S]; rw [P_29, P_30]
theorem S_30 : S 30 = 240 := by dsimp [S]; rw [P_30, P_31]
theorem S_31 : S 31 = 258 := by dsimp [S]; rw [P_31, P_32]
theorem S_32 : S 32 = 268 := by dsimp [S]; rw [P_32, P_33]
theorem S_33 : S 33 = 276 := by dsimp [S]; rw [P_33, P_34]
theorem S_34 : S 34 = 288 := by dsimp [S]; rw [P_34, P_35]
theorem S_35 : S 35 = 300 := by dsimp [S]; rw [P_35, P_36]
theorem S_36 : S 36 = 308 := by dsimp [S]; rw [P_36, P_37]
theorem S_37 : S 37 = 320 := by dsimp [S]; rw [P_37, P_38]
theorem S_38 : S 38 = 330 := by dsimp [S]; rw [P_38, P_39]
theorem S_39 : S 39 = 340 := by dsimp [S]; rw [P_39, P_40]
theorem S_40 : S 40 = 352 := by dsimp [S]; rw [P_40, P_41]
theorem S_41 : S 41 = 360 := by dsimp [S]; rw [P_41, P_42]
theorem S_42 : S 42 = 372 := by dsimp [S]; rw [P_42, P_43]
theorem S_43 : S 43 = 384 := by dsimp [S]; rw [P_43, P_44]
theorem S_44 : S 44 = 390 := by dsimp [S]; rw [P_44, P_45]
theorem S_45 : S 45 = 396 := by dsimp [S]; rw [P_45, P_46]
theorem S_46 : S 46 = 410 := by dsimp [S]; rw [P_46, P_47]
theorem S_47 : S 47 = 434 := by dsimp [S]; rw [P_47, P_48]
theorem S_48 : S 48 = 450 := by dsimp [S]; rw [P_48, P_49]
theorem S_49 : S 49 = 456 := by dsimp [S]; rw [P_49, P_50]
theorem S_50 : S 50 = 462 := by dsimp [S]; rw [P_50, P_51]
theorem S_51 : S 51 = 472 := by dsimp [S]; rw [P_51, P_52]
theorem S_52 : S 52 = 480 := by dsimp [S]; rw [P_52, P_53]
theorem S_53 : S 53 = 492 := by dsimp [S]; rw [P_53, P_54]
theorem S_54 : S 54 = 508 := by dsimp [S]; rw [P_54, P_55]
theorem S_55 : S 55 = 520 := by dsimp [S]; rw [P_55, P_56]
theorem S_56 : S 56 = 532 := by dsimp [S]; rw [P_56, P_57]

theorem P_58 : P 58 = 271 := next_prime (by decide) P_57 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_59 : P 59 = 277 := next_prime (by decide) P_58 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_60 : P 60 = 281 := next_prime (by decide) P_59 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_61 : P 61 = 283 := next_prime (by decide) P_60 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_62 : P 62 = 293 := next_prime (by decide) P_61 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_63 : P 63 = 307 := next_prime (by decide) P_62 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_64 : P 64 = 311 := next_prime (by decide) P_63 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_65 : P 65 = 313 := next_prime (by decide) P_64 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_66 : P 66 = 317 := next_prime (by decide) P_65 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_67 : P 67 = 331 := next_prime (by decide) P_66 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_68 : P 68 = 337 := next_prime (by decide) P_67 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_69 : P 69 = 347 := next_prime (by decide) P_68 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_70 : P 70 = 349 := next_prime (by decide) P_69 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_71 : P 71 = 353 := next_prime (by decide) P_70 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_72 : P 72 = 359 := next_prime (by decide) P_71 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_73 : P 73 = 367 := next_prime (by decide) P_72 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_74 : P 74 = 373 := next_prime (by decide) P_73 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_75 : P 75 = 379 := next_prime (by decide) P_74 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_76 : P 76 = 383 := next_prime (by decide) P_75 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_77 : P 77 = 389 := next_prime (by decide) P_76 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_78 : P 78 = 397 := next_prime (by decide) P_77 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_79 : P 79 = 401 := next_prime (by decide) P_78 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_80 : P 80 = 409 := next_prime (by decide) P_79 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_81 : P 81 = 419 := next_prime (by decide) P_80 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_82 : P 82 = 421 := next_prime (by decide) P_81 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_83 : P 83 = 431 := next_prime (by decide) P_82 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_84 : P 84 = 433 := next_prime (by decide) P_83 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_85 : P 85 = 439 := next_prime (by decide) P_84 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_86 : P 86 = 443 := next_prime (by decide) P_85 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_87 : P 87 = 449 := next_prime (by decide) P_86 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_88 : P 88 = 457 := next_prime (by decide) P_87 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_89 : P 89 = 461 := next_prime (by decide) P_88 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_90 : P 90 = 463 := next_prime (by decide) P_89 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_91 : P 91 = 467 := next_prime (by decide) P_90 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_92 : P 92 = 479 := next_prime (by decide) P_91 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_93 : P 93 = 487 := next_prime (by decide) P_92 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_94 : P 94 = 491 := next_prime (by decide) P_93 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_95 : P 95 = 499 := next_prime (by decide) P_94 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_96 : P 96 = 503 := next_prime (by decide) P_95 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_97 : P 97 = 509 := next_prime (by decide) P_96 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_98 : P 98 = 521 := next_prime (by decide) P_97 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_99 : P 99 = 523 := next_prime (by decide) P_98 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_100 : P 100 = 541 := next_prime (by decide) P_99 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_101 : P 101 = 547 := next_prime (by decide) P_100 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_102 : P 102 = 557 := next_prime (by decide) P_101 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_103 : P 103 = 563 := next_prime (by decide) P_102 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_104 : P 104 = 569 := next_prime (by decide) P_103 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_105 : P 105 = 571 := next_prime (by decide) P_104 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_106 : P 106 = 577 := next_prime (by decide) P_105 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_107 : P 107 = 587 := next_prime (by decide) P_106 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_108 : P 108 = 593 := next_prime (by decide) P_107 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_109 : P 109 = 599 := next_prime (by decide) P_108 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_110 : P 110 = 601 := next_prime (by decide) P_109 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_111 : P 111 = 607 := next_prime (by decide) P_110 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_112 : P 112 = 613 := next_prime (by decide) P_111 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_113 : P 113 = 617 := next_prime (by decide) P_112 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_114 : P 114 = 619 := next_prime (by decide) P_113 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_115 : P 115 = 631 := next_prime (by decide) P_114 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_116 : P 116 = 641 := next_prime (by decide) P_115 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_117 : P 117 = 643 := next_prime (by decide) P_116 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_118 : P 118 = 647 := next_prime (by decide) P_117 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_119 : P 119 = 653 := next_prime (by decide) P_118 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_120 : P 120 = 659 := next_prime (by decide) P_119 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_121 : P 121 = 661 := next_prime (by decide) P_120 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_122 : P 122 = 673 := next_prime (by decide) P_121 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_123 : P 123 = 677 := next_prime (by decide) P_122 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_124 : P 124 = 683 := next_prime (by decide) P_123 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_125 : P 125 = 691 := next_prime (by decide) P_124 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_126 : P 126 = 701 := next_prime (by decide) P_125 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_127 : P 127 = 709 := next_prime (by decide) P_126 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_128 : P 128 = 719 := next_prime (by decide) P_127 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_129 : P 129 = 727 := next_prime (by decide) P_128 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_130 : P 130 = 733 := next_prime (by decide) P_129 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_131 : P 131 = 739 := next_prime (by decide) P_130 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_132 : P 132 = 743 := next_prime (by decide) P_131 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_133 : P 133 = 751 := next_prime (by decide) P_132 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_134 : P 134 = 757 := next_prime (by decide) P_133 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_135 : P 135 = 761 := next_prime (by decide) P_134 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_136 : P 136 = 769 := next_prime (by decide) P_135 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_137 : P 137 = 773 := next_prime (by decide) P_136 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_138 : P 138 = 787 := next_prime (by decide) P_137 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_139 : P 139 = 797 := next_prime (by decide) P_138 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_140 : P 140 = 809 := next_prime (by decide) P_139 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_141 : P 141 = 811 := next_prime (by decide) P_140 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_142 : P 142 = 821 := next_prime (by decide) P_141 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_143 : P 143 = 823 := next_prime (by decide) P_142 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_144 : P 144 = 827 := next_prime (by decide) P_143 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_145 : P 145 = 829 := next_prime (by decide) P_144 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_146 : P 146 = 839 := next_prime (by decide) P_145 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_147 : P 147 = 853 := next_prime (by decide) P_146 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_148 : P 148 = 857 := next_prime (by decide) P_147 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_149 : P 149 = 859 := next_prime (by decide) P_148 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_150 : P 150 = 863 := next_prime (by decide) P_149 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_151 : P 151 = 877 := next_prime (by decide) P_150 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_152 : P 152 = 881 := next_prime (by decide) P_151 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_153 : P 153 = 883 := next_prime (by decide) P_152 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_154 : P 154 = 887 := next_prime (by decide) P_153 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_155 : P 155 = 907 := next_prime (by decide) P_154 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_156 : P 156 = 911 := next_prime (by decide) P_155 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_157 : P 157 = 919 := next_prime (by decide) P_156 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_158 : P 158 = 929 := next_prime (by decide) P_157 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_159 : P 159 = 937 := next_prime (by decide) P_158 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_160 : P 160 = 941 := next_prime (by decide) P_159 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_161 : P 161 = 947 := next_prime (by decide) P_160 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_162 : P 162 = 953 := next_prime (by decide) P_161 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_163 : P 163 = 967 := next_prime (by decide) P_162 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_164 : P 164 = 971 := next_prime (by decide) P_163 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_165 : P 165 = 977 := next_prime (by decide) P_164 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_166 : P 166 = 983 := next_prime (by decide) P_165 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_167 : P 167 = 991 := next_prime (by decide) P_166 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_168 : P 168 = 997 := next_prime (by decide) P_167 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_169 : P 169 = 1009 := next_prime (by decide) P_168 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_170 : P 170 = 1013 := next_prime (by decide) P_169 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_171 : P 171 = 1019 := next_prime (by decide) P_170 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_172 : P 172 = 1021 := next_prime (by decide) P_171 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_173 : P 173 = 1031 := next_prime (by decide) P_172 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_174 : P 174 = 1033 := next_prime (by decide) P_173 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_175 : P 175 = 1039 := next_prime (by decide) P_174 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_176 : P 176 = 1049 := next_prime (by decide) P_175 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_177 : P 177 = 1051 := next_prime (by decide) P_176 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_178 : P 178 = 1061 := next_prime (by decide) P_177 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_179 : P 179 = 1063 := next_prime (by decide) P_178 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_180 : P 180 = 1069 := next_prime (by decide) P_179 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_181 : P 181 = 1087 := next_prime (by decide) P_180 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_182 : P 182 = 1091 := next_prime (by decide) P_181 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_183 : P 183 = 1093 := next_prime (by decide) P_182 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_184 : P 184 = 1097 := next_prime (by decide) P_183 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_185 : P 185 = 1103 := next_prime (by decide) P_184 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_186 : P 186 = 1109 := next_prime (by decide) P_185 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_187 : P 187 = 1117 := next_prime (by decide) P_186 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_188 : P 188 = 1123 := next_prime (by decide) P_187 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_189 : P 189 = 1129 := next_prime (by decide) P_188 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_190 : P 190 = 1151 := next_prime (by decide) P_189 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_191 : P 191 = 1153 := next_prime (by decide) P_190 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_192 : P 192 = 1163 := next_prime (by decide) P_191 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_193 : P 193 = 1171 := next_prime (by decide) P_192 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_194 : P 194 = 1181 := next_prime (by decide) P_193 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_195 : P 195 = 1187 := next_prime (by decide) P_194 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_196 : P 196 = 1193 := next_prime (by decide) P_195 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_197 : P 197 = 1201 := next_prime (by decide) P_196 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_198 : P 198 = 1213 := next_prime (by decide) P_197 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_199 : P 199 = 1217 := next_prime (by decide) P_198 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_200 : P 200 = 1223 := next_prime (by decide) P_199 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_201 : P 201 = 1229 := next_prime (by decide) P_200 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_202 : P 202 = 1231 := next_prime (by decide) P_201 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_203 : P 203 = 1237 := next_prime (by decide) P_202 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_204 : P 204 = 1249 := next_prime (by decide) P_203 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_205 : P 205 = 1259 := next_prime (by decide) P_204 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_206 : P 206 = 1277 := next_prime (by decide) P_205 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_207 : P 207 = 1279 := next_prime (by decide) P_206 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_208 : P 208 = 1283 := next_prime (by decide) P_207 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_209 : P 209 = 1289 := next_prime (by decide) P_208 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_210 : P 210 = 1291 := next_prime (by decide) P_209 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_211 : P 211 = 1297 := next_prime (by decide) P_210 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_212 : P 212 = 1301 := next_prime (by decide) P_211 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_213 : P 213 = 1303 := next_prime (by decide) P_212 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_214 : P 214 = 1307 := next_prime (by decide) P_213 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_215 : P 215 = 1319 := next_prime (by decide) P_214 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_216 : P 216 = 1321 := next_prime (by decide) P_215 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_217 : P 217 = 1327 := next_prime (by decide) P_216 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_218 : P 218 = 1361 := next_prime (by decide) P_217 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_219 : P 219 = 1367 := next_prime (by decide) P_218 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_220 : P 220 = 1373 := next_prime (by decide) P_219 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_221 : P 221 = 1381 := next_prime (by decide) P_220 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_222 : P 222 = 1399 := next_prime (by decide) P_221 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_223 : P 223 = 1409 := next_prime (by decide) P_222 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_224 : P 224 = 1423 := next_prime (by decide) P_223 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_225 : P 225 = 1427 := next_prime (by decide) P_224 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_226 : P 226 = 1429 := next_prime (by decide) P_225 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_227 : P 227 = 1433 := next_prime (by decide) P_226 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_228 : P 228 = 1439 := next_prime (by decide) P_227 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)
theorem P_229 : P 229 = 1447 := next_prime (by decide) P_228 (by decide) (by decide) (by intro x h1 h2; interval_cases x <;> decide)


theorem S_57 : S 57 = 540 := by dsimp [S]; rw [P_57, P_58]
theorem S_58 : S 58 = 548 := by dsimp [S]; rw [P_58, P_59]
theorem S_59 : S 59 = 558 := by dsimp [S]; rw [P_59, P_60]
theorem S_60 : S 60 = 564 := by dsimp [S]; rw [P_60, P_61]
theorem S_61 : S 61 = 576 := by dsimp [S]; rw [P_61, P_62]
theorem S_62 : S 62 = 600 := by dsimp [S]; rw [P_62, P_63]
theorem S_63 : S 63 = 618 := by dsimp [S]; rw [P_63, P_64]
theorem S_64 : S 64 = 624 := by dsimp [S]; rw [P_64, P_65]
theorem S_65 : S 65 = 630 := by dsimp [S]; rw [P_65, P_66]
theorem S_66 : S 66 = 648 := by dsimp [S]; rw [P_66, P_67]
theorem S_67 : S 67 = 668 := by dsimp [S]; rw [P_67, P_68]
theorem S_68 : S 68 = 684 := by dsimp [S]; rw [P_68, P_69]
theorem S_69 : S 69 = 696 := by dsimp [S]; rw [P_69, P_70]
theorem S_70 : S 70 = 702 := by dsimp [S]; rw [P_70, P_71]
theorem S_71 : S 71 = 712 := by dsimp [S]; rw [P_71, P_72]
theorem S_72 : S 72 = 726 := by dsimp [S]; rw [P_72, P_73]
theorem S_73 : S 73 = 740 := by dsimp [S]; rw [P_73, P_74]
theorem S_74 : S 74 = 752 := by dsimp [S]; rw [P_74, P_75]
theorem S_75 : S 75 = 762 := by dsimp [S]; rw [P_75, P_76]
theorem S_76 : S 76 = 772 := by dsimp [S]; rw [P_76, P_77]
theorem S_77 : S 77 = 786 := by dsimp [S]; rw [P_77, P_78]
theorem S_78 : S 78 = 798 := by dsimp [S]; rw [P_78, P_79]
theorem S_79 : S 79 = 810 := by dsimp [S]; rw [P_79, P_80]
theorem S_80 : S 80 = 828 := by dsimp [S]; rw [P_80, P_81]
theorem S_81 : S 81 = 840 := by dsimp [S]; rw [P_81, P_82]
theorem S_82 : S 82 = 852 := by dsimp [S]; rw [P_82, P_83]
theorem S_83 : S 83 = 864 := by dsimp [S]; rw [P_83, P_84]
theorem S_84 : S 84 = 872 := by dsimp [S]; rw [P_84, P_85]
theorem S_85 : S 85 = 882 := by dsimp [S]; rw [P_85, P_86]
theorem S_86 : S 86 = 892 := by dsimp [S]; rw [P_86, P_87]
theorem S_87 : S 87 = 906 := by dsimp [S]; rw [P_87, P_88]
theorem S_88 : S 88 = 918 := by dsimp [S]; rw [P_88, P_89]
theorem S_89 : S 89 = 924 := by dsimp [S]; rw [P_89, P_90]
theorem S_90 : S 90 = 930 := by dsimp [S]; rw [P_90, P_91]
theorem S_91 : S 91 = 946 := by dsimp [S]; rw [P_91, P_92]
theorem S_92 : S 92 = 966 := by dsimp [S]; rw [P_92, P_93]
theorem S_93 : S 93 = 978 := by dsimp [S]; rw [P_93, P_94]
theorem S_94 : S 94 = 990 := by dsimp [S]; rw [P_94, P_95]
theorem S_95 : S 95 = 1002 := by dsimp [S]; rw [P_95, P_96]
theorem S_96 : S 96 = 1012 := by dsimp [S]; rw [P_96, P_97]
theorem S_97 : S 97 = 1030 := by dsimp [S]; rw [P_97, P_98]
theorem S_98 : S 98 = 1044 := by dsimp [S]; rw [P_98, P_99]
theorem S_99 : S 99 = 1064 := by dsimp [S]; rw [P_99, P_100]
theorem S_100 : S 100 = 1088 := by dsimp [S]; rw [P_100, P_101]
theorem S_101 : S 101 = 1104 := by dsimp [S]; rw [P_101, P_102]
theorem S_102 : S 102 = 1120 := by dsimp [S]; rw [P_102, P_103]
theorem S_103 : S 103 = 1132 := by dsimp [S]; rw [P_103, P_104]
theorem S_104 : S 104 = 1140 := by dsimp [S]; rw [P_104, P_105]
theorem S_105 : S 105 = 1148 := by dsimp [S]; rw [P_105, P_106]
theorem S_106 : S 106 = 1164 := by dsimp [S]; rw [P_106, P_107]
theorem S_107 : S 107 = 1180 := by dsimp [S]; rw [P_107, P_108]
theorem S_108 : S 108 = 1192 := by dsimp [S]; rw [P_108, P_109]
theorem S_109 : S 109 = 1200 := by dsimp [S]; rw [P_109, P_110]
theorem S_110 : S 110 = 1208 := by dsimp [S]; rw [P_110, P_111]
theorem S_111 : S 111 = 1220 := by dsimp [S]; rw [P_111, P_112]
theorem S_112 : S 112 = 1230 := by dsimp [S]; rw [P_112, P_113]
theorem S_113 : S 113 = 1236 := by dsimp [S]; rw [P_113, P_114]
theorem S_114 : S 114 = 1250 := by dsimp [S]; rw [P_114, P_115]
theorem S_115 : S 115 = 1272 := by dsimp [S]; rw [P_115, P_116]
theorem S_116 : S 116 = 1284 := by dsimp [S]; rw [P_116, P_117]
theorem S_117 : S 117 = 1290 := by dsimp [S]; rw [P_117, P_118]
theorem S_118 : S 118 = 1300 := by dsimp [S]; rw [P_118, P_119]
theorem S_119 : S 119 = 1312 := by dsimp [S]; rw [P_119, P_120]
theorem S_120 : S 120 = 1320 := by dsimp [S]; rw [P_120, P_121]
theorem S_121 : S 121 = 1334 := by dsimp [S]; rw [P_121, P_122]
theorem S_122 : S 122 = 1350 := by dsimp [S]; rw [P_122, P_123]
theorem S_123 : S 123 = 1360 := by dsimp [S]; rw [P_123, P_124]
theorem S_124 : S 124 = 1374 := by dsimp [S]; rw [P_124, P_125]
theorem S_125 : S 125 = 1392 := by dsimp [S]; rw [P_125, P_126]
theorem S_126 : S 126 = 1410 := by dsimp [S]; rw [P_126, P_127]
theorem S_127 : S 127 = 1428 := by dsimp [S]; rw [P_127, P_128]
theorem S_128 : S 128 = 1446 := by dsimp [S]; rw [P_128, P_129]
theorem S_129 : S 129 = 1460 := by dsimp [S]; rw [P_129, P_130]
theorem S_130 : S 130 = 1472 := by dsimp [S]; rw [P_130, P_131]
theorem S_131 : S 131 = 1482 := by dsimp [S]; rw [P_131, P_132]
theorem S_132 : S 132 = 1494 := by dsimp [S]; rw [P_132, P_133]
theorem S_133 : S 133 = 1508 := by dsimp [S]; rw [P_133, P_134]
theorem S_134 : S 134 = 1518 := by dsimp [S]; rw [P_134, P_135]
theorem S_135 : S 135 = 1530 := by dsimp [S]; rw [P_135, P_136]
theorem S_136 : S 136 = 1542 := by dsimp [S]; rw [P_136, P_137]
theorem S_137 : S 137 = 1560 := by dsimp [S]; rw [P_137, P_138]
theorem S_138 : S 138 = 1584 := by dsimp [S]; rw [P_138, P_139]
theorem S_139 : S 139 = 1606 := by dsimp [S]; rw [P_139, P_140]
theorem S_140 : S 140 = 1620 := by dsimp [S]; rw [P_140, P_141]
theorem S_141 : S 141 = 1632 := by dsimp [S]; rw [P_141, P_142]
theorem S_142 : S 142 = 1644 := by dsimp [S]; rw [P_142, P_143]
theorem S_143 : S 143 = 1650 := by dsimp [S]; rw [P_143, P_144]
theorem S_144 : S 144 = 1656 := by dsimp [S]; rw [P_144, P_145]
theorem S_145 : S 145 = 1668 := by dsimp [S]; rw [P_145, P_146]
theorem S_146 : S 146 = 1692 := by dsimp [S]; rw [P_146, P_147]
theorem S_147 : S 147 = 1710 := by dsimp [S]; rw [P_147, P_148]
theorem S_148 : S 148 = 1716 := by dsimp [S]; rw [P_148, P_149]
theorem S_149 : S 149 = 1722 := by dsimp [S]; rw [P_149, P_150]
theorem S_150 : S 150 = 1740 := by dsimp [S]; rw [P_150, P_151]
theorem S_151 : S 151 = 1758 := by dsimp [S]; rw [P_151, P_152]
theorem S_152 : S 152 = 1764 := by dsimp [S]; rw [P_152, P_153]
theorem S_153 : S 153 = 1770 := by dsimp [S]; rw [P_153, P_154]
theorem S_154 : S 154 = 1794 := by dsimp [S]; rw [P_154, P_155]
theorem S_155 : S 155 = 1818 := by dsimp [S]; rw [P_155, P_156]
theorem S_156 : S 156 = 1830 := by dsimp [S]; rw [P_156, P_157]
theorem S_157 : S 157 = 1848 := by dsimp [S]; rw [P_157, P_158]
theorem S_158 : S 158 = 1866 := by dsimp [S]; rw [P_158, P_159]
theorem S_159 : S 159 = 1878 := by dsimp [S]; rw [P_159, P_160]
theorem S_160 : S 160 = 1888 := by dsimp [S]; rw [P_160, P_161]
theorem S_161 : S 161 = 1900 := by dsimp [S]; rw [P_161, P_162]
theorem S_162 : S 162 = 1920 := by dsimp [S]; rw [P_162, P_163]
theorem S_163 : S 163 = 1938 := by dsimp [S]; rw [P_163, P_164]
theorem S_164 : S 164 = 1948 := by dsimp [S]; rw [P_164, P_165]
theorem S_165 : S 165 = 1960 := by dsimp [S]; rw [P_165, P_166]
theorem S_166 : S 166 = 1974 := by dsimp [S]; rw [P_166, P_167]
theorem S_167 : S 167 = 1988 := by dsimp [S]; rw [P_167, P_168]
theorem S_168 : S 168 = 2006 := by dsimp [S]; rw [P_168, P_169]
theorem S_169 : S 169 = 2022 := by dsimp [S]; rw [P_169, P_170]
theorem S_170 : S 170 = 2032 := by dsimp [S]; rw [P_170, P_171]
theorem S_171 : S 171 = 2040 := by dsimp [S]; rw [P_171, P_172]
theorem S_172 : S 172 = 2052 := by dsimp [S]; rw [P_172, P_173]
theorem S_173 : S 173 = 2064 := by dsimp [S]; rw [P_173, P_174]
theorem S_174 : S 174 = 2072 := by dsimp [S]; rw [P_174, P_175]
theorem S_175 : S 175 = 2088 := by dsimp [S]; rw [P_175, P_176]
theorem S_176 : S 176 = 2100 := by dsimp [S]; rw [P_176, P_177]
theorem S_177 : S 177 = 2112 := by dsimp [S]; rw [P_177, P_178]
theorem S_178 : S 178 = 2124 := by dsimp [S]; rw [P_178, P_179]
theorem S_179 : S 179 = 2132 := by dsimp [S]; rw [P_179, P_180]
theorem S_180 : S 180 = 2156 := by dsimp [S]; rw [P_180, P_181]
theorem S_181 : S 181 = 2178 := by dsimp [S]; rw [P_181, P_182]
theorem S_182 : S 182 = 2184 := by dsimp [S]; rw [P_182, P_183]
theorem S_183 : S 183 = 2190 := by dsimp [S]; rw [P_183, P_184]
theorem S_184 : S 184 = 2200 := by dsimp [S]; rw [P_184, P_185]
theorem S_185 : S 185 = 2212 := by dsimp [S]; rw [P_185, P_186]
theorem S_186 : S 186 = 2226 := by dsimp [S]; rw [P_186, P_187]
theorem S_187 : S 187 = 2240 := by dsimp [S]; rw [P_187, P_188]
theorem S_188 : S 188 = 2252 := by dsimp [S]; rw [P_188, P_189]
theorem S_189 : S 189 = 2280 := by dsimp [S]; rw [P_189, P_190]
theorem S_190 : S 190 = 2304 := by dsimp [S]; rw [P_190, P_191]
theorem S_191 : S 191 = 2316 := by dsimp [S]; rw [P_191, P_192]
theorem S_192 : S 192 = 2334 := by dsimp [S]; rw [P_192, P_193]
theorem S_193 : S 193 = 2352 := by dsimp [S]; rw [P_193, P_194]
theorem S_194 : S 194 = 2368 := by dsimp [S]; rw [P_194, P_195]
theorem S_195 : S 195 = 2380 := by dsimp [S]; rw [P_195, P_196]
theorem S_196 : S 196 = 2394 := by dsimp [S]; rw [P_196, P_197]
theorem S_197 : S 197 = 2414 := by dsimp [S]; rw [P_197, P_198]
theorem S_198 : S 198 = 2430 := by dsimp [S]; rw [P_198, P_199]
theorem S_199 : S 199 = 2440 := by dsimp [S]; rw [P_199, P_200]
theorem S_200 : S 200 = 2452 := by dsimp [S]; rw [P_200, P_201]
theorem S_201 : S 201 = 2460 := by dsimp [S]; rw [P_201, P_202]
theorem S_202 : S 202 = 2468 := by dsimp [S]; rw [P_202, P_203]
theorem S_203 : S 203 = 2486 := by dsimp [S]; rw [P_203, P_204]
theorem S_204 : S 204 = 2508 := by dsimp [S]; rw [P_204, P_205]
theorem S_205 : S 205 = 2536 := by dsimp [S]; rw [P_205, P_206]
theorem S_206 : S 206 = 2556 := by dsimp [S]; rw [P_206, P_207]
theorem S_207 : S 207 = 2562 := by dsimp [S]; rw [P_207, P_208]
theorem S_208 : S 208 = 2572 := by dsimp [S]; rw [P_208, P_209]
theorem S_209 : S 209 = 2580 := by dsimp [S]; rw [P_209, P_210]
theorem S_210 : S 210 = 2588 := by dsimp [S]; rw [P_210, P_211]
theorem S_211 : S 211 = 2598 := by dsimp [S]; rw [P_211, P_212]
theorem S_212 : S 212 = 2604 := by dsimp [S]; rw [P_212, P_213]
theorem S_213 : S 213 = 2610 := by dsimp [S]; rw [P_213, P_214]
theorem S_214 : S 214 = 2626 := by dsimp [S]; rw [P_214, P_215]
theorem S_215 : S 215 = 2640 := by dsimp [S]; rw [P_215, P_216]
theorem S_216 : S 216 = 2648 := by dsimp [S]; rw [P_216, P_217]
theorem S_217 : S 217 = 2688 := by dsimp [S]; rw [P_217, P_218]
theorem S_218 : S 218 = 2728 := by dsimp [S]; rw [P_218, P_219]
theorem S_219 : S 219 = 2740 := by dsimp [S]; rw [P_219, P_220]
theorem S_220 : S 220 = 2754 := by dsimp [S]; rw [P_220, P_221]
theorem S_221 : S 221 = 2780 := by dsimp [S]; rw [P_221, P_222]
theorem S_222 : S 222 = 2808 := by dsimp [S]; rw [P_222, P_223]
theorem S_223 : S 223 = 2832 := by dsimp [S]; rw [P_223, P_224]
theorem S_224 : S 224 = 2850 := by dsimp [S]; rw [P_224, P_225]
theorem S_225 : S 225 = 2856 := by dsimp [S]; rw [P_225, P_226]
theorem S_226 : S 226 = 2862 := by dsimp [S]; rw [P_226, P_227]
theorem S_227 : S 227 = 2872 := by dsimp [S]; rw [P_227, P_228]
theorem S_228 : S 228 = 2886 := by dsimp [S]; rw [P_228, P_229]

theorem A167918_29 : A167918 29 = 228 := by
  dsimp [A167918]
  have h228 : 228 ∈ { k : ℕ | k > 29 ∧ S 29 ∣ S k } := by
    simp only [mem_setOf_eq]
    refine ⟨by decide, ?_⟩
    rw [S_228, S_29]
    decide
  have h_le := Nat.sInf_le h228
  have h_ge : 228 ≤ sInf { k : ℕ | k > 29 ∧ S 29 ∣ S k } := by
    generalize h_val : sInf { k : ℕ | k > 29 ∧ S 29 ∣ S k } = val
    by_contra! hc
    have h_mem : val ∈ { k : ℕ | k > 29 ∧ S 29 ∣ S k } := h_val ▸ sInf_mem ⟨228, h228⟩
    simp only [mem_setOf_eq] at h_mem
    rcases h_mem with ⟨h_gt, h_div⟩
    interval_cases val
    · rw [S_29, S_30] at h_div; revert h_div; decide
    · rw [S_29, S_31] at h_div; revert h_div; decide
    · rw [S_29, S_32] at h_div; revert h_div; decide
    · rw [S_29, S_33] at h_div; revert h_div; decide
    · rw [S_29, S_34] at h_div; revert h_div; decide
    · rw [S_29, S_35] at h_div; revert h_div; decide
    · rw [S_29, S_36] at h_div; revert h_div; decide
    · rw [S_29, S_37] at h_div; revert h_div; decide
    · rw [S_29, S_38] at h_div; revert h_div; decide
    · rw [S_29, S_39] at h_div; revert h_div; decide
    · rw [S_29, S_40] at h_div; revert h_div; decide
    · rw [S_29, S_41] at h_div; revert h_div; decide
    · rw [S_29, S_42] at h_div; revert h_div; decide
    · rw [S_29, S_43] at h_div; revert h_div; decide
    · rw [S_29, S_44] at h_div; revert h_div; decide
    · rw [S_29, S_45] at h_div; revert h_div; decide
    · rw [S_29, S_46] at h_div; revert h_div; decide
    · rw [S_29, S_47] at h_div; revert h_div; decide
    · rw [S_29, S_48] at h_div; revert h_div; decide
    · rw [S_29, S_49] at h_div; revert h_div; decide
    · rw [S_29, S_50] at h_div; revert h_div; decide
    · rw [S_29, S_51] at h_div; revert h_div; decide
    · rw [S_29, S_52] at h_div; revert h_div; decide
    · rw [S_29, S_53] at h_div; revert h_div; decide
    · rw [S_29, S_54] at h_div; revert h_div; decide
    · rw [S_29, S_55] at h_div; revert h_div; decide
    · rw [S_29, S_56] at h_div; revert h_div; decide
    · rw [S_29, S_57] at h_div; revert h_div; decide
    · rw [S_29, S_58] at h_div; revert h_div; decide
    · rw [S_29, S_59] at h_div; revert h_div; decide
    · rw [S_29, S_60] at h_div; revert h_div; decide
    · rw [S_29, S_61] at h_div; revert h_div; decide
    · rw [S_29, S_62] at h_div; revert h_div; decide
    · rw [S_29, S_63] at h_div; revert h_div; decide
    · rw [S_29, S_64] at h_div; revert h_div; decide
    · rw [S_29, S_65] at h_div; revert h_div; decide
    · rw [S_29, S_66] at h_div; revert h_div; decide
    · rw [S_29, S_67] at h_div; revert h_div; decide
    · rw [S_29, S_68] at h_div; revert h_div; decide
    · rw [S_29, S_69] at h_div; revert h_div; decide
    · rw [S_29, S_70] at h_div; revert h_div; decide
    · rw [S_29, S_71] at h_div; revert h_div; decide
    · rw [S_29, S_72] at h_div; revert h_div; decide
    · rw [S_29, S_73] at h_div; revert h_div; decide
    · rw [S_29, S_74] at h_div; revert h_div; decide
    · rw [S_29, S_75] at h_div; revert h_div; decide
    · rw [S_29, S_76] at h_div; revert h_div; decide
    · rw [S_29, S_77] at h_div; revert h_div; decide
    · rw [S_29, S_78] at h_div; revert h_div; decide
    · rw [S_29, S_79] at h_div; revert h_div; decide
    · rw [S_29, S_80] at h_div; revert h_div; decide
    · rw [S_29, S_81] at h_div; revert h_div; decide
    · rw [S_29, S_82] at h_div; revert h_div; decide
    · rw [S_29, S_83] at h_div; revert h_div; decide
    · rw [S_29, S_84] at h_div; revert h_div; decide
    · rw [S_29, S_85] at h_div; revert h_div; decide
    · rw [S_29, S_86] at h_div; revert h_div; decide
    · rw [S_29, S_87] at h_div; revert h_div; decide
    · rw [S_29, S_88] at h_div; revert h_div; decide
    · rw [S_29, S_89] at h_div; revert h_div; decide
    · rw [S_29, S_90] at h_div; revert h_div; decide
    · rw [S_29, S_91] at h_div; revert h_div; decide
    · rw [S_29, S_92] at h_div; revert h_div; decide
    · rw [S_29, S_93] at h_div; revert h_div; decide
    · rw [S_29, S_94] at h_div; revert h_div; decide
    · rw [S_29, S_95] at h_div; revert h_div; decide
    · rw [S_29, S_96] at h_div; revert h_div; decide
    · rw [S_29, S_97] at h_div; revert h_div; decide
    · rw [S_29, S_98] at h_div; revert h_div; decide
    · rw [S_29, S_99] at h_div; revert h_div; decide
    · rw [S_29, S_100] at h_div; revert h_div; decide
    · rw [S_29, S_101] at h_div; revert h_div; decide
    · rw [S_29, S_102] at h_div; revert h_div; decide
    · rw [S_29, S_103] at h_div; revert h_div; decide
    · rw [S_29, S_104] at h_div; revert h_div; decide
    · rw [S_29, S_105] at h_div; revert h_div; decide
    · rw [S_29, S_106] at h_div; revert h_div; decide
    · rw [S_29, S_107] at h_div; revert h_div; decide
    · rw [S_29, S_108] at h_div; revert h_div; decide
    · rw [S_29, S_109] at h_div; revert h_div; decide
    · rw [S_29, S_110] at h_div; revert h_div; decide
    · rw [S_29, S_111] at h_div; revert h_div; decide
    · rw [S_29, S_112] at h_div; revert h_div; decide
    · rw [S_29, S_113] at h_div; revert h_div; decide
    · rw [S_29, S_114] at h_div; revert h_div; decide
    · rw [S_29, S_115] at h_div; revert h_div; decide
    · rw [S_29, S_116] at h_div; revert h_div; decide
    · rw [S_29, S_117] at h_div; revert h_div; decide
    · rw [S_29, S_118] at h_div; revert h_div; decide
    · rw [S_29, S_119] at h_div; revert h_div; decide
    · rw [S_29, S_120] at h_div; revert h_div; decide
    · rw [S_29, S_121] at h_div; revert h_div; decide
    · rw [S_29, S_122] at h_div; revert h_div; decide
    · rw [S_29, S_123] at h_div; revert h_div; decide
    · rw [S_29, S_124] at h_div; revert h_div; decide
    · rw [S_29, S_125] at h_div; revert h_div; decide
    · rw [S_29, S_126] at h_div; revert h_div; decide
    · rw [S_29, S_127] at h_div; revert h_div; decide
    · rw [S_29, S_128] at h_div; revert h_div; decide
    · rw [S_29, S_129] at h_div; revert h_div; decide
    · rw [S_29, S_130] at h_div; revert h_div; decide
    · rw [S_29, S_131] at h_div; revert h_div; decide
    · rw [S_29, S_132] at h_div; revert h_div; decide
    · rw [S_29, S_133] at h_div; revert h_div; decide
    · rw [S_29, S_134] at h_div; revert h_div; decide
    · rw [S_29, S_135] at h_div; revert h_div; decide
    · rw [S_29, S_136] at h_div; revert h_div; decide
    · rw [S_29, S_137] at h_div; revert h_div; decide
    · rw [S_29, S_138] at h_div; revert h_div; decide
    · rw [S_29, S_139] at h_div; revert h_div; decide
    · rw [S_29, S_140] at h_div; revert h_div; decide
    · rw [S_29, S_141] at h_div; revert h_div; decide
    · rw [S_29, S_142] at h_div; revert h_div; decide
    · rw [S_29, S_143] at h_div; revert h_div; decide
    · rw [S_29, S_144] at h_div; revert h_div; decide
    · rw [S_29, S_145] at h_div; revert h_div; decide
    · rw [S_29, S_146] at h_div; revert h_div; decide
    · rw [S_29, S_147] at h_div; revert h_div; decide
    · rw [S_29, S_148] at h_div; revert h_div; decide
    · rw [S_29, S_149] at h_div; revert h_div; decide
    · rw [S_29, S_150] at h_div; revert h_div; decide
    · rw [S_29, S_151] at h_div; revert h_div; decide
    · rw [S_29, S_152] at h_div; revert h_div; decide
    · rw [S_29, S_153] at h_div; revert h_div; decide
    · rw [S_29, S_154] at h_div; revert h_div; decide
    · rw [S_29, S_155] at h_div; revert h_div; decide
    · rw [S_29, S_156] at h_div; revert h_div; decide
    · rw [S_29, S_157] at h_div; revert h_div; decide
    · rw [S_29, S_158] at h_div; revert h_div; decide
    · rw [S_29, S_159] at h_div; revert h_div; decide
    · rw [S_29, S_160] at h_div; revert h_div; decide
    · rw [S_29, S_161] at h_div; revert h_div; decide
    · rw [S_29, S_162] at h_div; revert h_div; decide
    · rw [S_29, S_163] at h_div; revert h_div; decide
    · rw [S_29, S_164] at h_div; revert h_div; decide
    · rw [S_29, S_165] at h_div; revert h_div; decide
    · rw [S_29, S_166] at h_div; revert h_div; decide
    · rw [S_29, S_167] at h_div; revert h_div; decide
    · rw [S_29, S_168] at h_div; revert h_div; decide
    · rw [S_29, S_169] at h_div; revert h_div; decide
    · rw [S_29, S_170] at h_div; revert h_div; decide
    · rw [S_29, S_171] at h_div; revert h_div; decide
    · rw [S_29, S_172] at h_div; revert h_div; decide
    · rw [S_29, S_173] at h_div; revert h_div; decide
    · rw [S_29, S_174] at h_div; revert h_div; decide
    · rw [S_29, S_175] at h_div; revert h_div; decide
    · rw [S_29, S_176] at h_div; revert h_div; decide
    · rw [S_29, S_177] at h_div; revert h_div; decide
    · rw [S_29, S_178] at h_div; revert h_div; decide
    · rw [S_29, S_179] at h_div; revert h_div; decide
    · rw [S_29, S_180] at h_div; revert h_div; decide
    · rw [S_29, S_181] at h_div; revert h_div; decide
    · rw [S_29, S_182] at h_div; revert h_div; decide
    · rw [S_29, S_183] at h_div; revert h_div; decide
    · rw [S_29, S_184] at h_div; revert h_div; decide
    · rw [S_29, S_185] at h_div; revert h_div; decide
    · rw [S_29, S_186] at h_div; revert h_div; decide
    · rw [S_29, S_187] at h_div; revert h_div; decide
    · rw [S_29, S_188] at h_div; revert h_div; decide
    · rw [S_29, S_189] at h_div; revert h_div; decide
    · rw [S_29, S_190] at h_div; revert h_div; decide
    · rw [S_29, S_191] at h_div; revert h_div; decide
    · rw [S_29, S_192] at h_div; revert h_div; decide
    · rw [S_29, S_193] at h_div; revert h_div; decide
    · rw [S_29, S_194] at h_div; revert h_div; decide
    · rw [S_29, S_195] at h_div; revert h_div; decide
    · rw [S_29, S_196] at h_div; revert h_div; decide
    · rw [S_29, S_197] at h_div; revert h_div; decide
    · rw [S_29, S_198] at h_div; revert h_div; decide
    · rw [S_29, S_199] at h_div; revert h_div; decide
    · rw [S_29, S_200] at h_div; revert h_div; decide
    · rw [S_29, S_201] at h_div; revert h_div; decide
    · rw [S_29, S_202] at h_div; revert h_div; decide
    · rw [S_29, S_203] at h_div; revert h_div; decide
    · rw [S_29, S_204] at h_div; revert h_div; decide
    · rw [S_29, S_205] at h_div; revert h_div; decide
    · rw [S_29, S_206] at h_div; revert h_div; decide
    · rw [S_29, S_207] at h_div; revert h_div; decide
    · rw [S_29, S_208] at h_div; revert h_div; decide
    · rw [S_29, S_209] at h_div; revert h_div; decide
    · rw [S_29, S_210] at h_div; revert h_div; decide
    · rw [S_29, S_211] at h_div; revert h_div; decide
    · rw [S_29, S_212] at h_div; revert h_div; decide
    · rw [S_29, S_213] at h_div; revert h_div; decide
    · rw [S_29, S_214] at h_div; revert h_div; decide
    · rw [S_29, S_215] at h_div; revert h_div; decide
    · rw [S_29, S_216] at h_div; revert h_div; decide
    · rw [S_29, S_217] at h_div; revert h_div; decide
    · rw [S_29, S_218] at h_div; revert h_div; decide
    · rw [S_29, S_219] at h_div; revert h_div; decide
    · rw [S_29, S_220] at h_div; revert h_div; decide
    · rw [S_29, S_221] at h_div; revert h_div; decide
    · rw [S_29, S_222] at h_div; revert h_div; decide
    · rw [S_29, S_223] at h_div; revert h_div; decide
    · rw [S_29, S_224] at h_div; revert h_div; decide
    · rw [S_29, S_225] at h_div; revert h_div; decide
    · rw [S_29, S_226] at h_div; revert h_div; decide
    · rw [S_29, S_227] at h_div; revert h_div; decide
  omega

theorem A167918_ratio_29 : A167918_ratio 29 = 13 := by
  dsimp [A167918_ratio]
  rw [A167918_29]
  rw [S_228, S_29]


theorem P_lt_P {i j : ℕ} (h1 : 1 ≤ i) (h2 : i < j) : P i < P j := by
  dsimp [P]
  rw [Nat.nth_lt_nth Nat.infinite_setOf_prime]
  omega

theorem S_lt_S {i j : ℕ} (h1 : 1 ≤ i) (h2 : i < j) : S i < S j := by
  dsimp [S]
  have h3 : P i < P j := P_lt_P h1 h2
  have h4 : P (i + 1) < P (j + 1) := P_lt_P (by omega) (by omega)
  omega


lemma P_succ_le_two_mul (k : ℕ) (hk : k ≥ 1) : P (k + 1) ≤ 2 * P k := by
  have hP_pos : P k ≠ 0 := by
    dsimp [P]
    have h_prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (k - 1)
    exact Nat.Prime.ne_zero h_prime
  obtain ⟨p, hp, h_gt, h_le⟩ := exists_prime_lt_and_le_two_mul (P k) hP_pos
  have h_next : P (k + 1) ≤ p := by
    by_contra! h_lt
    dsimp [P] at h_lt
    have h_rew : k = k - 1 + 1 := (Nat.sub_add_cancel hk).symm
    rw [h_rew] at h_lt
    have h_le := Nat.le_nth_of_lt_nth_succ h_lt hp
    change p ≤ P k at h_le
    omega
  exact le_trans h_next h_le

lemma S_succ_le_two_mul (k : ℕ) (hk : k ≥ 1) : S (k + 1) ≤ 2 * S k := by
  dsimp [S]
  have h1 := P_succ_le_two_mul (k + 1) (by omega)
  have h2 := P_succ_le_two_mul k hk
  omega

lemma P_ge_three (k : ℕ) (hk : k ≥ 2) : P k ≥ 3 := by
  have h_le : P 2 ≤ P k := by
    by_cases h_eq : k = 2
    · rw [h_eq]
    · have h_lt : 2 < k := by omega
      have h_lt_P := P_lt_P (by decide) h_lt
      omega
  rw [P_2] at h_le
  omega

lemma P_odd (k : ℕ) (hk : k ≥ 2) : P k % 2 = 1 := by
  have h_prime : Nat.Prime (P k) := by
    dsimp [P]
    exact nth_mem_of_infinite Nat.infinite_setOf_prime (k - 1)
  have h_gt : P k > 2 := by
    have h3 := P_ge_three k hk
    omega
  rcases h_prime.eq_two_or_odd with h2 | h_odd
  · omega
  · exact h_odd

lemma S_even (k : ℕ) (hk : k ≥ 2) : S k % 2 = 0 := by
  dsimp [S]
  have h1 := P_odd k hk
  have h2 := P_odd (k + 1) (by omega)
  omega

lemma prime_factor_le_P (k : ℕ) (hk : k ≥ 2) (q : ℕ) (hq : Nat.Prime q) (hdvd : q ∣ S k) : q ≤ P (k + 1) := by
  have h_S_gt : S k > 0 := by
    dsimp [S]
    have h1 := P_ge_three k hk
    omega
  have h_le_S : q ≤ S k := Nat.le_of_dvd h_S_gt hdvd
  have h_lt_S : S k < 2 * P (k + 1) := by
    dsimp [S]
    have h_lt := P_lt_P (by omega) (by omega : k < k + 1)
    omega
  by_contra! h_gt
  have h_lt_2q : S k < 2 * q := by omega
  rcases hdvd with ⟨m, hm⟩
  have hm_pos : m > 0 := by
    by_contra! hm0
    have hm_eq0 : m = 0 := by omega
    rw [hm_eq0, mul_zero] at hm
    omega
  have hm_lt_2 : m < 2 := by
    by_contra!
    have h_mul : q * 2 ≤ q * m := Nat.mul_le_mul_left q this
    have : S k ≥ 2 * q := by
      rw [hm]
      omega
    omega
  have hm1 : m = 1 := by omega
  rw [hm1, mul_one] at hm
  -- Now we have S k = q
  have h_even : S k % 2 = 0 := S_even k hk
  have h_q_odd : q % 2 = 1 := by
    have h_q_gt : q > 2 := by
      have h3 := P_ge_three (k + 1) (by omega)
      omega
    rcases hq.eq_two_or_odd with rfl | h_odd
    · omega
    · exact h_odd
  rw [hm] at h_even
  omega



lemma S_not_dvd_S_succ (n : ℕ) (hn : n ≥ 2) : ¬ S n ∣ S (n + 1) := by
  intro h
  have h_gt : S (n + 1) > S n := S_lt_S (by omega) (by omega)
  have h_le : 2 * S n ≤ S (n + 1) := by
    rcases h with ⟨m, hm⟩
    have hm2 : m ≥ 2 := by
      by_contra! hm_lt
      interval_cases m
      · rw [mul_zero] at hm; omega
      · rw [mul_one] at hm; omega
    have hm_eq : S (n + 1) = m * S n := by rw [hm, mul_comm]
    have : 2 * S n ≤ m * S n := Nat.mul_le_mul_right (S n) hm2
    omega
  have h_P : P (n + 1 + 1) ≥ 2 * P n + P (n + 1) := by
    dsimp [S] at h_le
    omega
  have h_bet2 := P_succ_le_two_mul (n + 1) (by omega)
  have h_le2 : 2 * P n ≤ P (n + 1) := by omega
  have h_bet1 := P_succ_le_two_mul n (by omega)
  have h_eq : P (n + 1) = 2 * P n := by omega
  have h_prime : Nat.Prime (P (n + 1)) := by
    dsimp [P]
    exact nth_mem_of_infinite Nat.infinite_setOf_prime (n + 1 - 1)
  have h_ge3 : P n ≥ 3 := P_ge_three n hn
  have h_not_prime : ¬ Nat.Prime (2 * P n) := by
    intro hp2
    rcases hp2.eq_two_or_odd with h_two | h_odd
    · omega
    · have h_even : (2 * P n) % 2 = 0 := by omega
      omega
  rw [h_eq] at h_prime
  contradiction

theorem oeis_A167918_conjecture_5a.disproof :
  ¬ ∃ C : ℕ, ∀ n : ℕ, n > 0 → A167918_ratio n ≤ C := by
  intro h
  rcases h with ⟨C, hC⟩
  have h29 : A167918_ratio 29 ≤ C := hC 29 (by decide)
  rw [A167918_ratio_29] at h29
  -- We have 13 ≤ C.
  -- Test comment
  sorry
