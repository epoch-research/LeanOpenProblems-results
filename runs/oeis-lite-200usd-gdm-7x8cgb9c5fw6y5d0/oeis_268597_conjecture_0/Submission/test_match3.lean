import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option maxHeartbeats 0

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

lemma n_eq_of_sub_eq {n start k : ℕ} (h1 : n ≥ start) (h2 : n - start = k) : n = start + k := by
  omega

lemma solve_interval_0_99 (n : ℕ) (h : n < 100) : A268597 n > 0 := by
  match n with
  | 0 => exact solve_concrete 0 1 (by decide) (by rfl)
  | 1 => exact solve_concrete 1 4 (by decide) (by rfl)
  | 2 => exact solve_concrete 2 9 (by decide) (by rfl)
  | 3 => exact solve_concrete 3 8 (by decide) (by rfl)
  | 4 => exact solve_concrete 4 25 (by decide) (by rfl)
  | 5 => exact solve_concrete 5 18 (by decide) (by rfl)
  | 6 => exact solve_concrete 6 15 (by decide) (by rfl)
  | 7 => exact solve_concrete 7 16 (by decide) (by rfl)
  | 8 => exact solve_concrete 8 21 (by decide) (by rfl)
  | 9 => exact solve_concrete 9 50 (by decide) (by rfl)
  | 10 => exact solve_concrete 10 35 (by decide) (by rfl)
  | 11 => exact solve_concrete 11 36 (by decide) (by rfl)
  | 12 => exact solve_concrete 12 33 (by decide) (by rfl)
  | 13 => exact solve_concrete 13 98 (by decide) (by rfl)
  | 14 => exact solve_concrete 14 39 (by decide) (by rfl)
  | 15 => exact solve_concrete 15 32 (by decide) (by rfl)
  | 16 => exact solve_concrete 16 65 (by decide) (by rfl)
  | 17 => exact solve_concrete 17 54 (by decide) (by rfl)
  | 18 => exact solve_concrete 18 51 (by decide) (by rfl)
  | 19 => exact solve_concrete 19 100 (by decide) (by rfl)
  | 20 => exact solve_concrete 20 45 (by decide) (by rfl)
  | 21 => exact solve_concrete 21 70 (by decide) (by rfl)
  | 22 => exact solve_concrete 22 95 (by decide) (by rfl)
  | 23 => exact solve_concrete 23 72 (by decide) (by rfl)
  | 24 => exact solve_concrete 24 69 (by decide) (by rfl)
  | 25 => exact solve_concrete 25 338 (by decide) (by rfl)
  | 26 => exact solve_concrete 26 63 (by decide) (by rfl)
  | 27 => exact solve_concrete 27 196 (by decide) (by rfl)
  | 28 => exact solve_concrete 28 161 (by decide) (by rfl)
  | 29 => exact solve_concrete 29 110 (by decide) (by rfl)
  | 30 => exact solve_concrete 30 87 (by decide) (by rfl)
  | 31 => exact solve_concrete 31 64 (by decide) (by rfl)
  | 32 => exact solve_concrete 32 93 (by decide) (by rfl)
  | 33 => exact solve_concrete 33 130 (by decide) (by rfl)
  | 34 => exact solve_concrete 34 75 (by decide) (by rfl)
  | 35 => exact solve_concrete 35 108 (by decide) (by rfl)
  | 36 => exact solve_concrete 36 217 (by decide) (by rfl)
  | 37 => exact solve_concrete 37 182 (by decide) (by rfl)
  | 38 => exact solve_concrete 38 99 (by decide) (by rfl)
  | 39 => exact solve_concrete 39 200 (by decide) (by rfl)
  | 40 => exact solve_concrete 40 185 (by decide) (by rfl)
  | 41 => exact solve_concrete 41 170 (by decide) (by rfl)
  | 42 => exact solve_concrete 42 123 (by decide) (by rfl)
  | 43 => exact solve_concrete 43 140 (by decide) (by rfl)
  | 44 => exact solve_concrete 44 117 (by decide) (by rfl)
  | 45 => exact solve_concrete 45 190 (by decide) (by rfl)
  | 46 => exact solve_concrete 46 215 (by decide) (by rfl)
  | 47 => exact solve_concrete 47 144 (by decide) (by rfl)
  | 48 => exact solve_concrete 48 141 (by decide) (by rfl)
  | 49 => exact solve_concrete 49 250 (by decide) (by rfl)
  | 50 => exact solve_concrete 50 235 (by decide) (by rfl)
  | 51 => exact solve_concrete 51 676 (by decide) (by rfl)
  | 52 => exact solve_concrete 52 329 (by decide) (by rfl)
  | 53 => exact solve_concrete 53 162 (by decide) (by rfl)
  | 54 => exact solve_concrete 54 159 (by decide) (by rfl)
  | 55 => exact solve_concrete 55 392 (by decide) (by rfl)
  | 56 => exact solve_concrete 56 153 (by decide) (by rfl)
  | 57 => exact solve_concrete 57 322 (by decide) (by rfl)
  | 58 => exact solve_concrete 58 371 (by decide) (by rfl)
  | 59 => exact solve_concrete 59 220 (by decide) (by rfl)
  | 60 => exact solve_concrete 60 177 (by decide) (by rfl)
  | 61 => exact solve_concrete 61 494 (by decide) (by rfl)
  | 62 => exact solve_concrete 62 135 (by decide) (by rfl)
  | 63 => exact solve_concrete 63 128 (by decide) (by rfl)
  | 64 => exact solve_concrete 64 305 (by decide) (by rfl)
  | 65 => exact solve_concrete 65 290 (by decide) (by rfl)
  | 66 => exact solve_concrete 66 427 (by decide) (by rfl)
  | 67 => exact solve_concrete 67 260 (by decide) (by rfl)
  | 68 => exact solve_concrete 68 201 (by decide) (by rfl)
  | 69 => exact solve_concrete 69 310 (by decide) (by rfl)
  | 70 => exact solve_concrete 70 335 (by decide) (by rfl)
  | 71 => exact solve_concrete 71 216 (by decide) (by rfl)
  | 72 => exact solve_concrete 72 213 (by decide) (by rfl)
  | 73 => exact solve_concrete 73 434 (by decide) (by rfl)
  | 74 => exact solve_concrete 74 207 (by decide) (by rfl)
  | 75 => exact solve_concrete 75 364 (by decide) (by rfl)
  | 76 => exact solve_concrete 76 245 (by decide) (by rfl)
  | 77 => exact solve_concrete 77 638 (by decide) (by rfl)
  | 78 => exact solve_concrete 78 511 (by decide) (by rfl)
  | 79 => exact solve_concrete 79 400 (by decide) (by rfl)
  | 80 => exact solve_concrete 80 189 (by decide) (by rfl)
  | 81 => exact solve_concrete 81 370 (by decide) (by rfl)
  | 82 => exact solve_concrete 82 395 (by decide) (by rfl)
  | 83 => exact solve_concrete 83 340 (by decide) (by rfl)
  | 84 => exact solve_concrete 84 249 (by decide) (by rfl)
  | 85 => exact solve_concrete 85 518 (by decide) (by rfl)
  | 86 => exact solve_concrete 86 415 (by decide) (by rfl)
  | 87 => exact solve_concrete 87 280 (by decide) (by rfl)
  | 88 => exact solve_concrete 88 581 (by decide) (by rfl)
  | 89 => exact solve_concrete 89 410 (by decide) (by rfl)
  | 90 => exact solve_concrete 90 267 (by decide) (by rfl)
  | 91 => exact solve_concrete 91 380 (by decide) (by rfl)
  | 92 => exact solve_concrete 92 261 (by decide) (by rfl)
  | 93 => exact solve_concrete 93 430 (by decide) (by rfl)
  | 94 => exact solve_concrete 94 623 (by decide) (by rfl)
  | 95 => exact solve_concrete 95 288 (by decide) (by rfl)
  | 96 => exact solve_concrete 96 1501 (by decide) (by rfl)
  | 97 => exact solve_concrete 97 602 (by decide) (by rfl)
  | 98 => exact solve_concrete 98 279 (by decide) (by rfl)
  | 99 => exact solve_concrete 99 500 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_100_199 (n : ℕ) (h1 : n ≥ 100) (h2 : n < 200) : A268597 n > 0 := by
  have h : n - 100 < 100 := by omega
  generalize h_k : n - 100 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 100 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 100 485 (by decide) (by rfl)
  | 1 =>
    have hn : n = 100 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 101 462 (by decide) (by rfl)
  | 2 =>
    have hn : n = 100 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 102 303 (by decide) (by rfl)
  | 3 =>
    have hn : n = 100 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 103 1352 (by decide) (by rfl)
  | 4 =>
    have hn : n = 100 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 104 225 (by decide) (by rfl)
  | 5 =>
    have hn : n = 100 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 105 658 (by decide) (by rfl)
  | 6 =>
    have hn : n = 100 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 106 515 (by decide) (by rfl)
  | 7 =>
    have hn : n = 100 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 107 324 (by decide) (by rfl)
  | 8 =>
    have hn : n = 100 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 108 321 (by decide) (by rfl)
  | 9 =>
    have hn : n = 100 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 109 350 (by decide) (by rfl)
  | 10 =>
    have hn : n = 100 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 110 231 (by decide) (by rfl)
  | 11 =>
    have hn : n = 100 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 111 784 (by decide) (by rfl)
  | 12 =>
    have hn : n = 100 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 112 545 (by decide) (by rfl)
  | 13 =>
    have hn : n = 100 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 113 530 (by decide) (by rfl)
  | 14 =>
    have hn : n = 100 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 114 339 (by decide) (by rfl)
  | 15 =>
    have hn : n = 100 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 115 644 (by decide) (by rfl)
  | 16 =>
    have hn : n = 100 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 116 297 (by decide) (by rfl)
  | 17 =>
    have hn : n = 100 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 117 742 (by decide) (by rfl)
  | 18 =>
    have hn : n = 100 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 118 539 (by decide) (by rfl)
  | 19 =>
    have hn : n = 100 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 119 440 (by decide) (by rfl)
  | 20 =>
    have hn : n = 100 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 120 1331 (by decide) (by rfl)
  | 21 =>
    have hn : n = 100 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 121 1634 (by decide) (by rfl)
  | 22 =>
    have hn : n = 100 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 122 1243 (by decide) (by rfl)
  | 23 =>
    have hn : n = 100 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 123 988 (by decide) (by rfl)
  | 24 =>
    have hn : n = 100 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 124 625 (by decide) (by rfl)
  | 25 =>
    have hn : n = 100 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 125 510 (by decide) (by rfl)
  | 26 =>
    have hn : n = 100 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 126 255 (by decide) (by rfl)
  | 27 =>
    have hn : n = 100 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 127 256 (by decide) (by rfl)
  | 28 =>
    have hn : n = 100 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 128 273 (by decide) (by rfl)
  | 29 =>
    have hn : n = 100 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 129 610 (by decide) (by rfl)
  | 30 =>
    have hn : n = 100 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 130 635 (by decide) (by rfl)
  | 31 =>
    have hn : n = 100 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 131 580 (by decide) (by rfl)
  | 32 =>
    have hn : n = 100 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 132 393 (by decide) (by rfl)
  | 33 =>
    have hn : n = 100 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 133 854 (by decide) (by rfl)
  | 34 =>
    have hn : n = 100 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 134 351 (by decide) (by rfl)
  | 35 =>
    have hn : n = 100 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 135 520 (by decide) (by rfl)
  | 36 =>
    have hn : n = 100 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 136 917 (by decide) (by rfl)
  | 37 =>
    have hn : n = 100 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 137 570 (by decide) (by rfl)
  | 38 =>
    have hn : n = 100 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 138 411 (by decide) (by rfl)
  | 39 =>
    have hn : n = 100 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 139 620 (by decide) (by rfl)
  | 40 =>
    have hn : n = 100 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 140 285 (by decide) (by rfl)
  | 41 =>
    have hn : n = 100 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 141 670 (by decide) (by rfl)
  | 42 =>
    have hn : n = 100 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 142 363 (by decide) (by rfl)
  | 43 =>
    have hn : n = 100 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 143 432 (by decide) (by rfl)
  | 44 =>
    have hn : n = 100 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 144 385 (by decide) (by rfl)
  | 45 =>
    have hn : n = 100 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 145 938 (by decide) (by rfl)
  | 46 =>
    have hn : n = 100 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 146 423 (by decide) (by rfl)
  | 47 =>
    have hn : n = 100 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 147 868 (by decide) (by rfl)
  | 48 =>
    have hn : n = 100 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 148 1529 (by decide) (by rfl)
  | 49 =>
    have hn : n = 100 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 149 550 (by decide) (by rfl)
  | 50 =>
    have hn : n = 100 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 150 447 (by decide) (by rfl)
  | 51 =>
    have hn : n = 100 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 151 728 (by decide) (by rfl)
  | 52 =>
    have hn : n = 100 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 152 453 (by decide) (by rfl)
  | 53 =>
    have hn : n = 100 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 153 490 (by decide) (by rfl)
  | 54 =>
    have hn : n = 100 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 154 755 (by decide) (by rfl)
  | 55 =>
    have hn : n = 100 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 155 1276 (by decide) (by rfl)
  | 56 =>
    have hn : n = 100 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 156 1057 (by decide) (by rfl)
  | 57 =>
    have hn : n = 100 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 157 1022 (by decide) (by rfl)
  | 58 =>
    have hn : n = 100 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 158 471 (by decide) (by rfl)
  | 59 =>
    have hn : n = 100 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 159 800 (by decide) (by rfl)
  | 60 =>
    have hn : n = 100 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 160 785 (by decide) (by rfl)
  | 61 =>
    have hn : n = 100 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 161 486 (by decide) (by rfl)
  | 62 =>
    have hn : n = 100 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 162 1099 (by decide) (by rfl)
  | 63 =>
    have hn : n = 100 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 163 740 (by decide) (by rfl)
  | 64 =>
    have hn : n = 100 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 164 357 (by decide) (by rfl)
  | 65 =>
    have hn : n = 100 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 165 790 (by decide) (by rfl)
  | 66 =>
    have hn : n = 100 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 166 455 (by decide) (by rfl)
  | 67 =>
    have hn : n = 100 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 167 680 (by decide) (by rfl)
  | 68 =>
    have hn : n = 100 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 168 345 (by decide) (by rfl)
  | 69 =>
    have hn : n = 100 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 169 650 (by decide) (by rfl)
  | 70 =>
    have hn : n = 100 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 170 459 (by decide) (by rfl)
  | 71 =>
    have hn : n = 100 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 171 1036 (by decide) (by rfl)
  | 72 =>
    have hn : n = 100 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 172 1169 (by decide) (by rfl)
  | 73 =>
    have hn : n = 100 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 173 830 (by decide) (by rfl)
  | 74 =>
    have hn : n = 100 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 174 375 (by decide) (by rfl)
  | 75 =>
    have hn : n = 100 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 175 560 (by decide) (by rfl)
  | 76 =>
    have hn : n = 100 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 176 865 (by decide) (by rfl)
  | 77 =>
    have hn : n = 100 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 177 1162 (by decide) (by rfl)
  | 78 =>
    have hn : n = 100 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 178 1211 (by decide) (by rfl)
  | 79 =>
    have hn : n = 100 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 179 820 (by decide) (by rfl)
  | 80 =>
    have hn : n = 100 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 180 537 (by decide) (by rfl)
  | 81 =>
    have hn : n = 100 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 181 2054 (by decide) (by rfl)
  | 82 =>
    have hn : n = 100 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 182 399 (by decide) (by rfl)
  | 83 =>
    have hn : n = 100 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 183 760 (by decide) (by rfl)
  | 84 =>
    have hn : n = 100 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 184 905 (by decide) (by rfl)
  | 85 =>
    have hn : n = 100 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 185 890 (by decide) (by rfl)
  | 86 =>
    have hn : n = 100 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 186 847 (by decide) (by rfl)
  | 87 =>
    have hn : n = 100 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 187 860 (by decide) (by rfl)
  | 88 =>
    have hn : n = 100 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 188 405 (by decide) (by rfl)
  | 89 =>
    have hn : n = 100 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 189 1246 (by decide) (by rfl)
  | 90 =>
    have hn : n = 100 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 190 1991 (by decide) (by rfl)
  | 91 =>
    have hn : n = 100 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 191 576 (by decide) (by rfl)
  | 92 =>
    have hn : n = 100 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 192 573 (by decide) (by rfl)
  | 93 =>
    have hn : n = 100 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 193 3002 (by decide) (by rfl)
  | 94 =>
    have hn : n = 100 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 194 507 (by decide) (by rfl)
  | 95 =>
    have hn : n = 100 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 195 1204 (by decide) (by rfl)
  | 96 =>
    have hn : n = 100 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 196 965 (by decide) (by rfl)
  | 97 =>
    have hn : n = 100 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 197 870 (by decide) (by rfl)
  | 98 =>
    have hn : n = 100 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 198 591 (by decide) (by rfl)
  | 99 =>
    have hn : n = 100 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 199 1000 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_200_299 (n : ℕ) (h1 : n ≥ 200) (h2 : n < 300) : A268597 n > 0 := by
  have h : n - 200 < 100 := by omega
  generalize h_k : n - 200 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 200 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 200 597 (by decide) (by rfl)
  | 1 =>
    have hn : n = 200 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 201 970 (by decide) (by rfl)
  | 2 =>
    have hn : n = 200 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 202 995 (by decide) (by rfl)
  | 3 =>
    have hn : n = 200 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 203 924 (by decide) (by rfl)
  | 4 =>
    have hn : n = 200 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 204 925 (by decide) (by rfl)
  | 5 =>
    have hn : n = 200 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 205 1358 (by decide) (by rfl)
  | 6 =>
    have hn : n = 200 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 206 603 (by decide) (by rfl)
  | 7 =>
    have hn : n = 200 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 207 2704 (by decide) (by rfl)
  | 8 =>
    have hn : n = 200 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 208 2189 (by decide) (by rfl)
  | 9 =>
    have hn : n = 200 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 209 850 (by decide) (by rfl)
  | 10 =>
    have hn : n = 200 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 210 435 (by decide) (by rfl)
  | 11 =>
    have hn : n = 200 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 211 1316 (by decide) (by rfl)
  | 12 =>
    have hn : n = 200 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 212 633 (by decide) (by rfl)
  | 13 =>
    have hn : n = 200 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 213 1030 (by decide) (by rfl)
  | 14 =>
    have hn : n = 200 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 214 1055 (by decide) (by rfl)
  | 15 =>
    have hn : n = 200 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 215 648 (by decide) (by rfl)
  | 16 =>
    have hn : n = 200 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 216 1477 (by decide) (by rfl)
  | 17 =>
    have hn : n = 200 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 217 1442 (by decide) (by rfl)
  | 18 =>
    have hn : n = 200 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 218 483 (by decide) (by rfl)
  | 19 =>
    have hn : n = 200 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 219 700 (by decide) (by rfl)
  | 20 =>
    have hn : n = 200 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 220 845 (by decide) (by rfl)
  | 21 =>
    have hn : n = 200 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 221 1070 (by decide) (by rfl)
  | 22 =>
    have hn : n = 200 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 222 2743 (by decide) (by rfl)
  | 23 =>
    have hn : n = 200 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 223 1568 (by decide) (by rfl)
  | 24 =>
    have hn : n = 200 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 224 465 (by decide) (by rfl)
  | 25 =>
    have hn : n = 200 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 225 1090 (by decide) (by rfl)
  | 26 =>
    have hn : n = 200 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 226 1115 (by decide) (by rfl)
  | 27 =>
    have hn : n = 200 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 227 1060 (by decide) (by rfl)
  | 28 =>
    have hn : n = 200 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 228 681 (by decide) (by rfl)
  | 29 =>
    have hn : n = 200 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 229 950 (by decide) (by rfl)
  | 30 =>
    have hn : n = 200 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 230 687 (by decide) (by rfl)
  | 31 =>
    have hn : n = 200 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 231 1288 (by decide) (by rfl)
  | 32 =>
    have hn : n = 200 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 232 665 (by decide) (by rfl)
  | 33 =>
    have hn : n = 200 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 233 1130 (by decide) (by rfl)
  | 34 =>
    have hn : n = 200 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 234 699 (by decide) (by rfl)
  | 35 =>
    have hn : n = 200 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 235 1484 (by decide) (by rfl)
  | 36 =>
    have hn : n = 200 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 236 1165 (by decide) (by rfl)
  | 37 =>
    have hn : n = 200 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 237 1078 (by decide) (by rfl)
  | 38 =>
    have hn : n = 200 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 238 1631 (by decide) (by rfl)
  | 39 =>
    have hn : n = 200 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 239 880 (by decide) (by rfl)
  | 40 =>
    have hn : n = 200 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 240 561 (by decide) (by rfl)
  | 41 =>
    have hn : n = 200 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 241 2662 (by decide) (by rfl)
  | 42 =>
    have hn : n = 200 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 242 567 (by decide) (by rfl)
  | 43 =>
    have hn : n = 200 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 243 3268 (by decide) (by rfl)
  | 44 =>
    have hn : n = 200 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 244 1205 (by decide) (by rfl)
  | 45 =>
    have hn : n = 200 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 245 1110 (by decide) (by rfl)
  | 46 =>
    have hn : n = 200 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 246 1183 (by decide) (by rfl)
  | 47 =>
    have hn : n = 200 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 247 1976 (by decide) (by rfl)
  | 48 =>
    have hn : n = 200 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 248 1785 (by decide) (by rfl)
  | 49 =>
    have hn : n = 200 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 249 1250 (by decide) (by rfl)
  | 50 =>
    have hn : n = 200 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 250 2651 (by decide) (by rfl)
  | 51 =>
    have hn : n = 200 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 251 1020 (by decide) (by rfl)
  | 52 =>
    have hn : n = 200 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 252 753 (by decide) (by rfl)
  | 53 =>
    have hn : n = 200 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 253 4142 (by decide) (by rfl)
  | 54 =>
    have hn : n = 200 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 254 747 (by decide) (by rfl)
  | 55 =>
    have hn : n = 200 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 255 512 (by decide) (by rfl)
  | 56 =>
    have hn : n = 200 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 256 1757 (by decide) (by rfl)
  | 57 =>
    have hn : n = 200 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 257 1554 (by decide) (by rfl)
  | 58 =>
    have hn : n = 200 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 258 771 (by decide) (by rfl)
  | 59 =>
    have hn : n = 200 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 259 1220 (by decide) (by rfl)
  | 60 =>
    have hn : n = 200 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 260 1285 (by decide) (by rfl)
  | 61 =>
    have hn : n = 200 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 261 1270 (by decide) (by rfl)
  | 62 =>
    have hn : n = 200 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 262 1799 (by decide) (by rfl)
  | 63 =>
    have hn : n = 200 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 263 1160 (by decide) (by rfl)
  | 64 =>
    have hn : n = 200 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 264 789 (by decide) (by rfl)
  | 65 =>
    have hn : n = 200 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 265 1274 (by decide) (by rfl)
  | 66 =>
    have hn : n = 200 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 266 555 (by decide) (by rfl)
  | 67 =>
    have hn : n = 200 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 267 1708 (by decide) (by rfl)
  | 68 =>
    have hn : n = 200 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 268 1841 (by decide) (by rfl)
  | 69 =>
    have hn : n = 200 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 269 1150 (by decide) (by rfl)
  | 70 =>
    have hn : n = 200 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 270 807 (by decide) (by rfl)
  | 71 =>
    have hn : n = 200 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 271 1040 (by decide) (by rfl)
  | 72 =>
    have hn : n = 200 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 272 609 (by decide) (by rfl)
  | 73 =>
    have hn : n = 200 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 273 1834 (by decide) (by rfl)
  | 74 =>
    have hn : n = 200 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 274 875 (by decide) (by rfl)
  | 75 =>
    have hn : n = 200 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 275 1140 (by decide) (by rfl)
  | 76 =>
    have hn : n = 200 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 276 805 (by decide) (by rfl)
  | 77 =>
    have hn : n = 200 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 277 3302 (by decide) (by rfl)
  | 78 =>
    have hn : n = 200 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 278 663 (by decide) (by rfl)
  | 79 =>
    have hn : n = 200 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 279 1240 (by decide) (by rfl)
  | 80 =>
    have hn : n = 200 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 280 1001 (by decide) (by rfl)
  | 81 =>
    have hn : n = 200 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 281 1290 (by decide) (by rfl)
  | 82 =>
    have hn : n = 200 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 282 843 (by decide) (by rfl)
  | 83 =>
    have hn : n = 200 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 283 1340 (by decide) (by rfl)
  | 84 =>
    have hn : n = 200 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 284 849 (by decide) (by rfl)
  | 85 =>
    have hn : n = 200 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 285 1390 (by decide) (by rfl)
  | 86 =>
    have hn : n = 200 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 286 1415 (by decide) (by rfl)
  | 87 =>
    have hn : n = 200 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 287 864 (by decide) (by rfl)
  | 88 =>
    have hn : n = 200 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 288 1981 (by decide) (by rfl)
  | 89 =>
    have hn : n = 200 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 289 1946 (by decide) (by rfl)
  | 90 =>
    have hn : n = 200 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 290 651 (by decide) (by rfl)
  | 91 =>
    have hn : n = 200 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 291 1876 (by decide) (by rfl)
  | 92 =>
    have hn : n = 200 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 292 3113 (by decide) (by rfl)
  | 93 =>
    have hn : n = 200 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 293 1806 (by decide) (by rfl)
  | 94 =>
    have hn : n = 200 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 294 615 (by decide) (by rfl)
  | 95 =>
    have hn : n = 200 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 295 1736 (by decide) (by rfl)
  | 96 =>
    have hn : n = 200 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 296 837 (by decide) (by rfl)
  | 97 =>
    have hn : n = 200 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 297 3058 (by decide) (by rfl)
  | 98 =>
    have hn : n = 200 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 298 1859 (by decide) (by rfl)
  | 99 =>
    have hn : n = 200 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 299 1100 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_300_399 (n : ℕ) (h1 : n ≥ 300) (h2 : n < 400) : A268597 n > 0 := by
  have h : n - 300 < 100 := by omega
  generalize h_k : n - 300 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 300 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 300 1813 (by decide) (by rfl)
  | 1 =>
    have hn : n = 300 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 301 3614 (by decide) (by rfl)
  | 2 =>
    have hn : n = 300 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 302 2415 (by decide) (by rfl)
  | 3 =>
    have hn : n = 300 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 303 1456 (by decide) (by rfl)
  | 4 =>
    have hn : n = 300 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 304 3809 (by decide) (by rfl)
  | 5 =>
    have hn : n = 300 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 305 1386 (by decide) (by rfl)
  | 6 =>
    have hn : n = 300 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 306 8587 (by decide) (by rfl)
  | 7 =>
    have hn : n = 300 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 307 980 (by decide) (by rfl)
  | 8 =>
    have hn : n = 300 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 308 645 (by decide) (by rfl)
  | 9 =>
    have hn : n = 300 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 309 1510 (by decide) (by rfl)
  | 10 =>
    have hn : n = 300 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 310 1535 (by decide) (by rfl)
  | 11 =>
    have hn : n = 300 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 311 2552 (by decide) (by rfl)
  | 12 =>
    have hn : n = 300 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 312 933 (by decide) (by rfl)
  | 13 =>
    have hn : n = 300 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 313 2114 (by decide) (by rfl)
  | 14 =>
    have hn : n = 300 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 314 675 (by decide) (by rfl)
  | 15 =>
    have hn : n = 300 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 315 2044 (by decide) (by rfl)
  | 16 =>
    have hn : n = 300 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 316 1565 (by decide) (by rfl)
  | 17 =>
    have hn : n = 300 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 317 1974 (by decide) (by rfl)
  | 18 =>
    have hn : n = 300 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 318 759 (by decide) (by rfl)
  | 19 =>
    have hn : n = 300 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 319 1600 (by decide) (by rfl)
  | 20 =>
    have hn : n = 300 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 320 1585 (by decide) (by rfl)
  | 21 =>
    have hn : n = 300 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 321 1570 (by decide) (by rfl)
  | 22 =>
    have hn : n = 300 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 322 867 (by decide) (by rfl)
  | 23 =>
    have hn : n = 300 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 323 972 (by decide) (by rfl)
  | 24 =>
    have hn : n = 300 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 324 1045 (by decide) (by rfl)
  | 25 =>
    have hn : n = 300 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 325 2198 (by decide) (by rfl)
  | 26 =>
    have hn : n = 300 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 326 963 (by decide) (by rfl)
  | 27 =>
    have hn : n = 300 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 327 1480 (by decide) (by rfl)
  | 28 =>
    have hn : n = 300 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 328 2009 (by decide) (by rfl)
  | 29 =>
    have hn : n = 300 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 329 1210 (by decide) (by rfl)
  | 30 =>
    have hn : n = 300 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 330 5947 (by decide) (by rfl)
  | 31 =>
    have hn : n = 300 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 331 1580 (by decide) (by rfl)
  | 32 =>
    have hn : n = 300 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 332 693 (by decide) (by rfl)
  | 33 =>
    have hn : n = 300 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 333 1630 (by decide) (by rfl)
  | 34 =>
    have hn : n = 300 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 334 1655 (by decide) (by rfl)
  | 35 =>
    have hn : n = 300 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 335 1360 (by decide) (by rfl)
  | 36 =>
    have hn : n = 300 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 336 705 (by decide) (by rfl)
  | 37 =>
    have hn : n = 300 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 337 2282 (by decide) (by rfl)
  | 38 =>
    have hn : n = 300 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 338 1011 (by decide) (by rfl)
  | 39 =>
    have hn : n = 300 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 339 1300 (by decide) (by rfl)
  | 40 =>
    have hn : n = 300 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 340 1685 (by decide) (by rfl)
  | 41 =>
    have hn : n = 300 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 341 1590 (by decide) (by rfl)
  | 42 =>
    have hn : n = 300 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 342 1015 (by decide) (by rfl)
  | 43 =>
    have hn : n = 300 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 343 2072 (by decide) (by rfl)
  | 44 =>
    have hn : n = 300 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 344 777 (by decide) (by rfl)
  | 45 =>
    have hn : n = 300 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 345 2338 (by decide) (by rfl)
  | 46 =>
    have hn : n = 300 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 346 3707 (by decide) (by rfl)
  | 47 =>
    have hn : n = 300 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 347 1660 (by decide) (by rfl)
  | 48 =>
    have hn : n = 300 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 348 1041 (by decide) (by rfl)
  | 49 =>
    have hn : n = 300 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 349 1550 (by decide) (by rfl)
  | 50 =>
    have hn : n = 300 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 350 891 (by decide) (by rfl)
  | 51 =>
    have hn : n = 300 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 351 1120 (by decide) (by rfl)
  | 52 =>
    have hn : n = 300 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 352 1745 (by decide) (by rfl)
  | 53 =>
    have hn : n = 300 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 353 1730 (by decide) (by rfl)
  | 54 =>
    have hn : n = 300 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 354 1059 (by decide) (by rfl)
  | 55 =>
    have hn : n = 300 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 355 2324 (by decide) (by rfl)
  | 56 =>
    have hn : n = 300 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 356 1445 (by decide) (by rfl)
  | 57 =>
    have hn : n = 300 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 357 2422 (by decide) (by rfl)
  | 58 =>
    have hn : n = 300 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 358 2471 (by decide) (by rfl)
  | 59 =>
    have hn : n = 300 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 359 1640 (by decide) (by rfl)
  | 60 =>
    have hn : n = 300 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 360 1077 (by decide) (by rfl)
  | 61 =>
    have hn : n = 300 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 361 6194 (by decide) (by rfl)
  | 62 =>
    have hn : n = 300 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 362 1795 (by decide) (by rfl)
  | 63 =>
    have hn : n = 300 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 363 4108 (by decide) (by rfl)
  | 64 =>
    have hn : n = 300 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 364 1085 (by decide) (by rfl)
  | 65 =>
    have hn : n = 300 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 365 1790 (by decide) (by rfl)
  | 66 =>
    have hn : n = 300 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 366 6631 (by decide) (by rfl)
  | 67 =>
    have hn : n = 300 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 367 1520 (by decide) (by rfl)
  | 68 =>
    have hn : n = 300 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 368 897 (by decide) (by rfl)
  | 69 =>
    have hn : n = 300 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 369 1810 (by decide) (by rfl)
  | 70 =>
    have hn : n = 300 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 370 1235 (by decide) (by rfl)
  | 71 =>
    have hn : n = 300 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 371 1780 (by decide) (by rfl)
  | 72 =>
    have hn : n = 300 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 372 2569 (by decide) (by rfl)
  | 73 =>
    have hn : n = 300 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 373 1694 (by decide) (by rfl)
  | 74 =>
    have hn : n = 300 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 374 1119 (by decide) (by rfl)
  | 75 =>
    have hn : n = 300 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 375 1720 (by decide) (by rfl)
  | 76 =>
    have hn : n = 300 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 376 1865 (by decide) (by rfl)
  | 77 =>
    have hn : n = 300 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 377 1530 (by decide) (by rfl)
  | 78 =>
    have hn : n = 300 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 378 795 (by decide) (by rfl)
  | 79 =>
    have hn : n = 300 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 379 2492 (by decide) (by rfl)
  | 80 =>
    have hn : n = 300 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 380 765 (by decide) (by rfl)
  | 81 =>
    have hn : n = 300 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 381 3982 (by decide) (by rfl)
  | 82 =>
    have hn : n = 300 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 382 1463 (by decide) (by rfl)
  | 83 =>
    have hn : n = 300 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 383 1152 (by decide) (by rfl)
  | 84 =>
    have hn : n = 300 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 384 1149 (by decide) (by rfl)
  | 85 =>
    have hn : n = 300 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 385 4706 (by decide) (by rfl)
  | 86 =>
    have hn : n = 300 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 386 819 (by decide) (by rfl)
  | 87 =>
    have hn : n = 300 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 387 6004 (by decide) (by rfl)
  | 88 =>
    have hn : n = 300 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 388 2681 (by decide) (by rfl)
  | 89 =>
    have hn : n = 300 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 389 1830 (by decide) (by rfl)
  | 90 =>
    have hn : n = 300 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 390 1167 (by decide) (by rfl)
  | 91 =>
    have hn : n = 300 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 391 2408 (by decide) (by rfl)
  | 92 =>
    have hn : n = 300 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 392 969 (by decide) (by rfl)
  | 93 =>
    have hn : n = 300 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 393 1930 (by decide) (by rfl)
  | 94 =>
    have hn : n = 300 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 394 1547 (by decide) (by rfl)
  | 95 =>
    have hn : n = 300 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 395 1740 (by decide) (by rfl)
  | 96 =>
    have hn : n = 300 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 396 957 (by decide) (by rfl)
  | 97 =>
    have hn : n = 300 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 397 2702 (by decide) (by rfl)
  | 98 =>
    have hn : n = 300 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 398 903 (by decide) (by rfl)
  | 99 =>
    have hn : n = 300 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 399 2000 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_400_499 (n : ℕ) (h1 : n ≥ 400) (h2 : n < 500) : A268597 n > 0 := by
  have h : n - 400 < 100 := by omega
  generalize h_k : n - 400 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 400 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 400 1985 (by decide) (by rfl)
  | 1 =>
    have hn : n = 400 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 401 1970 (by decide) (by rfl)
  | 2 =>
    have hn : n = 400 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 402 1203 (by decide) (by rfl)
  | 3 =>
    have hn : n = 400 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 403 1940 (by decide) (by rfl)
  | 4 =>
    have hn : n = 400 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 404 1053 (by decide) (by rfl)
  | 5 =>
    have hn : n = 400 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 405 1990 (by decide) (by rfl)
  | 6 =>
    have hn : n = 400 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 406 2807 (by decide) (by rfl)
  | 7 =>
    have hn : n = 400 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 407 1848 (by decide) (by rfl)
  | 8 =>
    have hn : n = 400 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 408 5161 (by decide) (by rfl)
  | 9 =>
    have hn : n = 400 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 409 1850 (by decide) (by rfl)
  | 10 =>
    have hn : n = 400 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 410 1227 (by decide) (by rfl)
  | 11 =>
    have hn : n = 400 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 411 2716 (by decide) (by rfl)
  | 12 =>
    have hn : n = 400 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 412 2045 (by decide) (by rfl)
  | 13 =>
    have hn : n = 400 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 413 1710 (by decide) (by rfl)
  | 14 =>
    have hn : n = 400 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 414 1975 (by decide) (by rfl)
  | 15 =>
    have hn : n = 400 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 415 5408 (by decide) (by rfl)
  | 16 =>
    have hn : n = 400 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 416 1233 (by decide) (by rfl)
  | 17 =>
    have hn : n = 400 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 417 4378 (by decide) (by rfl)
  | 18 =>
    have hn : n = 400 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 418 4499 (by decide) (by rfl)
  | 19 =>
    have hn : n = 400 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 419 1700 (by decide) (by rfl)
  | 20 =>
    have hn : n = 400 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 420 885 (by decide) (by rfl)
  | 21 =>
    have hn : n = 400 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 421 5174 (by decide) (by rfl)
  | 22 =>
    have hn : n = 400 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 422 855 (by decide) (by rfl)
  | 23 =>
    have hn : n = 400 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 423 2632 (by decide) (by rfl)
  | 24 =>
    have hn : n = 400 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 424 1625 (by decide) (by rfl)
  | 25 =>
    have hn : n = 400 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 425 2010 (by decide) (by rfl)
  | 26 =>
    have hn : n = 400 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 426 2947 (by decide) (by rfl)
  | 27 =>
    have hn : n = 400 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 427 2060 (by decide) (by rfl)
  | 28 =>
    have hn : n = 400 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 428 1089 (by decide) (by rfl)
  | 29 =>
    have hn : n = 400 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 429 2110 (by decide) (by rfl)
  | 30 =>
    have hn : n = 400 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 430 1295 (by decide) (by rfl)
  | 31 =>
    have hn : n = 400 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 431 1296 (by decide) (by rfl)
  | 32 =>
    have hn : n = 400 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 432 1293 (by decide) (by rfl)
  | 33 =>
    have hn : n = 400 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 433 2954 (by decide) (by rfl)
  | 34 =>
    have hn : n = 400 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 434 915 (by decide) (by rfl)
  | 35 =>
    have hn : n = 400 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 435 2884 (by decide) (by rfl)
  | 36 =>
    have hn : n = 400 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 436 1805 (by decide) (by rfl)
  | 37 =>
    have hn : n = 400 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 437 2814 (by decide) (by rfl)
  | 38 =>
    have hn : n = 400 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 438 1495 (by decide) (by rfl)
  | 39 =>
    have hn : n = 400 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 439 1400 (by decide) (by rfl)
  | 40 =>
    have hn : n = 400 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 440 1029 (by decide) (by rfl)
  | 41 =>
    have hn : n = 400 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 441 1690 (by decide) (by rfl)
  | 42 =>
    have hn : n = 400 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 442 2195 (by decide) (by rfl)
  | 43 =>
    have hn : n = 400 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 443 2140 (by decide) (by rfl)
  | 44 =>
    have hn : n = 400 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 444 1329 (by decide) (by rfl)
  | 45 =>
    have hn : n = 400 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 445 5486 (by decide) (by rfl)
  | 46 =>
    have hn : n = 400 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 446 2215 (by decide) (by rfl)
  | 47 =>
    have hn : n = 400 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 447 3136 (by decide) (by rfl)
  | 48 =>
    have hn : n = 400 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 448 3101 (by decide) (by rfl)
  | 49 =>
    have hn : n = 400 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 449 2050 (by decide) (by rfl)
  | 50 =>
    have hn : n = 400 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 450 1347 (by decide) (by rfl)
  | 51 =>
    have hn : n = 400 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 451 2180 (by decide) (by rfl)
  | 52 =>
    have hn : n = 400 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 452 1341 (by decide) (by rfl)
  | 53 =>
    have hn : n = 400 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 453 2230 (by decide) (by rfl)
  | 54 =>
    have hn : n = 400 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 454 2891 (by decide) (by rfl)
  | 55 =>
    have hn : n = 400 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 455 2120 (by decide) (by rfl)
  | 56 =>
    have hn : n = 400 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 456 8341 (by decide) (by rfl)
  | 57 =>
    have hn : n = 400 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 457 3122 (by decide) (by rfl)
  | 58 =>
    have hn : n = 400 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 458 1131 (by decide) (by rfl)
  | 59 =>
    have hn : n = 400 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 459 1900 (by decide) (by rfl)
  | 60 =>
    have hn : n = 400 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 460 2285 (by decide) (by rfl)
  | 61 =>
    have hn : n = 400 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 461 2190 (by decide) (by rfl)
  | 62 =>
    have hn : n = 400 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 462 1383 (by decide) (by rfl)
  | 63 =>
    have hn : n = 400 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 463 2576 (by decide) (by rfl)
  | 64 =>
    have hn : n = 400 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 464 1389 (by decide) (by rfl)
  | 65 =>
    have hn : n = 400 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 465 2290 (by decide) (by rfl)
  | 66 =>
    have hn : n = 400 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 466 2315 (by decide) (by rfl)
  | 67 =>
    have hn : n = 400 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 467 2260 (by decide) (by rfl)
  | 68 =>
    have hn : n = 400 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 468 1173 (by decide) (by rfl)
  | 69 =>
    have hn : n = 400 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 469 1430 (by decide) (by rfl)
  | 70 =>
    have hn : n = 400 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 470 2335 (by decide) (by rfl)
  | 71 =>
    have hn : n = 400 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 471 2968 (by decide) (by rfl)
  | 72 =>
    have hn : n = 400 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 472 3269 (by decide) (by rfl)
  | 73 =>
    have hn : n = 400 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 473 2330 (by decide) (by rfl)
  | 74 =>
    have hn : n = 400 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 474 1435 (by decide) (by rfl)
  | 75 =>
    have hn : n = 400 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 475 2156 (by decide) (by rfl)
  | 76 =>
    have hn : n = 400 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 476 1005 (by decide) (by rfl)
  | 77 =>
    have hn : n = 400 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 477 3262 (by decide) (by rfl)
  | 78 =>
    have hn : n = 400 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 478 6071 (by decide) (by rfl)
  | 79 =>
    have hn : n = 400 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 479 1760 (by decide) (by rfl)
  | 80 =>
    have hn : n = 400 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 480 1437 (by decide) (by rfl)
  | 81 =>
    have hn : n = 400 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 481 5954 (by decide) (by rfl)
  | 82 =>
    have hn : n = 400 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 482 2395 (by decide) (by rfl)
  | 83 =>
    have hn : n = 400 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 483 5324 (by decide) (by rfl)
  | 84 =>
    have hn : n = 400 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 484 3353 (by decide) (by rfl)
  | 85 =>
    have hn : n = 400 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 485 1458 (by decide) (by rfl)
  | 86 =>
    have hn : n = 400 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 486 14167 (by decide) (by rfl)
  | 87 =>
    have hn : n = 400 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 487 6536 (by decide) (by rfl)
  | 88 =>
    have hn : n = 400 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 488 1113 (by decide) (by rfl)
  | 89 =>
    have hn : n = 400 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 489 2410 (by decide) (by rfl)
  | 90 =>
    have hn : n = 400 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 490 2435 (by decide) (by rfl)
  | 91 =>
    have hn : n = 400 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 491 2220 (by decide) (by rfl)
  | 92 =>
    have hn : n = 400 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 492 1473 (by decide) (by rfl)
  | 93 =>
    have hn : n = 400 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 493 2366 (by decide) (by rfl)
  | 94 =>
    have hn : n = 400 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 494 1071 (by decide) (by rfl)
  | 95 =>
    have hn : n = 400 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 495 3952 (by decide) (by rfl)
  | 96 =>
    have hn : n = 400 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 496 1505 (by decide) (by rfl)
  | 97 =>
    have hn : n = 400 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 497 2370 (by decide) (by rfl)
  | 98 =>
    have hn : n = 400 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 498 6331 (by decide) (by rfl)
  | 99 =>
    have hn : n = 400 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 499 2500 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_500_599 (n : ℕ) (h1 : n ≥ 500) (h2 : n < 600) : A268597 n > 0 := by
  have h : n - 500 < 100 := by omega
  generalize h_k : n - 500 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 500 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 500 1221 (by decide) (by rfl)
  | 1 =>
    have hn : n = 500 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 501 5302 (by decide) (by rfl)
  | 2 =>
    have hn : n = 500 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 502 2495 (by decide) (by rfl)
  | 3 =>
    have hn : n = 500 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 503 2040 (by decide) (by rfl)
  | 4 =>
    have hn : n = 500 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 504 1065 (by decide) (by rfl)
  | 5 =>
    have hn : n = 500 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 505 3146 (by decide) (by rfl)
  | 6 =>
    have hn : n = 500 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 506 1035 (by decide) (by rfl)
  | 7 =>
    have hn : n = 500 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 507 8284 (by decide) (by rfl)
  | 8 =>
    have hn : n = 500 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 508 2093 (by decide) (by rfl)
  | 9 =>
    have hn : n = 500 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 509 2350 (by decide) (by rfl)
  | 10 =>
    have hn : n = 500 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 510 1527 (by decide) (by rfl)
  | 11 =>
    have hn : n = 500 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 511 1024 (by decide) (by rfl)
  | 12 =>
    have hn : n = 500 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 512 1377 (by decide) (by rfl)
  | 13 =>
    have hn : n = 500 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 513 3514 (by decide) (by rfl)
  | 14 =>
    have hn : n = 500 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 514 3563 (by decide) (by rfl)
  | 15 =>
    have hn : n = 500 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 515 3108 (by decide) (by rfl)
  | 16 =>
    have hn : n = 500 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 516 4477 (by decide) (by rfl)
  | 17 =>
    have hn : n = 500 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 517 3038 (by decide) (by rfl)
  | 18 =>
    have hn : n = 500 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 518 1095 (by decide) (by rfl)
  | 19 =>
    have hn : n = 500 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 519 2440 (by decide) (by rfl)
  | 20 =>
    have hn : n = 500 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 520 6617 (by decide) (by rfl)
  | 21 =>
    have hn : n = 500 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 521 2490 (by decide) (by rfl)
  | 22 =>
    have hn : n = 500 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 522 1563 (by decide) (by rfl)
  | 23 =>
    have hn : n = 500 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 523 2540 (by decide) (by rfl)
  | 24 =>
    have hn : n = 500 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 524 1125 (by decide) (by rfl)
  | 25 =>
    have hn : n = 500 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 525 3598 (by decide) (by rfl)
  | 26 =>
    have hn : n = 500 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 526 2615 (by decide) (by rfl)
  | 27 =>
    have hn : n = 500 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 527 2320 (by decide) (by rfl)
  | 28 =>
    have hn : n = 500 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 528 3661 (by decide) (by rfl)
  | 29 =>
    have hn : n = 500 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 529 16946 (by decide) (by rfl)
  | 30 =>
    have hn : n = 500 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 530 5731 (by decide) (by rfl)
  | 31 =>
    have hn : n = 500 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 531 2548 (by decide) (by rfl)
  | 32 =>
    have hn : n = 500 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 532 2261 (by decide) (by rfl)
  | 33 =>
    have hn : n = 500 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 533 2630 (by decide) (by rfl)
  | 34 =>
    have hn : n = 500 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 534 2575 (by decide) (by rfl)
  | 35 =>
    have hn : n = 500 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 535 3416 (by decide) (by rfl)
  | 36 =>
    have hn : n = 500 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 536 8857 (by decide) (by rfl)
  | 37 =>
    have hn : n = 500 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 537 3682 (by decide) (by rfl)
  | 38 =>
    have hn : n = 500 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 538 1715 (by decide) (by rfl)
  | 39 =>
    have hn : n = 500 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 539 2300 (by decide) (by rfl)
  | 40 =>
    have hn : n = 500 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 540 1645 (by decide) (by rfl)
  | 41 =>
    have hn : n = 500 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 541 14942 (by decide) (by rfl)
  | 42 =>
    have hn : n = 500 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 542 1239 (by decide) (by rfl)
  | 43 =>
    have hn : n = 500 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 543 2080 (by decide) (by rfl)
  | 44 =>
    have hn : n = 500 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 544 2705 (by decide) (by rfl)
  | 45 =>
    have hn : n = 500 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 545 2690 (by decide) (by rfl)
  | 46 =>
    have hn : n = 500 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 546 1955 (by decide) (by rfl)
  | 47 =>
    have hn : n = 500 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 547 3668 (by decide) (by rfl)
  | 48 =>
    have hn : n = 500 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 548 1197 (by decide) (by rfl)
  | 49 =>
    have hn : n = 500 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 549 1750 (by decide) (by rfl)
  | 50 =>
    have hn : n = 500 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 550 2735 (by decide) (by rfl)
  | 51 =>
    have hn : n = 500 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 551 2280 (by decide) (by rfl)
  | 52 =>
    have hn : n = 500 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 552 1353 (by decide) (by rfl)
  | 53 =>
    have hn : n = 500 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 553 3794 (by decide) (by rfl)
  | 54 =>
    have hn : n = 500 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 554 2675 (by decide) (by rfl)
  | 55 =>
    have hn : n = 500 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 555 6604 (by decide) (by rfl)
  | 56 =>
    have hn : n = 500 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 556 2717 (by decide) (by rfl)
  | 57 =>
    have hn : n = 500 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 557 2670 (by decide) (by rfl)
  | 58 =>
    have hn : n = 500 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 558 1671 (by decide) (by rfl)
  | 59 =>
    have hn : n = 500 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 559 2480 (by decide) (by rfl)
  | 60 =>
    have hn : n = 500 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 560 1185 (by decide) (by rfl)
  | 61 =>
    have hn : n = 500 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 561 2002 (by decide) (by rfl)
  | 62 =>
    have hn : n = 500 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 562 3899 (by decide) (by rfl)
  | 63 =>
    have hn : n = 500 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 563 2580 (by decide) (by rfl)
  | 64 =>
    have hn : n = 500 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 564 1689 (by decide) (by rfl)
  | 65 =>
    have hn : n = 500 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 565 3878 (by decide) (by rfl)
  | 66 =>
    have hn : n = 500 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 566 1215 (by decide) (by rfl)
  | 67 =>
    have hn : n = 500 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 567 2680 (by decide) (by rfl)
  | 68 =>
    have hn : n = 500 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 568 3941 (by decide) (by rfl)
  | 69 =>
    have hn : n = 500 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 569 2650 (by decide) (by rfl)
  | 70 =>
    have hn : n = 500 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 570 1707 (by decide) (by rfl)
  | 71 =>
    have hn : n = 500 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 571 2780 (by decide) (by rfl)
  | 72 =>
    have hn : n = 500 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 572 1713 (by decide) (by rfl)
  | 73 =>
    have hn : n = 500 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 573 2830 (by decide) (by rfl)
  | 74 =>
    have hn : n = 500 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 574 1587 (by decide) (by rfl)
  | 75 =>
    have hn : n = 500 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 575 1728 (by decide) (by rfl)
  | 76 =>
    have hn : n = 500 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 576 3997 (by decide) (by rfl)
  | 77 =>
    have hn : n = 500 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 577 3962 (by decide) (by rfl)
  | 78 =>
    have hn : n = 500 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 578 1419 (by decide) (by rfl)
  | 79 =>
    have hn : n = 500 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 579 3892 (by decide) (by rfl)
  | 80 =>
    have hn : n = 500 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 580 2885 (by decide) (by rfl)
  | 81 =>
    have hn : n = 500 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 581 6182 (by decide) (by rfl)
  | 82 =>
    have hn : n = 500 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 582 1479 (by decide) (by rfl)
  | 83 =>
    have hn : n = 500 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 583 3752 (by decide) (by rfl)
  | 84 =>
    have hn : n = 500 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 584 1521 (by decide) (by rfl)
  | 85 =>
    have hn : n = 500 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 585 6226 (by decide) (by rfl)
  | 86 =>
    have hn : n = 500 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 586 2387 (by decide) (by rfl)
  | 87 =>
    have hn : n = 500 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 587 3612 (by decide) (by rfl)
  | 88 =>
    have hn : n = 500 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 588 1245 (by decide) (by rfl)
  | 89 =>
    have hn : n = 500 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 589 1870 (by decide) (by rfl)
  | 90 =>
    have hn : n = 500 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 590 2935 (by decide) (by rfl)
  | 91 =>
    have hn : n = 500 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 591 3472 (by decide) (by rfl)
  | 92 =>
    have hn : n = 500 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 592 4109 (by decide) (by rfl)
  | 93 =>
    have hn : n = 500 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 593 2610 (by decide) (by rfl)
  | 94 =>
    have hn : n = 500 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 594 1779 (by decide) (by rfl)
  | 95 =>
    have hn : n = 500 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 595 6116 (by decide) (by rfl)
  | 96 =>
    have hn : n = 500 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 596 1773 (by decide) (by rfl)
  | 97 =>
    have hn : n = 500 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 597 3718 (by decide) (by rfl)
  | 98 =>
    have hn : n = 500 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 598 4151 (by decide) (by rfl)
  | 99 =>
    have hn : n = 500 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 599 2200 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_600_699 (n : ℕ) (h1 : n ≥ 600) (h2 : n < 700) : A268597 n > 0 := by
  have h : n - 600 < 100 := by omega
  generalize h_k : n - 600 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 600 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 600 1797 (by decide) (by rfl)
  | 1 =>
    have hn : n = 600 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 601 3626 (by decide) (by rfl)
  | 2 =>
    have hn : n = 600 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 602 1791 (by decide) (by rfl)
  | 3 =>
    have hn : n = 600 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 603 7228 (by decide) (by rfl)
  | 4 =>
    have hn : n = 600 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 604 3005 (by decide) (by rfl)
  | 5 =>
    have hn : n = 600 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 605 2910 (by decide) (by rfl)
  | 6 =>
    have hn : n = 600 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 606 1855 (by decide) (by rfl)
  | 7 =>
    have hn : n = 600 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 607 2912 (by decide) (by rfl)
  | 8 =>
    have hn : n = 600 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 608 1821 (by decide) (by rfl)
  | 9 =>
    have hn : n = 600 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 609 7618 (by decide) (by rfl)
  | 10 =>
    have hn : n = 600 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 610 3035 (by decide) (by rfl)
  | 11 =>
    have hn : n = 600 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 611 2772 (by decide) (by rfl)
  | 12 =>
    have hn : n = 600 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 612 4249 (by decide) (by rfl)
  | 13 =>
    have hn : n = 600 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 613 17174 (by decide) (by rfl)
  | 14 =>
    have hn : n = 600 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 614 1407 (by decide) (by rfl)
  | 15 =>
    have hn : n = 600 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 615 1960 (by decide) (by rfl)
  | 16 =>
    have hn : n = 600 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 616 3065 (by decide) (by rfl)
  | 17 =>
    have hn : n = 600 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 617 4074 (by decide) (by rfl)
  | 18 =>
    have hn : n = 600 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 618 1851 (by decide) (by rfl)
  | 19 =>
    have hn : n = 600 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 619 3020 (by decide) (by rfl)
  | 20 =>
    have hn : n = 600 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 620 1581 (by decide) (by rfl)
  | 21 =>
    have hn : n = 600 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 621 3070 (by decide) (by rfl)
  | 22 =>
    have hn : n = 600 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 622 2639 (by decide) (by rfl)
  | 23 =>
    have hn : n = 600 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 623 5104 (by decide) (by rfl)
  | 24 =>
    have hn : n = 600 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 624 2737 (by decide) (by rfl)
  | 25 =>
    have hn : n = 600 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 625 4298 (by decide) (by rfl)
  | 26 =>
    have hn : n = 600 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 626 5687 (by decide) (by rfl)
  | 27 =>
    have hn : n = 600 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 627 4228 (by decide) (by rfl)
  | 28 =>
    have hn : n = 600 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 628 6809 (by decide) (by rfl)
  | 29 =>
    have hn : n = 600 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 629 2550 (by decide) (by rfl)
  | 30 =>
    have hn : n = 600 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 630 1335 (by decide) (by rfl)
  | 31 =>
    have hn : n = 600 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 631 4088 (by decide) (by rfl)
  | 32 =>
    have hn : n = 600 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 632 1305 (by decide) (by rfl)
  | 33 =>
    have hn : n = 600 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 633 3130 (by decide) (by rfl)
  | 34 =>
    have hn : n = 600 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 634 1275 (by decide) (by rfl)
  | 35 =>
    have hn : n = 600 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 635 3948 (by decide) (by rfl)
  | 36 =>
    have hn : n = 600 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 636 4417 (by decide) (by rfl)
  | 37 =>
    have hn : n = 600 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 637 4382 (by decide) (by rfl)
  | 38 =>
    have hn : n = 600 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 638 1599 (by decide) (by rfl)
  | 39 =>
    have hn : n = 600 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 639 3200 (by decide) (by rfl)
  | 40 =>
    have hn : n = 600 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 640 6941 (by decide) (by rfl)
  | 41 =>
    have hn : n = 600 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 641 3090 (by decide) (by rfl)
  | 42 =>
    have hn : n = 600 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 642 1923 (by decide) (by rfl)
  | 43 =>
    have hn : n = 600 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 643 3140 (by decide) (by rfl)
  | 44 =>
    have hn : n = 600 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 644 1653 (by decide) (by rfl)
  | 45 =>
    have hn : n = 600 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 645 4438 (by decide) (by rfl)
  | 46 =>
    have hn : n = 600 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 646 3215 (by decide) (by rfl)
  | 47 =>
    have hn : n = 600 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 647 1944 (by decide) (by rfl)
  | 48 =>
    have hn : n = 600 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 648 1941 (by decide) (by rfl)
  | 49 =>
    have hn : n = 600 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 649 2090 (by decide) (by rfl)
  | 50 =>
    have hn : n = 600 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 650 1491 (by decide) (by rfl)
  | 51 =>
    have hn : n = 600 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 651 4396 (by decide) (by rfl)
  | 52 =>
    have hn : n = 600 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 652 4529 (by decide) (by rfl)
  | 53 =>
    have hn : n = 600 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 653 4326 (by decide) (by rfl)
  | 54 =>
    have hn : n = 600 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 654 1959 (by decide) (by rfl)
  | 55 =>
    have hn : n = 600 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 655 2960 (by decide) (by rfl)
  | 56 =>
    have hn : n = 600 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 656 1449 (by decide) (by rfl)
  | 57 =>
    have hn : n = 600 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 657 4018 (by decide) (by rfl)
  | 58 =>
    have hn : n = 600 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 658 4571 (by decide) (by rfl)
  | 59 =>
    have hn : n = 600 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 659 2420 (by decide) (by rfl)
  | 60 =>
    have hn : n = 600 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 660 1977 (by decide) (by rfl)
  | 61 =>
    have hn : n = 600 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 661 11894 (by decide) (by rfl)
  | 62 =>
    have hn : n = 600 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 662 1983 (by decide) (by rfl)
  | 63 =>
    have hn : n = 600 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 663 3160 (by decide) (by rfl)
  | 64 =>
    have hn : n = 600 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 664 3305 (by decide) (by rfl)
  | 65 =>
    have hn : n = 600 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 665 3210 (by decide) (by rfl)
  | 66 =>
    have hn : n = 600 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 666 3703 (by decide) (by rfl)
  | 67 =>
    have hn : n = 600 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 667 3260 (by decide) (by rfl)
  | 68 =>
    have hn : n = 600 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 668 1533 (by decide) (by rfl)
  | 69 =>
    have hn : n = 600 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 669 3310 (by decide) (by rfl)
  | 70 =>
    have hn : n = 600 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 670 7271 (by decide) (by rfl)
  | 71 =>
    have hn : n = 600 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 671 2720 (by decide) (by rfl)
  | 72 =>
    have hn : n = 600 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 672 2065 (by decide) (by rfl)
  | 73 =>
    have hn : n = 600 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 673 2210 (by decide) (by rfl)
  | 74 =>
    have hn : n = 600 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 674 1395 (by decide) (by rfl)
  | 75 =>
    have hn : n = 600 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 675 4564 (by decide) (by rfl)
  | 76 =>
    have hn : n = 600 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 676 2405 (by decide) (by rfl)
  | 77 =>
    have hn : n = 600 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 677 3270 (by decide) (by rfl)
  | 78 =>
    have hn : n = 600 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 678 2031 (by decide) (by rfl)
  | 79 =>
    have hn : n = 600 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 679 2600 (by decide) (by rfl)
  | 80 =>
    have hn : n = 600 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 680 3385 (by decide) (by rfl)
  | 81 =>
    have hn : n = 600 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 681 3370 (by decide) (by rfl)
  | 82 =>
    have hn : n = 600 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 682 3059 (by decide) (by rfl)
  | 83 =>
    have hn : n = 600 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 683 3180 (by decide) (by rfl)
  | 84 =>
    have hn : n = 600 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 684 2049 (by decide) (by rfl)
  | 85 =>
    have hn : n = 600 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 685 4214 (by decide) (by rfl)
  | 86 =>
    have hn : n = 600 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 686 1455 (by decide) (by rfl)
  | 87 =>
    have hn : n = 600 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 687 4144 (by decide) (by rfl)
  | 88 =>
    have hn : n = 600 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 688 2849 (by decide) (by rfl)
  | 89 =>
    have hn : n = 600 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 689 2850 (by decide) (by rfl)
  | 90 =>
    have hn : n = 600 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 690 12787 (by decide) (by rfl)
  | 91 =>
    have hn : n = 600 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 691 4676 (by decide) (by rfl)
  | 92 =>
    have hn : n = 600 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 692 2061 (by decide) (by rfl)
  | 93 =>
    have hn : n = 600 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 693 7414 (by decide) (by rfl)
  | 94 =>
    have hn : n = 600 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 694 2135 (by decide) (by rfl)
  | 95 =>
    have hn : n = 600 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 695 3320 (by decide) (by rfl)
  | 96 =>
    have hn : n = 600 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 696 4837 (by decide) (by rfl)
  | 97 =>
    have hn : n = 600 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 697 2618 (by decide) (by rfl)
  | 98 =>
    have hn : n = 600 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 698 7035 (by decide) (by rfl)
  | 99 =>
    have hn : n = 600 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 699 3100 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_700_799 (n : ℕ) (h1 : n ≥ 700) (h2 : n < 800) : A268597 n > 0 := by
  have h : n - 700 < 100 := by omega
  generalize h_k : n - 700 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 700 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 700 7601 (by decide) (by rfl)
  | 1 =>
    have hn : n = 700 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 701 3390 (by decide) (by rfl)
  | 2 =>
    have hn : n = 700 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 702 2103 (by decide) (by rfl)
  | 3 =>
    have hn : n = 700 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 703 2240 (by decide) (by rfl)
  | 4 =>
    have hn : n = 700 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 704 1425 (by decide) (by rfl)
  | 5 =>
    have hn : n = 700 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 705 3490 (by decide) (by rfl)
  | 6 =>
    have hn : n = 700 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 706 4907 (by decide) (by rfl)
  | 7 =>
    have hn : n = 700 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 707 3460 (by decide) (by rfl)
  | 8 =>
    have hn : n = 700 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 708 1749 (by decide) (by rfl)
  | 9 =>
    have hn : n = 700 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 709 3350 (by decide) (by rfl)
  | 10 =>
    have hn : n = 700 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 710 2127 (by decide) (by rfl)
  | 11 =>
    have hn : n = 700 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 711 4648 (by decide) (by rfl)
  | 12 =>
    have hn : n = 700 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 712 3545 (by decide) (by rfl)
  | 13 =>
    have hn : n = 700 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 713 2890 (by decide) (by rfl)
  | 14 =>
    have hn : n = 700 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 714 1515 (by decide) (by rfl)
  | 15 =>
    have hn : n = 700 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 715 4844 (by decide) (by rfl)
  | 16 =>
    have hn : n = 700 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 716 11917 (by decide) (by rfl)
  | 17 =>
    have hn : n = 700 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 717 4942 (by decide) (by rfl)
  | 18 =>
    have hn : n = 700 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 718 7799 (by decide) (by rfl)
  | 19 =>
    have hn : n = 700 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 719 3280 (by decide) (by rfl)
  | 20 =>
    have hn : n = 700 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 720 2157 (by decide) (by rfl)
  | 21 =>
    have hn : n = 700 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 721 9074 (by decide) (by rfl)
  | 22 =>
    have hn : n = 700 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 722 1659 (by decide) (by rfl)
  | 23 =>
    have hn : n = 700 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 723 12388 (by decide) (by rfl)
  | 24 =>
    have hn : n = 700 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 724 1925 (by decide) (by rfl)
  | 25 =>
    have hn : n = 700 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 725 3590 (by decide) (by rfl)
  | 26 =>
    have hn : n = 700 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 726 13471 (by decide) (by rfl)
  | 27 =>
    have hn : n = 700 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 727 8216 (by decide) (by rfl)
  | 28 =>
    have hn : n = 700 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 728 1545 (by decide) (by rfl)
  | 29 =>
    have hn : n = 700 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 729 5026 (by decide) (by rfl)
  | 30 =>
    have hn : n = 700 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 730 3635 (by decide) (by rfl)
  | 31 =>
    have hn : n = 700 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 731 3580 (by decide) (by rfl)
  | 32 =>
    have hn : n = 700 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 732 5089 (by decide) (by rfl)
  | 33 =>
    have hn : n = 700 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 733 13262 (by decide) (by rfl)
  | 34 =>
    have hn : n = 700 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 734 1887 (by decide) (by rfl)
  | 35 =>
    have hn : n = 700 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 735 3040 (by decide) (by rfl)
  | 36 =>
    have hn : n = 700 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 736 3665 (by decide) (by rfl)
  | 37 =>
    have hn : n = 700 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 737 3330 (by decide) (by rfl)
  | 38 =>
    have hn : n = 700 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 738 2755 (by decide) (by rfl)
  | 39 =>
    have hn : n = 700 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 739 3620 (by decide) (by rfl)
  | 40 =>
    have hn : n = 700 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 740 2217 (by decide) (by rfl)
  | 41 =>
    have hn : n = 700 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 741 2470 (by decide) (by rfl)
  | 42 =>
    have hn : n = 700 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 742 3695 (by decide) (by rfl)
  | 43 =>
    have hn : n = 700 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 743 3560 (by decide) (by rfl)
  | 44 =>
    have hn : n = 700 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 744 2229 (by decide) (by rfl)
  | 45 =>
    have hn : n = 700 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 745 5138 (by decide) (by rfl)
  | 46 =>
    have hn : n = 700 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 746 3715 (by decide) (by rfl)
  | 47 =>
    have hn : n = 700 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 747 3388 (by decide) (by rfl)
  | 48 =>
    have hn : n = 700 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 748 4949 (by decide) (by rfl)
  | 49 =>
    have hn : n = 700 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 749 2750 (by decide) (by rfl)
  | 50 =>
    have hn : n = 700 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 750 9607 (by decide) (by rfl)
  | 51 =>
    have hn : n = 700 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 751 3440 (by decide) (by rfl)
  | 52 =>
    have hn : n = 700 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 752 2253 (by decide) (by rfl)
  | 53 =>
    have hn : n = 700 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 753 3730 (by decide) (by rfl)
  | 54 =>
    have hn : n = 700 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 754 3755 (by decide) (by rfl)
  | 55 =>
    have hn : n = 700 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 755 3060 (by decide) (by rfl)
  | 56 =>
    have hn : n = 700 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 756 1605 (by decide) (by rfl)
  | 57 =>
    have hn : n = 700 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 757 5222 (by decide) (by rfl)
  | 58 =>
    have hn : n = 700 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 758 1743 (by decide) (by rfl)
  | 59 =>
    have hn : n = 700 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 759 4984 (by decide) (by rfl)
  | 60 =>
    have hn : n = 700 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 760 2345 (by decide) (by rfl)
  | 61 =>
    have hn : n = 700 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 761 12426 (by decide) (by rfl)
  | 62 =>
    have hn : n = 700 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 762 2283 (by decide) (by rfl)
  | 63 =>
    have hn : n = 700 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 763 7964 (by decide) (by rfl)
  | 64 =>
    have hn : n = 700 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 764 2241 (by decide) (by rfl)
  | 65 =>
    have hn : n = 700 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 765 2926 (by decide) (by rfl)
  | 66 =>
    have hn : n = 700 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 766 5327 (by decide) (by rfl)
  | 67 =>
    have hn : n = 700 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 767 2304 (by decide) (by rfl)
  | 68 =>
    have hn : n = 700 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 768 2001 (by decide) (by rfl)
  | 69 =>
    have hn : n = 700 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 769 2450 (by decide) (by rfl)
  | 70 =>
    have hn : n = 700 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 770 1635 (by decide) (by rfl)
  | 71 =>
    have hn : n = 700 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 771 9412 (by decide) (by rfl)
  | 72 =>
    have hn : n = 700 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 772 3845 (by decide) (by rfl)
  | 73 =>
    have hn : n = 700 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 773 3830 (by decide) (by rfl)
  | 74 =>
    have hn : n = 700 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 774 2319 (by decide) (by rfl)
  | 75 =>
    have hn : n = 700 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 775 12008 (by decide) (by rfl)
  | 76 =>
    have hn : n = 700 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 776 1617 (by decide) (by rfl)
  | 77 =>
    have hn : n = 700 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 777 5362 (by decide) (by rfl)
  | 78 =>
    have hn : n = 700 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 778 2795 (by decide) (by rfl)
  | 79 =>
    have hn : n = 700 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 779 3660 (by decide) (by rfl)
  | 80 =>
    have hn : n = 700 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 780 4301 (by decide) (by rfl)
  | 81 =>
    have hn : n = 700 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 781 4046 (by decide) (by rfl)
  | 82 =>
    have hn : n = 700 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 782 8503 (by decide) (by rfl)
  | 83 =>
    have hn : n = 700 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 783 4816 (by decide) (by rfl)
  | 84 =>
    have hn : n = 700 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 784 2945 (by decide) (by rfl)
  | 85 =>
    have hn : n = 700 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 785 3810 (by decide) (by rfl)
  | 86 =>
    have hn : n = 700 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 786 1947 (by decide) (by rfl)
  | 87 =>
    have hn : n = 700 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 787 3860 (by decide) (by rfl)
  | 88 =>
    have hn : n = 700 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 788 2361 (by decide) (by rfl)
  | 89 =>
    have hn : n = 700 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 789 3094 (by decide) (by rfl)
  | 90 =>
    have hn : n = 700 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 790 3311 (by decide) (by rfl)
  | 91 =>
    have hn : n = 700 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 791 3480 (by decide) (by rfl)
  | 92 =>
    have hn : n = 700 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 792 5509 (by decide) (by rfl)
  | 93 =>
    have hn : n = 700 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 793 14402 (by decide) (by rfl)
  | 94 =>
    have hn : n = 700 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 794 2367 (by decide) (by rfl)
  | 95 =>
    have hn : n = 700 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 795 5404 (by decide) (by rfl)
  | 96 =>
    have hn : n = 700 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 796 8657 (by decide) (by rfl)
  | 97 =>
    have hn : n = 700 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 797 3822 (by decide) (by rfl)
  | 98 =>
    have hn : n = 700 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 798 1695 (by decide) (by rfl)
  | 99 =>
    have hn : n = 700 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 799 4000 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_800_899 (n : ℕ) (h1 : n ≥ 800) (h2 : n < 900) : A268597 n > 0 := by
  have h : n - 800 < 100 := by omega
  generalize h_k : n - 800 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 800 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 800 1665 (by decide) (by rfl)
  | 1 =>
    have hn : n = 800 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 801 3970 (by decide) (by rfl)
  | 2 =>
    have hn : n = 800 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 802 5579 (by decide) (by rfl)
  | 3 =>
    have hn : n = 800 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 803 3940 (by decide) (by rfl)
  | 4 =>
    have hn : n = 800 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 804 2485 (by decide) (by rfl)
  | 5 =>
    have hn : n = 800 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 805 5558 (by decide) (by rfl)
  | 6 =>
    have hn : n = 800 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 806 8295 (by decide) (by rfl)
  | 7 =>
    have hn : n = 800 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 807 3880 (by decide) (by rfl)
  | 8 =>
    have hn : n = 800 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 808 3689 (by decide) (by rfl)
  | 9 =>
    have hn : n = 800 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 809 3450 (by decide) (by rfl)
  | 10 =>
    have hn : n = 800 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 810 2091 (by decide) (by rfl)
  | 11 =>
    have hn : n = 800 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 811 3980 (by decide) (by rfl)
  | 12 =>
    have hn : n = 800 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 812 1869 (by decide) (by rfl)
  | 13 =>
    have hn : n = 800 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 813 5614 (by decide) (by rfl)
  | 14 =>
    have hn : n = 800 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 814 4055 (by decide) (by rfl)
  | 15 =>
    have hn : n = 800 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 815 3696 (by decide) (by rfl)
  | 16 =>
    have hn : n = 800 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 816 5677 (by decide) (by rfl)
  | 17 =>
    have hn : n = 800 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 817 10322 (by decide) (by rfl)
  | 18 =>
    have hn : n = 800 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 818 1827 (by decide) (by rfl)
  | 19 =>
    have hn : n = 800 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 819 3700 (by decide) (by rfl)
  | 20 =>
    have hn : n = 800 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 820 8921 (by decide) (by rfl)
  | 21 =>
    have hn : n = 800 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 821 5502 (by decide) (by rfl)
  | 22 =>
    have hn : n = 800 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 822 2463 (by decide) (by rfl)
  | 23 =>
    have hn : n = 800 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 823 5432 (by decide) (by rfl)
  | 24 =>
    have hn : n = 800 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 824 2469 (by decide) (by rfl)
  | 25 =>
    have hn : n = 800 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 825 4090 (by decide) (by rfl)
  | 26 =>
    have hn : n = 800 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 826 2555 (by decide) (by rfl)
  | 27 =>
    have hn : n = 800 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 827 3420 (by decide) (by rfl)
  | 28 =>
    have hn : n = 800 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 828 2481 (by decide) (by rfl)
  | 29 =>
    have hn : n = 800 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 829 3950 (by decide) (by rfl)
  | 30 =>
    have hn : n = 800 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 830 2487 (by decide) (by rfl)
  | 31 =>
    have hn : n = 800 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 831 10816 (by decide) (by rfl)
  | 32 =>
    have hn : n = 800 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 832 3773 (by decide) (by rfl)
  | 33 =>
    have hn : n = 800 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 833 9906 (by decide) (by rfl)
  | 34 =>
    have hn : n = 800 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 834 2275 (by decide) (by rfl)
  | 35 =>
    have hn : n = 800 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 835 8756 (by decide) (by rfl)
  | 36 =>
    have hn : n = 800 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 836 1989 (by decide) (by rfl)
  | 37 =>
    have hn : n = 800 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 837 8998 (by decide) (by rfl)
  | 38 =>
    have hn : n = 800 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 838 9119 (by decide) (by rfl)
  | 39 =>
    have hn : n = 800 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 839 3400 (by decide) (by rfl)
  | 40 =>
    have hn : n = 800 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 840 2517 (by decide) (by rfl)
  | 41 =>
    have hn : n = 800 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 841 10634 (by decide) (by rfl)
  | 42 =>
    have hn : n = 800 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 842 4195 (by decide) (by rfl)
  | 43 =>
    have hn : n = 800 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 843 10348 (by decide) (by rfl)
  | 44 =>
    have hn : n = 800 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 844 1725 (by decide) (by rfl)
  | 45 =>
    have hn : n = 800 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 845 3870 (by decide) (by rfl)
  | 46 =>
    have hn : n = 800 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 846 3055 (by decide) (by rfl)
  | 47 =>
    have hn : n = 800 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 847 5264 (by decide) (by rfl)
  | 48 =>
    have hn : n = 800 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 848 2193 (by decide) (by rfl)
  | 49 =>
    have hn : n = 800 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 849 3250 (by decide) (by rfl)
  | 50 =>
    have hn : n = 800 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 850 3731 (by decide) (by rfl)
  | 51 =>
    have hn : n = 800 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 851 4020 (by decide) (by rfl)
  | 52 =>
    have hn : n = 800 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 852 25513 (by decide) (by rfl)
  | 53 =>
    have hn : n = 800 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 853 5894 (by decide) (by rfl)
  | 54 =>
    have hn : n = 800 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 854 2547 (by decide) (by rfl)
  | 55 =>
    have hn : n = 800 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 855 4120 (by decide) (by rfl)
  | 56 =>
    have hn : n = 800 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 856 4265 (by decide) (by rfl)
  | 57 =>
    have hn : n = 800 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 857 4170 (by decide) (by rfl)
  | 58 =>
    have hn : n = 800 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 858 2571 (by decide) (by rfl)
  | 59 =>
    have hn : n = 800 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 859 4220 (by decide) (by rfl)
  | 60 =>
    have hn : n = 800 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 860 2577 (by decide) (by rfl)
  | 61 =>
    have hn : n = 800 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 861 2590 (by decide) (by rfl)
  | 62 =>
    have hn : n = 800 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 862 4295 (by decide) (by rfl)
  | 63 =>
    have hn : n = 800 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 863 2592 (by decide) (by rfl)
  | 64 =>
    have hn : n = 800 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 864 2589 (by decide) (by rfl)
  | 65 =>
    have hn : n = 800 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 865 3458 (by decide) (by rfl)
  | 66 =>
    have hn : n = 800 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 866 4315 (by decide) (by rfl)
  | 67 =>
    have hn : n = 800 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 867 5908 (by decide) (by rfl)
  | 68 =>
    have hn : n = 800 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 868 6041 (by decide) (by rfl)
  | 69 =>
    have hn : n = 800 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 869 4150 (by decide) (by rfl)
  | 70 =>
    have hn : n = 800 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 870 3335 (by decide) (by rfl)
  | 71 =>
    have hn : n = 800 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 871 5768 (by decide) (by rfl)
  | 72 =>
    have hn : n = 800 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 872 1953 (by decide) (by rfl)
  | 73 =>
    have hn : n = 800 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 873 3610 (by decide) (by rfl)
  | 74 =>
    have hn : n = 800 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 874 1875 (by decide) (by rfl)
  | 75 =>
    have hn : n = 800 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 875 5628 (by decide) (by rfl)
  | 76 =>
    have hn : n = 800 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 876 16321 (by decide) (by rfl)
  | 77 =>
    have hn : n = 800 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 877 2990 (by decide) (by rfl)
  | 78 =>
    have hn : n = 800 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 878 2631 (by decide) (by rfl)
  | 79 =>
    have hn : n = 800 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 879 2800 (by decide) (by rfl)
  | 80 =>
    have hn : n = 800 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 880 4385 (by decide) (by rfl)
  | 81 =>
    have hn : n = 800 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 881 5418 (by decide) (by rfl)
  | 82 =>
    have hn : n = 800 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 882 2643 (by decide) (by rfl)
  | 83 =>
    have hn : n = 800 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 883 3380 (by decide) (by rfl)
  | 84 =>
    have hn : n = 800 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 884 1845 (by decide) (by rfl)
  | 85 =>
    have hn : n = 800 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 885 4390 (by decide) (by rfl)
  | 86 =>
    have hn : n = 800 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 886 4415 (by decide) (by rfl)
  | 87 =>
    have hn : n = 800 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 887 4280 (by decide) (by rfl)
  | 88 =>
    have hn : n = 800 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 888 2661 (by decide) (by rfl)
  | 89 =>
    have hn : n = 800 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 889 6146 (by decide) (by rfl)
  | 90 =>
    have hn : n = 800 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 890 2211 (by decide) (by rfl)
  | 91 =>
    have hn : n = 800 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 891 10972 (by decide) (by rfl)
  | 92 =>
    have hn : n = 800 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 892 2765 (by decide) (by rfl)
  | 93 =>
    have hn : n = 800 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 893 4430 (by decide) (by rfl)
  | 94 =>
    have hn : n = 800 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 894 11479 (by decide) (by rfl)
  | 95 =>
    have hn : n = 800 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 895 6272 (by decide) (by rfl)
  | 96 =>
    have hn : n = 800 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 896 1905 (by decide) (by rfl)
  | 97 =>
    have hn : n = 800 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 897 6202 (by decide) (by rfl)
  | 98 =>
    have hn : n = 800 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 898 2523 (by decide) (by rfl)
  | 99 =>
    have hn : n = 800 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 899 4100 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_900_999 (n : ℕ) (h1 : n ≥ 900) (h2 : n < 1000) : A268597 n > 0 := by
  have h : n - 900 < 100 := by omega
  generalize h_k : n - 900 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 900 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 900 10693 (by decide) (by rfl)
  | 1 =>
    have hn : n = 900 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 901 3542 (by decide) (by rfl)
  | 2 =>
    have hn : n = 900 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 902 1911 (by decide) (by rfl)
  | 3 =>
    have hn : n = 900 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 903 4360 (by decide) (by rfl)
  | 4 =>
    have hn : n = 900 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 904 16853 (by decide) (by rfl)
  | 5 =>
    have hn : n = 900 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 905 4490 (by decide) (by rfl)
  | 6 =>
    have hn : n = 900 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 906 27187 (by decide) (by rfl)
  | 7 =>
    have hn : n = 900 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 907 4460 (by decide) (by rfl)
  | 8 =>
    have hn : n = 900 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 908 2301 (by decide) (by rfl)
  | 9 =>
    have hn : n = 900 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 909 5782 (by decide) (by rfl)
  | 10 =>
    have hn : n = 900 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 910 4535 (by decide) (by rfl)
  | 11 =>
    have hn : n = 900 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 911 4240 (by decide) (by rfl)
  | 12 =>
    have hn : n = 900 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 912 2733 (by decide) (by rfl)
  | 13 =>
    have hn : n = 900 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 913 16682 (by decide) (by rfl)
  | 14 =>
    have hn : n = 900 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 914 4475 (by decide) (by rfl)
  | 15 =>
    have hn : n = 900 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 915 6244 (by decide) (by rfl)
  | 16 =>
    have hn : n = 900 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 916 6377 (by decide) (by rfl)
  | 17 =>
    have hn : n = 900 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 917 4158 (by decide) (by rfl)
  | 18 =>
    have hn : n = 900 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 918 11791 (by decide) (by rfl)
  | 19 =>
    have hn : n = 900 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 919 3800 (by decide) (by rfl)
  | 20 =>
    have hn : n = 900 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 920 2121 (by decide) (by rfl)
  | 21 =>
    have hn : n = 900 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 921 4570 (by decide) (by rfl)
  | 22 =>
    have hn : n = 900 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 922 3515 (by decide) (by rfl)
  | 23 =>
    have hn : n = 900 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 923 4380 (by decide) (by rfl)
  | 24 =>
    have hn : n = 900 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 924 1965 (by decide) (by rfl)
  | 25 =>
    have hn : n = 900 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 925 3230 (by decide) (by rfl)
  | 26 =>
    have hn : n = 900 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 926 1935 (by decide) (by rfl)
  | 27 =>
    have hn : n = 900 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 927 5152 (by decide) (by rfl)
  | 28 =>
    have hn : n = 900 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 928 5681 (by decide) (by rfl)
  | 29 =>
    have hn : n = 900 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 929 4450 (by decide) (by rfl)
  | 30 =>
    have hn : n = 900 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 930 2787 (by decide) (by rfl)
  | 31 =>
    have hn : n = 900 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 931 4580 (by decide) (by rfl)
  | 32 =>
    have hn : n = 900 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 932 4645 (by decide) (by rfl)
  | 33 =>
    have hn : n = 900 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 933 4630 (by decide) (by rfl)
  | 34 =>
    have hn : n = 900 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 934 6503 (by decide) (by rfl)
  | 35 =>
    have hn : n = 900 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 935 4520 (by decide) (by rfl)
  | 36 =>
    have hn : n = 900 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 936 2905 (by decide) (by rfl)
  | 37 =>
    have hn : n = 900 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 937 5978 (by decide) (by rfl)
  | 38 =>
    have hn : n = 900 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 938 2163 (by decide) (by rfl)
  | 39 =>
    have hn : n = 900 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 939 2860 (by decide) (by rfl)
  | 40 =>
    have hn : n = 900 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 940 4685 (by decide) (by rfl)
  | 41 =>
    have hn : n = 900 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 941 4670 (by decide) (by rfl)
  | 42 =>
    have hn : n = 900 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 942 2343 (by decide) (by rfl)
  | 43 =>
    have hn : n = 900 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 943 5936 (by decide) (by rfl)
  | 44 =>
    have hn : n = 900 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 944 2025 (by decide) (by rfl)
  | 45 =>
    have hn : n = 900 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 945 6538 (by decide) (by rfl)
  | 46 =>
    have hn : n = 900 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 946 4403 (by decide) (by rfl)
  | 47 =>
    have hn : n = 900 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 947 4660 (by decide) (by rfl)
  | 48 =>
    have hn : n = 900 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 948 2841 (by decide) (by rfl)
  | 49 =>
    have hn : n = 900 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 949 2870 (by decide) (by rfl)
  | 50 =>
    have hn : n = 900 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 950 4735 (by decide) (by rfl)
  | 51 =>
    have hn : n = 900 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 951 4312 (by decide) (by rfl)
  | 52 =>
    have hn : n = 900 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 952 6629 (by decide) (by rfl)
  | 53 =>
    have hn : n = 900 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 953 5922 (by decide) (by rfl)
  | 54 =>
    have hn : n = 900 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 954 2859 (by decide) (by rfl)
  | 55 =>
    have hn : n = 900 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 955 6524 (by decide) (by rfl)
  | 56 =>
    have hn : n = 900 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 956 2277 (by decide) (by rfl)
  | 57 =>
    have hn : n = 900 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 957 12142 (by decide) (by rfl)
  | 58 =>
    have hn : n = 900 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 958 6419 (by decide) (by rfl)
  | 59 =>
    have hn : n = 900 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 959 3520 (by decide) (by rfl)
  | 60 =>
    have hn : n = 900 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 960 4081 (by decide) (by rfl)
  | 61 =>
    have hn : n = 900 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 961 17594 (by decide) (by rfl)
  | 62 =>
    have hn : n = 900 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 962 10483 (by decide) (by rfl)
  | 63 =>
    have hn : n = 900 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 963 11908 (by decide) (by rfl)
  | 64 =>
    have hn : n = 900 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 964 4277 (by decide) (by rfl)
  | 65 =>
    have hn : n = 900 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 965 4710 (by decide) (by rfl)
  | 66 =>
    have hn : n = 900 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 966 2055 (by decide) (by rfl)
  | 67 =>
    have hn : n = 900 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 967 10648 (by decide) (by rfl)
  | 68 =>
    have hn : n = 900 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 968 2409 (by decide) (by rfl)
  | 69 =>
    have hn : n = 900 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 969 6706 (by decide) (by rfl)
  | 70 =>
    have hn : n = 900 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 970 4835 (by decide) (by rfl)
  | 71 =>
    have hn : n = 900 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 971 2916 (by decide) (by rfl)
  | 72 =>
    have hn : n = 900 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 972 2913 (by decide) (by rfl)
  | 73 =>
    have hn : n = 900 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 973 28334 (by decide) (by rfl)
  | 74 =>
    have hn : n = 900 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 974 2247 (by decide) (by rfl)
  | 75 =>
    have hn : n = 900 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 975 13072 (by decide) (by rfl)
  | 76 =>
    have hn : n = 900 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 976 6797 (by decide) (by rfl)
  | 77 =>
    have hn : n = 900 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 977 6594 (by decide) (by rfl)
  | 78 =>
    have hn : n = 900 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 978 2931 (by decide) (by rfl)
  | 79 =>
    have hn : n = 900 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 979 4820 (by decide) (by rfl)
  | 80 =>
    have hn : n = 900 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 980 2085 (by decide) (by rfl)
  | 81 =>
    have hn : n = 900 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 981 4870 (by decide) (by rfl)
  | 82 =>
    have hn : n = 900 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 982 6839 (by decide) (by rfl)
  | 83 =>
    have hn : n = 900 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 983 4440 (by decide) (by rfl)
  | 84 =>
    have hn : n = 900 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 984 2949 (by decide) (by rfl)
  | 85 =>
    have hn : n = 900 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 985 6818 (by decide) (by rfl)
  | 86 =>
    have hn : n = 900 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 986 4915 (by decide) (by rfl)
  | 87 =>
    have hn : n = 900 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 987 4732 (by decide) (by rfl)
  | 88 =>
    have hn : n = 900 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 988 6881 (by decide) (by rfl)
  | 89 =>
    have hn : n = 900 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 989 4350 (by decide) (by rfl)
  | 90 =>
    have hn : n = 900 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 990 67087 (by decide) (by rfl)
  | 91 =>
    have hn : n = 900 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 991 7904 (by decide) (by rfl)
  | 92 =>
    have hn : n = 900 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 992 2289 (by decide) (by rfl)
  | 93 =>
    have hn : n = 900 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 993 3010 (by decide) (by rfl)
  | 94 =>
    have hn : n = 900 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 994 4955 (by decide) (by rfl)
  | 95 =>
    have hn : n = 900 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 995 4740 (by decide) (by rfl)
  | 96 =>
    have hn : n = 900 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 996 5797 (by decide) (by rfl)
  | 97 =>
    have hn : n = 900 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 997 12662 (by decide) (by rfl)
  | 98 =>
    have hn : n = 900 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 998 2079 (by decide) (by rfl)
  | 99 =>
    have hn : n = 900 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 999 5000 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_1000_1099 (n : ℕ) (h1 : n ≥ 1000) (h2 : n < 1100) : A268597 n > 0 := by
  have h : n - 1000 < 100 := by omega
  generalize h_k : n - 1000 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 1000 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1000 4985 (by decide) (by rfl)
  | 1 =>
    have hn : n = 1000 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1001 4890 (by decide) (by rfl)
  | 2 =>
    have hn : n = 1000 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1002 3115 (by decide) (by rfl)
  | 3 =>
    have hn : n = 1000 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1003 10604 (by decide) (by rfl)
  | 4 =>
    have hn : n = 1000 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1004 4925 (by decide) (by rfl)
  | 5 =>
    have hn : n = 1000 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1005 4990 (by decide) (by rfl)
  | 6 =>
    have hn : n = 1000 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1006 10967 (by decide) (by rfl)
  | 7 =>
    have hn : n = 1000 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1007 4080 (by decide) (by rfl)
  | 8 =>
    have hn : n = 1000 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1008 12961 (by decide) (by rfl)
  | 9 =>
    have hn : n = 1000 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1009 3410 (by decide) (by rfl)
  | 10 =>
    have hn : n = 1000 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1010 2115 (by decide) (by rfl)
  | 11 =>
    have hn : n = 1000 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1011 6292 (by decide) (by rfl)
  | 12 =>
    have hn : n = 1000 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1012 5045 (by decide) (by rfl)
  | 13 =>
    have hn : n = 1000 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1013 5030 (by decide) (by rfl)
  | 14 =>
    have hn : n = 1000 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1014 2695 (by decide) (by rfl)
  | 15 =>
    have hn : n = 1000 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1015 16568 (by decide) (by rfl)
  | 16 =>
    have hn : n = 1000 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1016 2697 (by decide) (by rfl)
  | 17 =>
    have hn : n = 1000 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1017 4186 (by decide) (by rfl)
  | 18 =>
    have hn : n = 1000 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1018 7091 (by decide) (by rfl)
  | 19 =>
    have hn : n = 1000 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1019 4700 (by decide) (by rfl)
  | 20 =>
    have hn : n = 1000 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1020 3057 (by decide) (by rfl)
  | 21 =>
    have hn : n = 1000 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1021 4862 (by decide) (by rfl)
  | 22 =>
    have hn : n = 1000 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1022 2679 (by decide) (by rfl)
  | 23 =>
    have hn : n = 1000 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1023 2048 (by decide) (by rfl)
  | 24 =>
    have hn : n = 1000 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1024 4625 (by decide) (by rfl)
  | 25 =>
    have hn : n = 1000 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1025 4770 (by decide) (by rfl)
  | 26 =>
    have hn : n = 1000 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1026 7147 (by decide) (by rfl)
  | 27 =>
    have hn : n = 1000 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1027 7028 (by decide) (by rfl)
  | 28 =>
    have hn : n = 1000 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1028 2373 (by decide) (by rfl)
  | 29 =>
    have hn : n = 1000 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1029 7126 (by decide) (by rfl)
  | 30 =>
    have hn : n = 1000 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1030 4991 (by decide) (by rfl)
  | 31 =>
    have hn : n = 1000 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1031 6216 (by decide) (by rfl)
  | 32 =>
    have hn : n = 1000 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1032 3093 (by decide) (by rfl)
  | 33 =>
    have hn : n = 1000 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1033 8954 (by decide) (by rfl)
  | 34 =>
    have hn : n = 1000 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1034 2331 (by decide) (by rfl)
  | 35 =>
    have hn : n = 1000 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1035 6076 (by decide) (by rfl)
  | 36 =>
    have hn : n = 1000 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1036 5165 (by decide) (by rfl)
  | 37 =>
    have hn : n = 1000 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1037 7014 (by decide) (by rfl)
  | 38 =>
    have hn : n = 1000 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1038 2703 (by decide) (by rfl)
  | 39 =>
    have hn : n = 1000 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1039 4880 (by decide) (by rfl)
  | 40 =>
    have hn : n = 1000 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1040 3117 (by decide) (by rfl)
  | 41 =>
    have hn : n = 1000 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1041 13234 (by decide) (by rfl)
  | 42 =>
    have hn : n = 1000 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1042 5195 (by decide) (by rfl)
  | 43 =>
    have hn : n = 1000 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1043 4980 (by decide) (by rfl)
  | 44 =>
    have hn : n = 1000 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1044 3685 (by decide) (by rfl)
  | 45 =>
    have hn : n = 1000 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1045 36038 (by decide) (by rfl)
  | 46 =>
    have hn : n = 1000 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1046 2607 (by decide) (by rfl)
  | 47 =>
    have hn : n = 1000 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1047 5080 (by decide) (by rfl)
  | 48 =>
    have hn : n = 1000 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1048 11429 (by decide) (by rfl)
  | 49 =>
    have hn : n = 1000 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1049 4250 (by decide) (by rfl)
  | 50 =>
    have hn : n = 1000 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1050 2235 (by decide) (by rfl)
  | 51 =>
    have hn : n = 1000 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1051 7196 (by decide) (by rfl)
  | 52 =>
    have hn : n = 1000 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1052 2673 (by decide) (by rfl)
  | 53 =>
    have hn : n = 1000 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1053 5230 (by decide) (by rfl)
  | 54 =>
    have hn : n = 1000 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1054 2175 (by decide) (by rfl)
  | 55 =>
    have hn : n = 1000 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1055 4640 (by decide) (by rfl)
  | 56 =>
    have hn : n = 1000 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1056 7357 (by decide) (by rfl)
  | 57 =>
    have hn : n = 1000 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1057 7322 (by decide) (by rfl)
  | 58 =>
    have hn : n = 1000 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1058 11235 (by decide) (by rfl)
  | 59 =>
    have hn : n = 1000 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1059 33892 (by decide) (by rfl)
  | 60 =>
    have hn : n = 1000 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1060 4085 (by decide) (by rfl)
  | 61 =>
    have hn : n = 1000 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1061 5190 (by decide) (by rfl)
  | 62 =>
    have hn : n = 1000 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1062 3183 (by decide) (by rfl)
  | 63 =>
    have hn : n = 1000 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1063 5096 (by decide) (by rfl)
  | 64 =>
    have hn : n = 1000 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1064 2265 (by decide) (by rfl)
  | 65 =>
    have hn : n = 1000 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1065 4522 (by decide) (by rfl)
  | 66 =>
    have hn : n = 1000 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1066 5315 (by decide) (by rfl)
  | 67 =>
    have hn : n = 1000 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1067 5260 (by decide) (by rfl)
  | 68 =>
    have hn : n = 1000 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1068 2829 (by decide) (by rfl)
  | 69 =>
    have hn : n = 1000 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1069 5150 (by decide) (by rfl)
  | 70 =>
    have hn : n = 1000 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1070 3207 (by decide) (by rfl)
  | 71 =>
    have hn : n = 1000 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1071 6832 (by decide) (by rfl)
  | 72 =>
    have hn : n = 1000 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1072 5345 (by decide) (by rfl)
  | 73 =>
    have hn : n = 1000 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1073 7266 (by decide) (by rfl)
  | 74 =>
    have hn : n = 1000 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1074 5275 (by decide) (by rfl)
  | 75 =>
    have hn : n = 1000 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1075 7364 (by decide) (by rfl)
  | 76 =>
    have hn : n = 1000 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1076 11445 (by decide) (by rfl)
  | 77 =>
    have hn : n = 1000 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1077 3430 (by decide) (by rfl)
  | 78 =>
    have hn : n = 1000 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1078 4823 (by decide) (by rfl)
  | 79 =>
    have hn : n = 1000 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1079 4600 (by decide) (by rfl)
  | 80 =>
    have hn : n = 1000 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1080 13897 (by decide) (by rfl)
  | 81 =>
    have hn : n = 1000 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1081 3290 (by decide) (by rfl)
  | 82 =>
    have hn : n = 1000 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1082 3231 (by decide) (by rfl)
  | 83 =>
    have hn : n = 1000 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1083 29884 (by decide) (by rfl)
  | 84 =>
    have hn : n = 1000 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1084 3965 (by decide) (by rfl)
  | 85 =>
    have hn : n = 1000 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1085 18582 (by decide) (by rfl)
  | 86 =>
    have hn : n = 1000 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1086 4255 (by decide) (by rfl)
  | 87 =>
    have hn : n = 1000 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1087 4160 (by decide) (by rfl)
  | 88 =>
    have hn : n = 1000 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1088 2769 (by decide) (by rfl)
  | 89 =>
    have hn : n = 1000 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1089 5410 (by decide) (by rfl)
  | 90 =>
    have hn : n = 1000 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1090 3395 (by decide) (by rfl)
  | 91 =>
    have hn : n = 1000 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1091 5380 (by decide) (by rfl)
  | 92 =>
    have hn : n = 1000 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1092 3273 (by decide) (by rfl)
  | 93 =>
    have hn : n = 1000 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1093 3910 (by decide) (by rfl)
  | 94 =>
    have hn : n = 1000 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1094 3279 (by decide) (by rfl)
  | 95 =>
    have hn : n = 1000 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1095 7336 (by decide) (by rfl)
  | 96 =>
    have hn : n = 1000 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1096 4697 (by decide) (by rfl)
  | 97 =>
    have hn : n = 1000 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1097 5370 (by decide) (by rfl)
  | 98 =>
    have hn : n = 1000 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1098 2739 (by decide) (by rfl)
  | 99 =>
    have hn : n = 1000 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1099 3500 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_1100_1199 (n : ℕ) (h1 : n ≥ 1100) (h2 : n < 1200) : A268597 n > 0 := by
  have h : n - 1100 < 100 := by omega
  generalize h_k : n - 1100 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 1100 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1100 5485 (by decide) (by rfl)
  | 1 =>
    have hn : n = 1100 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1101 5470 (by decide) (by rfl)
  | 2 =>
    have hn : n = 1100 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1102 7679 (by decide) (by rfl)
  | 3 =>
    have hn : n = 1100 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1103 4560 (by decide) (by rfl)
  | 4 =>
    have hn : n = 1100 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1104 3309 (by decide) (by rfl)
  | 5 =>
    have hn : n = 1100 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1105 4466 (by decide) (by rfl)
  | 6 =>
    have hn : n = 1100 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1106 2355 (by decide) (by rfl)
  | 7 =>
    have hn : n = 1100 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1107 7588 (by decide) (by rfl)
  | 8 =>
    have hn : n = 1100 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1108 6149 (by decide) (by rfl)
  | 9 =>
    have hn : n = 1100 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1109 5350 (by decide) (by rfl)
  | 10 =>
    have hn : n = 1100 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1110 3327 (by decide) (by rfl)
  | 11 =>
    have hn : n = 1100 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1111 13208 (by decide) (by rfl)
  | 12 =>
    have hn : n = 1100 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1112 5545 (by decide) (by rfl)
  | 13 =>
    have hn : n = 1100 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1113 5434 (by decide) (by rfl)
  | 14 =>
    have hn : n = 1100 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1114 7163 (by decide) (by rfl)
  | 15 =>
    have hn : n = 1100 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1115 5340 (by decide) (by rfl)
  | 16 =>
    have hn : n = 1100 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1116 33697 (by decide) (by rfl)
  | 17 =>
    have hn : n = 1100 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1117 10478 (by decide) (by rfl)
  | 18 =>
    have hn : n = 1100 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1118 2847 (by decide) (by rfl)
  | 19 =>
    have hn : n = 1100 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1119 4960 (by decide) (by rfl)
  | 20 =>
    have hn : n = 1100 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1120 5585 (by decide) (by rfl)
  | 21 =>
    have hn : n = 1100 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1121 5082 (by decide) (by rfl)
  | 22 =>
    have hn : n = 1100 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1122 7819 (by decide) (by rfl)
  | 23 =>
    have hn : n = 1100 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1123 4004 (by decide) (by rfl)
  | 24 =>
    have hn : n = 1100 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1124 2325 (by decide) (by rfl)
  | 25 =>
    have hn : n = 1100 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1125 7798 (by decide) (by rfl)
  | 26 =>
    have hn : n = 1100 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1126 5615 (by decide) (by rfl)
  | 27 =>
    have hn : n = 1100 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1127 5160 (by decide) (by rfl)
  | 28 =>
    have hn : n = 1100 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1128 7861 (by decide) (by rfl)
  | 29 =>
    have hn : n = 1100 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1129 5450 (by decide) (by rfl)
  | 30 =>
    have hn : n = 1100 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1130 3387 (by decide) (by rfl)
  | 31 =>
    have hn : n = 1100 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1131 7756 (by decide) (by rfl)
  | 32 =>
    have hn : n = 1100 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1132 5453 (by decide) (by rfl)
  | 33 =>
    have hn : n = 1100 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1133 4590 (by decide) (by rfl)
  | 34 =>
    have hn : n = 1100 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1134 3535 (by decide) (by rfl)
  | 35 =>
    have hn : n = 1100 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1135 5360 (by decide) (by rfl)
  | 36 =>
    have hn : n = 1100 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1136 2385 (by decide) (by rfl)
  | 37 =>
    have hn : n = 1100 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1137 7882 (by decide) (by rfl)
  | 38 =>
    have hn : n = 1100 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1138 12419 (by decide) (by rfl)
  | 39 =>
    have hn : n = 1100 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1139 5300 (by decide) (by rfl)
  | 40 =>
    have hn : n = 1100 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1140 7693 (by decide) (by rfl)
  | 41 =>
    have hn : n = 1100 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1141 33542 (by decide) (by rfl)
  | 42 =>
    have hn : n = 1100 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1142 2295 (by decide) (by rfl)
  | 43 =>
    have hn : n = 1100 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1143 5560 (by decide) (by rfl)
  | 44 =>
    have hn : n = 1100 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1144 19193 (by decide) (by rfl)
  | 45 =>
    have hn : n = 1100 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1145 5690 (by decide) (by rfl)
  | 46 =>
    have hn : n = 1100 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1146 6727 (by decide) (by rfl)
  | 47 =>
    have hn : n = 1100 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1147 5660 (by decide) (by rfl)
  | 48 =>
    have hn : n = 1100 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1148 2445 (by decide) (by rfl)
  | 49 =>
    have hn : n = 1100 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1149 4030 (by decide) (by rfl)
  | 50 =>
    have hn : n = 1100 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1150 25967 (by decide) (by rfl)
  | 51 =>
    have hn : n = 1100 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1151 3456 (by decide) (by rfl)
  | 52 =>
    have hn : n = 1100 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1152 3009 (by decide) (by rfl)
  | 53 =>
    have hn : n = 1100 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1153 7994 (by decide) (by rfl)
  | 54 =>
    have hn : n = 1100 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1154 2499 (by decide) (by rfl)
  | 55 =>
    have hn : n = 1100 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1155 7924 (by decide) (by rfl)
  | 56 =>
    have hn : n = 1100 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1156 3605 (by decide) (by rfl)
  | 57 =>
    have hn : n = 1100 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1157 12518 (by decide) (by rfl)
  | 58 =>
    have hn : n = 1100 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1158 6919 (by decide) (by rfl)
  | 59 =>
    have hn : n = 1100 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1159 7784 (by decide) (by rfl)
  | 60 =>
    have hn : n = 1100 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1160 2457 (by decide) (by rfl)
  | 61 =>
    have hn : n = 1100 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1161 5770 (by decide) (by rfl)
  | 62 =>
    have hn : n = 1100 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1162 12683 (by decide) (by rfl)
  | 63 =>
    have hn : n = 1100 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1163 12364 (by decide) (by rfl)
  | 64 =>
    have hn : n = 1100 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1164 3325 (by decide) (by rfl)
  | 65 =>
    have hn : n = 1100 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1165 8078 (by decide) (by rfl)
  | 66 =>
    have hn : n = 1100 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1166 5815 (by decide) (by rfl)
  | 67 =>
    have hn : n = 1100 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1167 7504 (by decide) (by rfl)
  | 68 =>
    have hn : n = 1100 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1168 3185 (by decide) (by rfl)
  | 69 =>
    have hn : n = 1100 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1169 5490 (by decide) (by rfl)
  | 70 =>
    have hn : n = 1100 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1170 21907 (by decide) (by rfl)
  | 71 =>
    have hn : n = 1100 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1171 12452 (by decide) (by rfl)
  | 72 =>
    have hn : n = 1100 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1172 3501 (by decide) (by rfl)
  | 73 =>
    have hn : n = 1100 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1173 4774 (by decide) (by rfl)
  | 74 =>
    have hn : n = 1100 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1174 3575 (by decide) (by rfl)
  | 75 =>
    have hn : n = 1100 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1175 7224 (by decide) (by rfl)
  | 76 =>
    have hn : n = 1100 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1176 2505 (by decide) (by rfl)
  | 77 =>
    have hn : n = 1100 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1177 9386 (by decide) (by rfl)
  | 78 =>
    have hn : n = 1100 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1178 2907 (by decide) (by rfl)
  | 79 =>
    have hn : n = 1100 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1179 3740 (by decide) (by rfl)
  | 80 =>
    have hn : n = 1100 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1180 12881 (by decide) (by rfl)
  | 81 =>
    have hn : n = 1100 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1181 5790 (by decide) (by rfl)
  | 82 =>
    have hn : n = 1100 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1182 3543 (by decide) (by rfl)
  | 83 =>
    have hn : n = 1100 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1183 6944 (by decide) (by rfl)
  | 84 =>
    have hn : n = 1100 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1184 5825 (by decide) (by rfl)
  | 85 =>
    have hn : n = 1100 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1185 8218 (by decide) (by rfl)
  | 86 =>
    have hn : n = 1100 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1186 4355 (by decide) (by rfl)
  | 87 =>
    have hn : n = 1100 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1187 5220 (by decide) (by rfl)
  | 88 =>
    have hn : n = 1100 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1188 3561 (by decide) (by rfl)
  | 89 =>
    have hn : n = 1100 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1189 4070 (by decide) (by rfl)
  | 90 =>
    have hn : n = 1100 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1190 2751 (by decide) (by rfl)
  | 91 =>
    have hn : n = 1100 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1191 12232 (by decide) (by rfl)
  | 92 =>
    have hn : n = 1100 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1192 5369 (by decide) (by rfl)
  | 93 =>
    have hn : n = 1100 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1193 5930 (by decide) (by rfl)
  | 94 =>
    have hn : n = 1100 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1194 3579 (by decide) (by rfl)
  | 95 =>
    have hn : n = 1100 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1195 7436 (by decide) (by rfl)
  | 96 =>
    have hn : n = 1100 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1196 2709 (by decide) (by rfl)
  | 97 =>
    have hn : n = 1100 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1197 8302 (by decide) (by rfl)
  | 98 =>
    have hn : n = 1100 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1198 5159 (by decide) (by rfl)
  | 99 =>
    have hn : n = 1100 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1199 4400 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_1200_1299 (n : ℕ) (h1 : n ≥ 1200) (h2 : n < 1300) : A268597 n > 0 := by
  have h : n - 1200 < 100 := by omega
  generalize h_k : n - 1200 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 1200 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1200 3745 (by decide) (by rfl)
  | 1 =>
    have hn : n = 1200 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1201 4370 (by decide) (by rfl)
  | 2 =>
    have hn : n = 1200 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1202 3219 (by decide) (by rfl)
  | 3 =>
    have hn : n = 1200 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1203 7252 (by decide) (by rfl)
  | 4 =>
    have hn : n = 1200 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1204 5957 (by decide) (by rfl)
  | 5 =>
    have hn : n = 1200 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1205 5910 (by decide) (by rfl)
  | 6 =>
    have hn : n = 1200 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1206 8407 (by decide) (by rfl)
  | 7 =>
    have hn : n = 1200 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1207 14456 (by decide) (by rfl)
  | 8 =>
    have hn : n = 1200 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1208 3081 (by decide) (by rfl)
  | 9 =>
    have hn : n = 1200 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1209 6010 (by decide) (by rfl)
  | 10 =>
    have hn : n = 1200 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1210 8183 (by decide) (by rfl)
  | 11 =>
    have hn : n = 1200 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1211 5820 (by decide) (by rfl)
  | 12 =>
    have hn : n = 1200 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1212 15613 (by decide) (by rfl)
  | 13 =>
    have hn : n = 1200 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1213 3710 (by decide) (by rfl)
  | 14 =>
    have hn : n = 1200 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1214 3159 (by decide) (by rfl)
  | 15 =>
    have hn : n = 1200 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1215 5824 (by decide) (by rfl)
  | 16 =>
    have hn : n = 1200 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1216 6065 (by decide) (by rfl)
  | 17 =>
    have hn : n = 1200 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1217 5970 (by decide) (by rfl)
  | 18 =>
    have hn : n = 1200 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1218 2595 (by decide) (by rfl)
  | 19 =>
    have hn : n = 1200 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1219 15236 (by decide) (by rfl)
  | 20 =>
    have hn : n = 1200 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1220 2541 (by decide) (by rfl)
  | 21 =>
    have hn : n = 1200 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1221 6070 (by decide) (by rfl)
  | 22 =>
    have hn : n = 1200 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1222 3815 (by decide) (by rfl)
  | 23 =>
    have hn : n = 1200 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1223 5544 (by decide) (by rfl)
  | 24 =>
    have hn : n = 1200 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1224 3669 (by decide) (by rfl)
  | 25 =>
    have hn : n = 1200 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1225 8498 (by decide) (by rfl)
  | 26 =>
    have hn : n = 1200 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1226 6115 (by decide) (by rfl)
  | 27 =>
    have hn : n = 1200 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1227 34348 (by decide) (by rfl)
  | 28 =>
    have hn : n = 1200 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1228 8561 (by decide) (by rfl)
  | 29 =>
    have hn : n = 1200 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1229 5550 (by decide) (by rfl)
  | 30 =>
    have hn : n = 1200 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1230 3687 (by decide) (by rfl)
  | 31 =>
    have hn : n = 1200 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1231 3920 (by decide) (by rfl)
  | 32 =>
    have hn : n = 1200 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1232 3681 (by decide) (by rfl)
  | 33 =>
    have hn : n = 1200 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1233 6130 (by decide) (by rfl)
  | 34 =>
    have hn : n = 1200 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1234 6155 (by decide) (by rfl)
  | 35 =>
    have hn : n = 1200 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1235 8148 (by decide) (by rfl)
  | 36 =>
    have hn : n = 1200 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1236 8617 (by decide) (by rfl)
  | 37 =>
    have hn : n = 1200 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1237 8582 (by decide) (by rfl)
  | 38 =>
    have hn : n = 1200 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1238 3711 (by decide) (by rfl)
  | 39 =>
    have hn : n = 1200 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1239 6040 (by decide) (by rfl)
  | 40 =>
    have hn : n = 1200 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1240 6185 (by decide) (by rfl)
  | 41 =>
    have hn : n = 1200 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1241 5130 (by decide) (by rfl)
  | 42 =>
    have hn : n = 1200 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1242 7843 (by decide) (by rfl)
  | 43 =>
    have hn : n = 1200 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1243 6140 (by decide) (by rfl)
  | 44 =>
    have hn : n = 1200 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1244 2877 (by decide) (by rfl)
  | 45 =>
    have hn : n = 1200 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1245 5278 (by decide) (by rfl)
  | 46 =>
    have hn : n = 1200 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1246 13607 (by decide) (by rfl)
  | 47 =>
    have hn : n = 1200 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1247 10208 (by decide) (by rfl)
  | 48 =>
    have hn : n = 1200 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1248 4945 (by decide) (by rfl)
  | 49 =>
    have hn : n = 1200 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1249 5474 (by decide) (by rfl)
  | 50 =>
    have hn : n = 1200 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1250 3699 (by decide) (by rfl)
  | 51 =>
    have hn : n = 1200 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1251 8596 (by decide) (by rfl)
  | 52 =>
    have hn : n = 1200 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1252 6245 (by decide) (by rfl)
  | 53 =>
    have hn : n = 1200 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1253 11374 (by decide) (by rfl)
  | 54 =>
    have hn : n = 1200 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1254 4615 (by decide) (by rfl)
  | 55 =>
    have hn : n = 1200 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1255 8456 (by decide) (by rfl)
  | 56 =>
    have hn : n = 1200 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1256 35641 (by decide) (by rfl)
  | 57 =>
    have hn : n = 1200 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1257 13618 (by decide) (by rfl)
  | 58 =>
    have hn : n = 1200 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1258 13739 (by decide) (by rfl)
  | 59 =>
    have hn : n = 1200 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1259 5100 (by decide) (by rfl)
  | 60 =>
    have hn : n = 1200 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1260 2685 (by decide) (by rfl)
  | 61 =>
    have hn : n = 1200 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1261 16094 (by decide) (by rfl)
  | 62 =>
    have hn : n = 1200 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1262 2655 (by decide) (by rfl)
  | 63 =>
    have hn : n = 1200 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1263 8176 (by decide) (by rfl)
  | 64 =>
    have hn : n = 1200 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1264 8177 (by decide) (by rfl)
  | 65 =>
    have hn : n = 1200 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1265 15522 (by decide) (by rfl)
  | 66 =>
    have hn : n = 1200 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1266 3955 (by decide) (by rfl)
  | 67 =>
    have hn : n = 1200 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1267 6260 (by decide) (by rfl)
  | 68 =>
    have hn : n = 1200 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1268 2565 (by decide) (by rfl)
  | 69 =>
    have hn : n = 1200 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1269 6310 (by decide) (by rfl)
  | 70 =>
    have hn : n = 1200 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1270 10571 (by decide) (by rfl)
  | 71 =>
    have hn : n = 1200 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1271 7896 (by decide) (by rfl)
  | 72 =>
    have hn : n = 1200 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1272 45769 (by decide) (by rfl)
  | 73 =>
    have hn : n = 1200 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1273 8834 (by decide) (by rfl)
  | 74 =>
    have hn : n = 1200 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1274 2715 (by decide) (by rfl)
  | 75 =>
    have hn : n = 1200 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1275 8764 (by decide) (by rfl)
  | 76 =>
    have hn : n = 1200 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1276 23921 (by decide) (by rfl)
  | 77 =>
    have hn : n = 1200 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1277 6030 (by decide) (by rfl)
  | 78 =>
    have hn : n = 1200 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1278 3831 (by decide) (by rfl)
  | 79 =>
    have hn : n = 1200 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1279 6400 (by decide) (by rfl)
  | 80 =>
    have hn : n = 1200 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1280 2793 (by decide) (by rfl)
  | 81 =>
    have hn : n = 1200 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1281 13882 (by decide) (by rfl)
  | 82 =>
    have hn : n = 1200 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1282 6251 (by decide) (by rfl)
  | 83 =>
    have hn : n = 1200 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1283 6180 (by decide) (by rfl)
  | 84 =>
    have hn : n = 1200 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1284 3849 (by decide) (by rfl)
  | 85 =>
    have hn : n = 1200 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1285 16406 (by decide) (by rfl)
  | 86 =>
    have hn : n = 1200 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1286 3267 (by decide) (by rfl)
  | 87 =>
    have hn : n = 1200 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1287 6280 (by decide) (by rfl)
  | 88 =>
    have hn : n = 1200 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1288 4745 (by decide) (by rfl)
  | 89 =>
    have hn : n = 1200 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1289 6330 (by decide) (by rfl)
  | 90 =>
    have hn : n = 1200 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1290 3867 (by decide) (by rfl)
  | 91 =>
    have hn : n = 1200 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1291 8876 (by decide) (by rfl)
  | 92 =>
    have hn : n = 1200 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1292 3873 (by decide) (by rfl)
  | 93 =>
    have hn : n = 1200 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1293 6430 (by decide) (by rfl)
  | 94 =>
    have hn : n = 1200 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1294 6455 (by decide) (by rfl)
  | 95 =>
    have hn : n = 1200 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1295 3888 (by decide) (by rfl)
  | 96 =>
    have hn : n = 1200 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1296 9037 (by decide) (by rfl)
  | 97 =>
    have hn : n = 1200 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1297 6578 (by decide) (by rfl)
  | 98 =>
    have hn : n = 1200 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1298 3879 (by decide) (by rfl)
  | 99 =>
    have hn : n = 1200 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1299 4180 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_1300_1399 (n : ℕ) (h1 : n ≥ 1300) (h2 : n < 1400) : A268597 n > 0 := by
  have h : n - 1300 < 100 := by omega
  generalize h_k : n - 1300 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 1300 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1300 5621 (by decide) (by rfl)
  | 1 =>
    have hn : n = 1300 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1301 6470 (by decide) (by rfl)
  | 2 =>
    have hn : n = 1300 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1302 3903 (by decide) (by rfl)
  | 3 =>
    have hn : n = 1300 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1303 8792 (by decide) (by rfl)
  | 4 =>
    have hn : n = 1300 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1304 2745 (by decide) (by rfl)
  | 5 =>
    have hn : n = 1300 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1305 9058 (by decide) (by rfl)
  | 6 =>
    have hn : n = 1300 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1306 6515 (by decide) (by rfl)
  | 7 =>
    have hn : n = 1300 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1307 8652 (by decide) (by rfl)
  | 8 =>
    have hn : n = 1300 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1308 3921 (by decide) (by rfl)
  | 9 =>
    have hn : n = 1300 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1309 4510 (by decide) (by rfl)
  | 10 =>
    have hn : n = 1300 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1310 6535 (by decide) (by rfl)
  | 11 =>
    have hn : n = 1300 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1311 5920 (by decide) (by rfl)
  | 12 =>
    have hn : n = 1300 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1312 9149 (by decide) (by rfl)
  | 13 =>
    have hn : n = 1300 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1313 6530 (by decide) (by rfl)
  | 14 =>
    have hn : n = 1300 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1314 6307 (by decide) (by rfl)
  | 15 =>
    have hn : n = 1300 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1315 8036 (by decide) (by rfl)
  | 16 =>
    have hn : n = 1300 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1316 3477 (by decide) (by rfl)
  | 17 =>
    have hn : n = 1300 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1317 9142 (by decide) (by rfl)
  | 18 =>
    have hn : n = 1300 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1318 16991 (by decide) (by rfl)
  | 19 =>
    have hn : n = 1300 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1319 4840 (by decide) (by rfl)
  | 20 =>
    have hn : n = 1300 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1320 3957 (by decide) (by rfl)
  | 21 =>
    have hn : n = 1300 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1321 5642 (by decide) (by rfl)
  | 22 =>
    have hn : n = 1300 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1322 3087 (by decide) (by rfl)
  | 23 =>
    have hn : n = 1300 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1323 23788 (by decide) (by rfl)
  | 24 =>
    have hn : n = 1300 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1324 6605 (by decide) (by rfl)
  | 25 =>
    have hn : n = 1300 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1325 6590 (by decide) (by rfl)
  | 26 =>
    have hn : n = 1300 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1326 3567 (by decide) (by rfl)
  | 27 =>
    have hn : n = 1300 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1327 6320 (by decide) (by rfl)
  | 28 =>
    have hn : n = 1300 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1328 3981 (by decide) (by rfl)
  | 29 =>
    have hn : n = 1300 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1329 6610 (by decide) (by rfl)
  | 30 =>
    have hn : n = 1300 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1330 6635 (by decide) (by rfl)
  | 31 =>
    have hn : n = 1300 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1331 6420 (by decide) (by rfl)
  | 32 =>
    have hn : n = 1300 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1332 3333 (by decide) (by rfl)
  | 33 =>
    have hn : n = 1300 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1333 7406 (by decide) (by rfl)
  | 34 =>
    have hn : n = 1300 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1334 2775 (by decide) (by rfl)
  | 35 =>
    have hn : n = 1300 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1335 6520 (by decide) (by rfl)
  | 36 =>
    have hn : n = 1300 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1336 14597 (by decide) (by rfl)
  | 37 =>
    have hn : n = 1300 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1337 14498 (by decide) (by rfl)
  | 38 =>
    have hn : n = 1300 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1338 7579 (by decide) (by rfl)
  | 39 =>
    have hn : n = 1300 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1339 6620 (by decide) (by rfl)
  | 40 =>
    have hn : n = 1300 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1340 30337 (by decide) (by rfl)
  | 41 =>
    have hn : n = 1300 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1341 14542 (by decide) (by rfl)
  | 42 =>
    have hn : n = 1300 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1342 22559 (by decide) (by rfl)
  | 43 =>
    have hn : n = 1300 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1343 5440 (by decide) (by rfl)
  | 44 =>
    have hn : n = 1300 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1344 2865 (by decide) (by rfl)
  | 45 =>
    have hn : n = 1300 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1345 4130 (by decide) (by rfl)
  | 46 =>
    have hn : n = 1300 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1346 14595 (by decide) (by rfl)
  | 47 =>
    have hn : n = 1300 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1347 4420 (by decide) (by rfl)
  | 48 =>
    have hn : n = 1300 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1348 9269 (by decide) (by rfl)
  | 49 =>
    have hn : n = 1300 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1349 5750 (by decide) (by rfl)
  | 50 =>
    have hn : n = 1300 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1350 40951 (by decide) (by rfl)
  | 51 =>
    have hn : n = 1300 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1351 9128 (by decide) (by rfl)
  | 52 =>
    have hn : n = 1300 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1352 3129 (by decide) (by rfl)
  | 53 =>
    have hn : n = 1300 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1353 4810 (by decide) (by rfl)
  | 54 =>
    have hn : n = 1300 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1354 38483 (by decide) (by rfl)
  | 55 =>
    have hn : n = 1300 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1355 6540 (by decide) (by rfl)
  | 56 =>
    have hn : n = 1300 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1356 5405 (by decide) (by rfl)
  | 57 =>
    have hn : n = 1300 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1357 9422 (by decide) (by rfl)
  | 58 =>
    have hn : n = 1300 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1358 2895 (by decide) (by rfl)
  | 59 =>
    have hn : n = 1300 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1359 5200 (by decide) (by rfl)
  | 60 =>
    have hn : n = 1300 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1360 54161 (by decide) (by rfl)
  | 61 =>
    have hn : n = 1300 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1361 6690 (by decide) (by rfl)
  | 62 =>
    have hn : n = 1300 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1362 4083 (by decide) (by rfl)
  | 63 =>
    have hn : n = 1300 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1363 6740 (by decide) (by rfl)
  | 64 =>
    have hn : n = 1300 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1364 6725 (by decide) (by rfl)
  | 65 =>
    have hn : n = 1300 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1365 6118 (by decide) (by rfl)
  | 66 =>
    have hn : n = 1300 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1366 9527 (by decide) (by rfl)
  | 67 =>
    have hn : n = 1300 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1367 6360 (by decide) (by rfl)
  | 68 =>
    have hn : n = 1300 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1368 3657 (by decide) (by rfl)
  | 69 =>
    have hn : n = 1300 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1369 4730 (by decide) (by rfl)
  | 70 =>
    have hn : n = 1300 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1370 3171 (by decide) (by rfl)
  | 71 =>
    have hn : n = 1300 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1371 8428 (by decide) (by rfl)
  | 72 =>
    have hn : n = 1300 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1372 9569 (by decide) (by rfl)
  | 73 =>
    have hn : n = 1300 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1373 6830 (by decide) (by rfl)
  | 74 =>
    have hn : n = 1300 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1374 4119 (by decide) (by rfl)
  | 75 =>
    have hn : n = 1300 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1375 8288 (by decide) (by rfl)
  | 76 =>
    have hn : n = 1300 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1376 3393 (by decide) (by rfl)
  | 77 =>
    have hn : n = 1300 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1377 5698 (by decide) (by rfl)
  | 78 =>
    have hn : n = 1300 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1378 6923 (by decide) (by rfl)
  | 79 =>
    have hn : n = 1300 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1379 5700 (by decide) (by rfl)
  | 80 =>
    have hn : n = 1300 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1380 3621 (by decide) (by rfl)
  | 81 =>
    have hn : n = 1300 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1381 25574 (by decide) (by rfl)
  | 82 =>
    have hn : n = 1300 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1382 4143 (by decide) (by rfl)
  | 83 =>
    have hn : n = 1300 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1383 9352 (by decide) (by rfl)
  | 84 =>
    have hn : n = 1300 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1384 4025 (by decide) (by rfl)
  | 85 =>
    have hn : n = 1300 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1385 6570 (by decide) (by rfl)
  | 86 =>
    have hn : n = 1300 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1386 2955 (by decide) (by rfl)
  | 87 =>
    have hn : n = 1300 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1387 14828 (by decide) (by rfl)
  | 88 =>
    have hn : n = 1300 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1388 3741 (by decide) (by rfl)
  | 89 =>
    have hn : n = 1300 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1389 4270 (by decide) (by rfl)
  | 90 =>
    have hn : n = 1300 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1390 5135 (by decide) (by rfl)
  | 91 =>
    have hn : n = 1300 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1391 6640 (by decide) (by rfl)
  | 92 =>
    have hn : n = 1300 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1392 9457 (by decide) (by rfl)
  | 93 =>
    have hn : n = 1300 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1393 9674 (by decide) (by rfl)
  | 94 =>
    have hn : n = 1300 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1394 4167 (by decide) (by rfl)
  | 95 =>
    have hn : n = 1300 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1395 5236 (by decide) (by rfl)
  | 96 =>
    have hn : n = 1300 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1396 23477 (by decide) (by rfl)
  | 97 =>
    have hn : n = 1300 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1397 6870 (by decide) (by rfl)
  | 98 =>
    have hn : n = 1300 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1398 26239 (by decide) (by rfl)
  | 99 =>
    have hn : n = 1300 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1399 6200 (by decide) (by rfl)
  | _ + 100 => omega

lemma solve_interval_1400_1499 (n : ℕ) (h1 : n ≥ 1400) (h2 : n < 1500) : A268597 n > 0 := by
  have h : n - 1400 < 100 := by omega
  generalize h_k : n - 1400 = k
  rw [h_k] at h
  match k with
  | 0 =>
    have hn : n = 1400 + 0 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1400 2985 (by decide) (by rfl)
  | 1 =>
    have hn : n = 1400 + 1 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1401 15202 (by decide) (by rfl)
  | 2 =>
    have hn : n = 1400 + 2 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1402 6083 (by decide) (by rfl)
  | 3 =>
    have hn : n = 1400 + 3 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1403 6780 (by decide) (by rfl)
  | 4 =>
    have hn : n = 1400 + 4 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1404 6925 (by decide) (by rfl)
  | 5 =>
    have hn : n = 1400 + 5 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1405 17966 (by decide) (by rfl)
  | 6 =>
    have hn : n = 1400 + 6 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1406 3519 (by decide) (by rfl)
  | 7 =>
    have hn : n = 1400 + 7 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1407 4480 (by decide) (by rfl)
  | 8 =>
    have hn : n = 1400 + 8 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1408 15389 (by decide) (by rfl)
  | 9 =>
    have hn : n = 1400 + 9 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1409 6450 (by decide) (by rfl)
  | 10 =>
    have hn : n = 1400 + 10 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1410 3531 (by decide) (by rfl)
  | 11 =>
    have hn : n = 1400 + 11 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1411 6980 (by decide) (by rfl)
  | 12 =>
    have hn : n = 1400 + 12 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1412 3813 (by decide) (by rfl)
  | 13 =>
    have hn : n = 1400 + 13 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1413 9814 (by decide) (by rfl)
  | 14 =>
    have hn : n = 1400 + 14 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1414 5735 (by decide) (by rfl)
  | 15 =>
    have hn : n = 1400 + 15 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1415 6920 (by decide) (by rfl)
  | 16 =>
    have hn : n = 1400 + 16 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1416 16393 (by decide) (by rfl)
  | 17 =>
    have hn : n = 1400 + 17 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1417 26258 (by decide) (by rfl)
  | 18 =>
    have hn : n = 1400 + 18 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1418 3723 (by decide) (by rfl)
  | 19 =>
    have hn : n = 1400 + 19 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1419 6700 (by decide) (by rfl)
  | 20 =>
    have hn : n = 1400 + 20 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1420 4445 (by decide) (by rfl)
  | 21 =>
    have hn : n = 1400 + 21 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1421 6990 (by decide) (by rfl)
  | 22 =>
    have hn : n = 1400 + 22 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1422 59383 (by decide) (by rfl)
  | 23 =>
    have hn : n = 1400 + 23 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1423 9296 (by decide) (by rfl)
  | 24 =>
    have hn : n = 1400 + 24 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1424 3297 (by decide) (by rfl)
  | 25 =>
    have hn : n = 1400 + 25 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1425 7090 (by decide) (by rfl)
  | 26 =>
    have hn : n = 1400 + 26 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1426 7115 (by decide) (by rfl)
  | 27 =>
    have hn : n = 1400 + 27 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1427 5780 (by decide) (by rfl)
  | 28 =>
    have hn : n = 1400 + 28 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1428 4281 (by decide) (by rfl)
  | 29 =>
    have hn : n = 1400 + 29 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1429 5270 (by decide) (by rfl)
  | 30 =>
    have hn : n = 1400 + 30 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1430 3015 (by decide) (by rfl)
  | 31 =>
    have hn : n = 1400 + 31 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1431 9688 (by decide) (by rfl)
  | 32 =>
    have hn : n = 1400 + 32 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1432 7049 (by decide) (by rfl)
  | 33 =>
    have hn : n = 1400 + 33 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1433 9786 (by decide) (by rfl)
  | 34 =>
    have hn : n = 1400 + 34 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1434 4299 (by decide) (by rfl)
  | 35 =>
    have hn : n = 1400 + 35 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1435 9884 (by decide) (by rfl)
  | 36 =>
    have hn : n = 1400 + 36 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1436 3597 (by decide) (by rfl)
  | 37 =>
    have hn : n = 1400 + 37 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1437 15598 (by decide) (by rfl)
  | 38 =>
    have hn : n = 1400 + 38 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1438 9503 (by decide) (by rfl)
  | 39 =>
    have hn : n = 1400 + 39 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1439 6560 (by decide) (by rfl)
  | 40 =>
    have hn : n = 1400 + 40 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1440 4317 (by decide) (by rfl)
  | 41 =>
    have hn : n = 1400 + 41 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1441 9506 (by decide) (by rfl)
  | 42 =>
    have hn : n = 1400 + 42 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1442 3819 (by decide) (by rfl)
  | 43 =>
    have hn : n = 1400 + 43 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1443 18148 (by decide) (by rfl)
  | 44 =>
    have hn : n = 1400 + 44 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1444 10073 (by decide) (by rfl)
  | 45 =>
    have hn : n = 1400 + 45 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1445 7190 (by decide) (by rfl)
  | 46 =>
    have hn : n = 1400 + 46 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1446 27151 (by decide) (by rfl)
  | 47 =>
    have hn : n = 1400 + 47 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1447 24776 (by decide) (by rfl)
  | 48 =>
    have hn : n = 1400 + 48 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1448 4341 (by decide) (by rfl)
  | 49 =>
    have hn : n = 1400 + 49 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1449 10066 (by decide) (by rfl)
  | 50 =>
    have hn : n = 1400 + 50 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1450 7235 (by decide) (by rfl)
  | 51 =>
    have hn : n = 1400 + 51 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1451 7180 (by decide) (by rfl)
  | 52 =>
    have hn : n = 1400 + 52 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1452 4353 (by decide) (by rfl)
  | 53 =>
    have hn : n = 1400 + 53 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1453 26942 (by decide) (by rfl)
  | 54 =>
    have hn : n = 1400 + 54 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1454 4359 (by decide) (by rfl)
  | 55 =>
    have hn : n = 1400 + 55 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1455 16432 (by decide) (by rfl)
  | 56 =>
    have hn : n = 1400 + 56 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1456 7265 (by decide) (by rfl)
  | 57 =>
    have hn : n = 1400 + 57 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1457 4374 (by decide) (by rfl)
  | 58 =>
    have hn : n = 1400 + 58 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1458 5395 (by decide) (by rfl)
  | 59 =>
    have hn : n = 1400 + 59 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1459 10052 (by decide) (by rfl)
  | 60 =>
    have hn : n = 1400 + 60 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1460 4377 (by decide) (by rfl)
  | 61 =>
    have hn : n = 1400 + 61 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1461 7270 (by decide) (by rfl)
  | 62 =>
    have hn : n = 1400 + 62 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1462 7295 (by decide) (by rfl)
  | 63 =>
    have hn : n = 1400 + 63 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1463 7160 (by decide) (by rfl)
  | 64 =>
    have hn : n = 1400 + 64 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1464 4585 (by decide) (by rfl)
  | 65 =>
    have hn : n = 1400 + 65 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1465 10178 (by decide) (by rfl)
  | 66 =>
    have hn : n = 1400 + 66 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1466 3339 (by decide) (by rfl)
  | 67 =>
    have hn : n = 1400 + 67 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1467 26524 (by decide) (by rfl)
  | 68 =>
    have hn : n = 1400 + 68 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1468 16049 (by decide) (by rfl)
  | 69 =>
    have hn : n = 1400 + 69 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1469 7230 (by decide) (by rfl)
  | 70 =>
    have hn : n = 1400 + 70 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1470 5695 (by decide) (by rfl)
  | 71 =>
    have hn : n = 1400 + 71 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1471 6080 (by decide) (by rfl)
  | 72 =>
    have hn : n = 1400 + 72 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1472 4413 (by decide) (by rfl)
  | 73 =>
    have hn : n = 1400 + 73 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1473 7330 (by decide) (by rfl)
  | 74 =>
    have hn : n = 1400 + 74 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1474 3075 (by decide) (by rfl)
  | 75 =>
    have hn : n = 1400 + 75 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1475 6660 (by decide) (by rfl)
  | 76 =>
    have hn : n = 1400 + 76 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1476 4165 (by decide) (by rfl)
  | 77 =>
    have hn : n = 1400 + 77 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1477 5510 (by decide) (by rfl)
  | 78 =>
    have hn : n = 1400 + 78 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1478 3423 (by decide) (by rfl)
  | 79 =>
    have hn : n = 1400 + 79 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1479 7240 (by decide) (by rfl)
  | 80 =>
    have hn : n = 1400 + 80 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1480 16181 (by decide) (by rfl)
  | 81 =>
    have hn : n = 1400 + 81 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1481 7098 (by decide) (by rfl)
  | 82 =>
    have hn : n = 1400 + 82 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1482 4443 (by decide) (by rfl)
  | 83 =>
    have hn : n = 1400 + 83 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1483 4940 (by decide) (by rfl)
  | 84 =>
    have hn : n = 1400 + 84 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1484 3165 (by decide) (by rfl)
  | 85 =>
    have hn : n = 1400 + 85 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1485 7390 (by decide) (by rfl)
  | 86 =>
    have hn : n = 1400 + 86 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1486 7415 (by decide) (by rfl)
  | 87 =>
    have hn : n = 1400 + 87 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1487 7120 (by decide) (by rfl)
  | 88 =>
    have hn : n = 1400 + 88 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1488 3729 (by decide) (by rfl)
  | 89 =>
    have hn : n = 1400 + 89 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1489 5170 (by decide) (by rfl)
  | 90 =>
    have hn : n = 1400 + 90 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1490 4467 (by decide) (by rfl)
  | 91 =>
    have hn : n = 1400 + 91 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1491 10276 (by decide) (by rfl)
  | 92 =>
    have hn : n = 1400 + 92 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1492 7445 (by decide) (by rfl)
  | 93 =>
    have hn : n = 1400 + 93 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1493 7110 (by decide) (by rfl)
  | 94 =>
    have hn : n = 1400 + 94 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1494 4479 (by decide) (by rfl)
  | 95 =>
    have hn : n = 1400 + 95 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1495 6776 (by decide) (by rfl)
  | 96 =>
    have hn : n = 1400 + 96 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1496 7465 (by decide) (by rfl)
  | 97 =>
    have hn : n = 1400 + 97 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1497 9898 (by decide) (by rfl)
  | 98 =>
    have hn : n = 1400 + 98 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1498 7259 (by decide) (by rfl)
  | 99 =>
    have hn : n = 1400 + 99 := n_eq_of_sub_eq h1 h_k
    subst hn
    exact solve_concrete 1499 5500 (by decide) (by rfl)
  | _ + 100 => omega
