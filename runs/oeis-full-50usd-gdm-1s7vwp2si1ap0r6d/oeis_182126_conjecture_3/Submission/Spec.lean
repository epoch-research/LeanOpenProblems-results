import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

theorem nth_prime_0 : nth Nat.Prime 0 = 2 := by
  have h : Nat.Prime 2 := by decide
  have hc : count Nat.Prime 2 = 0 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_1 : nth Nat.Prime 1 = 3 := by
  have h : Nat.Prime 3 := by decide
  have hc : count Nat.Prime 3 = 1 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_2 : nth Nat.Prime 2 = 5 := by
  have h : Nat.Prime 5 := by decide
  have hc : count Nat.Prime 5 = 2 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_3 : nth Nat.Prime 3 = 7 := by
  have h : Nat.Prime 7 := by decide
  have hc : count Nat.Prime 7 = 3 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_4 : nth Nat.Prime 4 = 11 := by
  have h : Nat.Prime 11 := by decide
  have hc : count Nat.Prime 11 = 4 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_5 : nth Nat.Prime 5 = 13 := by
  have h : Nat.Prime 13 := by decide
  have hc : count Nat.Prime 13 = 5 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_6 : nth Nat.Prime 6 = 17 := by
  have h : Nat.Prime 17 := by decide
  have hc : count Nat.Prime 17 = 6 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_7 : nth Nat.Prime 7 = 19 := by
  have h : Nat.Prime 19 := by decide
  have hc : count Nat.Prime 19 = 7 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_8 : nth Nat.Prime 8 = 23 := by
  have h : Nat.Prime 23 := by decide
  have hc : count Nat.Prime 23 = 8 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_9 : nth Nat.Prime 9 = 29 := by
  have h : Nat.Prime 29 := by decide
  have hc : count Nat.Prime 29 = 9 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_10 : nth Nat.Prime 10 = 31 := by
  have h : Nat.Prime 31 := by decide
  have hc : count Nat.Prime 31 = 10 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_11 : nth Nat.Prime 11 = 37 := by
  have h : Nat.Prime 37 := by decide
  have hc : count Nat.Prime 37 = 11 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_12 : nth Nat.Prime 12 = 41 := by
  have h : Nat.Prime 41 := by decide
  have hc : count Nat.Prime 41 = 12 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_13 : nth Nat.Prime 13 = 43 := by
  have h : Nat.Prime 43 := by decide
  have hc : count Nat.Prime 43 = 13 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_14 : nth Nat.Prime 14 = 47 := by
  have h : Nat.Prime 47 := by decide
  have hc : count Nat.Prime 47 = 14 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_15 : nth Nat.Prime 15 = 53 := by
  have h : Nat.Prime 53 := by decide
  have hc : count Nat.Prime 53 = 15 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_16 : nth Nat.Prime 16 = 59 := by
  have h : Nat.Prime 59 := by decide
  have hc : count Nat.Prime 59 = 16 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_17 : nth Nat.Prime 17 = 61 := by
  have h : Nat.Prime 61 := by decide
  have hc : count Nat.Prime 61 = 17 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_18 : nth Nat.Prime 18 = 67 := by
  have h : Nat.Prime 67 := by decide
  have hc : count Nat.Prime 67 = 18 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_19 : nth Nat.Prime 19 = 71 := by
  have h : Nat.Prime 71 := by decide
  have hc : count Nat.Prime 71 = 19 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_20 : nth Nat.Prime 20 = 73 := by
  have h : Nat.Prime 73 := by decide
  have hc : count Nat.Prime 73 = 20 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_21 : nth Nat.Prime 21 = 79 := by
  have h : Nat.Prime 79 := by decide
  have hc : count Nat.Prime 79 = 21 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_22 : nth Nat.Prime 22 = 83 := by
  have h : Nat.Prime 83 := by decide
  have hc : count Nat.Prime 83 = 22 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_23 : nth Nat.Prime 23 = 89 := by
  have h : Nat.Prime 89 := by decide
  have hc : count Nat.Prime 89 = 23 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_24 : nth Nat.Prime 24 = 97 := by
  have h : Nat.Prime 97 := by decide
  have hc : count Nat.Prime 97 = 24 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_25 : nth Nat.Prime 25 = 101 := by
  have h : Nat.Prime 101 := by decide
  have hc : count Nat.Prime 101 = 25 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_26 : nth Nat.Prime 26 = 103 := by
  have h : Nat.Prime 103 := by decide
  have hc : count Nat.Prime 103 = 26 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_27 : nth Nat.Prime 27 = 107 := by
  have h : Nat.Prime 107 := by decide
  have hc : count Nat.Prime 107 = 27 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_28 : nth Nat.Prime 28 = 109 := by
  have h : Nat.Prime 109 := by decide
  have hc : count Nat.Prime 109 = 28 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_29 : nth Nat.Prime 29 = 113 := by
  have h : Nat.Prime 113 := by decide
  have hc : count Nat.Prime 113 = 29 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_30 : nth Nat.Prime 30 = 127 := by
  have h : Nat.Prime 127 := by decide
  have hc : count Nat.Prime 127 = 30 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_31 : nth Nat.Prime 31 = 131 := by
  have h : Nat.Prime 131 := by decide
  have hc : count Nat.Prime 131 = 31 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_32 : nth Nat.Prime 32 = 137 := by
  have h : Nat.Prime 137 := by decide
  have hc : count Nat.Prime 137 = 32 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_33 : nth Nat.Prime 33 = 139 := by
  have h : Nat.Prime 139 := by decide
  have hc : count Nat.Prime 139 = 33 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_34 : nth Nat.Prime 34 = 149 := by
  have h : Nat.Prime 149 := by decide
  have hc : count Nat.Prime 149 = 34 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_35 : nth Nat.Prime 35 = 151 := by
  have h : Nat.Prime 151 := by decide
  have hc : count Nat.Prime 151 = 35 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_36 : nth Nat.Prime 36 = 157 := by
  have h : Nat.Prime 157 := by decide
  have hc : count Nat.Prime 157 = 36 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_37 : nth Nat.Prime 37 = 163 := by
  have h : Nat.Prime 163 := by decide
  have hc : count Nat.Prime 163 = 37 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_38 : nth Nat.Prime 38 = 167 := by
  have h : Nat.Prime 167 := by decide
  have hc : count Nat.Prime 167 = 38 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_39 : nth Nat.Prime 39 = 173 := by
  have h : Nat.Prime 173 := by decide
  have hc : count Nat.Prime 173 = 39 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_40 : nth Nat.Prime 40 = 179 := by
  have h : Nat.Prime 179 := by decide
  have hc : count Nat.Prime 179 = 40 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_41 : nth Nat.Prime 41 = 181 := by
  have h : Nat.Prime 181 := by decide
  have hc : count Nat.Prime 181 = 41 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_42 : nth Nat.Prime 42 = 191 := by
  have h : Nat.Prime 191 := by decide
  have hc : count Nat.Prime 191 = 42 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_43 : nth Nat.Prime 43 = 193 := by
  have h : Nat.Prime 193 := by decide
  have hc : count Nat.Prime 193 = 43 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_44 : nth Nat.Prime 44 = 197 := by
  have h : Nat.Prime 197 := by decide
  have hc : count Nat.Prime 197 = 44 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_45 : nth Nat.Prime 45 = 199 := by
  have h : Nat.Prime 199 := by decide
  have hc : count Nat.Prime 199 = 45 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_46 : nth Nat.Prime 46 = 211 := by
  have h : Nat.Prime 211 := by decide
  have hc : count Nat.Prime 211 = 46 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_47 : nth Nat.Prime 47 = 223 := by
  have h : Nat.Prime 223 := by decide
  have hc : count Nat.Prime 223 = 47 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_48 : nth Nat.Prime 48 = 227 := by
  have h : Nat.Prime 227 := by decide
  have hc : count Nat.Prime 227 = 48 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_49 : nth Nat.Prime 49 = 229 := by
  have h : Nat.Prime 229 := by decide
  have hc : count Nat.Prime 229 = 49 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_50 : nth Nat.Prime 50 = 233 := by
  have h : Nat.Prime 233 := by decide
  have hc : count Nat.Prime 233 = 50 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_51 : nth Nat.Prime 51 = 239 := by
  have h : Nat.Prime 239 := by decide
  have hc : count Nat.Prime 239 = 51 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_52 : nth Nat.Prime 52 = 241 := by
  have h : Nat.Prime 241 := by decide
  have hc : count Nat.Prime 241 = 52 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_53 : nth Nat.Prime 53 = 251 := by
  have h : Nat.Prime 251 := by decide
  have hc : count Nat.Prime 251 = 53 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_54 : nth Nat.Prime 54 = 257 := by
  have h : Nat.Prime 257 := by decide
  have hc : count Nat.Prime 257 = 54 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_55 : nth Nat.Prime 55 = 263 := by
  have h : Nat.Prime 263 := by decide
  have hc : count Nat.Prime 263 = 55 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_56 : nth Nat.Prime 56 = 269 := by
  have h : Nat.Prime 269 := by decide
  have hc : count Nat.Prime 269 = 56 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_57 : nth Nat.Prime 57 = 271 := by
  have h : Nat.Prime 271 := by decide
  have hc : count Nat.Prime 271 = 57 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_58 : nth Nat.Prime 58 = 277 := by
  have h : Nat.Prime 277 := by decide
  have hc : count Nat.Prime 277 = 58 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_59 : nth Nat.Prime 59 = 281 := by
  have h : Nat.Prime 281 := by decide
  have hc : count Nat.Prime 281 = 59 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_60 : nth Nat.Prime 60 = 283 := by
  have h : Nat.Prime 283 := by decide
  have hc : count Nat.Prime 283 = 60 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_61 : nth Nat.Prime 61 = 293 := by
  have h : Nat.Prime 293 := by decide
  have hc : count Nat.Prime 293 = 61 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_62 : nth Nat.Prime 62 = 307 := by
  have h : Nat.Prime 307 := by decide
  have hc : count Nat.Prime 307 = 62 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

theorem nth_prime_63 : nth Nat.Prime 63 = 311 := by
  have h : Nat.Prime 311 := by decide
  have hc : count Nat.Prime 311 = 63 := by rfl
  have hnth := nth_count h
  rw [hc] at hnth
  exact hnth

noncomputable def a (n : ℕ) : ℕ :=
  let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
  if n = 0 then 0
  else (p_n n * p_n (n + 1)) % p_n (n + 2)


theorem a_1 : a 1 = 1 := by
  dsimp [a]
  rw [nth_prime_0, nth_prime_1, nth_prime_2]

theorem a_2 : a 2 = 1 := by
  dsimp [a]
  rw [nth_prime_1, nth_prime_2, nth_prime_3]

theorem a_3 : a 3 = 2 := by
  dsimp [a]
  rw [nth_prime_2, nth_prime_3, nth_prime_4]

theorem a_4 : a 4 = 12 := by
  dsimp [a]
  rw [nth_prime_3, nth_prime_4, nth_prime_5]

theorem a_5 : a 5 = 7 := by
  dsimp [a]
  rw [nth_prime_4, nth_prime_5, nth_prime_6]

theorem a_6 : a 6 = 12 := by
  dsimp [a]
  rw [nth_prime_5, nth_prime_6, nth_prime_7]

theorem a_7 : a 7 = 1 := by
  dsimp [a]
  rw [nth_prime_6, nth_prime_7, nth_prime_8]

theorem a_8 : a 8 = 2 := by
  dsimp [a]
  rw [nth_prime_7, nth_prime_8, nth_prime_9]

theorem a_9 : a 9 = 16 := by
  dsimp [a]
  rw [nth_prime_8, nth_prime_9, nth_prime_10]

theorem a_10 : a 10 = 11 := by
  dsimp [a]
  rw [nth_prime_9, nth_prime_10, nth_prime_11]

theorem a_11 : a 11 = 40 := by
  dsimp [a]
  rw [nth_prime_10, nth_prime_11, nth_prime_12]

theorem a_12 : a 12 = 12 := by
  dsimp [a]
  rw [nth_prime_11, nth_prime_12, nth_prime_13]

theorem a_13 : a 13 = 24 := by
  dsimp [a]
  rw [nth_prime_12, nth_prime_13, nth_prime_14]

theorem a_14 : a 14 = 7 := by
  dsimp [a]
  rw [nth_prime_13, nth_prime_14, nth_prime_15]

theorem a_15 : a 15 = 13 := by
  dsimp [a]
  rw [nth_prime_14, nth_prime_15, nth_prime_16]

theorem a_16 : a 16 = 16 := by
  dsimp [a]
  rw [nth_prime_15, nth_prime_16, nth_prime_17]

theorem a_17 : a 17 = 48 := by
  dsimp [a]
  rw [nth_prime_16, nth_prime_17, nth_prime_18]

theorem a_18 : a 18 = 40 := by
  dsimp [a]
  rw [nth_prime_17, nth_prime_18, nth_prime_19]

theorem a_19 : a 19 = 12 := by
  dsimp [a]
  rw [nth_prime_18, nth_prime_19, nth_prime_20]

theorem a_20 : a 20 = 48 := by
  dsimp [a]
  rw [nth_prime_19, nth_prime_20, nth_prime_21]

theorem a_21 : a 21 = 40 := by
  dsimp [a]
  rw [nth_prime_20, nth_prime_21, nth_prime_22]

theorem a_22 : a 22 = 60 := by
  dsimp [a]
  rw [nth_prime_21, nth_prime_22, nth_prime_23]

theorem a_23 : a 23 = 15 := by
  dsimp [a]
  rw [nth_prime_22, nth_prime_23, nth_prime_24]

theorem a_24 : a 24 = 48 := by
  dsimp [a]
  rw [nth_prime_23, nth_prime_24, nth_prime_25]

theorem a_25 : a 25 = 12 := by
  dsimp [a]
  rw [nth_prime_24, nth_prime_25, nth_prime_26]

theorem a_26 : a 26 = 24 := by
  dsimp [a]
  rw [nth_prime_25, nth_prime_26, nth_prime_27]

theorem a_27 : a 27 = 12 := by
  dsimp [a]
  rw [nth_prime_26, nth_prime_27, nth_prime_28]

theorem a_28 : a 28 = 24 := by
  dsimp [a]
  rw [nth_prime_27, nth_prime_28, nth_prime_29]

theorem a_29 : a 29 = 125 := by
  dsimp [a]
  rw [nth_prime_28, nth_prime_29, nth_prime_30]

theorem a_30 : a 30 = 72 := by
  dsimp [a]
  rw [nth_prime_29, nth_prime_30, nth_prime_31]

theorem a_31 : a 31 = 60 := by
  dsimp [a]
  rw [nth_prime_30, nth_prime_31, nth_prime_32]

theorem a_32 : a 32 = 16 := by
  dsimp [a]
  rw [nth_prime_31, nth_prime_32, nth_prime_33]

theorem a_33 : a 33 = 120 := by
  dsimp [a]
  rw [nth_prime_32, nth_prime_33, nth_prime_34]

theorem a_34 : a 34 = 24 := by
  dsimp [a]
  rw [nth_prime_33, nth_prime_34, nth_prime_35]

theorem a_35 : a 35 = 48 := by
  dsimp [a]
  rw [nth_prime_34, nth_prime_35, nth_prime_36]

theorem a_36 : a 36 = 72 := by
  dsimp [a]
  rw [nth_prime_35, nth_prime_36, nth_prime_37]

theorem a_37 : a 37 = 40 := by
  dsimp [a]
  rw [nth_prime_36, nth_prime_37, nth_prime_38]

theorem a_38 : a 38 = 60 := by
  dsimp [a]
  rw [nth_prime_37, nth_prime_38, nth_prime_39]

theorem a_39 : a 39 = 72 := by
  dsimp [a]
  rw [nth_prime_38, nth_prime_39, nth_prime_40]

theorem a_40 : a 40 = 16 := by
  dsimp [a]
  rw [nth_prime_39, nth_prime_40, nth_prime_41]

theorem a_41 : a 41 = 120 := by
  dsimp [a]
  rw [nth_prime_40, nth_prime_41, nth_prime_42]

theorem a_42 : a 42 = 24 := by
  dsimp [a]
  rw [nth_prime_41, nth_prime_42, nth_prime_43]

theorem a_43 : a 43 = 24 := by
  dsimp [a]
  rw [nth_prime_42, nth_prime_43, nth_prime_44]

theorem a_44 : a 44 = 12 := by
  dsimp [a]
  rw [nth_prime_43, nth_prime_44, nth_prime_45]

theorem a_45 : a 45 = 168 := by
  dsimp [a]
  rw [nth_prime_44, nth_prime_45, nth_prime_46]

theorem a_46 : a 46 = 65 := by
  dsimp [a]
  rw [nth_prime_45, nth_prime_46, nth_prime_47]

theorem a_47 : a 47 = 64 := by
  dsimp [a]
  rw [nth_prime_46, nth_prime_47, nth_prime_48]

theorem a_48 : a 48 = 12 := by
  dsimp [a]
  rw [nth_prime_47, nth_prime_48, nth_prime_49]

theorem a_49 : a 49 = 24 := by
  dsimp [a]
  rw [nth_prime_48, nth_prime_49, nth_prime_50]

theorem a_50 : a 50 = 60 := by
  dsimp [a]
  rw [nth_prime_49, nth_prime_50, nth_prime_51]

theorem a_51 : a 51 = 16 := by
  dsimp [a]
  rw [nth_prime_50, nth_prime_51, nth_prime_52]

theorem a_52 : a 52 = 120 := by
  dsimp [a]
  rw [nth_prime_51, nth_prime_52, nth_prime_53]

theorem a_53 : a 53 = 96 := by
  dsimp [a]
  rw [nth_prime_52, nth_prime_53, nth_prime_54]

theorem a_54 : a 54 = 72 := by
  dsimp [a]
  rw [nth_prime_53, nth_prime_54, nth_prime_55]

theorem a_55 : a 55 = 72 := by
  dsimp [a]
  rw [nth_prime_54, nth_prime_55, nth_prime_56]

theorem a_56 : a 56 = 16 := by
  dsimp [a]
  rw [nth_prime_55, nth_prime_56, nth_prime_57]

theorem a_57 : a 57 = 48 := by
  dsimp [a]
  rw [nth_prime_56, nth_prime_57, nth_prime_58]

theorem a_58 : a 58 = 40 := by
  dsimp [a]
  rw [nth_prime_57, nth_prime_58, nth_prime_59]

theorem a_59 : a 59 = 12 := by
  dsimp [a]
  rw [nth_prime_58, nth_prime_59, nth_prime_60]

theorem a_60 : a 60 = 120 := by
  dsimp [a]
  rw [nth_prime_59, nth_prime_60, nth_prime_61]

theorem a_61 : a 61 = 29 := by
  dsimp [a]
  rw [nth_prime_60, nth_prime_61, nth_prime_62]



theorem next_prime_lt_two_mul (n : ℕ) :
    Nat.nth Nat.Prime (n + 1) < 2 * Nat.nth Nat.Prime n := by
  have h_pos : Nat.nth Nat.Prime n ≠ 0 := by
    have := Nat.prime_nth_prime n
    exact Nat.Prime.ne_zero this
  have h_bertrand := Nat.exists_prime_lt_and_le_two_mul (Nat.nth Nat.Prime n) h_pos
  rcases h_bertrand with ⟨p, hp_prime, hp_gt, hp_le⟩
  have hp_nth : Nat.nth Nat.Prime (n + 1) ≤ p := by
    have h_inf : { p | Nat.Prime p }.Infinite := Nat.infinite_setOf_prime
    have hp_mem : p ∈ { p | Nat.Prime p } := hp_prime
    rw [← Nat.range_nth_of_infinite h_inf] at hp_mem
    rcases hp_mem with ⟨k, rfl⟩
    rw [Nat.nth_lt_nth h_inf] at hp_gt
    rw [Nat.nth_le_nth h_inf]
    exact hp_gt
  have hp_lt : p < 2 * Nat.nth Nat.Prime n := by
    refine lt_of_le_of_ne hp_le ?_
    intro h_eq
    have h_div : 2 ∣ p := by
      rw [h_eq]
      exact dvd_mul_right 2 (Nat.nth Nat.Prime n)
    have hp_two : p = 2 := by
      have h_cases := hp_prime.eq_one_or_self_of_dvd 2 h_div
      rcases h_cases with h21 | h2p
      · contradiction
      · exact h2p.symm
    have h_n1 : Nat.nth Nat.Prime n = 1 := by
      rw [hp_two] at h_eq
      omega
    have hpn_prime := Nat.prime_nth_prime n
    rw [h_n1] at hpn_prime
    exact Nat.not_prime_one hpn_prime
  exact hp_nth.trans_lt hp_lt

theorem a_mem_list_imp_prime (n : ℕ) :
    a n ∈ ([2, 7, 11, 13, 29] : List ℕ) → Nat.Prime (a n) := by
  intro h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h2 | h7 | h11 | h13 | h29
  · rw [h2]; decide
  · rw [h7]; decide
  · rw [h11]; decide
  · rw [h13]; decide
  · rw [h29]; decide

theorem spec_case_1 (n : ℕ) (hn : n ≥ 62) :
    let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
    let d1 := p_n (n + 2) - p_n n
    let d2 := p_n (n + 2) - p_n (n + 1)
    d1 * d2 < p_n (n + 2) → ¬ Nat.Prime (a n) ∧ a n ∉ ([2, 7, 11, 13, 29] : List ℕ) := by
  intro p_n d1 d2 h_lt
  have h_inf : { p | Nat.Prime p }.Infinite := Nat.infinite_setOf_prime
  have hp_n_prime : Nat.Prime (p_n n) := by
    dsimp [p_n]
    have : n - 1 = n - 1 := rfl
    exact Nat.prime_nth_prime (n - 1)
  have hp_n1_prime : Nat.Prime (p_n (n + 1)) := by
    dsimp [p_n]
    exact Nat.prime_nth_prime n
  have hp_n2_prime : Nat.Prime (p_n (n + 2)) := by
    dsimp [p_n]
    exact Nat.prime_nth_prime (n + 1)
  have h_n_odd : p_n n % 2 = 1 := by
    have h_neq2 : p_n n ≠ 2 := by
      dsimp [p_n]
      rw [← Nat.nth_prime_zero_eq_two]
      intro h_eq
      have h_idx := Nat.nth_injective h_inf h_eq
      omega
    exact (Nat.Prime.eq_two_or_odd hp_n_prime).resolve_left h_neq2
  have h_n1_odd : p_n (n + 1) % 2 = 1 := by
    have h_neq2 : p_n (n + 1) ≠ 2 := by
      dsimp [p_n]
      rw [← Nat.nth_prime_zero_eq_two]
      intro h_eq
      have h_idx := Nat.nth_injective h_inf h_eq
      omega
    exact (Nat.Prime.eq_two_or_odd hp_n1_prime).resolve_left h_neq2
  have h_n2_odd : p_n (n + 2) % 2 = 1 := by
    have h_neq2 : p_n (n + 2) ≠ 2 := by
      dsimp [p_n]
      rw [← Nat.nth_prime_zero_eq_two]
      intro h_eq
      have h_idx := Nat.nth_injective h_inf h_eq
      omega
    exact (Nat.Prime.eq_two_or_odd hp_n2_prime).resolve_left h_neq2
  have hp_lt1 : p_n n < p_n (n + 1) := by
    dsimp [p_n]
    rw [Nat.nth_lt_nth h_inf]
    omega
  have hp_lt2 : p_n (n + 1) < p_n (n + 2) := by
    dsimp [p_n]
    rw [Nat.nth_lt_nth h_inf]
    omega
  have hd1_even : d1 % 2 = 0 := by
    dsimp [d1]
    omega
  have hd2_even : d2 % 2 = 0 := by
    dsimp [d2]
    omega
  have hd2_ge2 : d2 ≥ 2 := by
    dsimp [d2]
    omega
  have hd1_ge4 : d1 ≥ 4 := by
    dsimp [d1, d2]
    omega
  have hd2_dvd : d2 ∣ d1 * d2 := dvd_mul_left d2 d1
  have hd2_ne1 : d2 ≠ 1 := by omega
  have hd2_ne_prod : d2 ≠ d1 * d2 := by
    have : d1 * d2 > d2 := by
      calc
        d1 * d2 ≥ 4 * d2 := by gcongr
        _ > d2 := by omega
    omega
  have h_prod_not_prime : ¬ Nat.Prime (d1 * d2) :=
    Nat.not_prime_of_dvd_of_ne hd2_dvd hd2_ne1 hd2_ne_prod
  have h_ident : p_n n * p_n (n + 1) + (d1 + d2) * p_n (n + 2) = p_n (n + 2) ^ 2 + d1 * d2 := by
    have h_le1 : p_n n ≤ p_n (n + 2) := by omega
    have h_le2 : p_n (n + 1) ≤ p_n (n + 2) := by omega
    have hd1_cast : ((d1 : ℕ) : ℤ) = (p_n (n + 2) : ℤ) - (p_n n : ℤ) := by
      dsimp [d1]
      exact Nat.cast_sub h_le1
    have hd2_cast : ((d2 : ℕ) : ℤ) = (p_n (n + 2) : ℤ) - (p_n (n + 1) : ℤ) := by
      dsimp [d2]
      exact Nat.cast_sub h_le2
    have h_cast : ((p_n n * p_n (n + 1) + (d1 + d2) * p_n (n + 2) : ℕ) : ℤ) = ((p_n (n + 2) ^ 2 + d1 * d2 : ℕ) : ℤ) := by
      push_cast
      rw [hd1_cast, hd2_cast]
      ring
    exact Nat.cast_inj.mp h_cast
  have hd_add_le_mul : d1 + d2 ≤ d1 * d2 := by
    have h_mul2 : d1 * 2 ≤ d1 * d2 := by gcongr
    have h_eq2 : d1 * 2 = d1 + d1 := by ring
    omega
  have hd_add_lt : d1 + d2 < p_n (n + 2) := hd_add_le_mul.trans_lt h_lt
  have h_sub_mul : (p_n (n + 2) - (d1 + d2)) * p_n (n + 2) + (d1 + d2) * p_n (n + 2) = p_n (n + 2) ^ 2 := by
    rw [← Nat.add_mul]
    rw [Nat.sub_add_cancel (by omega)]
    ring
  have ha_eq : p_n n * p_n (n + 1) = (p_n (n + 2) - (d1 + d2)) * p_n (n + 2) + d1 * d2 := by
    omega
  have ha_mod : (p_n n * p_n (n + 1)) % p_n (n + 2) = d1 * d2 := by
    rw [ha_eq]
    rw [Nat.add_comm]
    rw [Nat.mul_comm (p_n (n + 2) - (d1 + d2)) (p_n (n + 2))]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt h_lt
  have ha_eq_val : a n = d1 * d2 := by
    dsimp [a]
    have h_n_ne0 : n ≠ 0 := by omega
    split_ifs
    · contradiction
    · exact ha_mod
  have h_a_not_prime : ¬ Nat.Prime (a n) := by
    rw [ha_eq_val]
    exact h_prod_not_prime
  have h_not_mem : a n ∉ ([2, 7, 11, 13, 29] : List ℕ) := by
    intro h_mem
    have h_prime := a_mem_list_imp_prime n h_mem
    contradiction
  exact ⟨h_a_not_prime, h_not_mem⟩


theorem oeis_182126_conjecture_3 :
  ∀ n : ℕ, n > 0 → (Nat.Prime (a n) ↔ a n ∈ ([2, 7, 11, 13, 29] : List ℕ)) := by
  intro n hn
  by_cases h : n ≤ 61
  · interval_cases n <;> (first | rw [a_1] | rw [a_2] | rw [a_3] | rw [a_4] | rw [a_5] | rw [a_6] | rw [a_7] | rw [a_8] | rw [a_9] | rw [a_10] | rw [a_11] | rw [a_12] | rw [a_13] | rw [a_14] | rw [a_15] | rw [a_16] | rw [a_17] | rw [a_18] | rw [a_19] | rw [a_20] | rw [a_21] | rw [a_22] | rw [a_23] | rw [a_24] | rw [a_25] | rw [a_26] | rw [a_27] | rw [a_28] | rw [a_29] | rw [a_30] | rw [a_31] | rw [a_32] | rw [a_33] | rw [a_34] | rw [a_35] | rw [a_36] | rw [a_37] | rw [a_38] | rw [a_39] | rw [a_40] | rw [a_41] | rw [a_42] | rw [a_43] | rw [a_44] | rw [a_45] | rw [a_46] | rw [a_47] | rw [a_48] | rw [a_49] | rw [a_50] | rw [a_51] | rw [a_52] | rw [a_53] | rw [a_54] | rw [a_55] | rw [a_56] | rw [a_57] | rw [a_58] | rw [a_59] | rw [a_60] | rw [a_61]) <;> decide
  · have hn62 : n ≥ 62 := by omega
    let p_n := fun k : ℕ => (Nat.nth Nat.Prime (k - 1))
    have h_lt : (p_n (n + 2) - p_n n) * (p_n (n + 2) - p_n (n + 1)) < p_n (n + 2) := sorry
    have h_case := spec_case_1 n hn62 h_lt
    rcases h_case with ⟨h1, h2⟩
    constructor
    · intro hp
      contradiction
    · intro h_mem
      contradiction



