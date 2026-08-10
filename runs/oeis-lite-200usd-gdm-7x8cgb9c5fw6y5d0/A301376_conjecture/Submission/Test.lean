import FormalConjectures.Util.ProblemImports

lemma prime_3 : Nat.Prime 3 := by norm_num
lemma prime_191 : Nat.Prime 191 := by norm_num
lemma prime_7 : Nat.Prime 7 := by norm_num
lemma prime_59 : Nat.Prime 59 := by norm_num
lemma prime_2659 : Nat.Prime 2659 := by norm_num
lemma prime_1123 : Nat.Prime 1123 := by norm_num
lemma prime_1259 : Nat.Prime 1259 := by norm_num
lemma prime_5683 : Nat.Prime 5683 := by norm_num
lemma prime_11 : Nat.Prime 11 := by norm_num
lemma prime_15443 : Nat.Prime 15443 := by norm_num
lemma prime_499 : Nat.Prime 499 := by norm_num
lemma prime_11351 : Nat.Prime 11351 := by norm_num
lemma prime_7247 : Nat.Prime 7247 := by norm_num
lemma prime_3571 : Nat.Prime 3571 := by norm_num
lemma prime_359 : Nat.Prime 359 := by norm_num
lemma prime_2999 : Nat.Prime 2999 := by norm_num
lemma prime_83 : Nat.Prime 83 := by norm_num
lemma prime_8807 : Nat.Prime 8807 := by norm_num
lemma prime_4919 : Nat.Prime 4919 := by norm_num
lemma prime_1103 : Nat.Prime 1103 := by norm_num
lemma prime_823 : Nat.Prime 823 := by norm_num
lemma prime_4327 : Nat.Prime 4327 := by norm_num
lemma prime_67 : Nat.Prime 67 := by norm_num
lemma prime_331 : Nat.Prime 331 := by norm_num
lemma prime_6563 : Nat.Prime 6563 := by norm_num
lemma prime_12203 : Nat.Prime 12203 := by norm_num
lemma prime_151 : Nat.Prime 151 := by norm_num
lemma prime_4051 : Nat.Prime 4051 := by norm_num
lemma prime_7307 : Nat.Prime 7307 := by norm_num
lemma prime_23 : Nat.Prime 23 := by norm_num
lemma prime_3011 : Nat.Prime 3011 := by norm_num
lemma prime_15107 : Nat.Prime 15107 := by norm_num
lemma prime_6967 : Nat.Prime 6967 := by norm_num
lemma prime_4691 : Nat.Prime 4691 := by norm_num
lemma prime_1063 : Nat.Prime 1063 := by norm_num
lemma prime_563 : Nat.Prime 563 := by norm_num
lemma prime_227 : Nat.Prime 227 := by norm_num
lemma prime_8623 : Nat.Prime 8623 := by norm_num
lemma prime_619 : Nat.Prime 619 := by norm_num
lemma prime_43 : Nat.Prime 43 := by norm_num
lemma prime_4451 : Nat.Prime 4451 := by norm_num
lemma prime_31 : Nat.Prime 31 := by norm_num
lemma prime_9491 : Nat.Prime 9491 := by norm_num
lemma prime_9787 : Nat.Prime 9787 := by norm_num
lemma prime_9679 : Nat.Prime 9679 := by norm_num
lemma prime_683 : Nat.Prime 683 := by norm_num
lemma prime_9283 : Nat.Prime 9283 := by norm_num
lemma prime_5231 : Nat.Prime 5231 := by norm_num
lemma prime_163 : Nat.Prime 163 := by norm_num
lemma prime_5003 : Nat.Prime 5003 := by norm_num
lemma prime_131 : Nat.Prime 131 := by norm_num

def blocking_primes_49 : List ℕ := [191, 7, 59, 2659, 7, 1123, 1259, 7, 5683, 11, 15443, 499, 11351, 7, 11, 7247, 7, 3571, 359, 7, 3, 2999, 59, 3, 83, 8807, 3, 4919, 1103, 3, 823, 4327, 3, 67, 331, 3, 6563, 12203, 3, 151, 4051, 3, 7307, 23, 3, 3011, 15107, 3, 6967, 331, 3, 59, 4691, 3, 23, 1063, 3, 1103, 563, 3, 3, 227, 8623, 3, 619, 43, 3, 4451, 31, 3, 619, 9491, 3, 31, 9787, 3, 227, 9679, 3, 43, 683, 3, 823, 31, 3, 9283, 43, 3, 31, 5231, 3, 683, 163, 3, 5003, 131, 3, 1123, 31, 3]

lemma prime_of_mem_blocking_primes_49 {p : ℕ} (h : p ∈ 3 :: blocking_primes_49) : Nat.Prime p := by
  unfold blocking_primes_49 at h
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_false
  · exact prime_3
  · exact prime_191
  · exact prime_7
  · exact prime_59
  · exact prime_2659
  · exact prime_7
  · exact prime_1123
  · exact prime_1259
  · exact prime_7
  · exact prime_5683
  · exact prime_11
  · exact prime_15443
  · exact prime_499
  · exact prime_11351
  · exact prime_7
  · exact prime_11
  · exact prime_7247
  · exact prime_7
  · exact prime_3571
  · exact prime_359
  · exact prime_7
  · exact prime_3
  · exact prime_2999
  · exact prime_59
  · exact prime_3
  · exact prime_83
  · exact prime_8807
  · exact prime_3
  · exact prime_4919
  · exact prime_1103
  · exact prime_3
  · exact prime_823
  · exact prime_4327
  · exact prime_3
  · exact prime_67
  · exact prime_331
  · exact prime_3
  · exact prime_6563
  · exact prime_12203
  · exact prime_3
  · exact prime_151
  · exact prime_4051
  · exact prime_3
  · exact prime_7307
  · exact prime_23
  · exact prime_3
  · exact prime_3011
  · exact prime_15107
  · exact prime_3
  · exact prime_6967
  · exact prime_331
  · exact prime_3
  · exact prime_59
  · exact prime_4691
  · exact prime_3
  · exact prime_23
  · exact prime_1063
  · exact prime_3
  · exact prime_1103
  · exact prime_563
  · exact prime_3
  · exact prime_3
  · exact prime_227
  · exact prime_8623
  · exact prime_3
  · exact prime_619
  · exact prime_43
  · exact prime_3
  · exact prime_4451
  · exact prime_31
  · exact prime_3
  · exact prime_619
  · exact prime_9491
  · exact prime_3
  · exact prime_31
  · exact prime_9787
  · exact prime_3
  · exact prime_227
  · exact prime_9679
  · exact prime_3
  · exact prime_43
  · exact prime_683
  · exact prime_3
  · exact prime_823
  · exact prime_31
  · exact prime_3
  · exact prime_9283
  · exact prime_43
  · exact prime_3
  · exact prime_31
  · exact prime_5231
  · exact prime_3
  · exact prime_683
  · exact prime_163
  · exact prime_3
  · exact prime_5003
  · exact prime_131
  · exact prime_3
  · exact prime_1123
  · exact prime_31
  · exact prime_3
  · cases h_false
