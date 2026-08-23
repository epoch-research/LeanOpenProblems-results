import FormalConjectures.Util.ProblemImports
open Nat
private lemma prime_dvd_list_prod {q : ℕ} (hq : q.Prime) :
    ∀ (ps : List ℕ), q ∣ ps.prod → ∃ p ∈ ps, q ∣ p
  | [], h => by
    simp at h
    exact (hq.ne_one h).elim
  | p :: ps, h => by
    rw [List.prod_cons] at h
    rcases hq.dvd_mul.mp h with h | h
    · exact ⟨p, List.mem_cons_self, h⟩
    · obtain ⟨p', hp', hq'⟩ := prime_dvd_list_prod hq ps h
      exact ⟨p', List.mem_cons_of_mem _ hp', hq'⟩
private lemma prime_eq_of_dvd_prime_pow {q p : ℕ} {e : ℕ} (hq : q.Prime) (hp : p.Prime)
    (h : q ∣ p ^ e) : q = p :=
  (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)
private lemma prime_127 : Nat.Prime 127 := by norm_num
private lemma prime_4001 : Nat.Prime 4001 := by norm_num
private lemma prime_9199 : Nat.Prime 9199 := by norm_num
private lemma prime_736103981_sub1 : (736103981 - 1 : ℕ) = 2 ^ 2 * 5 * 4001 * 9199 := by norm_num
private lemma prime_736103981_pow : (2 : ZMod 736103981) ^ (736103981 - 1) = 1 := by
  reduce_mod_char
private lemma prime_736103981_div_2 : (2 : ZMod 736103981) ^ ((736103981 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_736103981_div_5 : (2 : ZMod 736103981) ^ ((736103981 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_736103981_div_4001 : (2 : ZMod 736103981) ^ ((736103981 - 1) / 4001) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_736103981_div_9199 : (2 : ZMod 736103981) ^ ((736103981 - 1) / 9199) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_736103981 : Nat.Prime 736103981 := by
  refine lucas_primality 736103981 (2 : ZMod 736103981) prime_736103981_pow ?_
  intro q hq hqd
  rw [prime_736103981_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 4001, 9199].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_736103981_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_736103981_div_5
  · have : q = 4001 := (Nat.prime_dvd_prime_iff_eq hq prime_4001).mp hdf
    subst this; exact prime_736103981_div_4001
  · have : q = 9199 := (Nat.prime_dvd_prime_iff_eq hq prime_9199).mp hdf
    subst this; exact prime_736103981_div_9199
private lemma prime_1472207963_sub1 : (1472207963 - 1 : ℕ) = 2 * 736103981 := by norm_num
private lemma prime_1472207963_pow : (2 : ZMod 1472207963) ^ (1472207963 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1472207963_div_2 : (2 : ZMod 1472207963) ^ ((1472207963 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1472207963_div_736103981 : (2 : ZMod 1472207963) ^ ((1472207963 - 1) / 736103981) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1472207963 : Nat.Prime 1472207963 := by
  refine lucas_primality 1472207963 (2 : ZMod 1472207963) prime_1472207963_pow ?_
  intro q hq hqd
  rw [prime_1472207963_sub1] at hqd
  have : q ∣ [2, 736103981].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1472207963_div_2
  · have : q = 736103981 := (Nat.prime_dvd_prime_iff_eq hq prime_736103981).mp hdf
    subst this; exact prime_1472207963_div_736103981
private lemma prime_1543 : Nat.Prime 1543 := by norm_num
private lemma prime_92849 : Nat.Prime 92849 := by norm_num
private lemma prime_2865320141_sub1 : (2865320141 - 1 : ℕ) = 2 ^ 2 * 5 * 1543 * 92849 := by norm_num
private lemma prime_2865320141_pow : (3 : ZMod 2865320141) ^ (2865320141 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2865320141_div_2 : (3 : ZMod 2865320141) ^ ((2865320141 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2865320141_div_5 : (3 : ZMod 2865320141) ^ ((2865320141 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2865320141_div_1543 : (3 : ZMod 2865320141) ^ ((2865320141 - 1) / 1543) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2865320141_div_92849 : (3 : ZMod 2865320141) ^ ((2865320141 - 1) / 92849) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2865320141 : Nat.Prime 2865320141 := by
  refine lucas_primality 2865320141 (3 : ZMod 2865320141) prime_2865320141_pow ?_
  intro q hq hqd
  rw [prime_2865320141_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 1543, 92849].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_2865320141_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_2865320141_div_5
  · have : q = 1543 := (Nat.prime_dvd_prime_iff_eq hq prime_1543).mp hdf
    subst this; exact prime_2865320141_div_1543
  · have : q = 92849 := (Nat.prime_dvd_prime_iff_eq hq prime_92849).mp hdf
    subst this; exact prime_2865320141_div_92849
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_59 : Nat.Prime 59 := by norm_num
private lemma prime_80849 : Nat.Prime 80849 := by norm_num
private lemma prime_54969269 : Nat.Prime 54969269 := by norm_num
private lemma prime_19403422734677447_sub1 : (19403422734677447 - 1 : ℕ) = 2 * 37 * 59 * 80849 * 54969269 := by norm_num
private lemma prime_19403422734677447_pow : (5 : ZMod 19403422734677447) ^ (19403422734677447 - 1) = 1 := by
  reduce_mod_char
private lemma prime_19403422734677447_div_2 : (5 : ZMod 19403422734677447) ^ ((19403422734677447 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_19403422734677447_div_37 : (5 : ZMod 19403422734677447) ^ ((19403422734677447 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_19403422734677447_div_59 : (5 : ZMod 19403422734677447) ^ ((19403422734677447 - 1) / 59) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_19403422734677447_div_80849 : (5 : ZMod 19403422734677447) ^ ((19403422734677447 - 1) / 80849) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_19403422734677447_div_54969269 : (5 : ZMod 19403422734677447) ^ ((19403422734677447 - 1) / 54969269) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_19403422734677447 : Nat.Prime 19403422734677447 := by
  refine lucas_primality 19403422734677447 (5 : ZMod 19403422734677447) prime_19403422734677447_pow ?_
  intro q hq hqd
  rw [prime_19403422734677447_sub1] at hqd
  have : q ∣ [2, 37, 59, 80849, 54969269].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_19403422734677447_div_2
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_19403422734677447_div_37
  · have : q = 59 := (Nat.prime_dvd_prime_iff_eq hq prime_59).mp hdf
    subst this; exact prime_19403422734677447_div_59
  · have : q = 80849 := (Nat.prime_dvd_prime_iff_eq hq prime_80849).mp hdf
    subst this; exact prime_19403422734677447_div_80849
  · have : q = 54969269 := (Nat.prime_dvd_prime_iff_eq hq prime_54969269).mp hdf
    subst this; exact prime_19403422734677447_div_54969269
private lemma prime_811 : Nat.Prime 811 := by norm_num
private lemma prime_2801 : Nat.Prime 2801 := by norm_num
private lemma prime_22111 : Nat.Prime 22111 := by norm_num
private lemma prime_71 : Nat.Prime 71 := by norm_num
private lemma prime_3203 : Nat.Prime 3203 := by norm_num
private lemma prime_305643073_sub1 : (305643073 - 1 : ℕ) = 2 ^ 6 * 3 * 7 * 71 * 3203 := by norm_num
private lemma prime_305643073_pow : (10 : ZMod 305643073) ^ (305643073 - 1) = 1 := by
  reduce_mod_char
private lemma prime_305643073_div_2 : (10 : ZMod 305643073) ^ ((305643073 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_305643073_div_3 : (10 : ZMod 305643073) ^ ((305643073 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_305643073_div_7 : (10 : ZMod 305643073) ^ ((305643073 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_305643073_div_71 : (10 : ZMod 305643073) ^ ((305643073 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_305643073_div_3203 : (10 : ZMod 305643073) ^ ((305643073 - 1) / 3203) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_305643073 : Nat.Prime 305643073 := by
  refine lucas_primality 305643073 (10 : ZMod 305643073) prime_305643073_pow ?_
  intro q hq hqd
  rw [prime_305643073_sub1] at hqd
  have : q ∣ [2 ^ 6, 3, 7, 71, 3203].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_305643073_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_305643073_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_305643073_div_7
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_305643073_div_71
  · have : q = 3203 := (Nat.prime_dvd_prime_iff_eq hq prime_3203).mp hdf
    subst this; exact prime_305643073_div_3203
private lemma prime_1105323494970026371177_sub1 : (1105323494970026371177 - 1 : ℕ) = 2 ^ 3 * 3 ^ 2 * 811 * 2801 * 22111 * 305643073 := by norm_num
private lemma prime_1105323494970026371177_pow : (5 : ZMod 1105323494970026371177) ^ (1105323494970026371177 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1105323494970026371177_div_2 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177_div_3 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177_div_811 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 811) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177_div_2801 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 2801) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177_div_22111 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 22111) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177_div_305643073 : (5 : ZMod 1105323494970026371177) ^ ((1105323494970026371177 - 1) / 305643073) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1105323494970026371177 : Nat.Prime 1105323494970026371177 := by
  refine lucas_primality 1105323494970026371177 (5 : ZMod 1105323494970026371177) prime_1105323494970026371177_pow ?_
  intro q hq hqd
  rw [prime_1105323494970026371177_sub1] at hqd
  have : q ∣ [2 ^ 3, 3 ^ 2, 811, 2801, 22111, 305643073].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1105323494970026371177_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_1105323494970026371177_div_3
  · have : q = 811 := (Nat.prime_dvd_prime_iff_eq hq prime_811).mp hdf
    subst this; exact prime_1105323494970026371177_div_811
  · have : q = 2801 := (Nat.prime_dvd_prime_iff_eq hq prime_2801).mp hdf
    subst this; exact prime_1105323494970026371177_div_2801
  · have : q = 22111 := (Nat.prime_dvd_prime_iff_eq hq prime_22111).mp hdf
    subst this; exact prime_1105323494970026371177_div_22111
  · have : q = 305643073 := (Nat.prime_dvd_prime_iff_eq hq prime_305643073).mp hdf
    subst this; exact prime_1105323494970026371177_div_305643073
private lemma prime_A_75_sub1 : (22979669527522769358466110762530181082324623688578587688959 - 1 : ℕ) = 2 * 127 * 1472207963 * 2865320141 * 19403422734677447 * 1105323494970026371177 := by norm_num
private lemma prime_A_75_pow : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ (22979669527522769358466110762530181082324623688578587688959 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_75_div_2 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75_div_127 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 127) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75_div_1472207963 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 1472207963) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75_div_2865320141 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 2865320141) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75_div_19403422734677447 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 19403422734677447) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75_div_1105323494970026371177 : (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) ^ ((22979669527522769358466110762530181082324623688578587688959 - 1) / 1105323494970026371177) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_75 : Nat.Prime 22979669527522769358466110762530181082324623688578587688959 := by
  refine lucas_primality 22979669527522769358466110762530181082324623688578587688959 (7 : ZMod 22979669527522769358466110762530181082324623688578587688959) prime_A_75_pow ?_
  intro q hq hqd
  rw [prime_A_75_sub1] at hqd
  have : q ∣ [2, 127, 1472207963, 2865320141, 19403422734677447, 1105323494970026371177].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_75_div_2
  · have : q = 127 := (Nat.prime_dvd_prime_iff_eq hq prime_127).mp hdf
    subst this; exact prime_A_75_div_127
  · have : q = 1472207963 := (Nat.prime_dvd_prime_iff_eq hq prime_1472207963).mp hdf
    subst this; exact prime_A_75_div_1472207963
  · have : q = 2865320141 := (Nat.prime_dvd_prime_iff_eq hq prime_2865320141).mp hdf
    subst this; exact prime_A_75_div_2865320141
  · have : q = 19403422734677447 := (Nat.prime_dvd_prime_iff_eq hq prime_19403422734677447).mp hdf
    subst this; exact prime_A_75_div_19403422734677447
  · have : q = 1105323494970026371177 := (Nat.prime_dvd_prime_iff_eq hq prime_1105323494970026371177).mp hdf
    subst this; exact prime_A_75_div_1105323494970026371177
private lemma prime_1289593 : Nat.Prime 1289593 := by norm_num
private lemma prime_29 : Nat.Prime 29 := by norm_num
private lemma prime_97 : Nat.Prime 97 := by norm_num
private lemma prime_6221 : Nat.Prime 6221 := by norm_num
private lemma prime_699986921_sub1 : (699986921 - 1 : ℕ) = 2 ^ 3 * 5 * 29 * 97 * 6221 := by norm_num
private lemma prime_699986921_pow : (3 : ZMod 699986921) ^ (699986921 - 1) = 1 := by
  reduce_mod_char
private lemma prime_699986921_div_2 : (3 : ZMod 699986921) ^ ((699986921 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_699986921_div_5 : (3 : ZMod 699986921) ^ ((699986921 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_699986921_div_29 : (3 : ZMod 699986921) ^ ((699986921 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_699986921_div_97 : (3 : ZMod 699986921) ^ ((699986921 - 1) / 97) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_699986921_div_6221 : (3 : ZMod 699986921) ^ ((699986921 - 1) / 6221) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_699986921 : Nat.Prime 699986921 := by
  refine lucas_primality 699986921 (3 : ZMod 699986921) prime_699986921_pow ?_
  intro q hq hqd
  rw [prime_699986921_sub1] at hqd
  have : q ∣ [2 ^ 3, 5, 29, 97, 6221].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_699986921_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_699986921_div_5
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_699986921_div_29
  · have : q = 97 := (Nat.prime_dvd_prime_iff_eq hq prime_97).mp hdf
    subst this; exact prime_699986921_div_97
  · have : q = 6221 := (Nat.prime_dvd_prime_iff_eq hq prime_6221).mp hdf
    subst this; exact prime_699986921_div_6221
private lemma prime_1399973843_sub1 : (1399973843 - 1 : ℕ) = 2 * 699986921 := by norm_num
private lemma prime_1399973843_pow : (2 : ZMod 1399973843) ^ (1399973843 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1399973843_div_2 : (2 : ZMod 1399973843) ^ ((1399973843 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1399973843_div_699986921 : (2 : ZMod 1399973843) ^ ((1399973843 - 1) / 699986921) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1399973843 : Nat.Prime 1399973843 := by
  refine lucas_primality 1399973843 (2 : ZMod 1399973843) prime_1399973843_pow ?_
  intro q hq hqd
  rw [prime_1399973843_sub1] at hqd
  have : q ∣ [2, 699986921].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1399973843_div_2
  · have : q = 699986921 := (Nat.prime_dvd_prime_iff_eq hq prime_699986921).mp hdf
    subst this; exact prime_1399973843_div_699986921
private lemma prime_3610792936231799_sub1 : (3610792936231799 - 1 : ℕ) = 2 * 1289593 * 1399973843 := by norm_num
private lemma prime_3610792936231799_pow : (13 : ZMod 3610792936231799) ^ (3610792936231799 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3610792936231799_div_2 : (13 : ZMod 3610792936231799) ^ ((3610792936231799 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3610792936231799_div_1289593 : (13 : ZMod 3610792936231799) ^ ((3610792936231799 - 1) / 1289593) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3610792936231799_div_1399973843 : (13 : ZMod 3610792936231799) ^ ((3610792936231799 - 1) / 1399973843) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3610792936231799 : Nat.Prime 3610792936231799 := by
  refine lucas_primality 3610792936231799 (13 : ZMod 3610792936231799) prime_3610792936231799_pow ?_
  intro q hq hqd
  rw [prime_3610792936231799_sub1] at hqd
  have : q ∣ [2, 1289593, 1399973843].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3610792936231799_div_2
  · have : q = 1289593 := (Nat.prime_dvd_prime_iff_eq hq prime_1289593).mp hdf
    subst this; exact prime_3610792936231799_div_1289593
  · have : q = 1399973843 := (Nat.prime_dvd_prime_iff_eq hq prime_1399973843).mp hdf
    subst this; exact prime_3610792936231799_div_1399973843
private lemma prime_13171813 : Nat.Prime 13171813 := by norm_num
private lemma prime_49341343 : Nat.Prime 49341343 := by norm_num
private lemma prime_350954069309023861_sub1 : (350954069309023861 - 1 : ℕ) = 2 ^ 2 * 3 ^ 3 * 5 * 13171813 * 49341343 := by norm_num
private lemma prime_350954069309023861_pow : (6 : ZMod 350954069309023861) ^ (350954069309023861 - 1) = 1 := by
  reduce_mod_char
private lemma prime_350954069309023861_div_2 : (6 : ZMod 350954069309023861) ^ ((350954069309023861 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350954069309023861_div_3 : (6 : ZMod 350954069309023861) ^ ((350954069309023861 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350954069309023861_div_5 : (6 : ZMod 350954069309023861) ^ ((350954069309023861 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350954069309023861_div_13171813 : (6 : ZMod 350954069309023861) ^ ((350954069309023861 - 1) / 13171813) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350954069309023861_div_49341343 : (6 : ZMod 350954069309023861) ^ ((350954069309023861 - 1) / 49341343) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_350954069309023861 : Nat.Prime 350954069309023861 := by
  refine lucas_primality 350954069309023861 (6 : ZMod 350954069309023861) prime_350954069309023861_pow ?_
  intro q hq hqd
  rw [prime_350954069309023861_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 3, 5, 13171813, 49341343].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_350954069309023861_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_350954069309023861_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_350954069309023861_div_5
  · have : q = 13171813 := (Nat.prime_dvd_prime_iff_eq hq prime_13171813).mp hdf
    subst this; exact prime_350954069309023861_div_13171813
  · have : q = 49341343 := (Nat.prime_dvd_prime_iff_eq hq prime_49341343).mp hdf
    subst this; exact prime_350954069309023861_div_49341343
private lemma prime_B_75_sub1 : (22979669527522769358466110762530181082324623688578587688961 - 1 : ℕ) = 2 ^ 80 * 3 * 5 * 3610792936231799 * 350954069309023861 := by norm_num
private lemma prime_B_75_pow : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ (22979669527522769358466110762530181082324623688578587688961 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_75_div_2 : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ ((22979669527522769358466110762530181082324623688578587688961 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_75_div_3 : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ ((22979669527522769358466110762530181082324623688578587688961 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_75_div_5 : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ ((22979669527522769358466110762530181082324623688578587688961 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_75_div_3610792936231799 : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ ((22979669527522769358466110762530181082324623688578587688961 - 1) / 3610792936231799) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_75_div_350954069309023861 : (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) ^ ((22979669527522769358466110762530181082324623688578587688961 - 1) / 350954069309023861) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_75 : Nat.Prime 22979669527522769358466110762530181082324623688578587688961 := by
  refine lucas_primality 22979669527522769358466110762530181082324623688578587688961 (19 : ZMod 22979669527522769358466110762530181082324623688578587688961) prime_B_75_pow ?_
  intro q hq hqd
  rw [prime_B_75_sub1] at hqd
  have : q ∣ [2 ^ 80, 3, 5, 3610792936231799, 350954069309023861].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_75_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_75_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_75_div_5
  · have : q = 3610792936231799 := (Nat.prime_dvd_prime_iff_eq hq prime_3610792936231799).mp hdf
    subst this; exact prime_B_75_div_3610792936231799
  · have : q = 350954069309023861 := (Nat.prime_dvd_prime_iff_eq hq prime_350954069309023861).mp hdf
    subst this; exact prime_B_75_div_350954069309023861
private lemma pair_75 :
    Nat.Prime ((3 ^ 75 - 10587) * (2 ^ 75) - 1) ∧
    Nat.Prime ((3 ^ 75 - 10587) * (2 ^ 75) + 1) := by
  constructor
  · convert prime_A_75
  · convert prime_B_75
