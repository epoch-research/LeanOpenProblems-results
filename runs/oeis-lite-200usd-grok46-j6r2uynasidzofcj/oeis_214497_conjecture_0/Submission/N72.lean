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
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_859 : Nat.Prime 859 := by norm_num
private lemma prime_9323 : Nat.Prime 9323 := by norm_num
private lemma prime_47 : Nat.Prime 47 := by norm_num
private lemma prime_109 : Nat.Prime 109 := by norm_num
private lemma prime_571 : Nat.Prime 571 := by norm_num
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_71 : Nat.Prime 71 := by norm_num
private lemma prime_1667 : Nat.Prime 1667 := by norm_num
private lemma prime_14705891 : Nat.Prime 14705891 := by norm_num
private lemma prime_10099 : Nat.Prime 10099 := by norm_num
private lemma prime_23036183 : Nat.Prime 23036183 := by norm_num
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_1231459 : Nat.Prime 1231459 := by norm_num
private lemma prime_421158979_sub1 : (421158979 - 1 : ℕ) = 2 * 3 ^ 2 * 19 * 1231459 := by norm_num
private lemma prime_421158979_pow : (2 : ZMod 421158979) ^ (421158979 - 1) = 1 := by
  reduce_mod_char
private lemma prime_421158979_div_2 : (2 : ZMod 421158979) ^ ((421158979 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_421158979_div_3 : (2 : ZMod 421158979) ^ ((421158979 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_421158979_div_19 : (2 : ZMod 421158979) ^ ((421158979 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_421158979_div_1231459 : (2 : ZMod 421158979) ^ ((421158979 - 1) / 1231459) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_421158979 : Nat.Prime 421158979 := by
  refine lucas_primality 421158979 (2 : ZMod 421158979) prime_421158979_pow ?_
  intro q hq hqd
  rw [prime_421158979_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 19, 1231459].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_421158979_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_421158979_div_3
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_421158979_div_19
  · have : q = 1231459 := (Nat.prime_dvd_prime_iff_eq hq prime_1231459).mp hdf
    subst this; exact prime_421158979_div_1231459
private lemma prime_195958881518585897087_sub1 : (195958881518585897087 - 1 : ℕ) = 2 * 10099 * 23036183 * 421158979 := by norm_num
private lemma prime_195958881518585897087_pow : (5 : ZMod 195958881518585897087) ^ (195958881518585897087 - 1) = 1 := by
  reduce_mod_char
private lemma prime_195958881518585897087_div_2 : (5 : ZMod 195958881518585897087) ^ ((195958881518585897087 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_195958881518585897087_div_10099 : (5 : ZMod 195958881518585897087) ^ ((195958881518585897087 - 1) / 10099) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_195958881518585897087_div_23036183 : (5 : ZMod 195958881518585897087) ^ ((195958881518585897087 - 1) / 23036183) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_195958881518585897087_div_421158979 : (5 : ZMod 195958881518585897087) ^ ((195958881518585897087 - 1) / 421158979) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_195958881518585897087 : Nat.Prime 195958881518585897087 := by
  refine lucas_primality 195958881518585897087 (5 : ZMod 195958881518585897087) prime_195958881518585897087_pow ?_
  intro q hq hqd
  rw [prime_195958881518585897087_sub1] at hqd
  have : q ∣ [2, 10099, 23036183, 421158979].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_195958881518585897087_div_2
  · have : q = 10099 := (Nat.prime_dvd_prime_iff_eq hq prime_10099).mp hdf
    subst this; exact prime_195958881518585897087_div_10099
  · have : q = 23036183 := (Nat.prime_dvd_prime_iff_eq hq prime_23036183).mp hdf
    subst this; exact prime_195958881518585897087_div_23036183
  · have : q = 421158979 := (Nat.prime_dvd_prime_iff_eq hq prime_421158979).mp hdf
    subst this; exact prime_195958881518585897087_div_421158979
private lemma prime_11526999808376954706794558069_sub1 : (11526999808376954706794558069 - 1 : ℕ) = 2 ^ 2 * 14705891 * 195958881518585897087 := by norm_num
private lemma prime_11526999808376954706794558069_pow : (2 : ZMod 11526999808376954706794558069) ^ (11526999808376954706794558069 - 1) = 1 := by
  reduce_mod_char
private lemma prime_11526999808376954706794558069_div_2 : (2 : ZMod 11526999808376954706794558069) ^ ((11526999808376954706794558069 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11526999808376954706794558069_div_14705891 : (2 : ZMod 11526999808376954706794558069) ^ ((11526999808376954706794558069 - 1) / 14705891) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11526999808376954706794558069_div_195958881518585897087 : (2 : ZMod 11526999808376954706794558069) ^ ((11526999808376954706794558069 - 1) / 195958881518585897087) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11526999808376954706794558069 : Nat.Prime 11526999808376954706794558069 := by
  refine lucas_primality 11526999808376954706794558069 (2 : ZMod 11526999808376954706794558069) prime_11526999808376954706794558069_pow ?_
  intro q hq hqd
  rw [prime_11526999808376954706794558069_sub1] at hqd
  have : q ∣ [2 ^ 2, 14705891, 195958881518585897087].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_11526999808376954706794558069_div_2
  · have : q = 14705891 := (Nat.prime_dvd_prime_iff_eq hq prime_14705891).mp hdf
    subst this; exact prime_11526999808376954706794558069_div_14705891
  · have : q = 195958881518585897087 := (Nat.prime_dvd_prime_iff_eq hq prime_195958881518585897087).mp hdf
    subst this; exact prime_11526999808376954706794558069_div_195958881518585897087
private lemma prime_1461166495578796285436561438538089943001_sub1 : (1461166495578796285436561438538089943001 - 1 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 ^ 3 * 7 * 17 * 71 * 1667 * 11526999808376954706794558069 := by norm_num
private lemma prime_1461166495578796285436561438538089943001_pow : (11 : ZMod 1461166495578796285436561438538089943001) ^ (1461166495578796285436561438538089943001 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1461166495578796285436561438538089943001_div_2 : (11 : ZMod 1461166495578796285436561438538089943001) ^ ((1461166495578796285436561438538089943001 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1461166495578796285436561438538089943001_div_3 : (11 : ZMod 1461166495578796285436561438538089943001) ^ ((1461166495578796285436561438538089943001 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1461166495578796285436561438538089943001_div_5 : (11 : ZMod 1461166495578796285436561438538089943001) ^ ((1461166495578796285436561438538089943001 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1461166495578796285436561438538089943001_div_7 : (11 : ZMod 1461166495578796285436561438538089943001) ^ ((1461166495578796285436561438538089943001 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1461166495578796285436561438538089943001_div_17 : (11 : ZMod 1461166495578796285436561438538089943001) ^ ((1461166495578796285436561438538089943001 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1461166495578796285436561438538089943001_div_71 : (11 : ZMod 1461166495578796285436561438538089943001) ^ ((1461166495578796285436561438538089943001 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1461166495578796285436561438538089943001_div_1667 : (11 : ZMod 1461166495578796285436561438538089943001) ^ ((1461166495578796285436561438538089943001 - 1) / 1667) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1461166495578796285436561438538089943001_div_11526999808376954706794558069 : (11 : ZMod 1461166495578796285436561438538089943001) ^ ((1461166495578796285436561438538089943001 - 1) / 11526999808376954706794558069) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1461166495578796285436561438538089943001 : Nat.Prime 1461166495578796285436561438538089943001 := by
  refine lucas_primality 1461166495578796285436561438538089943001 (11 : ZMod 1461166495578796285436561438538089943001) prime_1461166495578796285436561438538089943001_pow ?_
  intro q hq hqd
  rw [prime_1461166495578796285436561438538089943001_sub1] at hqd
  have : q ∣ [2 ^ 3, 3 ^ 2, 5 ^ 3, 7, 17, 71, 1667, 11526999808376954706794558069].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1461166495578796285436561438538089943001_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_1461166495578796285436561438538089943001_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_1461166495578796285436561438538089943001_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_1461166495578796285436561438538089943001_div_7
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_1461166495578796285436561438538089943001_div_17
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_1461166495578796285436561438538089943001_div_71
  · have : q = 1667 := (Nat.prime_dvd_prime_iff_eq hq prime_1667).mp hdf
    subst this; exact prime_1461166495578796285436561438538089943001_div_1667
  · have : q = 11526999808376954706794558069 := (Nat.prime_dvd_prime_iff_eq hq prime_11526999808376954706794558069).mp hdf
    subst this; exact prime_1461166495578796285436561438538089943001_div_11526999808376954706794558069
private lemma prime_179518602957180857766330854914641883245855057787_sub1 : (179518602957180857766330854914641883245855057787 - 1 : ℕ) = 2 * 3 * 7 * 47 * 109 * 571 * 1461166495578796285436561438538089943001 := by norm_num
private lemma prime_179518602957180857766330854914641883245855057787_pow : (3 : ZMod 179518602957180857766330854914641883245855057787) ^ (179518602957180857766330854914641883245855057787 - 1) = 1 := by
  reduce_mod_char
private lemma prime_179518602957180857766330854914641883245855057787_div_2 : (3 : ZMod 179518602957180857766330854914641883245855057787) ^ ((179518602957180857766330854914641883245855057787 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_179518602957180857766330854914641883245855057787_div_3 : (3 : ZMod 179518602957180857766330854914641883245855057787) ^ ((179518602957180857766330854914641883245855057787 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_179518602957180857766330854914641883245855057787_div_7 : (3 : ZMod 179518602957180857766330854914641883245855057787) ^ ((179518602957180857766330854914641883245855057787 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_179518602957180857766330854914641883245855057787_div_47 : (3 : ZMod 179518602957180857766330854914641883245855057787) ^ ((179518602957180857766330854914641883245855057787 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_179518602957180857766330854914641883245855057787_div_109 : (3 : ZMod 179518602957180857766330854914641883245855057787) ^ ((179518602957180857766330854914641883245855057787 - 1) / 109) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_179518602957180857766330854914641883245855057787_div_571 : (3 : ZMod 179518602957180857766330854914641883245855057787) ^ ((179518602957180857766330854914641883245855057787 - 1) / 571) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_179518602957180857766330854914641883245855057787_div_1461166495578796285436561438538089943001 : (3 : ZMod 179518602957180857766330854914641883245855057787) ^ ((179518602957180857766330854914641883245855057787 - 1) / 1461166495578796285436561438538089943001) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_179518602957180857766330854914641883245855057787 : Nat.Prime 179518602957180857766330854914641883245855057787 := by
  refine lucas_primality 179518602957180857766330854914641883245855057787 (3 : ZMod 179518602957180857766330854914641883245855057787) prime_179518602957180857766330854914641883245855057787_pow ?_
  intro q hq hqd
  rw [prime_179518602957180857766330854914641883245855057787_sub1] at hqd
  have : q ∣ [2, 3, 7, 47, 109, 571, 1461166495578796285436561438538089943001].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_179518602957180857766330854914641883245855057787_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_179518602957180857766330854914641883245855057787_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_179518602957180857766330854914641883245855057787_div_7
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_179518602957180857766330854914641883245855057787_div_47
  · have : q = 109 := (Nat.prime_dvd_prime_iff_eq hq prime_109).mp hdf
    subst this; exact prime_179518602957180857766330854914641883245855057787_div_109
  · have : q = 571 := (Nat.prime_dvd_prime_iff_eq hq prime_571).mp hdf
    subst this; exact prime_179518602957180857766330854914641883245855057787_div_571
  · have : q = 1461166495578796285436561438538089943001 := (Nat.prime_dvd_prime_iff_eq hq prime_1461166495578796285436561438538089943001).mp hdf
    subst this; exact prime_179518602957180857766330854914641883245855057787_div_1461166495578796285436561438538089943001
private lemma prime_A_72_sub1 : (106387358923716524807713475752428966235635348730458144767 - 1 : ℕ) = 2 * 37 * 859 * 9323 * 179518602957180857766330854914641883245855057787 := by norm_num
private lemma prime_A_72_pow : (5 : ZMod 106387358923716524807713475752428966235635348730458144767) ^ (106387358923716524807713475752428966235635348730458144767 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_72_div_2 : (5 : ZMod 106387358923716524807713475752428966235635348730458144767) ^ ((106387358923716524807713475752428966235635348730458144767 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_72_div_37 : (5 : ZMod 106387358923716524807713475752428966235635348730458144767) ^ ((106387358923716524807713475752428966235635348730458144767 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_72_div_859 : (5 : ZMod 106387358923716524807713475752428966235635348730458144767) ^ ((106387358923716524807713475752428966235635348730458144767 - 1) / 859) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_72_div_9323 : (5 : ZMod 106387358923716524807713475752428966235635348730458144767) ^ ((106387358923716524807713475752428966235635348730458144767 - 1) / 9323) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_72_div_179518602957180857766330854914641883245855057787 : (5 : ZMod 106387358923716524807713475752428966235635348730458144767) ^ ((106387358923716524807713475752428966235635348730458144767 - 1) / 179518602957180857766330854914641883245855057787) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_72 : Nat.Prime 106387358923716524807713475752428966235635348730458144767 := by
  refine lucas_primality 106387358923716524807713475752428966235635348730458144767 (5 : ZMod 106387358923716524807713475752428966235635348730458144767) prime_A_72_pow ?_
  intro q hq hqd
  rw [prime_A_72_sub1] at hqd
  have : q ∣ [2, 37, 859, 9323, 179518602957180857766330854914641883245855057787].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_72_div_2
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_A_72_div_37
  · have : q = 859 := (Nat.prime_dvd_prime_iff_eq hq prime_859).mp hdf
    subst this; exact prime_A_72_div_859
  · have : q = 9323 := (Nat.prime_dvd_prime_iff_eq hq prime_9323).mp hdf
    subst this; exact prime_A_72_div_9323
  · have : q = 179518602957180857766330854914641883245855057787 := (Nat.prime_dvd_prime_iff_eq hq prime_179518602957180857766330854914641883245855057787).mp hdf
    subst this; exact prime_A_72_div_179518602957180857766330854914641883245855057787
private lemma prime_1321 : Nat.Prime 1321 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_18313907 : Nat.Prime 18313907 := by norm_num
private lemma prime_476161583_sub1 : (476161583 - 1 : ℕ) = 2 * 13 * 18313907 := by norm_num
private lemma prime_476161583_pow : (5 : ZMod 476161583) ^ (476161583 - 1) = 1 := by
  reduce_mod_char
private lemma prime_476161583_div_2 : (5 : ZMod 476161583) ^ ((476161583 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_476161583_div_13 : (5 : ZMod 476161583) ^ ((476161583 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_476161583_div_18313907 : (5 : ZMod 476161583) ^ ((476161583 - 1) / 18313907) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_476161583 : Nat.Prime 476161583 := by
  refine lucas_primality 476161583 (5 : ZMod 476161583) prime_476161583_pow ?_
  intro q hq hqd
  rw [prime_476161583_sub1] at hqd
  have : q ∣ [2, 13, 18313907].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_476161583_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_476161583_div_13
  · have : q = 18313907 := (Nat.prime_dvd_prime_iff_eq hq prime_18313907).mp hdf
    subst this; exact prime_476161583_div_18313907
private lemma prime_952323167_sub1 : (952323167 - 1 : ℕ) = 2 * 476161583 := by norm_num
private lemma prime_952323167_pow : (5 : ZMod 952323167) ^ (952323167 - 1) = 1 := by
  reduce_mod_char
private lemma prime_952323167_div_2 : (5 : ZMod 952323167) ^ ((952323167 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_952323167_div_476161583 : (5 : ZMod 952323167) ^ ((952323167 - 1) / 476161583) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_952323167 : Nat.Prime 952323167 := by
  refine lucas_primality 952323167 (5 : ZMod 952323167) prime_952323167_pow ?_
  intro q hq hqd
  rw [prime_952323167_sub1] at hqd
  have : q ∣ [2, 476161583].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_952323167_div_2
  · have : q = 476161583 := (Nat.prime_dvd_prime_iff_eq hq prime_476161583).mp hdf
    subst this; exact prime_952323167_div_476161583
private lemma prime_41 : Nat.Prime 41 := by norm_num
private lemma prime_151 : Nat.Prime 151 := by norm_num
private lemma prime_67 : Nat.Prime 67 := by norm_num
private lemma prime_167 : Nat.Prime 167 := by norm_num
private lemma prime_37501 : Nat.Prime 37501 := by norm_num
private lemma prime_150980376037_sub1 : (150980376037 - 1 : ℕ) = 2 ^ 2 * 3 * 7 ^ 2 * 41 * 167 * 37501 := by norm_num
private lemma prime_150980376037_pow : (2 : ZMod 150980376037) ^ (150980376037 - 1) = 1 := by
  reduce_mod_char
private lemma prime_150980376037_div_2 : (2 : ZMod 150980376037) ^ ((150980376037 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150980376037_div_3 : (2 : ZMod 150980376037) ^ ((150980376037 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150980376037_div_7 : (2 : ZMod 150980376037) ^ ((150980376037 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150980376037_div_41 : (2 : ZMod 150980376037) ^ ((150980376037 - 1) / 41) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150980376037_div_167 : (2 : ZMod 150980376037) ^ ((150980376037 - 1) / 167) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150980376037_div_37501 : (2 : ZMod 150980376037) ^ ((150980376037 - 1) / 37501) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150980376037 : Nat.Prime 150980376037 := by
  refine lucas_primality 150980376037 (2 : ZMod 150980376037) prime_150980376037_pow ?_
  intro q hq hqd
  rw [prime_150980376037_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 7 ^ 2, 41, 167, 37501].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_150980376037_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_150980376037_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_150980376037_div_7
  · have : q = 41 := (Nat.prime_dvd_prime_iff_eq hq prime_41).mp hdf
    subst this; exact prime_150980376037_div_41
  · have : q = 167 := (Nat.prime_dvd_prime_iff_eq hq prime_167).mp hdf
    subst this; exact prime_150980376037_div_167
  · have : q = 37501 := (Nat.prime_dvd_prime_iff_eq hq prime_37501).mp hdf
    subst this; exact prime_150980376037_div_37501
private lemma prime_789023445169363_sub1 : (789023445169363 - 1 : ℕ) = 2 * 3 * 13 * 67 * 150980376037 := by norm_num
private lemma prime_789023445169363_pow : (3 : ZMod 789023445169363) ^ (789023445169363 - 1) = 1 := by
  reduce_mod_char
private lemma prime_789023445169363_div_2 : (3 : ZMod 789023445169363) ^ ((789023445169363 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_789023445169363_div_3 : (3 : ZMod 789023445169363) ^ ((789023445169363 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_789023445169363_div_13 : (3 : ZMod 789023445169363) ^ ((789023445169363 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_789023445169363_div_67 : (3 : ZMod 789023445169363) ^ ((789023445169363 - 1) / 67) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_789023445169363_div_150980376037 : (3 : ZMod 789023445169363) ^ ((789023445169363 - 1) / 150980376037) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_789023445169363 : Nat.Prime 789023445169363 := by
  refine lucas_primality 789023445169363 (3 : ZMod 789023445169363) prime_789023445169363_pow ?_
  intro q hq hqd
  rw [prime_789023445169363_sub1] at hqd
  have : q ∣ [2, 3, 13, 67, 150980376037].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_789023445169363_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_789023445169363_div_3
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_789023445169363_div_13
  · have : q = 67 := (Nat.prime_dvd_prime_iff_eq hq prime_67).mp hdf
    subst this; exact prime_789023445169363_div_67
  · have : q = 150980376037 := (Nat.prime_dvd_prime_iff_eq hq prime_150980376037).mp hdf
    subst this; exact prime_789023445169363_div_150980376037
private lemma prime_127005947875131684659_sub1 : (127005947875131684659 - 1 : ℕ) = 2 * 13 * 41 * 151 * 789023445169363 := by norm_num
private lemma prime_127005947875131684659_pow : (2 : ZMod 127005947875131684659) ^ (127005947875131684659 - 1) = 1 := by
  reduce_mod_char
private lemma prime_127005947875131684659_div_2 : (2 : ZMod 127005947875131684659) ^ ((127005947875131684659 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_127005947875131684659_div_13 : (2 : ZMod 127005947875131684659) ^ ((127005947875131684659 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_127005947875131684659_div_41 : (2 : ZMod 127005947875131684659) ^ ((127005947875131684659 - 1) / 41) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_127005947875131684659_div_151 : (2 : ZMod 127005947875131684659) ^ ((127005947875131684659 - 1) / 151) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_127005947875131684659_div_789023445169363 : (2 : ZMod 127005947875131684659) ^ ((127005947875131684659 - 1) / 789023445169363) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_127005947875131684659 : Nat.Prime 127005947875131684659 := by
  refine lucas_primality 127005947875131684659 (2 : ZMod 127005947875131684659) prime_127005947875131684659_pow ?_
  intro q hq hqd
  rw [prime_127005947875131684659_sub1] at hqd
  have : q ∣ [2, 13, 41, 151, 789023445169363].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_127005947875131684659_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_127005947875131684659_div_13
  · have : q = 41 := (Nat.prime_dvd_prime_iff_eq hq prime_41).mp hdf
    subst this; exact prime_127005947875131684659_div_41
  · have : q = 151 := (Nat.prime_dvd_prime_iff_eq hq prime_151).mp hdf
    subst this; exact prime_127005947875131684659_div_151
  · have : q = 789023445169363 := (Nat.prime_dvd_prime_iff_eq hq prime_789023445169363).mp hdf
    subst this; exact prime_127005947875131684659_div_789023445169363
private lemma prime_B_72_sub1 : (106387358923716524807713475752428966235635348730458144769 - 1 : ℕ) = 2 ^ 72 * 3 * 47 * 1321 * 952323167 * 127005947875131684659 := by norm_num
private lemma prime_B_72_pow : (26 : ZMod 106387358923716524807713475752428966235635348730458144769) ^ (106387358923716524807713475752428966235635348730458144769 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_72_div_2 : (26 : ZMod 106387358923716524807713475752428966235635348730458144769) ^ ((106387358923716524807713475752428966235635348730458144769 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_72_div_3 : (26 : ZMod 106387358923716524807713475752428966235635348730458144769) ^ ((106387358923716524807713475752428966235635348730458144769 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_72_div_47 : (26 : ZMod 106387358923716524807713475752428966235635348730458144769) ^ ((106387358923716524807713475752428966235635348730458144769 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_72_div_1321 : (26 : ZMod 106387358923716524807713475752428966235635348730458144769) ^ ((106387358923716524807713475752428966235635348730458144769 - 1) / 1321) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_72_div_952323167 : (26 : ZMod 106387358923716524807713475752428966235635348730458144769) ^ ((106387358923716524807713475752428966235635348730458144769 - 1) / 952323167) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_72_div_127005947875131684659 : (26 : ZMod 106387358923716524807713475752428966235635348730458144769) ^ ((106387358923716524807713475752428966235635348730458144769 - 1) / 127005947875131684659) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_72 : Nat.Prime 106387358923716524807713475752428966235635348730458144769 := by
  refine lucas_primality 106387358923716524807713475752428966235635348730458144769 (26 : ZMod 106387358923716524807713475752428966235635348730458144769) prime_B_72_pow ?_
  intro q hq hqd
  rw [prime_B_72_sub1] at hqd
  have : q ∣ [2 ^ 72, 3, 47, 1321, 952323167, 127005947875131684659].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_72_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_72_div_3
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_B_72_div_47
  · have : q = 1321 := (Nat.prime_dvd_prime_iff_eq hq prime_1321).mp hdf
    subst this; exact prime_B_72_div_1321
  · have : q = 952323167 := (Nat.prime_dvd_prime_iff_eq hq prime_952323167).mp hdf
    subst this; exact prime_B_72_div_952323167
  · have : q = 127005947875131684659 := (Nat.prime_dvd_prime_iff_eq hq prime_127005947875131684659).mp hdf
    subst this; exact prime_B_72_div_127005947875131684659
private lemma pair_72 :
    Nat.Prime ((3 ^ 72 - 5808) * (2 ^ 72) - 1) ∧
    Nat.Prime ((3 ^ 72 - 5808) * (2 ^ 72) + 1) := by
  constructor
  · convert prime_A_72
  · convert prime_B_72
