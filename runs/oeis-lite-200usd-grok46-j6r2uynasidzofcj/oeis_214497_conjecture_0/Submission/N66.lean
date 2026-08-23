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

/- n=66 -/
private lemma prime_43 : Nat.Prime 43 := by norm_num
private lemma prime_3797 : Nat.Prime 3797 := by norm_num
private lemma prime_31 : Nat.Prime 31 := by norm_num
private lemma prime_4919333 : Nat.Prime 4919333 := by norm_num
private lemma prime_304998647_sub1 : (304998647 - 1 : ℕ) = 2 * 31 * 4919333 := by norm_num
private lemma prime_304998647_pow : (5 : ZMod 304998647) ^ (304998647 - 1) = 1 := by
  reduce_mod_char
private lemma prime_304998647_div_2 : (5 : ZMod 304998647) ^ ((304998647 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_304998647_div_31 : (5 : ZMod 304998647) ^ ((304998647 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_304998647_div_4919333 : (5 : ZMod 304998647) ^ ((304998647 - 1) / 4919333) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_304998647 : Nat.Prime 304998647 := by
  refine lucas_primality 304998647 (5 : ZMod 304998647) prime_304998647_pow ?_
  intro q hq hqd
  rw [prime_304998647_sub1] at hqd
  have : q ∣ [2, 31, 4919333].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_304998647_div_2
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_304998647_div_31
  · have : q = 4919333 := (Nat.prime_dvd_prime_iff_eq hq prime_4919333).mp hdf
    subst this; exact prime_304998647_div_4919333
private lemma prime_1829991883_sub1 : (1829991883 - 1 : ℕ) = 2 * 3 * 304998647 := by norm_num
private lemma prime_1829991883_pow : (2 : ZMod 1829991883) ^ (1829991883 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1829991883_div_2 : (2 : ZMod 1829991883) ^ ((1829991883 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1829991883_div_3 : (2 : ZMod 1829991883) ^ ((1829991883 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1829991883_div_304998647 : (2 : ZMod 1829991883) ^ ((1829991883 - 1) / 304998647) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1829991883 : Nat.Prime 1829991883 := by
  refine lucas_primality 1829991883 (2 : ZMod 1829991883) prime_1829991883_pow ?_
  intro q hq hqd
  rw [prime_1829991883_sub1] at hqd
  have : q ∣ [2, 3, 304998647].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1829991883_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1829991883_div_3
  · have : q = 304998647 := (Nat.prime_dvd_prime_iff_eq hq prime_304998647).mp hdf
    subst this; exact prime_1829991883_div_304998647
private lemma prime_7319967533_sub1 : (7319967533 - 1 : ℕ) = 2 ^ 2 * 1829991883 := by norm_num
private lemma prime_7319967533_pow : (2 : ZMod 7319967533) ^ (7319967533 - 1) = 1 := by
  reduce_mod_char
private lemma prime_7319967533_div_2 : (2 : ZMod 7319967533) ^ ((7319967533 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7319967533_div_1829991883 : (2 : ZMod 7319967533) ^ ((7319967533 - 1) / 1829991883) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7319967533 : Nat.Prime 7319967533 := by
  refine lucas_primality 7319967533 (2 : ZMod 7319967533) prime_7319967533_pow ?_
  intro q hq hqd
  rw [prime_7319967533_sub1] at hqd
  have : q ∣ [2 ^ 2, 1829991883].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_7319967533_div_2
  · have : q = 1829991883 := (Nat.prime_dvd_prime_iff_eq hq prime_1829991883).mp hdf
    subst this; exact prime_7319967533_div_1829991883
private lemma prime_37313 : Nat.Prime 37313 := by norm_num
private lemma prime_514117 : Nat.Prime 514117 := by norm_num
private lemma prime_38366495243_sub1 : (38366495243 - 1 : ℕ) = 2 * 37313 * 514117 := by norm_num
private lemma prime_38366495243_pow : (2 : ZMod 38366495243) ^ (38366495243 - 1) = 1 := by
  reduce_mod_char
private lemma prime_38366495243_div_2 : (2 : ZMod 38366495243) ^ ((38366495243 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_38366495243_div_37313 : (2 : ZMod 38366495243) ^ ((38366495243 - 1) / 37313) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_38366495243_div_514117 : (2 : ZMod 38366495243) ^ ((38366495243 - 1) / 514117) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_38366495243 : Nat.Prime 38366495243 := by
  refine lucas_primality 38366495243 (2 : ZMod 38366495243) prime_38366495243_pow ?_
  intro q hq hqd
  rw [prime_38366495243_sub1] at hqd
  have : q ∣ [2, 37313, 514117].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_38366495243_div_2
  · have : q = 37313 := (Nat.prime_dvd_prime_iff_eq hq prime_37313).mp hdf
    subst this; exact prime_38366495243_div_37313
  · have : q = 514117 := (Nat.prime_dvd_prime_iff_eq hq prime_514117).mp hdf
    subst this; exact prime_38366495243_div_514117
private lemma prime_620003 : Nat.Prime 620003 := by norm_num
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_16927441 : Nat.Prime 16927441 := by norm_num
private lemma prime_73 : Nat.Prime 73 := by norm_num
private lemma prime_136139 : Nat.Prime 136139 := by norm_num
private lemma prime_854680643_sub1 : (854680643 - 1 : ℕ) = 2 * 43 * 73 * 136139 := by norm_num
private lemma prime_854680643_pow : (2 : ZMod 854680643) ^ (854680643 - 1) = 1 := by
  reduce_mod_char
private lemma prime_854680643_div_2 : (2 : ZMod 854680643) ^ ((854680643 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_854680643_div_43 : (2 : ZMod 854680643) ^ ((854680643 - 1) / 43) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_854680643_div_73 : (2 : ZMod 854680643) ^ ((854680643 - 1) / 73) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_854680643_div_136139 : (2 : ZMod 854680643) ^ ((854680643 - 1) / 136139) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_854680643 : Nat.Prime 854680643 := by
  refine lucas_primality 854680643 (2 : ZMod 854680643) prime_854680643_pow ?_
  intro q hq hqd
  rw [prime_854680643_sub1] at hqd
  have : q ∣ [2, 43, 73, 136139].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_854680643_div_2
  · have : q = 43 := (Nat.prime_dvd_prime_iff_eq hq prime_43).mp hdf
    subst this; exact prime_854680643_div_43
  · have : q = 73 := (Nat.prime_dvd_prime_iff_eq hq prime_73).mp hdf
    subst this; exact prime_854680643_div_73
  · have : q = 136139 := (Nat.prime_dvd_prime_iff_eq hq prime_136139).mp hdf
    subst this; exact prime_854680643_div_136139
private lemma prime_6684010945099748107_sub1 : (6684010945099748107 - 1 : ℕ) = 2 * 3 * 7 * 11 * 16927441 * 854680643 := by norm_num
private lemma prime_6684010945099748107_pow : (7 : ZMod 6684010945099748107) ^ (6684010945099748107 - 1) = 1 := by
  reduce_mod_char
private lemma prime_6684010945099748107_div_2 : (7 : ZMod 6684010945099748107) ^ ((6684010945099748107 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6684010945099748107_div_3 : (7 : ZMod 6684010945099748107) ^ ((6684010945099748107 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6684010945099748107_div_7 : (7 : ZMod 6684010945099748107) ^ ((6684010945099748107 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6684010945099748107_div_11 : (7 : ZMod 6684010945099748107) ^ ((6684010945099748107 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6684010945099748107_div_16927441 : (7 : ZMod 6684010945099748107) ^ ((6684010945099748107 - 1) / 16927441) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6684010945099748107_div_854680643 : (7 : ZMod 6684010945099748107) ^ ((6684010945099748107 - 1) / 854680643) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6684010945099748107 : Nat.Prime 6684010945099748107 := by
  refine lucas_primality 6684010945099748107 (7 : ZMod 6684010945099748107) prime_6684010945099748107_pow ?_
  intro q hq hqd
  rw [prime_6684010945099748107_sub1] at hqd
  have : q ∣ [2, 3, 7, 11, 16927441, 854680643].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_6684010945099748107_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_6684010945099748107_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_6684010945099748107_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_6684010945099748107_div_11
  · have : q = 16927441 := (Nat.prime_dvd_prime_iff_eq hq prime_16927441).mp hdf
    subst this; exact prime_6684010945099748107_div_16927441
  · have : q = 854680643 := (Nat.prime_dvd_prime_iff_eq hq prime_854680643).mp hdf
    subst this; exact prime_6684010945099748107_div_854680643
private lemma prime_24864641027968074753505927_sub1 : (24864641027968074753505927 - 1 : ℕ) = 2 * 3 * 620003 * 6684010945099748107 := by norm_num
private lemma prime_24864641027968074753505927_pow : (5 : ZMod 24864641027968074753505927) ^ (24864641027968074753505927 - 1) = 1 := by
  reduce_mod_char
private lemma prime_24864641027968074753505927_div_2 : (5 : ZMod 24864641027968074753505927) ^ ((24864641027968074753505927 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_24864641027968074753505927_div_3 : (5 : ZMod 24864641027968074753505927) ^ ((24864641027968074753505927 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_24864641027968074753505927_div_620003 : (5 : ZMod 24864641027968074753505927) ^ ((24864641027968074753505927 - 1) / 620003) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_24864641027968074753505927_div_6684010945099748107 : (5 : ZMod 24864641027968074753505927) ^ ((24864641027968074753505927 - 1) / 6684010945099748107) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_24864641027968074753505927 : Nat.Prime 24864641027968074753505927 := by
  refine lucas_primality 24864641027968074753505927 (5 : ZMod 24864641027968074753505927) prime_24864641027968074753505927_pow ?_
  intro q hq hqd
  rw [prime_24864641027968074753505927_sub1] at hqd
  have : q ∣ [2, 3, 620003, 6684010945099748107].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_24864641027968074753505927_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_24864641027968074753505927_div_3
  · have : q = 620003 := (Nat.prime_dvd_prime_iff_eq hq prime_620003).mp hdf
    subst this; exact prime_24864641027968074753505927_div_620003
  · have : q = 6684010945099748107 := (Nat.prime_dvd_prime_iff_eq hq prime_6684010945099748107).mp hdf
    subst this; exact prime_24864641027968074753505927_div_6684010945099748107
private lemma prime_A_66_sub1 : (2280250319867037997421842329797680071335288135221247 - 1 : ℕ) = 2 * 43 * 3797 * 7319967533 * 38366495243 * 24864641027968074753505927 := by norm_num
private lemma prime_A_66_pow : (5 : ZMod 2280250319867037997421842329797680071335288135221247) ^ (2280250319867037997421842329797680071335288135221247 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_66_div_2 : (5 : ZMod 2280250319867037997421842329797680071335288135221247) ^ ((2280250319867037997421842329797680071335288135221247 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_66_div_43 : (5 : ZMod 2280250319867037997421842329797680071335288135221247) ^ ((2280250319867037997421842329797680071335288135221247 - 1) / 43) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_66_div_3797 : (5 : ZMod 2280250319867037997421842329797680071335288135221247) ^ ((2280250319867037997421842329797680071335288135221247 - 1) / 3797) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_66_div_7319967533 : (5 : ZMod 2280250319867037997421842329797680071335288135221247) ^ ((2280250319867037997421842329797680071335288135221247 - 1) / 7319967533) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_66_div_38366495243 : (5 : ZMod 2280250319867037997421842329797680071335288135221247) ^ ((2280250319867037997421842329797680071335288135221247 - 1) / 38366495243) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_66_div_24864641027968074753505927 : (5 : ZMod 2280250319867037997421842329797680071335288135221247) ^ ((2280250319867037997421842329797680071335288135221247 - 1) / 24864641027968074753505927) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_66 : Nat.Prime 2280250319867037997421842329797680071335288135221247 := by
  refine lucas_primality 2280250319867037997421842329797680071335288135221247 (5 : ZMod 2280250319867037997421842329797680071335288135221247) prime_A_66_pow ?_
  intro q hq hqd
  rw [prime_A_66_sub1] at hqd
  have : q ∣ [2, 43, 3797, 7319967533, 38366495243, 24864641027968074753505927].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_66_div_2
  · have : q = 43 := (Nat.prime_dvd_prime_iff_eq hq prime_43).mp hdf
    subst this; exact prime_A_66_div_43
  · have : q = 3797 := (Nat.prime_dvd_prime_iff_eq hq prime_3797).mp hdf
    subst this; exact prime_A_66_div_3797
  · have : q = 7319967533 := (Nat.prime_dvd_prime_iff_eq hq prime_7319967533).mp hdf
    subst this; exact prime_A_66_div_7319967533
  · have : q = 38366495243 := (Nat.prime_dvd_prime_iff_eq hq prime_38366495243).mp hdf
    subst this; exact prime_A_66_div_38366495243
  · have : q = 24864641027968074753505927 := (Nat.prime_dvd_prime_iff_eq hq prime_24864641027968074753505927).mp hdf
    subst this; exact prime_A_66_div_24864641027968074753505927
private lemma prime_3517 : Nat.Prime 3517 := by norm_num
private lemma prime_155453 : Nat.Prime 155453 := by norm_num
private lemma prime_9668479 : Nat.Prime 9668479 := by norm_num
private lemma prime_11689 : Nat.Prime 11689 := by norm_num
private lemma prime_39468503 : Nat.Prime 39468503 := by norm_num
private lemma prime_3690778652537_sub1 : (3690778652537 - 1 : ℕ) = 2 ^ 3 * 11689 * 39468503 := by norm_num
private lemma prime_3690778652537_pow : (3 : ZMod 3690778652537) ^ (3690778652537 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3690778652537_div_2 : (3 : ZMod 3690778652537) ^ ((3690778652537 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3690778652537_div_11689 : (3 : ZMod 3690778652537) ^ ((3690778652537 - 1) / 11689) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3690778652537_div_39468503 : (3 : ZMod 3690778652537) ^ ((3690778652537 - 1) / 39468503) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3690778652537 : Nat.Prime 3690778652537 := by
  refine lucas_primality 3690778652537 (3 : ZMod 3690778652537) prime_3690778652537_pow ?_
  intro q hq hqd
  rw [prime_3690778652537_sub1] at hqd
  have : q ∣ [2 ^ 3, 11689, 39468503].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_3690778652537_div_2
  · have : q = 11689 := (Nat.prime_dvd_prime_iff_eq hq prime_11689).mp hdf
    subst this; exact prime_3690778652537_div_11689
  · have : q = 39468503 := (Nat.prime_dvd_prime_iff_eq hq prime_39468503).mp hdf
    subst this; exact prime_3690778652537_div_39468503
private lemma prime_B_66_sub1 : (2280250319867037997421842329797680071335288135221249 - 1 : ℕ) = 2 ^ 70 * 3 ^ 2 * 11 * 3517 * 155453 * 9668479 * 3690778652537 := by norm_num
private lemma prime_B_66_pow : (23 : ZMod 2280250319867037997421842329797680071335288135221249) ^ (2280250319867037997421842329797680071335288135221249 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_66_div_2 : (23 : ZMod 2280250319867037997421842329797680071335288135221249) ^ ((2280250319867037997421842329797680071335288135221249 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_66_div_3 : (23 : ZMod 2280250319867037997421842329797680071335288135221249) ^ ((2280250319867037997421842329797680071335288135221249 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_66_div_11 : (23 : ZMod 2280250319867037997421842329797680071335288135221249) ^ ((2280250319867037997421842329797680071335288135221249 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_66_div_3517 : (23 : ZMod 2280250319867037997421842329797680071335288135221249) ^ ((2280250319867037997421842329797680071335288135221249 - 1) / 3517) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_66_div_155453 : (23 : ZMod 2280250319867037997421842329797680071335288135221249) ^ ((2280250319867037997421842329797680071335288135221249 - 1) / 155453) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_66_div_9668479 : (23 : ZMod 2280250319867037997421842329797680071335288135221249) ^ ((2280250319867037997421842329797680071335288135221249 - 1) / 9668479) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_66_div_3690778652537 : (23 : ZMod 2280250319867037997421842329797680071335288135221249) ^ ((2280250319867037997421842329797680071335288135221249 - 1) / 3690778652537) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_66 : Nat.Prime 2280250319867037997421842329797680071335288135221249 := by
  refine lucas_primality 2280250319867037997421842329797680071335288135221249 (23 : ZMod 2280250319867037997421842329797680071335288135221249) prime_B_66_pow ?_
  intro q hq hqd
  rw [prime_B_66_sub1] at hqd
  have : q ∣ [2 ^ 70, 3 ^ 2, 11, 3517, 155453, 9668479, 3690778652537].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_66_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_66_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_66_div_11
  · have : q = 3517 := (Nat.prime_dvd_prime_iff_eq hq prime_3517).mp hdf
    subst this; exact prime_B_66_div_3517
  · have : q = 155453 := (Nat.prime_dvd_prime_iff_eq hq prime_155453).mp hdf
    subst this; exact prime_B_66_div_155453
  · have : q = 9668479 := (Nat.prime_dvd_prime_iff_eq hq prime_9668479).mp hdf
    subst this; exact prime_B_66_div_9668479
  · have : q = 3690778652537 := (Nat.prime_dvd_prime_iff_eq hq prime_3690778652537).mp hdf
    subst this; exact prime_B_66_div_3690778652537
private lemma pair_66 :
    Nat.Prime ((3 ^ 66 - 3897) * (2 ^ 66) - 1) ∧
    Nat.Prime ((3 ^ 66 - 3897) * (2 ^ 66) + 1) := by
  constructor
  · convert prime_A_66
  · convert prime_B_66
