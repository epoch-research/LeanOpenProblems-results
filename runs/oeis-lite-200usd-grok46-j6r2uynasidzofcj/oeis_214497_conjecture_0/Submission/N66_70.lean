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

/- Pair for n = 66 -/
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

/- Pair for n = 67 -/
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_4591 : Nat.Prime 4591 := by norm_num
private lemma prime_409 : Nat.Prime 409 := by norm_num
private lemma prime_1942027 : Nat.Prime 1942027 := by norm_num
private lemma prime_3177156173_sub1 : (3177156173 - 1 : ℕ) = 2 ^ 2 * 409 * 1942027 := by norm_num
private lemma prime_3177156173_pow : (2 : ZMod 3177156173) ^ (3177156173 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3177156173_div_2 : (2 : ZMod 3177156173) ^ ((3177156173 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3177156173_div_409 : (2 : ZMod 3177156173) ^ ((3177156173 - 1) / 409) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3177156173_div_1942027 : (2 : ZMod 3177156173) ^ ((3177156173 - 1) / 1942027) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3177156173 : Nat.Prime 3177156173 := by
  refine lucas_primality 3177156173 (2 : ZMod 3177156173) prime_3177156173_pow ?_
  intro q hq hqd
  rw [prime_3177156173_sub1] at hqd
  have : q ∣ [2 ^ 2, 409, 1942027].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_3177156173_div_2
  · have : q = 409 := (Nat.prime_dvd_prime_iff_eq hq prime_409).mp hdf
    subst this; exact prime_3177156173_div_409
  · have : q = 1942027 := (Nat.prime_dvd_prime_iff_eq hq prime_1942027).mp hdf
    subst this; exact prime_3177156173_div_1942027
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_19889 : Nat.Prime 19889 := by norm_num
private lemma prime_147178601_sub1 : (147178601 - 1 : ℕ) = 2 ^ 3 * 5 ^ 2 * 37 * 19889 := by norm_num
private lemma prime_147178601_pow : (7 : ZMod 147178601) ^ (147178601 - 1) = 1 := by
  reduce_mod_char
private lemma prime_147178601_div_2 : (7 : ZMod 147178601) ^ ((147178601 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_147178601_div_5 : (7 : ZMod 147178601) ^ ((147178601 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_147178601_div_37 : (7 : ZMod 147178601) ^ ((147178601 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_147178601_div_19889 : (7 : ZMod 147178601) ^ ((147178601 - 1) / 19889) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_147178601 : Nat.Prime 147178601 := by
  refine lucas_primality 147178601 (7 : ZMod 147178601) prime_147178601_pow ?_
  intro q hq hqd
  rw [prime_147178601_sub1] at hqd
  have : q ∣ [2 ^ 3, 5 ^ 2, 37, 19889].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_147178601_div_2
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_147178601_div_5
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_147178601_div_37
  · have : q = 19889 := (Nat.prime_dvd_prime_iff_eq hq prime_19889).mp hdf
    subst this; exact prime_147178601_div_19889
private lemma prime_18544503727_sub1 : (18544503727 - 1 : ℕ) = 2 * 3 ^ 2 * 7 * 147178601 := by norm_num
private lemma prime_18544503727_pow : (3 : ZMod 18544503727) ^ (18544503727 - 1) = 1 := by
  reduce_mod_char
private lemma prime_18544503727_div_2 : (3 : ZMod 18544503727) ^ ((18544503727 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18544503727_div_3 : (3 : ZMod 18544503727) ^ ((18544503727 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18544503727_div_7 : (3 : ZMod 18544503727) ^ ((18544503727 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18544503727_div_147178601 : (3 : ZMod 18544503727) ^ ((18544503727 - 1) / 147178601) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18544503727 : Nat.Prime 18544503727 := by
  refine lucas_primality 18544503727 (3 : ZMod 18544503727) prime_18544503727_pow ?_
  intro q hq hqd
  rw [prime_18544503727_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 7, 147178601].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_18544503727_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_18544503727_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_18544503727_div_7
  · have : q = 147178601 := (Nat.prime_dvd_prime_iff_eq hq prime_147178601).mp hdf
    subst this; exact prime_18544503727_div_147178601
private lemma prime_29 : Nat.Prime 29 := by norm_num
private lemma prime_18947 : Nat.Prime 18947 := by norm_num
private lemma prime_201517 : Nat.Prime 201517 := by norm_num
private lemma prime_4349987 : Nat.Prime 4349987 := by norm_num
private lemma prime_20319457 : Nat.Prime 20319457 := by norm_num
private lemma prime_78296110147288600925391113_sub1 : (78296110147288600925391113 - 1 : ℕ) = 2 ^ 3 * 29 * 18947 * 201517 * 4349987 * 20319457 := by norm_num
private lemma prime_78296110147288600925391113_pow : (3 : ZMod 78296110147288600925391113) ^ (78296110147288600925391113 - 1) = 1 := by
  reduce_mod_char
private lemma prime_78296110147288600925391113_div_2 : (3 : ZMod 78296110147288600925391113) ^ ((78296110147288600925391113 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_78296110147288600925391113_div_29 : (3 : ZMod 78296110147288600925391113) ^ ((78296110147288600925391113 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_78296110147288600925391113_div_18947 : (3 : ZMod 78296110147288600925391113) ^ ((78296110147288600925391113 - 1) / 18947) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_78296110147288600925391113_div_201517 : (3 : ZMod 78296110147288600925391113) ^ ((78296110147288600925391113 - 1) / 201517) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_78296110147288600925391113_div_4349987 : (3 : ZMod 78296110147288600925391113) ^ ((78296110147288600925391113 - 1) / 4349987) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_78296110147288600925391113_div_20319457 : (3 : ZMod 78296110147288600925391113) ^ ((78296110147288600925391113 - 1) / 20319457) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_78296110147288600925391113 : Nat.Prime 78296110147288600925391113 := by
  refine lucas_primality 78296110147288600925391113 (3 : ZMod 78296110147288600925391113) prime_78296110147288600925391113_pow ?_
  intro q hq hqd
  rw [prime_78296110147288600925391113_sub1] at hqd
  have : q ∣ [2 ^ 3, 29, 18947, 201517, 4349987, 20319457].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_78296110147288600925391113_div_2
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_78296110147288600925391113_div_29
  · have : q = 18947 := (Nat.prime_dvd_prime_iff_eq hq prime_18947).mp hdf
    subst this; exact prime_78296110147288600925391113_div_18947
  · have : q = 201517 := (Nat.prime_dvd_prime_iff_eq hq prime_201517).mp hdf
    subst this; exact prime_78296110147288600925391113_div_201517
  · have : q = 4349987 := (Nat.prime_dvd_prime_iff_eq hq prime_4349987).mp hdf
    subst this; exact prime_78296110147288600925391113_div_4349987
  · have : q = 20319457 := (Nat.prime_dvd_prime_iff_eq hq prime_20319457).mp hdf
    subst this; exact prime_78296110147288600925391113_div_20319457
private lemma prime_A_67_sub1 : (13681501919202227984531053980286022082133199872327679 - 1 : ℕ) = 2 * 17 * 19 * 4591 * 3177156173 * 18544503727 * 78296110147288600925391113 := by norm_num
private lemma prime_A_67_pow : (26 : ZMod 13681501919202227984531053980286022082133199872327679) ^ (13681501919202227984531053980286022082133199872327679 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_67_div_2 : (26 : ZMod 13681501919202227984531053980286022082133199872327679) ^ ((13681501919202227984531053980286022082133199872327679 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_67_div_17 : (26 : ZMod 13681501919202227984531053980286022082133199872327679) ^ ((13681501919202227984531053980286022082133199872327679 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_67_div_19 : (26 : ZMod 13681501919202227984531053980286022082133199872327679) ^ ((13681501919202227984531053980286022082133199872327679 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_67_div_4591 : (26 : ZMod 13681501919202227984531053980286022082133199872327679) ^ ((13681501919202227984531053980286022082133199872327679 - 1) / 4591) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_67_div_3177156173 : (26 : ZMod 13681501919202227984531053980286022082133199872327679) ^ ((13681501919202227984531053980286022082133199872327679 - 1) / 3177156173) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_67_div_18544503727 : (26 : ZMod 13681501919202227984531053980286022082133199872327679) ^ ((13681501919202227984531053980286022082133199872327679 - 1) / 18544503727) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_67_div_78296110147288600925391113 : (26 : ZMod 13681501919202227984531053980286022082133199872327679) ^ ((13681501919202227984531053980286022082133199872327679 - 1) / 78296110147288600925391113) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_67 : Nat.Prime 13681501919202227984531053980286022082133199872327679 := by
  refine lucas_primality 13681501919202227984531053980286022082133199872327679 (26 : ZMod 13681501919202227984531053980286022082133199872327679) prime_A_67_pow ?_
  intro q hq hqd
  rw [prime_A_67_sub1] at hqd
  have : q ∣ [2, 17, 19, 4591, 3177156173, 18544503727, 78296110147288600925391113].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_67_div_2
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_A_67_div_17
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_A_67_div_19
  · have : q = 4591 := (Nat.prime_dvd_prime_iff_eq hq prime_4591).mp hdf
    subst this; exact prime_A_67_div_4591
  · have : q = 3177156173 := (Nat.prime_dvd_prime_iff_eq hq prime_3177156173).mp hdf
    subst this; exact prime_A_67_div_3177156173
  · have : q = 18544503727 := (Nat.prime_dvd_prime_iff_eq hq prime_18544503727).mp hdf
    subst this; exact prime_A_67_div_18544503727
  · have : q = 78296110147288600925391113 := (Nat.prime_dvd_prime_iff_eq hq prime_78296110147288600925391113).mp hdf
    subst this; exact prime_A_67_div_78296110147288600925391113
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_61 : Nat.Prime 61 := by norm_num
private lemma prime_271 : Nat.Prime 271 := by norm_num
private lemma prime_1181 : Nat.Prime 1181 := by norm_num
private lemma prime_4561 : Nat.Prime 4561 := by norm_num
private lemma prime_47763361 : Nat.Prime 47763361 := by norm_num
private lemma prime_140468883557420965281457462741_sub1 : (140468883557420965281457462741 - 1 : ℕ) = 2 ^ 2 * 3 ^ 6 * 5 * 7 * 11 * 13 * 31 * 61 * 73 * 271 * 1181 * 4561 * 47763361 := by norm_num
private lemma prime_140468883557420965281457462741_pow : (10 : ZMod 140468883557420965281457462741) ^ (140468883557420965281457462741 - 1) = 1 := by
  reduce_mod_char
private lemma prime_140468883557420965281457462741_div_2 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_3 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_5 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_7 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_11 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_13 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_31 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_61 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 61) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_73 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 73) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_271 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 271) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_1181 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 1181) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_4561 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 4561) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741_div_47763361 : (10 : ZMod 140468883557420965281457462741) ^ ((140468883557420965281457462741 - 1) / 47763361) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_140468883557420965281457462741 : Nat.Prime 140468883557420965281457462741 := by
  refine lucas_primality 140468883557420965281457462741 (10 : ZMod 140468883557420965281457462741) prime_140468883557420965281457462741_pow ?_
  intro q hq hqd
  rw [prime_140468883557420965281457462741_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 6, 5, 7, 11, 13, 31, 61, 73, 271, 1181, 4561, 47763361].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_140468883557420965281457462741_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_140468883557420965281457462741_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_11
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_13
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_31
  · have : q = 61 := (Nat.prime_dvd_prime_iff_eq hq prime_61).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_61
  · have : q = 73 := (Nat.prime_dvd_prime_iff_eq hq prime_73).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_73
  · have : q = 271 := (Nat.prime_dvd_prime_iff_eq hq prime_271).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_271
  · have : q = 1181 := (Nat.prime_dvd_prime_iff_eq hq prime_1181).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_1181
  · have : q = 4561 := (Nat.prime_dvd_prime_iff_eq hq prime_4561).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_4561
  · have : q = 47763361 := (Nat.prime_dvd_prime_iff_eq hq prime_47763361).mp hdf
    subst this; exact prime_140468883557420965281457462741_div_47763361
private lemma prime_B_67_sub1 : (13681501919202227984531053980286022082133199872327681 - 1 : ℕ) = 2 ^ 69 * 3 * 5 * 11 * 140468883557420965281457462741 := by norm_num
private lemma prime_B_67_pow : (19 : ZMod 13681501919202227984531053980286022082133199872327681) ^ (13681501919202227984531053980286022082133199872327681 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_67_div_2 : (19 : ZMod 13681501919202227984531053980286022082133199872327681) ^ ((13681501919202227984531053980286022082133199872327681 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_67_div_3 : (19 : ZMod 13681501919202227984531053980286022082133199872327681) ^ ((13681501919202227984531053980286022082133199872327681 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_67_div_5 : (19 : ZMod 13681501919202227984531053980286022082133199872327681) ^ ((13681501919202227984531053980286022082133199872327681 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_67_div_11 : (19 : ZMod 13681501919202227984531053980286022082133199872327681) ^ ((13681501919202227984531053980286022082133199872327681 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_67_div_140468883557420965281457462741 : (19 : ZMod 13681501919202227984531053980286022082133199872327681) ^ ((13681501919202227984531053980286022082133199872327681 - 1) / 140468883557420965281457462741) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_67 : Nat.Prime 13681501919202227984531053980286022082133199872327681 := by
  refine lucas_primality 13681501919202227984531053980286022082133199872327681 (19 : ZMod 13681501919202227984531053980286022082133199872327681) prime_B_67_pow ?_
  intro q hq hqd
  rw [prime_B_67_sub1] at hqd
  have : q ∣ [2 ^ 69, 3, 5, 11, 140468883557420965281457462741].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_67_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_67_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_67_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_67_div_11
  · have : q = 140468883557420965281457462741 := (Nat.prime_dvd_prime_iff_eq hq prime_140468883557420965281457462741).mp hdf
    subst this; exact prime_B_67_div_140468883557420965281457462741
private lemma pair_67 :
    Nat.Prime ((3 ^ 67 - 1527) * (2 ^ 67) - 1) ∧
    Nat.Prime ((3 ^ 67 - 1527) * (2 ^ 67) + 1) := by
  constructor
  · convert prime_A_67
  · convert prime_B_67

/- Pair for n = 68 -/
private lemma prime_59 : Nat.Prime 59 := by norm_num
private lemma prime_576469 : Nat.Prime 576469 := by norm_num
private lemma prime_59931593 : Nat.Prime 59931593 := by norm_num
private lemma prime_119863187_sub1 : (119863187 - 1 : ℕ) = 2 * 59931593 := by norm_num
private lemma prime_119863187_pow : (2 : ZMod 119863187) ^ (119863187 - 1) = 1 := by
  reduce_mod_char
private lemma prime_119863187_div_2 : (2 : ZMod 119863187) ^ ((119863187 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_119863187_div_59931593 : (2 : ZMod 119863187) ^ ((119863187 - 1) / 59931593) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_119863187 : Nat.Prime 119863187 := by
  refine lucas_primality 119863187 (2 : ZMod 119863187) prime_119863187_pow ?_
  intro q hq hqd
  rw [prime_119863187_sub1] at hqd
  have : q ∣ [2, 59931593].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_119863187_div_2
  · have : q = 59931593 := (Nat.prime_dvd_prime_iff_eq hq prime_59931593).mp hdf
    subst this; exact prime_119863187_div_59931593
private lemma prime_311 : Nat.Prime 311 := by norm_num
private lemma prime_3769 : Nat.Prime 3769 := by norm_num
private lemma prime_5443 : Nat.Prime 5443 := by norm_num
private lemma prime_123088003_sub1 : (123088003 - 1 : ℕ) = 2 * 3 * 3769 * 5443 := by norm_num
private lemma prime_123088003_pow : (3 : ZMod 123088003) ^ (123088003 - 1) = 1 := by
  reduce_mod_char
private lemma prime_123088003_div_2 : (3 : ZMod 123088003) ^ ((123088003 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_123088003_div_3 : (3 : ZMod 123088003) ^ ((123088003 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_123088003_div_3769 : (3 : ZMod 123088003) ^ ((123088003 - 1) / 3769) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_123088003_div_5443 : (3 : ZMod 123088003) ^ ((123088003 - 1) / 5443) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_123088003 : Nat.Prime 123088003 := by
  refine lucas_primality 123088003 (3 : ZMod 123088003) prime_123088003_pow ?_
  intro q hq hqd
  rw [prime_123088003_sub1] at hqd
  have : q ∣ [2, 3, 3769, 5443].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_123088003_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_123088003_div_3
  · have : q = 3769 := (Nat.prime_dvd_prime_iff_eq hq prime_3769).mp hdf
    subst this; exact prime_123088003_div_3769
  · have : q = 5443 := (Nat.prime_dvd_prime_iff_eq hq prime_5443).mp hdf
    subst this; exact prime_123088003_div_5443
private lemma prime_1018257813617801_sub1 : (1018257813617801 - 1 : ℕ) = 2 ^ 3 * 5 ^ 2 * 7 * 19 * 311 * 123088003 := by norm_num
private lemma prime_1018257813617801_pow : (3 : ZMod 1018257813617801) ^ (1018257813617801 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1018257813617801_div_2 : (3 : ZMod 1018257813617801) ^ ((1018257813617801 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1018257813617801_div_5 : (3 : ZMod 1018257813617801) ^ ((1018257813617801 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1018257813617801_div_7 : (3 : ZMod 1018257813617801) ^ ((1018257813617801 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1018257813617801_div_19 : (3 : ZMod 1018257813617801) ^ ((1018257813617801 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1018257813617801_div_311 : (3 : ZMod 1018257813617801) ^ ((1018257813617801 - 1) / 311) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1018257813617801_div_123088003 : (3 : ZMod 1018257813617801) ^ ((1018257813617801 - 1) / 123088003) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1018257813617801 : Nat.Prime 1018257813617801 := by
  refine lucas_primality 1018257813617801 (3 : ZMod 1018257813617801) prime_1018257813617801_pow ?_
  intro q hq hqd
  rw [prime_1018257813617801_sub1] at hqd
  have : q ∣ [2 ^ 3, 5 ^ 2, 7, 19, 311, 123088003].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1018257813617801_div_2
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_1018257813617801_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_1018257813617801_div_7
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_1018257813617801_div_19
  · have : q = 311 := (Nat.prime_dvd_prime_iff_eq hq prime_311).mp hdf
    subst this; exact prime_1018257813617801_div_311
  · have : q = 123088003 := (Nat.prime_dvd_prime_iff_eq hq prime_123088003).mp hdf
    subst this; exact prime_1018257813617801_div_123088003
private lemma prime_2803 : Nat.Prime 2803 := by norm_num
private lemma prime_91331 : Nat.Prime 91331 := by norm_num
private lemma prime_479 : Nat.Prime 479 := by norm_num
private lemma prime_31957 : Nat.Prime 31957 := by norm_num
private lemma prime_214303643_sub1 : (214303643 - 1 : ℕ) = 2 * 7 * 479 * 31957 := by norm_num
private lemma prime_214303643_pow : (2 : ZMod 214303643) ^ (214303643 - 1) = 1 := by
  reduce_mod_char
private lemma prime_214303643_div_2 : (2 : ZMod 214303643) ^ ((214303643 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_214303643_div_7 : (2 : ZMod 214303643) ^ ((214303643 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_214303643_div_479 : (2 : ZMod 214303643) ^ ((214303643 - 1) / 479) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_214303643_div_31957 : (2 : ZMod 214303643) ^ ((214303643 - 1) / 31957) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_214303643 : Nat.Prime 214303643 := by
  refine lucas_primality 214303643 (2 : ZMod 214303643) prime_214303643_pow ?_
  intro q hq hqd
  rw [prime_214303643_sub1] at hqd
  have : q ∣ [2, 7, 479, 31957].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_214303643_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_214303643_div_7
  · have : q = 479 := (Nat.prime_dvd_prime_iff_eq hq prime_479).mp hdf
    subst this; exact prime_214303643_div_479
  · have : q = 31957 := (Nat.prime_dvd_prime_iff_eq hq prime_31957).mp hdf
    subst this; exact prime_214303643_div_31957
private lemma prime_898857411392125321217_sub1 : (898857411392125321217 - 1 : ℕ) = 2 ^ 14 * 2803 * 91331 * 214303643 := by norm_num
private lemma prime_898857411392125321217_pow : (3 : ZMod 898857411392125321217) ^ (898857411392125321217 - 1) = 1 := by
  reduce_mod_char
private lemma prime_898857411392125321217_div_2 : (3 : ZMod 898857411392125321217) ^ ((898857411392125321217 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_898857411392125321217_div_2803 : (3 : ZMod 898857411392125321217) ^ ((898857411392125321217 - 1) / 2803) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_898857411392125321217_div_91331 : (3 : ZMod 898857411392125321217) ^ ((898857411392125321217 - 1) / 91331) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_898857411392125321217_div_214303643 : (3 : ZMod 898857411392125321217) ^ ((898857411392125321217 - 1) / 214303643) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_898857411392125321217 : Nat.Prime 898857411392125321217 := by
  refine lucas_primality 898857411392125321217 (3 : ZMod 898857411392125321217) prime_898857411392125321217_pow ?_
  intro q hq hqd
  rw [prime_898857411392125321217_sub1] at hqd
  have : q ∣ [2 ^ 14, 2803, 91331, 214303643].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_898857411392125321217_div_2
  · have : q = 2803 := (Nat.prime_dvd_prime_iff_eq hq prime_2803).mp hdf
    subst this; exact prime_898857411392125321217_div_2803
  · have : q = 91331 := (Nat.prime_dvd_prime_iff_eq hq prime_91331).mp hdf
    subst this; exact prime_898857411392125321217_div_91331
  · have : q = 214303643 := (Nat.prime_dvd_prime_iff_eq hq prime_214303643).mp hdf
    subst this; exact prime_898857411392125321217_div_214303643
private lemma prime_A_68_sub1 : (82089011515213367907186323881286692290763240872345599 - 1 : ℕ) = 2 * 11 * 59 * 576469 * 119863187 * 1018257813617801 * 898857411392125321217 := by norm_num
private lemma prime_A_68_pow : (11 : ZMod 82089011515213367907186323881286692290763240872345599) ^ (82089011515213367907186323881286692290763240872345599 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_68_div_2 : (11 : ZMod 82089011515213367907186323881286692290763240872345599) ^ ((82089011515213367907186323881286692290763240872345599 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_68_div_11 : (11 : ZMod 82089011515213367907186323881286692290763240872345599) ^ ((82089011515213367907186323881286692290763240872345599 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_68_div_59 : (11 : ZMod 82089011515213367907186323881286692290763240872345599) ^ ((82089011515213367907186323881286692290763240872345599 - 1) / 59) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_68_div_576469 : (11 : ZMod 82089011515213367907186323881286692290763240872345599) ^ ((82089011515213367907186323881286692290763240872345599 - 1) / 576469) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_68_div_119863187 : (11 : ZMod 82089011515213367907186323881286692290763240872345599) ^ ((82089011515213367907186323881286692290763240872345599 - 1) / 119863187) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_68_div_1018257813617801 : (11 : ZMod 82089011515213367907186323881286692290763240872345599) ^ ((82089011515213367907186323881286692290763240872345599 - 1) / 1018257813617801) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_68_div_898857411392125321217 : (11 : ZMod 82089011515213367907186323881286692290763240872345599) ^ ((82089011515213367907186323881286692290763240872345599 - 1) / 898857411392125321217) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_68 : Nat.Prime 82089011515213367907186323881286692290763240872345599 := by
  refine lucas_primality 82089011515213367907186323881286692290763240872345599 (11 : ZMod 82089011515213367907186323881286692290763240872345599) prime_A_68_pow ?_
  intro q hq hqd
  rw [prime_A_68_sub1] at hqd
  have : q ∣ [2, 11, 59, 576469, 119863187, 1018257813617801, 898857411392125321217].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_68_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_A_68_div_11
  · have : q = 59 := (Nat.prime_dvd_prime_iff_eq hq prime_59).mp hdf
    subst this; exact prime_A_68_div_59
  · have : q = 576469 := (Nat.prime_dvd_prime_iff_eq hq prime_576469).mp hdf
    subst this; exact prime_A_68_div_576469
  · have : q = 119863187 := (Nat.prime_dvd_prime_iff_eq hq prime_119863187).mp hdf
    subst this; exact prime_A_68_div_119863187
  · have : q = 1018257813617801 := (Nat.prime_dvd_prime_iff_eq hq prime_1018257813617801).mp hdf
    subst this; exact prime_A_68_div_1018257813617801
  · have : q = 898857411392125321217 := (Nat.prime_dvd_prime_iff_eq hq prime_898857411392125321217).mp hdf
    subst this; exact prime_A_68_div_898857411392125321217
private lemma prime_12697193 : Nat.Prime 12697193 := by norm_num
private lemma prime_149 : Nat.Prime 149 := by norm_num
private lemma prime_1166773 : Nat.Prime 1166773 := by norm_num
private lemma prime_8344760497_sub1 : (8344760497 - 1 : ℕ) = 2 ^ 4 * 3 * 149 * 1166773 := by norm_num
private lemma prime_8344760497_pow : (5 : ZMod 8344760497) ^ (8344760497 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8344760497_div_2 : (5 : ZMod 8344760497) ^ ((8344760497 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8344760497_div_3 : (5 : ZMod 8344760497) ^ ((8344760497 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8344760497_div_149 : (5 : ZMod 8344760497) ^ ((8344760497 - 1) / 149) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8344760497_div_1166773 : (5 : ZMod 8344760497) ^ ((8344760497 - 1) / 1166773) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8344760497 : Nat.Prime 8344760497 := by
  refine lucas_primality 8344760497 (5 : ZMod 8344760497) prime_8344760497_pow ?_
  intro q hq hqd
  rw [prime_8344760497_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 149, 1166773].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_8344760497_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_8344760497_div_3
  · have : q = 149 := (Nat.prime_dvd_prime_iff_eq hq prime_149).mp hdf
    subst this; exact prime_8344760497_div_149
  · have : q = 1166773 := (Nat.prime_dvd_prime_iff_eq hq prime_1166773).mp hdf
    subst this; exact prime_8344760497_div_1166773
private lemma prime_3203 : Nat.Prime 3203 := by norm_num
private lemma prime_16729 : Nat.Prime 16729 := by norm_num
private lemma prime_195127057_sub1 : (195127057 - 1 : ℕ) = 2 ^ 4 * 3 ^ 6 * 16729 := by norm_num
private lemma prime_195127057_pow : (7 : ZMod 195127057) ^ (195127057 - 1) = 1 := by
  reduce_mod_char
private lemma prime_195127057_div_2 : (7 : ZMod 195127057) ^ ((195127057 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_195127057_div_3 : (7 : ZMod 195127057) ^ ((195127057 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_195127057_div_16729 : (7 : ZMod 195127057) ^ ((195127057 - 1) / 16729) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_195127057 : Nat.Prime 195127057 := by
  refine lucas_primality 195127057 (7 : ZMod 195127057) prime_195127057_pow ?_
  intro q hq hqd
  rw [prime_195127057_sub1] at hqd
  have : q ∣ [2 ^ 4, 3 ^ 6, 16729].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_195127057_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_195127057_div_3
  · have : q = 16729 := (Nat.prime_dvd_prime_iff_eq hq prime_16729).mp hdf
    subst this; exact prime_195127057_div_16729
private lemma prime_4999935708569_sub1 : (4999935708569 - 1 : ℕ) = 2 ^ 3 * 3203 * 195127057 := by norm_num
private lemma prime_4999935708569_pow : (3 : ZMod 4999935708569) ^ (4999935708569 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4999935708569_div_2 : (3 : ZMod 4999935708569) ^ ((4999935708569 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4999935708569_div_3203 : (3 : ZMod 4999935708569) ^ ((4999935708569 - 1) / 3203) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4999935708569_div_195127057 : (3 : ZMod 4999935708569) ^ ((4999935708569 - 1) / 195127057) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4999935708569 : Nat.Prime 4999935708569 := by
  refine lucas_primality 4999935708569 (3 : ZMod 4999935708569) prime_4999935708569_pow ?_
  intro q hq hqd
  rw [prime_4999935708569_sub1] at hqd
  have : q ∣ [2 ^ 3, 3203, 195127057].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_4999935708569_div_2
  · have : q = 3203 := (Nat.prime_dvd_prime_iff_eq hq prime_3203).mp hdf
    subst this; exact prime_4999935708569_div_3203
  · have : q = 195127057 := (Nat.prime_dvd_prime_iff_eq hq prime_195127057).mp hdf
    subst this; exact prime_4999935708569_div_195127057
private lemma prime_B_68_sub1 : (82089011515213367907186323881286692290763240872345601 - 1 : ℕ) = 2 ^ 68 * 3 * 5 ^ 2 * 7 * 12697193 * 8344760497 * 4999935708569 := by norm_num
private lemma prime_B_68_pow : (23 : ZMod 82089011515213367907186323881286692290763240872345601) ^ (82089011515213367907186323881286692290763240872345601 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_68_div_2 : (23 : ZMod 82089011515213367907186323881286692290763240872345601) ^ ((82089011515213367907186323881286692290763240872345601 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_68_div_3 : (23 : ZMod 82089011515213367907186323881286692290763240872345601) ^ ((82089011515213367907186323881286692290763240872345601 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_68_div_5 : (23 : ZMod 82089011515213367907186323881286692290763240872345601) ^ ((82089011515213367907186323881286692290763240872345601 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_68_div_7 : (23 : ZMod 82089011515213367907186323881286692290763240872345601) ^ ((82089011515213367907186323881286692290763240872345601 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_68_div_12697193 : (23 : ZMod 82089011515213367907186323881286692290763240872345601) ^ ((82089011515213367907186323881286692290763240872345601 - 1) / 12697193) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_68_div_8344760497 : (23 : ZMod 82089011515213367907186323881286692290763240872345601) ^ ((82089011515213367907186323881286692290763240872345601 - 1) / 8344760497) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_68_div_4999935708569 : (23 : ZMod 82089011515213367907186323881286692290763240872345601) ^ ((82089011515213367907186323881286692290763240872345601 - 1) / 4999935708569) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_68 : Nat.Prime 82089011515213367907186323881286692290763240872345601 := by
  refine lucas_primality 82089011515213367907186323881286692290763240872345601 (23 : ZMod 82089011515213367907186323881286692290763240872345601) prime_B_68_pow ?_
  intro q hq hqd
  rw [prime_B_68_sub1] at hqd
  have : q ∣ [2 ^ 68, 3, 5 ^ 2, 7, 12697193, 8344760497, 4999935708569].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_68_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_68_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_B_68_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_B_68_div_7
  · have : q = 12697193 := (Nat.prime_dvd_prime_iff_eq hq prime_12697193).mp hdf
    subst this; exact prime_B_68_div_12697193
  · have : q = 8344760497 := (Nat.prime_dvd_prime_iff_eq hq prime_8344760497).mp hdf
    subst this; exact prime_B_68_div_8344760497
  · have : q = 4999935708569 := (Nat.prime_dvd_prime_iff_eq hq prime_4999935708569).mp hdf
    subst this; exact prime_B_68_div_4999935708569
private lemma pair_68 :
    Nat.Prime ((3 ^ 68 - 6036) * (2 ^ 68) - 1) ∧
    Nat.Prime ((3 ^ 68 - 6036) * (2 ^ 68) + 1) := by
  constructor
  · convert prime_A_68
  · convert prime_B_68

/- Pair for n = 69 -/
private lemma prime_1770983 : Nat.Prime 1770983 := by norm_num
private lemma prime_131 : Nat.Prime 131 := by norm_num
private lemma prime_34741027 : Nat.Prime 34741027 := by norm_num
private lemma prime_55958251 : Nat.Prime 55958251 := by norm_num
private lemma prime_877 : Nat.Prime 877 := by norm_num
private lemma prime_127 : Nat.Prime 127 := by norm_num
private lemma prime_509 : Nat.Prime 509 := by norm_num
private lemma prime_53 : Nat.Prime 53 := by norm_num
private lemma prime_113 : Nat.Prime 113 := by norm_num
private lemma prime_619 : Nat.Prime 619 := by norm_num
private lemma prime_751 : Nat.Prime 751 := by norm_num
private lemma prime_409084721_sub1 : (409084721 - 1 : ℕ) = 2 ^ 4 * 5 * 11 * 619 * 751 := by norm_num
private lemma prime_409084721_pow : (3 : ZMod 409084721) ^ (409084721 - 1) = 1 := by
  reduce_mod_char
private lemma prime_409084721_div_2 : (3 : ZMod 409084721) ^ ((409084721 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_409084721_div_5 : (3 : ZMod 409084721) ^ ((409084721 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_409084721_div_11 : (3 : ZMod 409084721) ^ ((409084721 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_409084721_div_619 : (3 : ZMod 409084721) ^ ((409084721 - 1) / 619) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_409084721_div_751 : (3 : ZMod 409084721) ^ ((409084721 - 1) / 751) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_409084721 : Nat.Prime 409084721 := by
  refine lucas_primality 409084721 (3 : ZMod 409084721) prime_409084721_pow ?_
  intro q hq hqd
  rw [prime_409084721_sub1] at hqd
  have : q ∣ [2 ^ 4, 5, 11, 619, 751].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_409084721_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_409084721_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_409084721_div_11
  · have : q = 619 := (Nat.prime_dvd_prime_iff_eq hq prime_619).mp hdf
    subst this; exact prime_409084721_div_619
  · have : q = 751 := (Nat.prime_dvd_prime_iff_eq hq prime_751).mp hdf
    subst this; exact prime_409084721_div_751
private lemma prime_196000671525521_sub1 : (196000671525521 - 1 : ℕ) = 2 ^ 4 * 5 * 53 * 113 * 409084721 := by norm_num
private lemma prime_196000671525521_pow : (3 : ZMod 196000671525521) ^ (196000671525521 - 1) = 1 := by
  reduce_mod_char
private lemma prime_196000671525521_div_2 : (3 : ZMod 196000671525521) ^ ((196000671525521 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_196000671525521_div_5 : (3 : ZMod 196000671525521) ^ ((196000671525521 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_196000671525521_div_53 : (3 : ZMod 196000671525521) ^ ((196000671525521 - 1) / 53) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_196000671525521_div_113 : (3 : ZMod 196000671525521) ^ ((196000671525521 - 1) / 113) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_196000671525521_div_409084721 : (3 : ZMod 196000671525521) ^ ((196000671525521 - 1) / 409084721) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_196000671525521 : Nat.Prime 196000671525521 := by
  refine lucas_primality 196000671525521 (3 : ZMod 196000671525521) prime_196000671525521_pow ?_
  intro q hq hqd
  rw [prime_196000671525521_sub1] at hqd
  have : q ∣ [2 ^ 4, 5, 53, 113, 409084721].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_196000671525521_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_196000671525521_div_5
  · have : q = 53 := (Nat.prime_dvd_prime_iff_eq hq prime_53).mp hdf
    subst this; exact prime_196000671525521_div_53
  · have : q = 113 := (Nat.prime_dvd_prime_iff_eq hq prime_113).mp hdf
    subst this; exact prime_196000671525521_div_113
  · have : q = 409084721 := (Nat.prime_dvd_prime_iff_eq hq prime_409084721).mp hdf
    subst this; exact prime_196000671525521_div_409084721
private lemma prime_1900510711413638100451_sub1 : (1900510711413638100451 - 1 : ℕ) = 2 * 3 * 5 ^ 2 * 127 * 509 * 196000671525521 := by norm_num
private lemma prime_1900510711413638100451_pow : (11 : ZMod 1900510711413638100451) ^ (1900510711413638100451 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1900510711413638100451_div_2 : (11 : ZMod 1900510711413638100451) ^ ((1900510711413638100451 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1900510711413638100451_div_3 : (11 : ZMod 1900510711413638100451) ^ ((1900510711413638100451 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1900510711413638100451_div_5 : (11 : ZMod 1900510711413638100451) ^ ((1900510711413638100451 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1900510711413638100451_div_127 : (11 : ZMod 1900510711413638100451) ^ ((1900510711413638100451 - 1) / 127) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1900510711413638100451_div_509 : (11 : ZMod 1900510711413638100451) ^ ((1900510711413638100451 - 1) / 509) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1900510711413638100451_div_196000671525521 : (11 : ZMod 1900510711413638100451) ^ ((1900510711413638100451 - 1) / 196000671525521) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1900510711413638100451 : Nat.Prime 1900510711413638100451 := by
  refine lucas_primality 1900510711413638100451 (11 : ZMod 1900510711413638100451) prime_1900510711413638100451_pow ?_
  intro q hq hqd
  rw [prime_1900510711413638100451_sub1] at hqd
  have : q ∣ [2, 3, 5 ^ 2, 127, 509, 196000671525521].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1900510711413638100451_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1900510711413638100451_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_1900510711413638100451_div_5
  · have : q = 127 := (Nat.prime_dvd_prime_iff_eq hq prime_127).mp hdf
    subst this; exact prime_1900510711413638100451_div_127
  · have : q = 509 := (Nat.prime_dvd_prime_iff_eq hq prime_509).mp hdf
    subst this; exact prime_1900510711413638100451_div_509
  · have : q = 196000671525521 := (Nat.prime_dvd_prime_iff_eq hq prime_196000671525521).mp hdf
    subst this; exact prime_1900510711413638100451_div_196000671525521
private lemma prime_780038014349767967396706637_sub1 : (780038014349767967396706637 - 1 : ℕ) = 2 ^ 2 * 3 ^ 2 * 13 * 877 * 1900510711413638100451 := by norm_num
private lemma prime_780038014349767967396706637_pow : (2 : ZMod 780038014349767967396706637) ^ (780038014349767967396706637 - 1) = 1 := by
  reduce_mod_char
private lemma prime_780038014349767967396706637_div_2 : (2 : ZMod 780038014349767967396706637) ^ ((780038014349767967396706637 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_780038014349767967396706637_div_3 : (2 : ZMod 780038014349767967396706637) ^ ((780038014349767967396706637 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_780038014349767967396706637_div_13 : (2 : ZMod 780038014349767967396706637) ^ ((780038014349767967396706637 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_780038014349767967396706637_div_877 : (2 : ZMod 780038014349767967396706637) ^ ((780038014349767967396706637 - 1) / 877) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_780038014349767967396706637_div_1900510711413638100451 : (2 : ZMod 780038014349767967396706637) ^ ((780038014349767967396706637 - 1) / 1900510711413638100451) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_780038014349767967396706637 : Nat.Prime 780038014349767967396706637 := by
  refine lucas_primality 780038014349767967396706637 (2 : ZMod 780038014349767967396706637) prime_780038014349767967396706637_pow ?_
  intro q hq hqd
  rw [prime_780038014349767967396706637_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 2, 13, 877, 1900510711413638100451].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_780038014349767967396706637_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_780038014349767967396706637_div_3
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_780038014349767967396706637_div_13
  · have : q = 877 := (Nat.prime_dvd_prime_iff_eq hq prime_877).mp hdf
    subst this; exact prime_780038014349767967396706637_div_877
  · have : q = 1900510711413638100451 := (Nat.prime_dvd_prime_iff_eq hq prime_1900510711413638100451).mp hdf
    subst this; exact prime_780038014349767967396706637_div_1900510711413638100451
private lemma prime_27811338058653313297932162154914871060210984661_sub1 : (27811338058653313297932162154914871060210984661 - 1 : ℕ) = 2 ^ 2 * 5 * 7 * 131 * 34741027 * 55958251 * 780038014349767967396706637 := by norm_num
private lemma prime_27811338058653313297932162154914871060210984661_pow : (3 : ZMod 27811338058653313297932162154914871060210984661) ^ (27811338058653313297932162154914871060210984661 - 1) = 1 := by
  reduce_mod_char
private lemma prime_27811338058653313297932162154914871060210984661_div_2 : (3 : ZMod 27811338058653313297932162154914871060210984661) ^ ((27811338058653313297932162154914871060210984661 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27811338058653313297932162154914871060210984661_div_5 : (3 : ZMod 27811338058653313297932162154914871060210984661) ^ ((27811338058653313297932162154914871060210984661 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27811338058653313297932162154914871060210984661_div_7 : (3 : ZMod 27811338058653313297932162154914871060210984661) ^ ((27811338058653313297932162154914871060210984661 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27811338058653313297932162154914871060210984661_div_131 : (3 : ZMod 27811338058653313297932162154914871060210984661) ^ ((27811338058653313297932162154914871060210984661 - 1) / 131) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27811338058653313297932162154914871060210984661_div_34741027 : (3 : ZMod 27811338058653313297932162154914871060210984661) ^ ((27811338058653313297932162154914871060210984661 - 1) / 34741027) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27811338058653313297932162154914871060210984661_div_55958251 : (3 : ZMod 27811338058653313297932162154914871060210984661) ^ ((27811338058653313297932162154914871060210984661 - 1) / 55958251) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27811338058653313297932162154914871060210984661_div_780038014349767967396706637 : (3 : ZMod 27811338058653313297932162154914871060210984661) ^ ((27811338058653313297932162154914871060210984661 - 1) / 780038014349767967396706637) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27811338058653313297932162154914871060210984661 : Nat.Prime 27811338058653313297932162154914871060210984661 := by
  refine lucas_primality 27811338058653313297932162154914871060210984661 (3 : ZMod 27811338058653313297932162154914871060210984661) prime_27811338058653313297932162154914871060210984661_pow ?_
  intro q hq hqd
  rw [prime_27811338058653313297932162154914871060210984661_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 7, 131, 34741027, 55958251, 780038014349767967396706637].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_27811338058653313297932162154914871060210984661_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_27811338058653313297932162154914871060210984661_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_27811338058653313297932162154914871060210984661_div_7
  · have : q = 131 := (Nat.prime_dvd_prime_iff_eq hq prime_131).mp hdf
    subst this; exact prime_27811338058653313297932162154914871060210984661_div_131
  · have : q = 34741027 := (Nat.prime_dvd_prime_iff_eq hq prime_34741027).mp hdf
    subst this; exact prime_27811338058653313297932162154914871060210984661_div_34741027
  · have : q = 55958251 := (Nat.prime_dvd_prime_iff_eq hq prime_55958251).mp hdf
    subst this; exact prime_27811338058653313297932162154914871060210984661_div_55958251
  · have : q = 780038014349767967396706637 := (Nat.prime_dvd_prime_iff_eq hq prime_780038014349767967396706637).mp hdf
    subst this; exact prime_27811338058653313297932162154914871060210984661_div_780038014349767967396706637
private lemma prime_A_69_sub1 : (492534069091280207443117943295976030948256302478917631 - 1 : ℕ) = 2 * 5 * 1770983 * 27811338058653313297932162154914871060210984661 := by norm_num
private lemma prime_A_69_pow : (31 : ZMod 492534069091280207443117943295976030948256302478917631) ^ (492534069091280207443117943295976030948256302478917631 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_69_div_2 : (31 : ZMod 492534069091280207443117943295976030948256302478917631) ^ ((492534069091280207443117943295976030948256302478917631 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_69_div_5 : (31 : ZMod 492534069091280207443117943295976030948256302478917631) ^ ((492534069091280207443117943295976030948256302478917631 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_69_div_1770983 : (31 : ZMod 492534069091280207443117943295976030948256302478917631) ^ ((492534069091280207443117943295976030948256302478917631 - 1) / 1770983) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_69_div_27811338058653313297932162154914871060210984661 : (31 : ZMod 492534069091280207443117943295976030948256302478917631) ^ ((492534069091280207443117943295976030948256302478917631 - 1) / 27811338058653313297932162154914871060210984661) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_69 : Nat.Prime 492534069091280207443117943295976030948256302478917631 := by
  refine lucas_primality 492534069091280207443117943295976030948256302478917631 (31 : ZMod 492534069091280207443117943295976030948256302478917631) prime_A_69_pow ?_
  intro q hq hqd
  rw [prime_A_69_sub1] at hqd
  have : q ∣ [2, 5, 1770983, 27811338058653313297932162154914871060210984661].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_69_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_69_div_5
  · have : q = 1770983 := (Nat.prime_dvd_prime_iff_eq hq prime_1770983).mp hdf
    subst this; exact prime_A_69_div_1770983
  · have : q = 27811338058653313297932162154914871060210984661 := (Nat.prime_dvd_prime_iff_eq hq prime_27811338058653313297932162154914871060210984661).mp hdf
    subst this; exact prime_A_69_div_27811338058653313297932162154914871060210984661
private lemma prime_3331 : Nat.Prime 3331 := by norm_num
private lemma prime_294347 : Nat.Prime 294347 := by norm_num
private lemma prime_83 : Nat.Prime 83 := by norm_num
private lemma prime_1277 : Nat.Prime 1277 := by norm_num
private lemma prime_10513 : Nat.Prime 10513 := by norm_num
private lemma prime_1321897 : Nat.Prime 1321897 := by norm_num
private lemma prime_12369984097833153299_sub1 : (12369984097833153299 - 1 : ℕ) = 2 * 13 * 17 * 19 * 83 * 1277 * 10513 * 1321897 := by norm_num
private lemma prime_12369984097833153299_pow : (2 : ZMod 12369984097833153299) ^ (12369984097833153299 - 1) = 1 := by
  reduce_mod_char
private lemma prime_12369984097833153299_div_2 : (2 : ZMod 12369984097833153299) ^ ((12369984097833153299 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12369984097833153299_div_13 : (2 : ZMod 12369984097833153299) ^ ((12369984097833153299 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12369984097833153299_div_17 : (2 : ZMod 12369984097833153299) ^ ((12369984097833153299 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12369984097833153299_div_19 : (2 : ZMod 12369984097833153299) ^ ((12369984097833153299 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12369984097833153299_div_83 : (2 : ZMod 12369984097833153299) ^ ((12369984097833153299 - 1) / 83) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12369984097833153299_div_1277 : (2 : ZMod 12369984097833153299) ^ ((12369984097833153299 - 1) / 1277) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12369984097833153299_div_10513 : (2 : ZMod 12369984097833153299) ^ ((12369984097833153299 - 1) / 10513) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12369984097833153299_div_1321897 : (2 : ZMod 12369984097833153299) ^ ((12369984097833153299 - 1) / 1321897) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12369984097833153299 : Nat.Prime 12369984097833153299 := by
  refine lucas_primality 12369984097833153299 (2 : ZMod 12369984097833153299) prime_12369984097833153299_pow ?_
  intro q hq hqd
  rw [prime_12369984097833153299_sub1] at hqd
  have : q ∣ [2, 13, 17, 19, 83, 1277, 10513, 1321897].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_12369984097833153299_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_12369984097833153299_div_13
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_12369984097833153299_div_17
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_12369984097833153299_div_19
  · have : q = 83 := (Nat.prime_dvd_prime_iff_eq hq prime_83).mp hdf
    subst this; exact prime_12369984097833153299_div_83
  · have : q = 1277 := (Nat.prime_dvd_prime_iff_eq hq prime_1277).mp hdf
    subst this; exact prime_12369984097833153299_div_1277
  · have : q = 10513 := (Nat.prime_dvd_prime_iff_eq hq prime_10513).mp hdf
    subst this; exact prime_12369984097833153299_div_10513
  · have : q = 1321897 := (Nat.prime_dvd_prime_iff_eq hq prime_1321897).mp hdf
    subst this; exact prime_12369984097833153299_div_1321897
private lemma prime_145540758473936949899155298917_sub1 : (145540758473936949899155298917 - 1 : ℕ) = 2 ^ 2 * 3 * 3331 * 294347 * 12369984097833153299 := by norm_num
private lemma prime_145540758473936949899155298917_pow : (5 : ZMod 145540758473936949899155298917) ^ (145540758473936949899155298917 - 1) = 1 := by
  reduce_mod_char
private lemma prime_145540758473936949899155298917_div_2 : (5 : ZMod 145540758473936949899155298917) ^ ((145540758473936949899155298917 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_145540758473936949899155298917_div_3 : (5 : ZMod 145540758473936949899155298917) ^ ((145540758473936949899155298917 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_145540758473936949899155298917_div_3331 : (5 : ZMod 145540758473936949899155298917) ^ ((145540758473936949899155298917 - 1) / 3331) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_145540758473936949899155298917_div_294347 : (5 : ZMod 145540758473936949899155298917) ^ ((145540758473936949899155298917 - 1) / 294347) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_145540758473936949899155298917_div_12369984097833153299 : (5 : ZMod 145540758473936949899155298917) ^ ((145540758473936949899155298917 - 1) / 12369984097833153299) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_145540758473936949899155298917 : Nat.Prime 145540758473936949899155298917 := by
  refine lucas_primality 145540758473936949899155298917 (5 : ZMod 145540758473936949899155298917) prime_145540758473936949899155298917_pow ?_
  intro q hq hqd
  rw [prime_145540758473936949899155298917_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 3331, 294347, 12369984097833153299].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_145540758473936949899155298917_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_145540758473936949899155298917_div_3
  · have : q = 3331 := (Nat.prime_dvd_prime_iff_eq hq prime_3331).mp hdf
    subst this; exact prime_145540758473936949899155298917_div_3331
  · have : q = 294347 := (Nat.prime_dvd_prime_iff_eq hq prime_294347).mp hdf
    subst this; exact prime_145540758473936949899155298917_div_294347
  · have : q = 12369984097833153299 := (Nat.prime_dvd_prime_iff_eq hq prime_12369984097833153299).mp hdf
    subst this; exact prime_145540758473936949899155298917_div_12369984097833153299
private lemma prime_B_69_sub1 : (492534069091280207443117943295976030948256302478917633 - 1 : ℕ) = 2 ^ 69 * 3 ^ 2 * 7 ^ 2 * 13 * 145540758473936949899155298917 := by norm_num
private lemma prime_B_69_pow : (10 : ZMod 492534069091280207443117943295976030948256302478917633) ^ (492534069091280207443117943295976030948256302478917633 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_69_div_2 : (10 : ZMod 492534069091280207443117943295976030948256302478917633) ^ ((492534069091280207443117943295976030948256302478917633 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_69_div_3 : (10 : ZMod 492534069091280207443117943295976030948256302478917633) ^ ((492534069091280207443117943295976030948256302478917633 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_69_div_7 : (10 : ZMod 492534069091280207443117943295976030948256302478917633) ^ ((492534069091280207443117943295976030948256302478917633 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_69_div_13 : (10 : ZMod 492534069091280207443117943295976030948256302478917633) ^ ((492534069091280207443117943295976030948256302478917633 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_69_div_145540758473936949899155298917 : (10 : ZMod 492534069091280207443117943295976030948256302478917633) ^ ((492534069091280207443117943295976030948256302478917633 - 1) / 145540758473936949899155298917) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_69 : Nat.Prime 492534069091280207443117943295976030948256302478917633 := by
  refine lucas_primality 492534069091280207443117943295976030948256302478917633 (10 : ZMod 492534069091280207443117943295976030948256302478917633) prime_B_69_pow ?_
  intro q hq hqd
  rw [prime_B_69_sub1] at hqd
  have : q ∣ [2 ^ 69, 3 ^ 2, 7 ^ 2, 13, 145540758473936949899155298917].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_69_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_69_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_B_69_div_7
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_B_69_div_13
  · have : q = 145540758473936949899155298917 := (Nat.prime_dvd_prime_iff_eq hq prime_145540758473936949899155298917).mp hdf
    subst this; exact prime_B_69_div_145540758473936949899155298917
private lemma pair_69 :
    Nat.Prime ((3 ^ 69 - 4122) * (2 ^ 69) - 1) ∧
    Nat.Prime ((3 ^ 69 - 4122) * (2 ^ 69) + 1) := by
  constructor
  · convert prime_A_69
  · convert prime_B_69

/- Pair for n = 70 -/
private lemma prime_1031 : Nat.Prime 1031 := by norm_num
private lemma prime_46747 : Nat.Prime 46747 := by norm_num
private lemma prime_94873 : Nat.Prime 94873 := by norm_num
private lemma prime_656384163389_sub1 : (656384163389 - 1 : ℕ) = 2 ^ 2 * 37 * 46747 * 94873 := by norm_num
private lemma prime_656384163389_pow : (2 : ZMod 656384163389) ^ (656384163389 - 1) = 1 := by
  reduce_mod_char
private lemma prime_656384163389_div_2 : (2 : ZMod 656384163389) ^ ((656384163389 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_656384163389_div_37 : (2 : ZMod 656384163389) ^ ((656384163389 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_656384163389_div_46747 : (2 : ZMod 656384163389) ^ ((656384163389 - 1) / 46747) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_656384163389_div_94873 : (2 : ZMod 656384163389) ^ ((656384163389 - 1) / 94873) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_656384163389 : Nat.Prime 656384163389 := by
  refine lucas_primality 656384163389 (2 : ZMod 656384163389) prime_656384163389_pow ?_
  intro q hq hqd
  rw [prime_656384163389_sub1] at hqd
  have : q ∣ [2 ^ 2, 37, 46747, 94873].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_656384163389_div_2
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_656384163389_div_37
  · have : q = 46747 := (Nat.prime_dvd_prime_iff_eq hq prime_46747).mp hdf
    subst this; exact prime_656384163389_div_46747
  · have : q = 94873 := (Nat.prime_dvd_prime_iff_eq hq prime_94873).mp hdf
    subst this; exact prime_656384163389_div_94873
private lemma prime_47 : Nat.Prime 47 := by norm_num
private lemma prime_89 : Nat.Prime 89 := by norm_num
private lemma prime_46337 : Nat.Prime 46337 := by norm_num
private lemma prime_387655343_sub1 : (387655343 - 1 : ℕ) = 2 * 47 * 89 * 46337 := by norm_num
private lemma prime_387655343_pow : (5 : ZMod 387655343) ^ (387655343 - 1) = 1 := by
  reduce_mod_char
private lemma prime_387655343_div_2 : (5 : ZMod 387655343) ^ ((387655343 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_387655343_div_47 : (5 : ZMod 387655343) ^ ((387655343 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_387655343_div_89 : (5 : ZMod 387655343) ^ ((387655343 - 1) / 89) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_387655343_div_46337 : (5 : ZMod 387655343) ^ ((387655343 - 1) / 46337) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_387655343 : Nat.Prime 387655343 := by
  refine lucas_primality 387655343 (5 : ZMod 387655343) prime_387655343_pow ?_
  intro q hq hqd
  rw [prime_387655343_sub1] at hqd
  have : q ∣ [2, 47, 89, 46337].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_387655343_div_2
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_387655343_div_47
  · have : q = 89 := (Nat.prime_dvd_prime_iff_eq hq prime_89).mp hdf
    subst this; exact prime_387655343_div_89
  · have : q = 46337 := (Nat.prime_dvd_prime_iff_eq hq prime_46337).mp hdf
    subst this; exact prime_387655343_div_46337
private lemma prime_137 : Nat.Prime 137 := by norm_num
private lemma prime_1981649 : Nat.Prime 1981649 := by norm_num
private lemma prime_3257830957_sub1 : (3257830957 - 1 : ℕ) = 2 ^ 2 * 3 * 137 * 1981649 := by norm_num
private lemma prime_3257830957_pow : (6 : ZMod 3257830957) ^ (3257830957 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3257830957_div_2 : (6 : ZMod 3257830957) ^ ((3257830957 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3257830957_div_3 : (6 : ZMod 3257830957) ^ ((3257830957 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3257830957_div_137 : (6 : ZMod 3257830957) ^ ((3257830957 - 1) / 137) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3257830957_div_1981649 : (6 : ZMod 3257830957) ^ ((3257830957 - 1) / 1981649) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3257830957 : Nat.Prime 3257830957 := by
  refine lucas_primality 3257830957 (6 : ZMod 3257830957) prime_3257830957_pow ?_
  intro q hq hqd
  rw [prime_3257830957_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 137, 1981649].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_3257830957_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_3257830957_div_3
  · have : q = 137 := (Nat.prime_dvd_prime_iff_eq hq prime_137).mp hdf
    subst this; exact prime_3257830957_div_137
  · have : q = 1981649 := (Nat.prime_dvd_prime_iff_eq hq prime_1981649).mp hdf
    subst this; exact prime_3257830957_div_1981649
private lemma prime_2525831154143706503_sub1 : (2525831154143706503 - 1 : ℕ) = 2 * 387655343 * 3257830957 := by norm_num
private lemma prime_2525831154143706503_pow : (5 : ZMod 2525831154143706503) ^ (2525831154143706503 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2525831154143706503_div_2 : (5 : ZMod 2525831154143706503) ^ ((2525831154143706503 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2525831154143706503_div_387655343 : (5 : ZMod 2525831154143706503) ^ ((2525831154143706503 - 1) / 387655343) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2525831154143706503_div_3257830957 : (5 : ZMod 2525831154143706503) ^ ((2525831154143706503 - 1) / 3257830957) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2525831154143706503 : Nat.Prime 2525831154143706503 := by
  refine lucas_primality 2525831154143706503 (5 : ZMod 2525831154143706503) prime_2525831154143706503_pow ?_
  intro q hq hqd
  rw [prime_2525831154143706503_sub1] at hqd
  have : q ∣ [2, 387655343, 3257830957].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2525831154143706503_div_2
  · have : q = 387655343 := (Nat.prime_dvd_prime_iff_eq hq prime_387655343).mp hdf
    subst this; exact prime_2525831154143706503_div_387655343
  · have : q = 3257830957 := (Nat.prime_dvd_prime_iff_eq hq prime_3257830957).mp hdf
    subst this; exact prime_2525831154143706503_div_3257830957
private lemma prime_6029689 : Nat.Prime 6029689 := by norm_num
private lemma prime_8731 : Nat.Prime 8731 := by norm_num
private lemma prime_66853 : Nat.Prime 66853 := by norm_num
private lemma prime_79382321849_sub1 : (79382321849 - 1 : ℕ) = 2 ^ 3 * 17 * 8731 * 66853 := by norm_num
private lemma prime_79382321849_pow : (3 : ZMod 79382321849) ^ (79382321849 - 1) = 1 := by
  reduce_mod_char
private lemma prime_79382321849_div_2 : (3 : ZMod 79382321849) ^ ((79382321849 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79382321849_div_17 : (3 : ZMod 79382321849) ^ ((79382321849 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79382321849_div_8731 : (3 : ZMod 79382321849) ^ ((79382321849 - 1) / 8731) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79382321849_div_66853 : (3 : ZMod 79382321849) ^ ((79382321849 - 1) / 66853) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79382321849 : Nat.Prime 79382321849 := by
  refine lucas_primality 79382321849 (3 : ZMod 79382321849) prime_79382321849_pow ?_
  intro q hq hqd
  rw [prime_79382321849_sub1] at hqd
  have : q ∣ [2 ^ 3, 17, 8731, 66853].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_79382321849_div_2
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_79382321849_div_17
  · have : q = 8731 := (Nat.prime_dvd_prime_iff_eq hq prime_8731).mp hdf
    subst this; exact prime_79382321849_div_8731
  · have : q = 66853 := (Nat.prime_dvd_prime_iff_eq hq prime_66853).mp hdf
    subst this; exact prime_79382321849_div_66853
private lemma prime_2871904277084249767_sub1 : (2871904277084249767 - 1 : ℕ) = 2 * 3 * 6029689 * 79382321849 := by norm_num
private lemma prime_2871904277084249767_pow : (5 : ZMod 2871904277084249767) ^ (2871904277084249767 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2871904277084249767_div_2 : (5 : ZMod 2871904277084249767) ^ ((2871904277084249767 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2871904277084249767_div_3 : (5 : ZMod 2871904277084249767) ^ ((2871904277084249767 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2871904277084249767_div_6029689 : (5 : ZMod 2871904277084249767) ^ ((2871904277084249767 - 1) / 6029689) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2871904277084249767_div_79382321849 : (5 : ZMod 2871904277084249767) ^ ((2871904277084249767 - 1) / 79382321849) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2871904277084249767 : Nat.Prime 2871904277084249767 := by
  refine lucas_primality 2871904277084249767 (5 : ZMod 2871904277084249767) prime_2871904277084249767_pow ?_
  intro q hq hqd
  rw [prime_2871904277084249767_sub1] at hqd
  have : q ∣ [2, 3, 6029689, 79382321849].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2871904277084249767_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_2871904277084249767_div_3
  · have : q = 6029689 := (Nat.prime_dvd_prime_iff_eq hq prime_6029689).mp hdf
    subst this; exact prime_2871904277084249767_div_6029689
  · have : q = 79382321849 := (Nat.prime_dvd_prime_iff_eq hq prime_79382321849).mp hdf
    subst this; exact prime_2871904277084249767_div_79382321849
private lemma prime_A_70_sub1 : (2955204414547681244658707659778774608175951255615569919 - 1 : ℕ) = 2 * 7 * 43 * 1031 * 656384163389 * 2525831154143706503 * 2871904277084249767 := by norm_num
private lemma prime_A_70_pow : (7 : ZMod 2955204414547681244658707659778774608175951255615569919) ^ (2955204414547681244658707659778774608175951255615569919 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_70_div_2 : (7 : ZMod 2955204414547681244658707659778774608175951255615569919) ^ ((2955204414547681244658707659778774608175951255615569919 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_70_div_7 : (7 : ZMod 2955204414547681244658707659778774608175951255615569919) ^ ((2955204414547681244658707659778774608175951255615569919 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_70_div_43 : (7 : ZMod 2955204414547681244658707659778774608175951255615569919) ^ ((2955204414547681244658707659778774608175951255615569919 - 1) / 43) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_70_div_1031 : (7 : ZMod 2955204414547681244658707659778774608175951255615569919) ^ ((2955204414547681244658707659778774608175951255615569919 - 1) / 1031) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_70_div_656384163389 : (7 : ZMod 2955204414547681244658707659778774608175951255615569919) ^ ((2955204414547681244658707659778774608175951255615569919 - 1) / 656384163389) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_70_div_2525831154143706503 : (7 : ZMod 2955204414547681244658707659778774608175951255615569919) ^ ((2955204414547681244658707659778774608175951255615569919 - 1) / 2525831154143706503) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_70_div_2871904277084249767 : (7 : ZMod 2955204414547681244658707659778774608175951255615569919) ^ ((2955204414547681244658707659778774608175951255615569919 - 1) / 2871904277084249767) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_70 : Nat.Prime 2955204414547681244658707659778774608175951255615569919 := by
  refine lucas_primality 2955204414547681244658707659778774608175951255615569919 (7 : ZMod 2955204414547681244658707659778774608175951255615569919) prime_A_70_pow ?_
  intro q hq hqd
  rw [prime_A_70_sub1] at hqd
  have : q ∣ [2, 7, 43, 1031, 656384163389, 2525831154143706503, 2871904277084249767].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_70_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_70_div_7
  · have : q = 43 := (Nat.prime_dvd_prime_iff_eq hq prime_43).mp hdf
    subst this; exact prime_A_70_div_43
  · have : q = 1031 := (Nat.prime_dvd_prime_iff_eq hq prime_1031).mp hdf
    subst this; exact prime_A_70_div_1031
  · have : q = 656384163389 := (Nat.prime_dvd_prime_iff_eq hq prime_656384163389).mp hdf
    subst this; exact prime_A_70_div_656384163389
  · have : q = 2525831154143706503 := (Nat.prime_dvd_prime_iff_eq hq prime_2525831154143706503).mp hdf
    subst this; exact prime_A_70_div_2525831154143706503
  · have : q = 2871904277084249767 := (Nat.prime_dvd_prime_iff_eq hq prime_2871904277084249767).mp hdf
    subst this; exact prime_A_70_div_2871904277084249767
private lemma prime_191 : Nat.Prime 191 := by norm_num
private lemma prime_38501 : Nat.Prime 38501 := by norm_num
private lemma prime_21967031 : Nat.Prime 21967031 := by norm_num
private lemma prime_107 : Nat.Prime 107 := by norm_num
private lemma prime_25561 : Nat.Prime 25561 := by norm_num
private lemma prime_34921391 : Nat.Prime 34921391 := by norm_num
private lemma prime_907956167_sub1 : (907956167 - 1 : ℕ) = 2 * 13 * 34921391 := by norm_num
private lemma prime_907956167_pow : (5 : ZMod 907956167) ^ (907956167 - 1) = 1 := by
  reduce_mod_char
private lemma prime_907956167_div_2 : (5 : ZMod 907956167) ^ ((907956167 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_907956167_div_13 : (5 : ZMod 907956167) ^ ((907956167 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_907956167_div_34921391 : (5 : ZMod 907956167) ^ ((907956167 - 1) / 34921391) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_907956167 : Nat.Prime 907956167 := by
  refine lucas_primality 907956167 (5 : ZMod 907956167) prime_907956167_pow ?_
  intro q hq hqd
  rw [prime_907956167_sub1] at hqd
  have : q ∣ [2, 13, 34921391].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_907956167_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_907956167_div_13
  · have : q = 34921391 := (Nat.prime_dvd_prime_iff_eq hq prime_34921391).mp hdf
    subst this; exact prime_907956167_div_34921391
private lemma prime_603414957201863_sub1 : (603414957201863 - 1 : ℕ) = 2 * 13 * 25561 * 907956167 := by norm_num
private lemma prime_603414957201863_pow : (5 : ZMod 603414957201863) ^ (603414957201863 - 1) = 1 := by
  reduce_mod_char
private lemma prime_603414957201863_div_2 : (5 : ZMod 603414957201863) ^ ((603414957201863 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_603414957201863_div_13 : (5 : ZMod 603414957201863) ^ ((603414957201863 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_603414957201863_div_25561 : (5 : ZMod 603414957201863) ^ ((603414957201863 - 1) / 25561) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_603414957201863_div_907956167 : (5 : ZMod 603414957201863) ^ ((603414957201863 - 1) / 907956167) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_603414957201863 : Nat.Prime 603414957201863 := by
  refine lucas_primality 603414957201863 (5 : ZMod 603414957201863) prime_603414957201863_pow ?_
  intro q hq hqd
  rw [prime_603414957201863_sub1] at hqd
  have : q ∣ [2, 13, 25561, 907956167].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_603414957201863_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_603414957201863_div_13
  · have : q = 25561 := (Nat.prime_dvd_prime_iff_eq hq prime_25561).mp hdf
    subst this; exact prime_603414957201863_div_25561
  · have : q = 907956167 := (Nat.prime_dvd_prime_iff_eq hq prime_907956167).mp hdf
    subst this; exact prime_603414957201863_div_907956167
private lemma prime_1033046406729589457_sub1 : (1033046406729589457 - 1 : ℕ) = 2 ^ 4 * 107 * 603414957201863 := by norm_num
private lemma prime_1033046406729589457_pow : (3 : ZMod 1033046406729589457) ^ (1033046406729589457 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1033046406729589457_div_2 : (3 : ZMod 1033046406729589457) ^ ((1033046406729589457 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1033046406729589457_div_107 : (3 : ZMod 1033046406729589457) ^ ((1033046406729589457 - 1) / 107) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1033046406729589457_div_603414957201863 : (3 : ZMod 1033046406729589457) ^ ((1033046406729589457 - 1) / 603414957201863) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1033046406729589457 : Nat.Prime 1033046406729589457 := by
  refine lucas_primality 1033046406729589457 (3 : ZMod 1033046406729589457) prime_1033046406729589457_pow ?_
  intro q hq hqd
  rw [prime_1033046406729589457_sub1] at hqd
  have : q ∣ [2 ^ 4, 107, 603414957201863].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1033046406729589457_div_2
  · have : q = 107 := (Nat.prime_dvd_prime_iff_eq hq prime_107).mp hdf
    subst this; exact prime_1033046406729589457_div_107
  · have : q = 603414957201863 := (Nat.prime_dvd_prime_iff_eq hq prime_603414957201863).mp hdf
    subst this; exact prime_1033046406729589457_div_603414957201863
private lemma prime_B_70_sub1 : (2955204414547681244658707659778774608175951255615569921 - 1 : ℕ) = 2 ^ 70 * 3 * 5 * 191 * 38501 * 21967031 * 1033046406729589457 := by norm_num
private lemma prime_B_70_pow : (11 : ZMod 2955204414547681244658707659778774608175951255615569921) ^ (2955204414547681244658707659778774608175951255615569921 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_70_div_2 : (11 : ZMod 2955204414547681244658707659778774608175951255615569921) ^ ((2955204414547681244658707659778774608175951255615569921 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_70_div_3 : (11 : ZMod 2955204414547681244658707659778774608175951255615569921) ^ ((2955204414547681244658707659778774608175951255615569921 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_70_div_5 : (11 : ZMod 2955204414547681244658707659778774608175951255615569921) ^ ((2955204414547681244658707659778774608175951255615569921 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_70_div_191 : (11 : ZMod 2955204414547681244658707659778774608175951255615569921) ^ ((2955204414547681244658707659778774608175951255615569921 - 1) / 191) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_70_div_38501 : (11 : ZMod 2955204414547681244658707659778774608175951255615569921) ^ ((2955204414547681244658707659778774608175951255615569921 - 1) / 38501) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_70_div_21967031 : (11 : ZMod 2955204414547681244658707659778774608175951255615569921) ^ ((2955204414547681244658707659778774608175951255615569921 - 1) / 21967031) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_70_div_1033046406729589457 : (11 : ZMod 2955204414547681244658707659778774608175951255615569921) ^ ((2955204414547681244658707659778774608175951255615569921 - 1) / 1033046406729589457) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_70 : Nat.Prime 2955204414547681244658707659778774608175951255615569921 := by
  refine lucas_primality 2955204414547681244658707659778774608175951255615569921 (11 : ZMod 2955204414547681244658707659778774608175951255615569921) prime_B_70_pow ?_
  intro q hq hqd
  rw [prime_B_70_sub1] at hqd
  have : q ∣ [2 ^ 70, 3, 5, 191, 38501, 21967031, 1033046406729589457].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_70_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_70_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_70_div_5
  · have : q = 191 := (Nat.prime_dvd_prime_iff_eq hq prime_191).mp hdf
    subst this; exact prime_B_70_div_191
  · have : q = 38501 := (Nat.prime_dvd_prime_iff_eq hq prime_38501).mp hdf
    subst this; exact prime_B_70_div_38501
  · have : q = 21967031 := (Nat.prime_dvd_prime_iff_eq hq prime_21967031).mp hdf
    subst this; exact prime_B_70_div_21967031
  · have : q = 1033046406729589457 := (Nat.prime_dvd_prime_iff_eq hq prime_1033046406729589457).mp hdf
    subst this; exact prime_B_70_div_1033046406729589457
private lemma pair_70 :
    Nat.Prime ((3 ^ 70 - 9894) * (2 ^ 70) - 1) ∧
    Nat.Prime ((3 ^ 70 - 9894) * (2 ^ 70) + 1) := by
  constructor
  · convert prime_A_70
  · convert prime_B_70
