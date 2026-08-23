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
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_439 : Nat.Prime 439 := by norm_num
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_16696447 : Nat.Prime 16696447 := by norm_num
private lemma prime_1168751291_sub1 : (1168751291 - 1 : ℕ) = 2 * 5 * 7 * 16696447 := by norm_num
private lemma prime_1168751291_pow : (2 : ZMod 1168751291) ^ (1168751291 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1168751291_div_2 : (2 : ZMod 1168751291) ^ ((1168751291 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1168751291_div_5 : (2 : ZMod 1168751291) ^ ((1168751291 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1168751291_div_7 : (2 : ZMod 1168751291) ^ ((1168751291 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1168751291_div_16696447 : (2 : ZMod 1168751291) ^ ((1168751291 - 1) / 16696447) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1168751291 : Nat.Prime 1168751291 := by
  refine lucas_primality 1168751291 (2 : ZMod 1168751291) prime_1168751291_pow ?_
  intro q hq hqd
  rw [prime_1168751291_sub1] at hqd
  have : q ∣ [2, 5, 7, 16696447].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1168751291_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_1168751291_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_1168751291_div_7
  · have : q = 16696447 := (Nat.prime_dvd_prime_iff_eq hq prime_16696447).mp hdf
    subst this; exact prime_1168751291_div_16696447
private lemma prime_79475087789_sub1 : (79475087789 - 1 : ℕ) = 2 ^ 2 * 17 * 1168751291 := by norm_num
private lemma prime_79475087789_pow : (2 : ZMod 79475087789) ^ (79475087789 - 1) = 1 := by
  reduce_mod_char
private lemma prime_79475087789_div_2 : (2 : ZMod 79475087789) ^ ((79475087789 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79475087789_div_17 : (2 : ZMod 79475087789) ^ ((79475087789 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79475087789_div_1168751291 : (2 : ZMod 79475087789) ^ ((79475087789 - 1) / 1168751291) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79475087789 : Nat.Prime 79475087789 := by
  refine lucas_primality 79475087789 (2 : ZMod 79475087789) prime_79475087789_pow ?_
  intro q hq hqd
  rw [prime_79475087789_sub1] at hqd
  have : q ∣ [2 ^ 2, 17, 1168751291].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_79475087789_div_2
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_79475087789_div_17
  · have : q = 1168751291 := (Nat.prime_dvd_prime_iff_eq hq prime_1168751291).mp hdf
    subst this; exact prime_79475087789_div_1168751291
private lemma prime_1116466033259873_sub1 : (1116466033259873 - 1 : ℕ) = 2 ^ 5 * 439 * 79475087789 := by norm_num
private lemma prime_1116466033259873_pow : (3 : ZMod 1116466033259873) ^ (1116466033259873 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1116466033259873_div_2 : (3 : ZMod 1116466033259873) ^ ((1116466033259873 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1116466033259873_div_439 : (3 : ZMod 1116466033259873) ^ ((1116466033259873 - 1) / 439) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1116466033259873_div_79475087789 : (3 : ZMod 1116466033259873) ^ ((1116466033259873 - 1) / 79475087789) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1116466033259873 : Nat.Prime 1116466033259873 := by
  refine lucas_primality 1116466033259873 (3 : ZMod 1116466033259873) prime_1116466033259873_pow ?_
  intro q hq hqd
  rw [prime_1116466033259873_sub1] at hqd
  have : q ∣ [2 ^ 5, 439, 79475087789].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1116466033259873_div_2
  · have : q = 439 := (Nat.prime_dvd_prime_iff_eq hq prime_439).mp hdf
    subst this; exact prime_1116466033259873_div_439
  · have : q = 79475087789 := (Nat.prime_dvd_prime_iff_eq hq prime_79475087789).mp hdf
    subst this; exact prime_1116466033259873_div_79475087789
private lemma prime_100481942993388571_sub1 : (100481942993388571 - 1 : ℕ) = 2 * 3 ^ 2 * 5 * 1116466033259873 := by norm_num
private lemma prime_100481942993388571_pow : (2 : ZMod 100481942993388571) ^ (100481942993388571 - 1) = 1 := by
  reduce_mod_char
private lemma prime_100481942993388571_div_2 : (2 : ZMod 100481942993388571) ^ ((100481942993388571 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_100481942993388571_div_3 : (2 : ZMod 100481942993388571) ^ ((100481942993388571 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_100481942993388571_div_5 : (2 : ZMod 100481942993388571) ^ ((100481942993388571 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_100481942993388571_div_1116466033259873 : (2 : ZMod 100481942993388571) ^ ((100481942993388571 - 1) / 1116466033259873) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_100481942993388571 : Nat.Prime 100481942993388571 := by
  refine lucas_primality 100481942993388571 (2 : ZMod 100481942993388571) prime_100481942993388571_pow ?_
  intro q hq hqd
  rw [prime_100481942993388571_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 5, 1116466033259873].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_100481942993388571_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_100481942993388571_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_100481942993388571_div_5
  · have : q = 1116466033259873 := (Nat.prime_dvd_prime_iff_eq hq prime_1116466033259873).mp hdf
    subst this; exact prime_100481942993388571_div_1116466033259873
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_8807 : Nat.Prime 8807 := by norm_num
private lemma prime_7529 : Nat.Prime 7529 := by norm_num
private lemma prime_114479 : Nat.Prime 114479 := by norm_num
private lemma prime_205135149059_sub1 : (205135149059 - 1 : ℕ) = 2 * 7 * 17 * 7529 * 114479 := by norm_num
private lemma prime_205135149059_pow : (2 : ZMod 205135149059) ^ (205135149059 - 1) = 1 := by
  reduce_mod_char
private lemma prime_205135149059_div_2 : (2 : ZMod 205135149059) ^ ((205135149059 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_205135149059_div_7 : (2 : ZMod 205135149059) ^ ((205135149059 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_205135149059_div_17 : (2 : ZMod 205135149059) ^ ((205135149059 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_205135149059_div_7529 : (2 : ZMod 205135149059) ^ ((205135149059 - 1) / 7529) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_205135149059_div_114479 : (2 : ZMod 205135149059) ^ ((205135149059 - 1) / 114479) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_205135149059 : Nat.Prime 205135149059 := by
  refine lucas_primality 205135149059 (2 : ZMod 205135149059) prime_205135149059_pow ?_
  intro q hq hqd
  rw [prime_205135149059_sub1] at hqd
  have : q ∣ [2, 7, 17, 7529, 114479].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_205135149059_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_205135149059_div_7
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_205135149059_div_17
  · have : q = 7529 := (Nat.prime_dvd_prime_iff_eq hq prime_7529).mp hdf
    subst this; exact prime_205135149059_div_7529
  · have : q = 114479 := (Nat.prime_dvd_prime_iff_eq hq prime_114479).mp hdf
    subst this; exact prime_205135149059_div_114479
private lemma prime_89 : Nat.Prime 89 := by norm_num
private lemma prime_4877 : Nat.Prime 4877 := by norm_num
private lemma prime_6959 : Nat.Prime 6959 := by norm_num
private lemma prime_2558203 : Nat.Prime 2558203 := by norm_num
private lemma prime_107444527_sub1 : (107444527 - 1 : ℕ) = 2 * 3 * 7 * 2558203 := by norm_num
private lemma prime_107444527_pow : (3 : ZMod 107444527) ^ (107444527 - 1) = 1 := by
  reduce_mod_char
private lemma prime_107444527_div_2 : (3 : ZMod 107444527) ^ ((107444527 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_107444527_div_3 : (3 : ZMod 107444527) ^ ((107444527 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_107444527_div_7 : (3 : ZMod 107444527) ^ ((107444527 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_107444527_div_2558203 : (3 : ZMod 107444527) ^ ((107444527 - 1) / 2558203) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_107444527 : Nat.Prime 107444527 := by
  refine lucas_primality 107444527 (3 : ZMod 107444527) prime_107444527_pow ?_
  intro q hq hqd
  rw [prime_107444527_sub1] at hqd
  have : q ∣ [2, 3, 7, 2558203].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_107444527_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_107444527_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_107444527_div_7
  · have : q = 2558203 := (Nat.prime_dvd_prime_iff_eq hq prime_2558203).mp hdf
    subst this; exact prime_107444527_div_2558203
private lemma prime_649088467110243659_sub1 : (649088467110243659 - 1 : ℕ) = 2 * 89 * 4877 * 6959 * 107444527 := by norm_num
private lemma prime_649088467110243659_pow : (2 : ZMod 649088467110243659) ^ (649088467110243659 - 1) = 1 := by
  reduce_mod_char
private lemma prime_649088467110243659_div_2 : (2 : ZMod 649088467110243659) ^ ((649088467110243659 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_649088467110243659_div_89 : (2 : ZMod 649088467110243659) ^ ((649088467110243659 - 1) / 89) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_649088467110243659_div_4877 : (2 : ZMod 649088467110243659) ^ ((649088467110243659 - 1) / 4877) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_649088467110243659_div_6959 : (2 : ZMod 649088467110243659) ^ ((649088467110243659 - 1) / 6959) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_649088467110243659_div_107444527 : (2 : ZMod 649088467110243659) ^ ((649088467110243659 - 1) / 107444527) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_649088467110243659 : Nat.Prime 649088467110243659 := by
  refine lucas_primality 649088467110243659 (2 : ZMod 649088467110243659) prime_649088467110243659_pow ?_
  intro q hq hqd
  rw [prime_649088467110243659_sub1] at hqd
  have : q ∣ [2, 89, 4877, 6959, 107444527].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_649088467110243659_div_2
  · have : q = 89 := (Nat.prime_dvd_prime_iff_eq hq prime_89).mp hdf
    subst this; exact prime_649088467110243659_div_89
  · have : q = 4877 := (Nat.prime_dvd_prime_iff_eq hq prime_4877).mp hdf
    subst this; exact prime_649088467110243659_div_4877
  · have : q = 6959 := (Nat.prime_dvd_prime_iff_eq hq prime_6959).mp hdf
    subst this; exact prime_649088467110243659_div_6959
  · have : q = 107444527 := (Nat.prime_dvd_prime_iff_eq hq prime_107444527).mp hdf
    subst this; exact prime_649088467110243659_div_107444527
private lemma prime_7989051567188259118486474012861_sub1 : (7989051567188259118486474012861 - 1 : ℕ) = 2 ^ 2 * 3 * 5 * 205135149059 * 649088467110243659 := by norm_num
private lemma prime_7989051567188259118486474012861_pow : (2 : ZMod 7989051567188259118486474012861) ^ (7989051567188259118486474012861 - 1) = 1 := by
  reduce_mod_char
private lemma prime_7989051567188259118486474012861_div_2 : (2 : ZMod 7989051567188259118486474012861) ^ ((7989051567188259118486474012861 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7989051567188259118486474012861_div_3 : (2 : ZMod 7989051567188259118486474012861) ^ ((7989051567188259118486474012861 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7989051567188259118486474012861_div_5 : (2 : ZMod 7989051567188259118486474012861) ^ ((7989051567188259118486474012861 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7989051567188259118486474012861_div_205135149059 : (2 : ZMod 7989051567188259118486474012861) ^ ((7989051567188259118486474012861 - 1) / 205135149059) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7989051567188259118486474012861_div_649088467110243659 : (2 : ZMod 7989051567188259118486474012861) ^ ((7989051567188259118486474012861 - 1) / 649088467110243659) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7989051567188259118486474012861 : Nat.Prime 7989051567188259118486474012861 := by
  refine lucas_primality 7989051567188259118486474012861 (2 : ZMod 7989051567188259118486474012861) prime_7989051567188259118486474012861_pow ?_
  intro q hq hqd
  rw [prime_7989051567188259118486474012861_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 5, 205135149059, 649088467110243659].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_7989051567188259118486474012861_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_7989051567188259118486474012861_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_7989051567188259118486474012861_div_5
  · have : q = 205135149059 := (Nat.prime_dvd_prime_iff_eq hq prime_205135149059).mp hdf
    subst this; exact prime_7989051567188259118486474012861_div_205135149059
  · have : q = 649088467110243659 := (Nat.prime_dvd_prime_iff_eq hq prime_649088467110243659).mp hdf
    subst this; exact prime_7989051567188259118486474012861_div_649088467110243659
private lemma prime_8020991795353877778442182935964418279_sub1 : (8020991795353877778442182935964418279 - 1 : ℕ) = 2 * 3 * 19 * 8807 * 7989051567188259118486474012861 := by norm_num
private lemma prime_8020991795353877778442182935964418279_pow : (3 : ZMod 8020991795353877778442182935964418279) ^ (8020991795353877778442182935964418279 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8020991795353877778442182935964418279_div_2 : (3 : ZMod 8020991795353877778442182935964418279) ^ ((8020991795353877778442182935964418279 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8020991795353877778442182935964418279_div_3 : (3 : ZMod 8020991795353877778442182935964418279) ^ ((8020991795353877778442182935964418279 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8020991795353877778442182935964418279_div_19 : (3 : ZMod 8020991795353877778442182935964418279) ^ ((8020991795353877778442182935964418279 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8020991795353877778442182935964418279_div_8807 : (3 : ZMod 8020991795353877778442182935964418279) ^ ((8020991795353877778442182935964418279 - 1) / 8807) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8020991795353877778442182935964418279_div_7989051567188259118486474012861 : (3 : ZMod 8020991795353877778442182935964418279) ^ ((8020991795353877778442182935964418279 - 1) / 7989051567188259118486474012861) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8020991795353877778442182935964418279 : Nat.Prime 8020991795353877778442182935964418279 := by
  refine lucas_primality 8020991795353877778442182935964418279 (3 : ZMod 8020991795353877778442182935964418279) prime_8020991795353877778442182935964418279_pow ?_
  intro q hq hqd
  rw [prime_8020991795353877778442182935964418279_sub1] at hqd
  have : q ∣ [2, 3, 19, 8807, 7989051567188259118486474012861].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_8020991795353877778442182935964418279_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_8020991795353877778442182935964418279_div_3
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_8020991795353877778442182935964418279_div_19
  · have : q = 8807 := (Nat.prime_dvd_prime_iff_eq hq prime_8807).mp hdf
    subst this; exact prime_8020991795353877778442182935964418279_div_8807
  · have : q = 7989051567188259118486474012861 := (Nat.prime_dvd_prime_iff_eq hq prime_7989051567188259118486474012861).mp hdf
    subst this; exact prime_8020991795353877778442182935964418279_div_7989051567188259118486474012861
private lemma prime_A_71_sub1 : (17731226487286087467952245958726624297954907578485964799 - 1 : ℕ) = 2 * 11 * 100481942993388571 * 8020991795353877778442182935964418279 := by norm_num
private lemma prime_A_71_pow : (11 : ZMod 17731226487286087467952245958726624297954907578485964799) ^ (17731226487286087467952245958726624297954907578485964799 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_71_div_2 : (11 : ZMod 17731226487286087467952245958726624297954907578485964799) ^ ((17731226487286087467952245958726624297954907578485964799 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_71_div_11 : (11 : ZMod 17731226487286087467952245958726624297954907578485964799) ^ ((17731226487286087467952245958726624297954907578485964799 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_71_div_100481942993388571 : (11 : ZMod 17731226487286087467952245958726624297954907578485964799) ^ ((17731226487286087467952245958726624297954907578485964799 - 1) / 100481942993388571) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_71_div_8020991795353877778442182935964418279 : (11 : ZMod 17731226487286087467952245958726624297954907578485964799) ^ ((17731226487286087467952245958726624297954907578485964799 - 1) / 8020991795353877778442182935964418279) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_71 : Nat.Prime 17731226487286087467952245958726624297954907578485964799 := by
  refine lucas_primality 17731226487286087467952245958726624297954907578485964799 (11 : ZMod 17731226487286087467952245958726624297954907578485964799) prime_A_71_pow ?_
  intro q hq hqd
  rw [prime_A_71_sub1] at hqd
  have : q ∣ [2, 11, 100481942993388571, 8020991795353877778442182935964418279].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_71_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_A_71_div_11
  · have : q = 100481942993388571 := (Nat.prime_dvd_prime_iff_eq hq prime_100481942993388571).mp hdf
    subst this; exact prime_A_71_div_100481942993388571
  · have : q = 8020991795353877778442182935964418279 := (Nat.prime_dvd_prime_iff_eq hq prime_8020991795353877778442182935964418279).mp hdf
    subst this; exact prime_A_71_div_8020991795353877778442182935964418279
private lemma prime_97 : Nat.Prime 97 := by norm_num
private lemma prime_205433 : Nat.Prime 205433 := by norm_num
private lemma prime_181 : Nat.Prime 181 := by norm_num
private lemma prime_1367 : Nat.Prime 1367 := by norm_num
private lemma prime_4409 : Nat.Prime 4409 := by norm_num
private lemma prime_4363622573_sub1 : (4363622573 - 1 : ℕ) = 2 ^ 2 * 181 * 1367 * 4409 := by norm_num
private lemma prime_4363622573_pow : (2 : ZMod 4363622573) ^ (4363622573 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4363622573_div_2 : (2 : ZMod 4363622573) ^ ((4363622573 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4363622573_div_181 : (2 : ZMod 4363622573) ^ ((4363622573 - 1) / 181) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4363622573_div_1367 : (2 : ZMod 4363622573) ^ ((4363622573 - 1) / 1367) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4363622573_div_4409 : (2 : ZMod 4363622573) ^ ((4363622573 - 1) / 4409) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4363622573 : Nat.Prime 4363622573 := by
  refine lucas_primality 4363622573 (2 : ZMod 4363622573) prime_4363622573_pow ?_
  intro q hq hqd
  rw [prime_4363622573_sub1] at hqd
  have : q ∣ [2 ^ 2, 181, 1367, 4409].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_4363622573_div_2
  · have : q = 181 := (Nat.prime_dvd_prime_iff_eq hq prime_181).mp hdf
    subst this; exact prime_4363622573_div_181
  · have : q = 1367 := (Nat.prime_dvd_prime_iff_eq hq prime_1367).mp hdf
    subst this; exact prime_4363622573_div_1367
  · have : q = 4409 := (Nat.prime_dvd_prime_iff_eq hq prime_4409).mp hdf
    subst this; exact prime_4363622573_div_4409
private lemma prime_83 : Nat.Prime 83 := by norm_num
private lemma prime_233 : Nat.Prime 233 := by norm_num
private lemma prime_277 : Nat.Prime 277 := by norm_num
private lemma prime_248789 : Nat.Prime 248789 := by norm_num
private lemma prime_383828699654497_sub1 : (383828699654497 - 1 : ℕ) = 2 ^ 5 * 3 ^ 2 * 83 * 233 * 277 * 248789 := by norm_num
private lemma prime_383828699654497_pow : (5 : ZMod 383828699654497) ^ (383828699654497 - 1) = 1 := by
  reduce_mod_char
private lemma prime_383828699654497_div_2 : (5 : ZMod 383828699654497) ^ ((383828699654497 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_383828699654497_div_3 : (5 : ZMod 383828699654497) ^ ((383828699654497 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_383828699654497_div_83 : (5 : ZMod 383828699654497) ^ ((383828699654497 - 1) / 83) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_383828699654497_div_233 : (5 : ZMod 383828699654497) ^ ((383828699654497 - 1) / 233) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_383828699654497_div_277 : (5 : ZMod 383828699654497) ^ ((383828699654497 - 1) / 277) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_383828699654497_div_248789 : (5 : ZMod 383828699654497) ^ ((383828699654497 - 1) / 248789) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_383828699654497 : Nat.Prime 383828699654497 := by
  refine lucas_primality 383828699654497 (5 : ZMod 383828699654497) prime_383828699654497_pow ?_
  intro q hq hqd
  rw [prime_383828699654497_sub1] at hqd
  have : q ∣ [2 ^ 5, 3 ^ 2, 83, 233, 277, 248789].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_383828699654497_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_383828699654497_div_3
  · have : q = 83 := (Nat.prime_dvd_prime_iff_eq hq prime_83).mp hdf
    subst this; exact prime_383828699654497_div_83
  · have : q = 233 := (Nat.prime_dvd_prime_iff_eq hq prime_233).mp hdf
    subst this; exact prime_383828699654497_div_233
  · have : q = 277 := (Nat.prime_dvd_prime_iff_eq hq prime_277).mp hdf
    subst this; exact prime_383828699654497_div_277
  · have : q = 248789 := (Nat.prime_dvd_prime_iff_eq hq prime_248789).mp hdf
    subst this; exact prime_383828699654497_div_248789
private lemma prime_B_71_sub1 : (17731226487286087467952245958726624297954907578485964801 - 1 : ℕ) = 2 ^ 71 * 3 ^ 2 * 5 ^ 2 * 97 * 205433 * 4363622573 * 383828699654497 := by norm_num
private lemma prime_B_71_pow : (14 : ZMod 17731226487286087467952245958726624297954907578485964801) ^ (17731226487286087467952245958726624297954907578485964801 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_71_div_2 : (14 : ZMod 17731226487286087467952245958726624297954907578485964801) ^ ((17731226487286087467952245958726624297954907578485964801 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_71_div_3 : (14 : ZMod 17731226487286087467952245958726624297954907578485964801) ^ ((17731226487286087467952245958726624297954907578485964801 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_71_div_5 : (14 : ZMod 17731226487286087467952245958726624297954907578485964801) ^ ((17731226487286087467952245958726624297954907578485964801 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_71_div_97 : (14 : ZMod 17731226487286087467952245958726624297954907578485964801) ^ ((17731226487286087467952245958726624297954907578485964801 - 1) / 97) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_71_div_205433 : (14 : ZMod 17731226487286087467952245958726624297954907578485964801) ^ ((17731226487286087467952245958726624297954907578485964801 - 1) / 205433) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_71_div_4363622573 : (14 : ZMod 17731226487286087467952245958726624297954907578485964801) ^ ((17731226487286087467952245958726624297954907578485964801 - 1) / 4363622573) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_71_div_383828699654497 : (14 : ZMod 17731226487286087467952245958726624297954907578485964801) ^ ((17731226487286087467952245958726624297954907578485964801 - 1) / 383828699654497) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_71 : Nat.Prime 17731226487286087467952245958726624297954907578485964801 := by
  refine lucas_primality 17731226487286087467952245958726624297954907578485964801 (14 : ZMod 17731226487286087467952245958726624297954907578485964801) prime_B_71_pow ?_
  intro q hq hqd
  rw [prime_B_71_sub1] at hqd
  have : q ∣ [2 ^ 71, 3 ^ 2, 5 ^ 2, 97, 205433, 4363622573, 383828699654497].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_71_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_71_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_B_71_div_5
  · have : q = 97 := (Nat.prime_dvd_prime_iff_eq hq prime_97).mp hdf
    subst this; exact prime_B_71_div_97
  · have : q = 205433 := (Nat.prime_dvd_prime_iff_eq hq prime_205433).mp hdf
    subst this; exact prime_B_71_div_205433
  · have : q = 4363622573 := (Nat.prime_dvd_prime_iff_eq hq prime_4363622573).mp hdf
    subst this; exact prime_B_71_div_4363622573
  · have : q = 383828699654497 := (Nat.prime_dvd_prime_iff_eq hq prime_383828699654497).mp hdf
    subst this; exact prime_B_71_div_383828699654497
private lemma pair_71 :
    Nat.Prime ((3 ^ 71 - 6822) * (2 ^ 71) - 1) ∧
    Nat.Prime ((3 ^ 71 - 6822) * (2 ^ 71) + 1) := by
  constructor
  · convert prime_A_71
  · convert prime_B_71
