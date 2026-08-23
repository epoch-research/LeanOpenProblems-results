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

/- Pair for n = 71 -/
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

/- Pair for n = 72 -/
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_859 : Nat.Prime 859 := by norm_num
private lemma prime_9323 : Nat.Prime 9323 := by norm_num
private lemma prime_47 : Nat.Prime 47 := by norm_num
private lemma prime_109 : Nat.Prime 109 := by norm_num
private lemma prime_571 : Nat.Prime 571 := by norm_num
private lemma prime_71 : Nat.Prime 71 := by norm_num
private lemma prime_1667 : Nat.Prime 1667 := by norm_num
private lemma prime_14705891 : Nat.Prime 14705891 := by norm_num
private lemma prime_10099 : Nat.Prime 10099 := by norm_num
private lemma prime_23036183 : Nat.Prime 23036183 := by norm_num
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

/- Pair for n = 73 -/
private lemma prime_113 : Nat.Prime 113 := by norm_num
private lemma prime_517499 : Nat.Prime 517499 := by norm_num
private lemma prime_999611 : Nat.Prime 999611 := by norm_num
private lemma prime_436283 : Nat.Prime 436283 := by norm_num
private lemma prime_141355693_sub1 : (141355693 - 1 : ℕ) = 2 ^ 2 * 3 ^ 4 * 436283 := by norm_num
private lemma prime_141355693_pow : (2 : ZMod 141355693) ^ (141355693 - 1) = 1 := by
  reduce_mod_char
private lemma prime_141355693_div_2 : (2 : ZMod 141355693) ^ ((141355693 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_141355693_div_3 : (2 : ZMod 141355693) ^ ((141355693 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_141355693_div_436283 : (2 : ZMod 141355693) ^ ((141355693 - 1) / 436283) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_141355693 : Nat.Prime 141355693 := by
  refine lucas_primality 141355693 (2 : ZMod 141355693) prime_141355693_pow ?_
  intro q hq hqd
  rw [prime_141355693_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 4, 436283].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_141355693_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_141355693_div_3
  · have : q = 436283 := (Nat.prime_dvd_prime_iff_eq hq prime_436283).mp hdf
    subst this; exact prime_141355693_div_436283
private lemma prime_5654227721_sub1 : (5654227721 - 1 : ℕ) = 2 ^ 3 * 5 * 141355693 := by norm_num
private lemma prime_5654227721_pow : (3 : ZMod 5654227721) ^ (5654227721 - 1) = 1 := by
  reduce_mod_char
private lemma prime_5654227721_div_2 : (3 : ZMod 5654227721) ^ ((5654227721 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5654227721_div_5 : (3 : ZMod 5654227721) ^ ((5654227721 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5654227721_div_141355693 : (3 : ZMod 5654227721) ^ ((5654227721 - 1) / 141355693) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5654227721 : Nat.Prime 5654227721 := by
  refine lucas_primality 5654227721 (3 : ZMod 5654227721) prime_5654227721_pow ?_
  intro q hq hqd
  rw [prime_5654227721_sub1] at hqd
  have : q ∣ [2 ^ 3, 5, 141355693].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_5654227721_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_5654227721_div_5
  · have : q = 141355693 := (Nat.prime_dvd_prime_iff_eq hq prime_141355693).mp hdf
    subst this; exact prime_5654227721_div_141355693
private lemma prime_28300007 : Nat.Prime 28300007 := by norm_num
private lemma prime_30360417309643_sub1 : (30360417309643 - 1 : ℕ) = 2 * 3 * 7 ^ 2 * 41 * 89 * 28300007 := by norm_num
private lemma prime_30360417309643_pow : (2 : ZMod 30360417309643) ^ (30360417309643 - 1) = 1 := by
  reduce_mod_char
private lemma prime_30360417309643_div_2 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643_div_3 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643_div_7 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643_div_41 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 41) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643_div_89 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 89) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643_div_28300007 : (2 : ZMod 30360417309643) ^ ((30360417309643 - 1) / 28300007) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_30360417309643 : Nat.Prime 30360417309643 := by
  refine lucas_primality 30360417309643 (2 : ZMod 30360417309643) prime_30360417309643_pow ?_
  intro q hq hqd
  rw [prime_30360417309643_sub1] at hqd
  have : q ∣ [2, 3, 7 ^ 2, 41, 89, 28300007].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_30360417309643_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_30360417309643_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_30360417309643_div_7
  · have : q = 41 := (Nat.prime_dvd_prime_iff_eq hq prime_41).mp hdf
    subst this; exact prime_30360417309643_div_41
  · have : q = 89 := (Nat.prime_dvd_prime_iff_eq hq prime_89).mp hdf
    subst this; exact prime_30360417309643_div_89
  · have : q = 28300007 := (Nat.prime_dvd_prime_iff_eq hq prime_28300007).mp hdf
    subst this; exact prime_30360417309643_div_28300007
private lemma prime_2677 : Nat.Prime 2677 := by norm_num
private lemma prime_12433 : Nat.Prime 12433 := by norm_num
private lemma prime_19990457 : Nat.Prime 19990457 := by norm_num
private lemma prime_31806161892299830349_sub1 : (31806161892299830349 - 1 : ℕ) = 2 ^ 2 * 17 * 19 * 37 * 2677 * 12433 * 19990457 := by norm_num
private lemma prime_31806161892299830349_pow : (2 : ZMod 31806161892299830349) ^ (31806161892299830349 - 1) = 1 := by
  reduce_mod_char
private lemma prime_31806161892299830349_div_2 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_17 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_19 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_37 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_2677 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 2677) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_12433 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 12433) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349_div_19990457 : (2 : ZMod 31806161892299830349) ^ ((31806161892299830349 - 1) / 19990457) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_31806161892299830349 : Nat.Prime 31806161892299830349 := by
  refine lucas_primality 31806161892299830349 (2 : ZMod 31806161892299830349) prime_31806161892299830349_pow ?_
  intro q hq hqd
  rw [prime_31806161892299830349_sub1] at hqd
  have : q ∣ [2 ^ 2, 17, 19, 37, 2677, 12433, 19990457].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_31806161892299830349_div_2
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_31806161892299830349_div_17
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_31806161892299830349_div_19
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_31806161892299830349_div_37
  · have : q = 2677 := (Nat.prime_dvd_prime_iff_eq hq prime_2677).mp hdf
    subst this; exact prime_31806161892299830349_div_2677
  · have : q = 12433 := (Nat.prime_dvd_prime_iff_eq hq prime_12433).mp hdf
    subst this; exact prime_31806161892299830349_div_12433
  · have : q = 19990457 := (Nat.prime_dvd_prime_iff_eq hq prime_19990457).mp hdf
    subst this; exact prime_31806161892299830349_div_19990457
private lemma prime_A_73_sub1 : (638324153542299148846280854514488143130545802757862850559 - 1 : ℕ) = 2 * 113 * 517499 * 999611 * 5654227721 * 30360417309643 * 31806161892299830349 := by norm_num
private lemma prime_A_73_pow : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ (638324153542299148846280854514488143130545802757862850559 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_73_div_2 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_113 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 113) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_517499 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 517499) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_999611 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 999611) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_5654227721 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 5654227721) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_30360417309643 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 30360417309643) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73_div_31806161892299830349 : (7 : ZMod 638324153542299148846280854514488143130545802757862850559) ^ ((638324153542299148846280854514488143130545802757862850559 - 1) / 31806161892299830349) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_73 : Nat.Prime 638324153542299148846280854514488143130545802757862850559 := by
  refine lucas_primality 638324153542299148846280854514488143130545802757862850559 (7 : ZMod 638324153542299148846280854514488143130545802757862850559) prime_A_73_pow ?_
  intro q hq hqd
  rw [prime_A_73_sub1] at hqd
  have : q ∣ [2, 113, 517499, 999611, 5654227721, 30360417309643, 31806161892299830349].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_73_div_2
  · have : q = 113 := (Nat.prime_dvd_prime_iff_eq hq prime_113).mp hdf
    subst this; exact prime_A_73_div_113
  · have : q = 517499 := (Nat.prime_dvd_prime_iff_eq hq prime_517499).mp hdf
    subst this; exact prime_A_73_div_517499
  · have : q = 999611 := (Nat.prime_dvd_prime_iff_eq hq prime_999611).mp hdf
    subst this; exact prime_A_73_div_999611
  · have : q = 5654227721 := (Nat.prime_dvd_prime_iff_eq hq prime_5654227721).mp hdf
    subst this; exact prime_A_73_div_5654227721
  · have : q = 30360417309643 := (Nat.prime_dvd_prime_iff_eq hq prime_30360417309643).mp hdf
    subst this; exact prime_A_73_div_30360417309643
  · have : q = 31806161892299830349 := (Nat.prime_dvd_prime_iff_eq hq prime_31806161892299830349).mp hdf
    subst this; exact prime_A_73_div_31806161892299830349
private lemma prime_10867 : Nat.Prime 10867 := by norm_num
private lemma prime_7547 : Nat.Prime 7547 := by norm_num
private lemma prime_4126417 : Nat.Prime 4126417 := by norm_num
private lemma prime_271 : Nat.Prime 271 := by norm_num
private lemma prime_4463 : Nat.Prime 4463 := by norm_num
private lemma prime_7001 : Nat.Prime 7001 := by norm_num
private lemma prime_59991288961_sub1 : (59991288961 - 1 : ℕ) = 2 ^ 7 * 3 * 5 * 4463 * 7001 := by norm_num
private lemma prime_59991288961_pow : (11 : ZMod 59991288961) ^ (59991288961 - 1) = 1 := by
  reduce_mod_char
private lemma prime_59991288961_div_2 : (11 : ZMod 59991288961) ^ ((59991288961 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_59991288961_div_3 : (11 : ZMod 59991288961) ^ ((59991288961 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_59991288961_div_5 : (11 : ZMod 59991288961) ^ ((59991288961 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_59991288961_div_4463 : (11 : ZMod 59991288961) ^ ((59991288961 - 1) / 4463) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_59991288961_div_7001 : (11 : ZMod 59991288961) ^ ((59991288961 - 1) / 7001) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_59991288961 : Nat.Prime 59991288961 := by
  refine lucas_primality 59991288961 (11 : ZMod 59991288961) prime_59991288961_pow ?_
  intro q hq hqd
  rw [prime_59991288961_sub1] at hqd
  have : q ∣ [2 ^ 7, 3, 5, 4463, 7001].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_59991288961_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_59991288961_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_59991288961_div_5
  · have : q = 4463 := (Nat.prime_dvd_prime_iff_eq hq prime_4463).mp hdf
    subst this; exact prime_59991288961_div_4463
  · have : q = 7001 := (Nat.prime_dvd_prime_iff_eq hq prime_7001).mp hdf
    subst this; exact prime_59991288961_div_7001
private lemma prime_13753962854932627_sub1 : (13753962854932627 - 1 : ℕ) = 2 * 3 ^ 2 * 47 * 271 * 59991288961 := by norm_num
private lemma prime_13753962854932627_pow : (3 : ZMod 13753962854932627) ^ (13753962854932627 - 1) = 1 := by
  reduce_mod_char
private lemma prime_13753962854932627_div_2 : (3 : ZMod 13753962854932627) ^ ((13753962854932627 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13753962854932627_div_3 : (3 : ZMod 13753962854932627) ^ ((13753962854932627 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13753962854932627_div_47 : (3 : ZMod 13753962854932627) ^ ((13753962854932627 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13753962854932627_div_271 : (3 : ZMod 13753962854932627) ^ ((13753962854932627 - 1) / 271) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13753962854932627_div_59991288961 : (3 : ZMod 13753962854932627) ^ ((13753962854932627 - 1) / 59991288961) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13753962854932627 : Nat.Prime 13753962854932627 := by
  refine lucas_primality 13753962854932627 (3 : ZMod 13753962854932627) prime_13753962854932627_pow ?_
  intro q hq hqd
  rw [prime_13753962854932627_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 47, 271, 59991288961].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_13753962854932627_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_13753962854932627_div_3
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_13753962854932627_div_47
  · have : q = 271 := (Nat.prime_dvd_prime_iff_eq hq prime_271).mp hdf
    subst this; exact prime_13753962854932627_div_271
  · have : q = 59991288961 := (Nat.prime_dvd_prime_iff_eq hq prime_59991288961).mp hdf
    subst this; exact prime_13753962854932627_div_59991288961
private lemma prime_18846381910989212053038095213_sub1 : (18846381910989212053038095213 - 1 : ℕ) = 2 ^ 2 * 11 * 7547 * 4126417 * 13753962854932627 := by norm_num
private lemma prime_18846381910989212053038095213_pow : (2 : ZMod 18846381910989212053038095213) ^ (18846381910989212053038095213 - 1) = 1 := by
  reduce_mod_char
private lemma prime_18846381910989212053038095213_div_2 : (2 : ZMod 18846381910989212053038095213) ^ ((18846381910989212053038095213 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18846381910989212053038095213_div_11 : (2 : ZMod 18846381910989212053038095213) ^ ((18846381910989212053038095213 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18846381910989212053038095213_div_7547 : (2 : ZMod 18846381910989212053038095213) ^ ((18846381910989212053038095213 - 1) / 7547) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18846381910989212053038095213_div_4126417 : (2 : ZMod 18846381910989212053038095213) ^ ((18846381910989212053038095213 - 1) / 4126417) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18846381910989212053038095213_div_13753962854932627 : (2 : ZMod 18846381910989212053038095213) ^ ((18846381910989212053038095213 - 1) / 13753962854932627) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18846381910989212053038095213 : Nat.Prime 18846381910989212053038095213 := by
  refine lucas_primality 18846381910989212053038095213 (2 : ZMod 18846381910989212053038095213) prime_18846381910989212053038095213_pow ?_
  intro q hq hqd
  rw [prime_18846381910989212053038095213_sub1] at hqd
  have : q ∣ [2 ^ 2, 11, 7547, 4126417, 13753962854932627].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_18846381910989212053038095213_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_18846381910989212053038095213_div_11
  · have : q = 7547 := (Nat.prime_dvd_prime_iff_eq hq prime_7547).mp hdf
    subst this; exact prime_18846381910989212053038095213_div_7547
  · have : q = 4126417 := (Nat.prime_dvd_prime_iff_eq hq prime_4126417).mp hdf
    subst this; exact prime_18846381910989212053038095213_div_4126417
  · have : q = 13753962854932627 := (Nat.prime_dvd_prime_iff_eq hq prime_13753962854932627).mp hdf
    subst this; exact prime_18846381910989212053038095213_div_13753962854932627
private lemma prime_B_73_sub1 : (638324153542299148846280854514488143130545802757862850561 - 1 : ℕ) = 2 ^ 74 * 3 * 5 * 11 * 10867 * 18846381910989212053038095213 := by norm_num
private lemma prime_B_73_pow : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ (638324153542299148846280854514488143130545802757862850561 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_73_div_2 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73_div_3 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73_div_5 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73_div_11 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73_div_10867 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 10867) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73_div_18846381910989212053038095213 : (19 : ZMod 638324153542299148846280854514488143130545802757862850561) ^ ((638324153542299148846280854514488143130545802757862850561 - 1) / 18846381910989212053038095213) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_73 : Nat.Prime 638324153542299148846280854514488143130545802757862850561 := by
  refine lucas_primality 638324153542299148846280854514488143130545802757862850561 (19 : ZMod 638324153542299148846280854514488143130545802757862850561) prime_B_73_pow ?_
  intro q hq hqd
  rw [prime_B_73_sub1] at hqd
  have : q ∣ [2 ^ 74, 3, 5, 11, 10867, 18846381910989212053038095213].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_73_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_73_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_73_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_73_div_11
  · have : q = 10867 := (Nat.prime_dvd_prime_iff_eq hq prime_10867).mp hdf
    subst this; exact prime_B_73_div_10867
  · have : q = 18846381910989212053038095213 := (Nat.prime_dvd_prime_iff_eq hq prime_18846381910989212053038095213).mp hdf
    subst this; exact prime_B_73_div_18846381910989212053038095213
private lemma pair_73 :
    Nat.Prime ((3 ^ 73 - 26493) * (2 ^ 73) - 1) ∧
    Nat.Prime ((3 ^ 73 - 26493) * (2 ^ 73) + 1) := by
  constructor
  · convert prime_A_73
  · convert prime_B_73

/- Pair for n = 74 -/
private lemma prime_73 : Nat.Prime 73 := by norm_num
private lemma prime_613 : Nat.Prime 613 := by norm_num
private lemma prime_1181 : Nat.Prime 1181 := by norm_num
private lemma prime_1856083 : Nat.Prime 1856083 := by norm_num
private lemma prime_4384068047_sub1 : (4384068047 - 1 : ℕ) = 2 * 1181 * 1856083 := by norm_num
private lemma prime_4384068047_pow : (5 : ZMod 4384068047) ^ (4384068047 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4384068047_div_2 : (5 : ZMod 4384068047) ^ ((4384068047 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4384068047_div_1181 : (5 : ZMod 4384068047) ^ ((4384068047 - 1) / 1181) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4384068047_div_1856083 : (5 : ZMod 4384068047) ^ ((4384068047 - 1) / 1856083) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4384068047 : Nat.Prime 4384068047 := by
  refine lucas_primality 4384068047 (5 : ZMod 4384068047) prime_4384068047_pow ?_
  intro q hq hqd
  rw [prime_4384068047_sub1] at hqd
  have : q ∣ [2, 1181, 1856083].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_4384068047_div_2
  · have : q = 1181 := (Nat.prime_dvd_prime_iff_eq hq prime_1181).mp hdf
    subst this; exact prime_4384068047_div_1181
  · have : q = 1856083 := (Nat.prime_dvd_prime_iff_eq hq prime_1856083).mp hdf
    subst this; exact prime_4384068047_div_1856083
private lemma prime_673 : Nat.Prime 673 := by norm_num
private lemma prime_1697 : Nat.Prime 1697 := by norm_num
private lemma prime_12203 : Nat.Prime 12203 := by norm_num
private lemma prime_27253 : Nat.Prime 27253 := by norm_num
private lemma prime_1334833 : Nat.Prime 1334833 := by norm_num
private lemma prime_25561 : Nat.Prime 25561 := by norm_num
private lemma prime_395224183_sub1 : (395224183 - 1 : ℕ) = 2 * 3 ^ 2 * 859 * 25561 := by norm_num
private lemma prime_395224183_pow : (3 : ZMod 395224183) ^ (395224183 - 1) = 1 := by
  reduce_mod_char
private lemma prime_395224183_div_2 : (3 : ZMod 395224183) ^ ((395224183 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_395224183_div_3 : (3 : ZMod 395224183) ^ ((395224183 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_395224183_div_859 : (3 : ZMod 395224183) ^ ((395224183 - 1) / 859) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_395224183_div_25561 : (3 : ZMod 395224183) ^ ((395224183 - 1) / 25561) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_395224183 : Nat.Prime 395224183 := by
  refine lucas_primality 395224183 (3 : ZMod 395224183) prime_395224183_pow ?_
  intro q hq hqd
  rw [prime_395224183_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 859, 25561].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_395224183_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_395224183_div_3
  · have : q = 859 := (Nat.prime_dvd_prime_iff_eq hq prime_859).mp hdf
    subst this; exact prime_395224183_div_859
  · have : q = 25561 := (Nat.prime_dvd_prime_iff_eq hq prime_25561).mp hdf
    subst this; exact prime_395224183_div_25561
private lemma prime_61 : Nat.Prime 61 := by norm_num
private lemma prime_1109 : Nat.Prime 1109 := by norm_num
private lemma prime_6834172577_sub1 : (6834172577 - 1 : ℕ) = 2 ^ 5 * 7 * 11 * 41 * 61 * 1109 := by norm_num
private lemma prime_6834172577_pow : (3 : ZMod 6834172577) ^ (6834172577 - 1) = 1 := by
  reduce_mod_char
private lemma prime_6834172577_div_2 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577_div_7 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577_div_11 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577_div_41 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 41) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577_div_61 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 61) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577_div_1109 : (3 : ZMod 6834172577) ^ ((6834172577 - 1) / 1109) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6834172577 : Nat.Prime 6834172577 := by
  refine lucas_primality 6834172577 (3 : ZMod 6834172577) prime_6834172577_pow ?_
  intro q hq hqd
  rw [prime_6834172577_sub1] at hqd
  have : q ∣ [2 ^ 5, 7, 11, 41, 61, 1109].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_6834172577_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_6834172577_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_6834172577_div_11
  · have : q = 41 := (Nat.prime_dvd_prime_iff_eq hq prime_41).mp hdf
    subst this; exact prime_6834172577_div_41
  · have : q = 61 := (Nat.prime_dvd_prime_iff_eq hq prime_61).mp hdf
    subst this; exact prime_6834172577_div_61
  · have : q = 1109 := (Nat.prime_dvd_prime_iff_eq hq prime_1109).mp hdf
    subst this; exact prime_6834172577_div_1109
private lemma prime_8216473729924211106919060089235839395623_sub1 : (8216473729924211106919060089235839395623 - 1 : ℕ) = 2 * 3 * 673 * 1697 * 12203 * 27253 * 1334833 * 395224183 * 6834172577 := by norm_num
private lemma prime_8216473729924211106919060089235839395623_pow : (7 : ZMod 8216473729924211106919060089235839395623) ^ (8216473729924211106919060089235839395623 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8216473729924211106919060089235839395623_div_2 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_3 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_673 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 673) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_1697 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 1697) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_12203 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 12203) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_27253 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 27253) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_1334833 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 1334833) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_395224183 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 395224183) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623_div_6834172577 : (7 : ZMod 8216473729924211106919060089235839395623) ^ ((8216473729924211106919060089235839395623 - 1) / 6834172577) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8216473729924211106919060089235839395623 : Nat.Prime 8216473729924211106919060089235839395623 := by
  refine lucas_primality 8216473729924211106919060089235839395623 (7 : ZMod 8216473729924211106919060089235839395623) prime_8216473729924211106919060089235839395623_pow ?_
  intro q hq hqd
  rw [prime_8216473729924211106919060089235839395623_sub1] at hqd
  have : q ∣ [2, 3, 673, 1697, 12203, 27253, 1334833, 395224183, 6834172577].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_3
  · have : q = 673 := (Nat.prime_dvd_prime_iff_eq hq prime_673).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_673
  · have : q = 1697 := (Nat.prime_dvd_prime_iff_eq hq prime_1697).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_1697
  · have : q = 12203 := (Nat.prime_dvd_prime_iff_eq hq prime_12203).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_12203
  · have : q = 27253 := (Nat.prime_dvd_prime_iff_eq hq prime_27253).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_27253
  · have : q = 1334833 := (Nat.prime_dvd_prime_iff_eq hq prime_1334833).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_1334833
  · have : q = 395224183 := (Nat.prime_dvd_prime_iff_eq hq prime_395224183).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_395224183
  · have : q = 6834172577 := (Nat.prime_dvd_prime_iff_eq hq prime_6834172577).mp hdf
    subst this; exact prime_8216473729924211106919060089235839395623_div_6834172577
private lemma prime_174088405511536131503531142140382058964518683881088578653_sub1 : (174088405511536131503531142140382058964518683881088578653 - 1 : ℕ) = 2 ^ 2 * 3 ^ 3 * 73 * 613 * 4384068047 * 8216473729924211106919060089235839395623 := by norm_num
private lemma prime_174088405511536131503531142140382058964518683881088578653_pow : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ (174088405511536131503531142140382058964518683881088578653 - 1) = 1 := by
  reduce_mod_char
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_2 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_3 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_73 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 73) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_613 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 613) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_4384068047 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 4384068047) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653_div_8216473729924211106919060089235839395623 : (5 : ZMod 174088405511536131503531142140382058964518683881088578653) ^ ((174088405511536131503531142140382058964518683881088578653 - 1) / 8216473729924211106919060089235839395623) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174088405511536131503531142140382058964518683881088578653 : Nat.Prime 174088405511536131503531142140382058964518683881088578653 := by
  refine lucas_primality 174088405511536131503531142140382058964518683881088578653 (5 : ZMod 174088405511536131503531142140382058964518683881088578653) prime_174088405511536131503531142140382058964518683881088578653_pow ?_
  intro q hq hqd
  rw [prime_174088405511536131503531142140382058964518683881088578653_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 3, 73, 613, 4384068047, 8216473729924211106919060089235839395623].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_3
  · have : q = 73 := (Nat.prime_dvd_prime_iff_eq hq prime_73).mp hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_73
  · have : q = 613 := (Nat.prime_dvd_prime_iff_eq hq prime_613).mp hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_613
  · have : q = 4384068047 := (Nat.prime_dvd_prime_iff_eq hq prime_4384068047).mp hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_4384068047
  · have : q = 8216473729924211106919060089235839395623 := (Nat.prime_dvd_prime_iff_eq hq prime_8216473729924211106919060089235839395623).mp hdf
    subst this; exact prime_174088405511536131503531142140382058964518683881088578653_div_8216473729924211106919060089235839395623
private lemma prime_A_74_sub1 : (3829944921253794893077685127088405297219411045383948730367 - 1 : ℕ) = 2 * 11 * 174088405511536131503531142140382058964518683881088578653 := by norm_num
private lemma prime_A_74_pow : (5 : ZMod 3829944921253794893077685127088405297219411045383948730367) ^ (3829944921253794893077685127088405297219411045383948730367 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_74_div_2 : (5 : ZMod 3829944921253794893077685127088405297219411045383948730367) ^ ((3829944921253794893077685127088405297219411045383948730367 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_74_div_11 : (5 : ZMod 3829944921253794893077685127088405297219411045383948730367) ^ ((3829944921253794893077685127088405297219411045383948730367 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_74_div_174088405511536131503531142140382058964518683881088578653 : (5 : ZMod 3829944921253794893077685127088405297219411045383948730367) ^ ((3829944921253794893077685127088405297219411045383948730367 - 1) / 174088405511536131503531142140382058964518683881088578653) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_74 : Nat.Prime 3829944921253794893077685127088405297219411045383948730367 := by
  refine lucas_primality 3829944921253794893077685127088405297219411045383948730367 (5 : ZMod 3829944921253794893077685127088405297219411045383948730367) prime_A_74_pow ?_
  intro q hq hqd
  rw [prime_A_74_sub1] at hqd
  have : q ∣ [2, 11, 174088405511536131503531142140382058964518683881088578653].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_74_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_A_74_div_11
  · have : q = 174088405511536131503531142140382058964518683881088578653 := (Nat.prime_dvd_prime_iff_eq hq prime_174088405511536131503531142140382058964518683881088578653).mp hdf
    subst this; exact prime_A_74_div_174088405511536131503531142140382058964518683881088578653
private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_107 : Nat.Prime 107 := by norm_num
private lemma prime_211 : Nat.Prime 211 := by norm_num
private lemma prime_431 : Nat.Prime 431 := by norm_num
private lemma prime_5557 : Nat.Prime 5557 := by norm_num
private lemma prime_15753371 : Nat.Prime 15753371 := by norm_num
private lemma prime_31 : Nat.Prime 31 := by norm_num
private lemma prime_157 : Nat.Prime 157 := by norm_num
private lemma prime_9103 : Nat.Prime 9103 := by norm_num
private lemma prime_797477419_sub1 : (797477419 - 1 : ℕ) = 2 * 3 ^ 2 * 31 * 157 * 9103 := by norm_num
private lemma prime_797477419_pow : (2 : ZMod 797477419) ^ (797477419 - 1) = 1 := by
  reduce_mod_char
private lemma prime_797477419_div_2 : (2 : ZMod 797477419) ^ ((797477419 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_797477419_div_3 : (2 : ZMod 797477419) ^ ((797477419 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_797477419_div_31 : (2 : ZMod 797477419) ^ ((797477419 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_797477419_div_157 : (2 : ZMod 797477419) ^ ((797477419 - 1) / 157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_797477419_div_9103 : (2 : ZMod 797477419) ^ ((797477419 - 1) / 9103) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_797477419 : Nat.Prime 797477419 := by
  refine lucas_primality 797477419 (2 : ZMod 797477419) prime_797477419_pow ?_
  intro q hq hqd
  rw [prime_797477419_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 31, 157, 9103].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_797477419_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_797477419_div_3
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_797477419_div_31
  · have : q = 157 := (Nat.prime_dvd_prime_iff_eq hq prime_157).mp hdf
    subst this; exact prime_797477419_div_157
  · have : q = 9103 := (Nat.prime_dvd_prime_iff_eq hq prime_9103).mp hdf
    subst this; exact prime_797477419_div_9103
private lemma prime_50729133577429_sub1 : (50729133577429 - 1 : ℕ) = 2 ^ 2 * 3 ^ 3 * 19 * 31 * 797477419 := by norm_num
private lemma prime_50729133577429_pow : (2 : ZMod 50729133577429) ^ (50729133577429 - 1) = 1 := by
  reduce_mod_char
private lemma prime_50729133577429_div_2 : (2 : ZMod 50729133577429) ^ ((50729133577429 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_50729133577429_div_3 : (2 : ZMod 50729133577429) ^ ((50729133577429 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_50729133577429_div_19 : (2 : ZMod 50729133577429) ^ ((50729133577429 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_50729133577429_div_31 : (2 : ZMod 50729133577429) ^ ((50729133577429 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_50729133577429_div_797477419 : (2 : ZMod 50729133577429) ^ ((50729133577429 - 1) / 797477419) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_50729133577429 : Nat.Prime 50729133577429 := by
  refine lucas_primality 50729133577429 (2 : ZMod 50729133577429) prime_50729133577429_pow ?_
  intro q hq hqd
  rw [prime_50729133577429_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 3, 19, 31, 797477419].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_50729133577429_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_50729133577429_div_3
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_50729133577429_div_19
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_50729133577429_div_31
  · have : q = 797477419 := (Nat.prime_dvd_prime_iff_eq hq prime_797477419).mp hdf
    subst this; exact prime_50729133577429_div_797477419
private lemma prime_B_74_sub1 : (3829944921253794893077685127088405297219411045383948730369 - 1 : ℕ) = 2 ^ 76 * 3 * 17 * 23 * 107 * 211 * 431 * 5557 * 15753371 * 50729133577429 := by norm_num
private lemma prime_B_74_pow : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ (3829944921253794893077685127088405297219411045383948730369 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_74_div_2 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_3 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_17 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_23 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_107 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 107) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_211 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 211) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_431 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 431) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_5557 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 5557) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_15753371 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 15753371) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74_div_50729133577429 : (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) ^ ((3829944921253794893077685127088405297219411045383948730369 - 1) / 50729133577429) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_74 : Nat.Prime 3829944921253794893077685127088405297219411045383948730369 := by
  refine lucas_primality 3829944921253794893077685127088405297219411045383948730369 (13 : ZMod 3829944921253794893077685127088405297219411045383948730369) prime_B_74_pow ?_
  intro q hq hqd
  rw [prime_B_74_sub1] at hqd
  have : q ∣ [2 ^ 76, 3, 17, 23, 107, 211, 431, 5557, 15753371, 50729133577429].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_74_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_74_div_3
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_B_74_div_17
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_B_74_div_23
  · have : q = 107 := (Nat.prime_dvd_prime_iff_eq hq prime_107).mp hdf
    subst this; exact prime_B_74_div_107
  · have : q = 211 := (Nat.prime_dvd_prime_iff_eq hq prime_211).mp hdf
    subst this; exact prime_B_74_div_211
  · have : q = 431 := (Nat.prime_dvd_prime_iff_eq hq prime_431).mp hdf
    subst this; exact prime_B_74_div_431
  · have : q = 5557 := (Nat.prime_dvd_prime_iff_eq hq prime_5557).mp hdf
    subst this; exact prime_B_74_div_5557
  · have : q = 15753371 := (Nat.prime_dvd_prime_iff_eq hq prime_15753371).mp hdf
    subst this; exact prime_B_74_div_15753371
  · have : q = 50729133577429 := (Nat.prime_dvd_prime_iff_eq hq prime_50729133577429).mp hdf
    subst this; exact prime_B_74_div_50729133577429
private lemma pair_74 :
    Nat.Prime ((3 ^ 74 - 1317) * (2 ^ 74) - 1) ∧
    Nat.Prime ((3 ^ 74 - 1317) * (2 ^ 74) + 1) := by
  constructor
  · convert prime_A_74
  · convert prime_B_74

/- Pair for n = 75 -/
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
