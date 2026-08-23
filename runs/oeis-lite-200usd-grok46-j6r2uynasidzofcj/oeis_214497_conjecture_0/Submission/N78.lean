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
private lemma prime_853 : Nat.Prime 853 := by norm_num
private lemma prime_1367 : Nat.Prime 1367 := by norm_num
private lemma prime_5119 : Nat.Prime 5119 := by norm_num
private lemma prime_174157 : Nat.Prime 174157 := by norm_num
private lemma prime_3566038733_sub1 : (3566038733 - 1 : ℕ) = 2 ^ 2 * 5119 * 174157 := by norm_num
private lemma prime_3566038733_pow : (2 : ZMod 3566038733) ^ (3566038733 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3566038733_div_2 : (2 : ZMod 3566038733) ^ ((3566038733 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3566038733_div_5119 : (2 : ZMod 3566038733) ^ ((3566038733 - 1) / 5119) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3566038733_div_174157 : (2 : ZMod 3566038733) ^ ((3566038733 - 1) / 174157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3566038733 : Nat.Prime 3566038733 := by
  refine lucas_primality 3566038733 (2 : ZMod 3566038733) prime_3566038733_pow ?_
  intro q hq hqd
  rw [prime_3566038733_sub1] at hqd
  have : q ∣ [2 ^ 2, 5119, 174157].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_3566038733_div_2
  · have : q = 5119 := (Nat.prime_dvd_prime_iff_eq hq prime_5119).mp hdf
    subst this; exact prime_3566038733_div_5119
  · have : q = 174157 := (Nat.prime_dvd_prime_iff_eq hq prime_174157).mp hdf
    subst this; exact prime_3566038733_div_174157
private lemma prime_83 : Nat.Prime 83 := by norm_num
private lemma prime_709 : Nat.Prime 709 := by norm_num
private lemma prime_3456517 : Nat.Prime 3456517 := by norm_num
private lemma prime_406811311799_sub1 : (406811311799 - 1 : ℕ) = 2 * 83 * 709 * 3456517 := by norm_num
private lemma prime_406811311799_pow : (7 : ZMod 406811311799) ^ (406811311799 - 1) = 1 := by
  reduce_mod_char
private lemma prime_406811311799_div_2 : (7 : ZMod 406811311799) ^ ((406811311799 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_406811311799_div_83 : (7 : ZMod 406811311799) ^ ((406811311799 - 1) / 83) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_406811311799_div_709 : (7 : ZMod 406811311799) ^ ((406811311799 - 1) / 709) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_406811311799_div_3456517 : (7 : ZMod 406811311799) ^ ((406811311799 - 1) / 3456517) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_406811311799 : Nat.Prime 406811311799 := by
  refine lucas_primality 406811311799 (7 : ZMod 406811311799) prime_406811311799_pow ?_
  intro q hq hqd
  rw [prime_406811311799_sub1] at hqd
  have : q ∣ [2, 83, 709, 3456517].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_406811311799_div_2
  · have : q = 83 := (Nat.prime_dvd_prime_iff_eq hq prime_83).mp hdf
    subst this; exact prime_406811311799_div_83
  · have : q = 709 := (Nat.prime_dvd_prime_iff_eq hq prime_709).mp hdf
    subst this; exact prime_406811311799_div_709
  · have : q = 3456517 := (Nat.prime_dvd_prime_iff_eq hq prime_3456517).mp hdf
    subst this; exact prime_406811311799_div_3456517
private lemma prime_634596349224082219482172481_sub1 : (634596349224082219482172481 - 1 : ℕ) = 2 ^ 6 * 5 * 1367 * 3566038733 * 406811311799 := by norm_num
private lemma prime_634596349224082219482172481_pow : (3 : ZMod 634596349224082219482172481) ^ (634596349224082219482172481 - 1) = 1 := by
  reduce_mod_char
private lemma prime_634596349224082219482172481_div_2 : (3 : ZMod 634596349224082219482172481) ^ ((634596349224082219482172481 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_634596349224082219482172481_div_5 : (3 : ZMod 634596349224082219482172481) ^ ((634596349224082219482172481 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_634596349224082219482172481_div_1367 : (3 : ZMod 634596349224082219482172481) ^ ((634596349224082219482172481 - 1) / 1367) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_634596349224082219482172481_div_3566038733 : (3 : ZMod 634596349224082219482172481) ^ ((634596349224082219482172481 - 1) / 3566038733) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_634596349224082219482172481_div_406811311799 : (3 : ZMod 634596349224082219482172481) ^ ((634596349224082219482172481 - 1) / 406811311799) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_634596349224082219482172481 : Nat.Prime 634596349224082219482172481 := by
  refine lucas_primality 634596349224082219482172481 (3 : ZMod 634596349224082219482172481) prime_634596349224082219482172481_pow ?_
  intro q hq hqd
  rw [prime_634596349224082219482172481_sub1] at hqd
  have : q ∣ [2 ^ 6, 5, 1367, 3566038733, 406811311799].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_634596349224082219482172481_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_634596349224082219482172481_div_5
  · have : q = 1367 := (Nat.prime_dvd_prime_iff_eq hq prime_1367).mp hdf
    subst this; exact prime_634596349224082219482172481_div_1367
  · have : q = 3566038733 := (Nat.prime_dvd_prime_iff_eq hq prime_3566038733).mp hdf
    subst this; exact prime_634596349224082219482172481_div_3566038733
  · have : q = 406811311799 := (Nat.prime_dvd_prime_iff_eq hq prime_406811311799).mp hdf
    subst this; exact prime_634596349224082219482172481_div_406811311799
private lemma prime_234809 : Nat.Prime 234809 := by norm_num
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_31 : Nat.Prime 31 := by norm_num
private lemma prime_43177 : Nat.Prime 43177 := by norm_num
private lemma prime_7233049 : Nat.Prime 7233049 := by norm_num
private lemma prime_29 : Nat.Prime 29 := by norm_num
private lemma prime_71 : Nat.Prime 71 := by norm_num
private lemma prime_9547 : Nat.Prime 9547 := by norm_num
private lemma prime_2948590951_sub1 : (2948590951 - 1 : ℕ) = 2 * 3 * 5 ^ 2 * 29 * 71 * 9547 := by norm_num
private lemma prime_2948590951_pow : (13 : ZMod 2948590951) ^ (2948590951 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2948590951_div_2 : (13 : ZMod 2948590951) ^ ((2948590951 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2948590951_div_3 : (13 : ZMod 2948590951) ^ ((2948590951 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2948590951_div_5 : (13 : ZMod 2948590951) ^ ((2948590951 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2948590951_div_29 : (13 : ZMod 2948590951) ^ ((2948590951 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2948590951_div_71 : (13 : ZMod 2948590951) ^ ((2948590951 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2948590951_div_9547 : (13 : ZMod 2948590951) ^ ((2948590951 - 1) / 9547) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2948590951 : Nat.Prime 2948590951 := by
  refine lucas_primality 2948590951 (13 : ZMod 2948590951) prime_2948590951_pow ?_
  intro q hq hqd
  rw [prime_2948590951_sub1] at hqd
  have : q ∣ [2, 3, 5 ^ 2, 29, 71, 9547].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2948590951_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_2948590951_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_2948590951_div_5
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_2948590951_div_29
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_2948590951_div_71
  · have : q = 9547 := (Nat.prime_dvd_prime_iff_eq hq prime_9547).mp hdf
    subst this; exact prime_2948590951_div_9547
private lemma prime_3254280204393824494125283_sub1 : (3254280204393824494125283 - 1 : ℕ) = 2 * 3 * 19 * 31 * 43177 * 7233049 * 2948590951 := by norm_num
private lemma prime_3254280204393824494125283_pow : (5 : ZMod 3254280204393824494125283) ^ (3254280204393824494125283 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3254280204393824494125283_div_2 : (5 : ZMod 3254280204393824494125283) ^ ((3254280204393824494125283 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3254280204393824494125283_div_3 : (5 : ZMod 3254280204393824494125283) ^ ((3254280204393824494125283 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3254280204393824494125283_div_19 : (5 : ZMod 3254280204393824494125283) ^ ((3254280204393824494125283 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3254280204393824494125283_div_31 : (5 : ZMod 3254280204393824494125283) ^ ((3254280204393824494125283 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3254280204393824494125283_div_43177 : (5 : ZMod 3254280204393824494125283) ^ ((3254280204393824494125283 - 1) / 43177) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3254280204393824494125283_div_7233049 : (5 : ZMod 3254280204393824494125283) ^ ((3254280204393824494125283 - 1) / 7233049) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3254280204393824494125283_div_2948590951 : (5 : ZMod 3254280204393824494125283) ^ ((3254280204393824494125283 - 1) / 2948590951) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3254280204393824494125283 : Nat.Prime 3254280204393824494125283 := by
  refine lucas_primality 3254280204393824494125283 (5 : ZMod 3254280204393824494125283) prime_3254280204393824494125283_pow ?_
  intro q hq hqd
  rw [prime_3254280204393824494125283_sub1] at hqd
  have : q ∣ [2, 3, 19, 31, 43177, 7233049, 2948590951].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3254280204393824494125283_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_3254280204393824494125283_div_3
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_3254280204393824494125283_div_19
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_3254280204393824494125283_div_31
  · have : q = 43177 := (Nat.prime_dvd_prime_iff_eq hq prime_43177).mp hdf
    subst this; exact prime_3254280204393824494125283_div_43177
  · have : q = 7233049 := (Nat.prime_dvd_prime_iff_eq hq prime_7233049).mp hdf
    subst this; exact prime_3254280204393824494125283_div_7233049
  · have : q = 2948590951 := (Nat.prime_dvd_prime_iff_eq hq prime_2948590951).mp hdf
    subst this; exact prime_3254280204393824494125283_div_2948590951
private lemma prime_4584805683081057213846381455683_sub1 : (4584805683081057213846381455683 - 1 : ℕ) = 2 * 3 * 234809 * 3254280204393824494125283 := by norm_num
private lemma prime_4584805683081057213846381455683_pow : (2 : ZMod 4584805683081057213846381455683) ^ (4584805683081057213846381455683 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4584805683081057213846381455683_div_2 : (2 : ZMod 4584805683081057213846381455683) ^ ((4584805683081057213846381455683 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4584805683081057213846381455683_div_3 : (2 : ZMod 4584805683081057213846381455683) ^ ((4584805683081057213846381455683 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4584805683081057213846381455683_div_234809 : (2 : ZMod 4584805683081057213846381455683) ^ ((4584805683081057213846381455683 - 1) / 234809) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4584805683081057213846381455683_div_3254280204393824494125283 : (2 : ZMod 4584805683081057213846381455683) ^ ((4584805683081057213846381455683 - 1) / 3254280204393824494125283) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4584805683081057213846381455683 : Nat.Prime 4584805683081057213846381455683 := by
  refine lucas_primality 4584805683081057213846381455683 (2 : ZMod 4584805683081057213846381455683) prime_4584805683081057213846381455683_pow ?_
  intro q hq hqd
  rw [prime_4584805683081057213846381455683_sub1] at hqd
  have : q ∣ [2, 3, 234809, 3254280204393824494125283].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_4584805683081057213846381455683_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_4584805683081057213846381455683_div_3
  · have : q = 234809 := (Nat.prime_dvd_prime_iff_eq hq prime_234809).mp hdf
    subst this; exact prime_4584805683081057213846381455683_div_234809
  · have : q = 3254280204393824494125283 := (Nat.prime_dvd_prime_iff_eq hq prime_3254280204393824494125283).mp hdf
    subst this; exact prime_4584805683081057213846381455683_div_3254280204393824494125283
private lemma prime_A_78_sub1 : (4963608617944918181428679924706603177950142894490924603146239 - 1 : ℕ) = 2 * 853 * 634596349224082219482172481 * 4584805683081057213846381455683 := by norm_num
private lemma prime_A_78_pow : (13 : ZMod 4963608617944918181428679924706603177950142894490924603146239) ^ (4963608617944918181428679924706603177950142894490924603146239 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_78_div_2 : (13 : ZMod 4963608617944918181428679924706603177950142894490924603146239) ^ ((4963608617944918181428679924706603177950142894490924603146239 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_78_div_853 : (13 : ZMod 4963608617944918181428679924706603177950142894490924603146239) ^ ((4963608617944918181428679924706603177950142894490924603146239 - 1) / 853) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_78_div_634596349224082219482172481 : (13 : ZMod 4963608617944918181428679924706603177950142894490924603146239) ^ ((4963608617944918181428679924706603177950142894490924603146239 - 1) / 634596349224082219482172481) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_78_div_4584805683081057213846381455683 : (13 : ZMod 4963608617944918181428679924706603177950142894490924603146239) ^ ((4963608617944918181428679924706603177950142894490924603146239 - 1) / 4584805683081057213846381455683) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_78 : Nat.Prime 4963608617944918181428679924706603177950142894490924603146239 := by
  refine lucas_primality 4963608617944918181428679924706603177950142894490924603146239 (13 : ZMod 4963608617944918181428679924706603177950142894490924603146239) prime_A_78_pow ?_
  intro q hq hqd
  rw [prime_A_78_sub1] at hqd
  have : q ∣ [2, 853, 634596349224082219482172481, 4584805683081057213846381455683].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_78_div_2
  · have : q = 853 := (Nat.prime_dvd_prime_iff_eq hq prime_853).mp hdf
    subst this; exact prime_A_78_div_853
  · have : q = 634596349224082219482172481 := (Nat.prime_dvd_prime_iff_eq hq prime_634596349224082219482172481).mp hdf
    subst this; exact prime_A_78_div_634596349224082219482172481
  · have : q = 4584805683081057213846381455683 := (Nat.prime_dvd_prime_iff_eq hq prime_4584805683081057213846381455683).mp hdf
    subst this; exact prime_A_78_div_4584805683081057213846381455683
private lemma prime_79 : Nat.Prime 79 := by norm_num
private lemma prime_12170783 : Nat.Prime 12170783 := by norm_num
private lemma prime_23075804569_sub1 : (23075804569 - 1 : ℕ) = 2 ^ 3 * 3 * 79 * 12170783 := by norm_num
private lemma prime_23075804569_pow : (7 : ZMod 23075804569) ^ (23075804569 - 1) = 1 := by
  reduce_mod_char
private lemma prime_23075804569_div_2 : (7 : ZMod 23075804569) ^ ((23075804569 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23075804569_div_3 : (7 : ZMod 23075804569) ^ ((23075804569 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23075804569_div_79 : (7 : ZMod 23075804569) ^ ((23075804569 - 1) / 79) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23075804569_div_12170783 : (7 : ZMod 23075804569) ^ ((23075804569 - 1) / 12170783) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_23075804569 : Nat.Prime 23075804569 := by
  refine lucas_primality 23075804569 (7 : ZMod 23075804569) prime_23075804569_pow ?_
  intro q hq hqd
  rw [prime_23075804569_sub1] at hqd
  have : q ∣ [2 ^ 3, 3, 79, 12170783].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_23075804569_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_23075804569_div_3
  · have : q = 79 := (Nat.prime_dvd_prime_iff_eq hq prime_79).mp hdf
    subst this; exact prime_23075804569_div_79
  · have : q = 12170783 := (Nat.prime_dvd_prime_iff_eq hq prime_12170783).mp hdf
    subst this; exact prime_23075804569_div_12170783
private lemma prime_139 : Nat.Prime 139 := by norm_num
private lemma prime_657197 : Nat.Prime 657197 := by norm_num
private lemma prime_182700767_sub1 : (182700767 - 1 : ℕ) = 2 * 139 * 657197 := by norm_num
private lemma prime_182700767_pow : (5 : ZMod 182700767) ^ (182700767 - 1) = 1 := by
  reduce_mod_char
private lemma prime_182700767_div_2 : (5 : ZMod 182700767) ^ ((182700767 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_182700767_div_139 : (5 : ZMod 182700767) ^ ((182700767 - 1) / 139) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_182700767_div_657197 : (5 : ZMod 182700767) ^ ((182700767 - 1) / 657197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_182700767 : Nat.Prime 182700767 := by
  refine lucas_primality 182700767 (5 : ZMod 182700767) prime_182700767_pow ?_
  intro q hq hqd
  rw [prime_182700767_sub1] at hqd
  have : q ∣ [2, 139, 657197].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_182700767_div_2
  · have : q = 139 := (Nat.prime_dvd_prime_iff_eq hq prime_139).mp hdf
    subst this; exact prime_182700767_div_139
  · have : q = 657197 := (Nat.prime_dvd_prime_iff_eq hq prime_657197).mp hdf
    subst this; exact prime_182700767_div_657197
private lemma prime_690608899261_sub1 : (690608899261 - 1 : ℕ) = 2 ^ 2 * 3 ^ 3 * 5 * 7 * 182700767 := by norm_num
private lemma prime_690608899261_pow : (17 : ZMod 690608899261) ^ (690608899261 - 1) = 1 := by
  reduce_mod_char
private lemma prime_690608899261_div_2 : (17 : ZMod 690608899261) ^ ((690608899261 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_690608899261_div_3 : (17 : ZMod 690608899261) ^ ((690608899261 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_690608899261_div_5 : (17 : ZMod 690608899261) ^ ((690608899261 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_690608899261_div_7 : (17 : ZMod 690608899261) ^ ((690608899261 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_690608899261_div_182700767 : (17 : ZMod 690608899261) ^ ((690608899261 - 1) / 182700767) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_690608899261 : Nat.Prime 690608899261 := by
  refine lucas_primality 690608899261 (17 : ZMod 690608899261) prime_690608899261_pow ?_
  intro q hq hqd
  rw [prime_690608899261_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 3, 5, 7, 182700767].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_690608899261_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_690608899261_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_690608899261_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_690608899261_div_7
  · have : q = 182700767 := (Nat.prime_dvd_prime_iff_eq hq prime_182700767).mp hdf
    subst this; exact prime_690608899261_div_182700767
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_4451 : Nat.Prime 4451 := by norm_num
private lemma prime_900763 : Nat.Prime 900763 := by norm_num
private lemma prime_22901099397457_sub1 : (22901099397457 - 1 : ℕ) = 2 ^ 4 * 3 * 7 * 17 * 4451 * 900763 := by norm_num
private lemma prime_22901099397457_pow : (11 : ZMod 22901099397457) ^ (22901099397457 - 1) = 1 := by
  reduce_mod_char
private lemma prime_22901099397457_div_2 : (11 : ZMod 22901099397457) ^ ((22901099397457 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22901099397457_div_3 : (11 : ZMod 22901099397457) ^ ((22901099397457 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22901099397457_div_7 : (11 : ZMod 22901099397457) ^ ((22901099397457 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22901099397457_div_17 : (11 : ZMod 22901099397457) ^ ((22901099397457 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22901099397457_div_4451 : (11 : ZMod 22901099397457) ^ ((22901099397457 - 1) / 4451) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22901099397457_div_900763 : (11 : ZMod 22901099397457) ^ ((22901099397457 - 1) / 900763) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_22901099397457 : Nat.Prime 22901099397457 := by
  refine lucas_primality 22901099397457 (11 : ZMod 22901099397457) prime_22901099397457_pow ?_
  intro q hq hqd
  rw [prime_22901099397457_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 7, 17, 4451, 900763].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_22901099397457_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_22901099397457_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_22901099397457_div_7
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_22901099397457_div_17
  · have : q = 4451 := (Nat.prime_dvd_prime_iff_eq hq prime_4451).mp hdf
    subst this; exact prime_22901099397457_div_4451
  · have : q = 900763 := (Nat.prime_dvd_prime_iff_eq hq prime_900763).mp hdf
    subst this; exact prime_22901099397457_div_900763
private lemma prime_B_78_sub1 : (4963608617944918181428679924706603177950142894490924603146241 - 1 : ℕ) = 2 ^ 78 * 3 ^ 2 * 5 * 23075804569 * 690608899261 * 22901099397457 := by norm_num
private lemma prime_B_78_pow : (7 : ZMod 4963608617944918181428679924706603177950142894490924603146241) ^ (4963608617944918181428679924706603177950142894490924603146241 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_78_div_2 : (7 : ZMod 4963608617944918181428679924706603177950142894490924603146241) ^ ((4963608617944918181428679924706603177950142894490924603146241 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_78_div_3 : (7 : ZMod 4963608617944918181428679924706603177950142894490924603146241) ^ ((4963608617944918181428679924706603177950142894490924603146241 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_78_div_5 : (7 : ZMod 4963608617944918181428679924706603177950142894490924603146241) ^ ((4963608617944918181428679924706603177950142894490924603146241 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_78_div_23075804569 : (7 : ZMod 4963608617944918181428679924706603177950142894490924603146241) ^ ((4963608617944918181428679924706603177950142894490924603146241 - 1) / 23075804569) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_78_div_690608899261 : (7 : ZMod 4963608617944918181428679924706603177950142894490924603146241) ^ ((4963608617944918181428679924706603177950142894490924603146241 - 1) / 690608899261) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_78_div_22901099397457 : (7 : ZMod 4963608617944918181428679924706603177950142894490924603146241) ^ ((4963608617944918181428679924706603177950142894490924603146241 - 1) / 22901099397457) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_78 : Nat.Prime 4963608617944918181428679924706603177950142894490924603146241 := by
  refine lucas_primality 4963608617944918181428679924706603177950142894490924603146241 (7 : ZMod 4963608617944918181428679924706603177950142894490924603146241) prime_B_78_pow ?_
  intro q hq hqd
  rw [prime_B_78_sub1] at hqd
  have : q ∣ [2 ^ 78, 3 ^ 2, 5, 23075804569, 690608899261, 22901099397457].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_78_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_78_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_78_div_5
  · have : q = 23075804569 := (Nat.prime_dvd_prime_iff_eq hq prime_23075804569).mp hdf
    subst this; exact prime_B_78_div_23075804569
  · have : q = 690608899261 := (Nat.prime_dvd_prime_iff_eq hq prime_690608899261).mp hdf
    subst this; exact prime_B_78_div_690608899261
  · have : q = 22901099397457 := (Nat.prime_dvd_prime_iff_eq hq prime_22901099397457).mp hdf
    subst this; exact prime_B_78_div_22901099397457
private lemma pair_78 :
    Nat.Prime ((3 ^ 78 - 7704) * (2 ^ 78) - 1) ∧
    Nat.Prime ((3 ^ 78 - 7704) * (2 ^ 78) + 1) := by
  constructor
  · convert prime_A_78
  · convert prime_B_78
