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
private lemma prime_53 : Nat.Prime 53 := by norm_num
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_29 : Nat.Prime 29 := by norm_num
private lemma prime_12197 : Nat.Prime 12197 := by norm_num
private lemma prime_1399 : Nat.Prime 1399 := by norm_num
private lemma prime_43261697 : Nat.Prime 43261697 := by norm_num
private lemma prime_363138684619_sub1 : (363138684619 - 1 : ℕ) = 2 * 3 * 1399 * 43261697 := by norm_num
private lemma prime_363138684619_pow : (2 : ZMod 363138684619) ^ (363138684619 - 1) = 1 := by
  reduce_mod_char
private lemma prime_363138684619_div_2 : (2 : ZMod 363138684619) ^ ((363138684619 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_363138684619_div_3 : (2 : ZMod 363138684619) ^ ((363138684619 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_363138684619_div_1399 : (2 : ZMod 363138684619) ^ ((363138684619 - 1) / 1399) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_363138684619_div_43261697 : (2 : ZMod 363138684619) ^ ((363138684619 - 1) / 43261697) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_363138684619 : Nat.Prime 363138684619 := by
  refine lucas_primality 363138684619 (2 : ZMod 363138684619) prime_363138684619_pow ?_
  intro q hq hqd
  rw [prime_363138684619_sub1] at hqd
  have : q ∣ [2, 3, 1399, 43261697].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_363138684619_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_363138684619_div_3
  · have : q = 1399 := (Nat.prime_dvd_prime_iff_eq hq prime_1399).mp hdf
    subst this; exact prime_363138684619_div_1399
  · have : q = 43261697 := (Nat.prime_dvd_prime_iff_eq hq prime_43261697).mp hdf
    subst this; exact prime_363138684619_div_43261697
private lemma prime_8858405072595887_sub1 : (8858405072595887 - 1 : ℕ) = 2 * 12197 * 363138684619 := by norm_num
private lemma prime_8858405072595887_pow : (5 : ZMod 8858405072595887) ^ (8858405072595887 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8858405072595887_div_2 : (5 : ZMod 8858405072595887) ^ ((8858405072595887 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8858405072595887_div_12197 : (5 : ZMod 8858405072595887) ^ ((8858405072595887 - 1) / 12197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8858405072595887_div_363138684619 : (5 : ZMod 8858405072595887) ^ ((8858405072595887 - 1) / 363138684619) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8858405072595887 : Nat.Prime 8858405072595887 := by
  refine lucas_primality 8858405072595887 (5 : ZMod 8858405072595887) prime_8858405072595887_pow ?_
  intro q hq hqd
  rw [prime_8858405072595887_sub1] at hqd
  have : q ∣ [2, 12197, 363138684619].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_8858405072595887_div_2
  · have : q = 12197 := (Nat.prime_dvd_prime_iff_eq hq prime_12197).mp hdf
    subst this; exact prime_8858405072595887_div_12197
  · have : q = 363138684619 := (Nat.prime_dvd_prime_iff_eq hq prime_363138684619).mp hdf
    subst this; exact prime_8858405072595887_div_363138684619
private lemma prime_90426598981058814497_sub1 : (90426598981058814497 - 1 : ℕ) = 2 ^ 5 * 11 * 29 * 8858405072595887 := by norm_num
private lemma prime_90426598981058814497_pow : (3 : ZMod 90426598981058814497) ^ (90426598981058814497 - 1) = 1 := by
  reduce_mod_char
private lemma prime_90426598981058814497_div_2 : (3 : ZMod 90426598981058814497) ^ ((90426598981058814497 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_90426598981058814497_div_11 : (3 : ZMod 90426598981058814497) ^ ((90426598981058814497 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_90426598981058814497_div_29 : (3 : ZMod 90426598981058814497) ^ ((90426598981058814497 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_90426598981058814497_div_8858405072595887 : (3 : ZMod 90426598981058814497) ^ ((90426598981058814497 - 1) / 8858405072595887) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_90426598981058814497 : Nat.Prime 90426598981058814497 := by
  refine lucas_primality 90426598981058814497 (3 : ZMod 90426598981058814497) prime_90426598981058814497_pow ?_
  intro q hq hqd
  rw [prime_90426598981058814497_sub1] at hqd
  have : q ∣ [2 ^ 5, 11, 29, 8858405072595887].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_90426598981058814497_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_90426598981058814497_div_11
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_90426598981058814497_div_29
  · have : q = 8858405072595887 := (Nat.prime_dvd_prime_iff_eq hq prime_8858405072595887).mp hdf
    subst this; exact prime_90426598981058814497_div_8858405072595887
private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_397 : Nat.Prime 397 := by norm_num
private lemma prime_739 : Nat.Prime 739 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_137 : Nat.Prime 137 := by norm_num
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_8573 : Nat.Prime 8573 := by norm_num
private lemma prime_131 : Nat.Prime 131 := by norm_num
private lemma prime_8893 : Nat.Prime 8893 := by norm_num
private lemma prime_441146442577_sub1 : (441146442577 - 1 : ℕ) = 2 ^ 4 * 3 * 7 ^ 3 * 23 * 131 * 8893 := by norm_num
private lemma prime_441146442577_pow : (5 : ZMod 441146442577) ^ (441146442577 - 1) = 1 := by
  reduce_mod_char
private lemma prime_441146442577_div_2 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577_div_3 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577_div_7 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577_div_23 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577_div_131 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 131) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577_div_8893 : (5 : ZMod 441146442577) ^ ((441146442577 - 1) / 8893) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_441146442577 : Nat.Prime 441146442577 := by
  refine lucas_primality 441146442577 (5 : ZMod 441146442577) prime_441146442577_pow ?_
  intro q hq hqd
  rw [prime_441146442577_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 7 ^ 3, 23, 131, 8893].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_441146442577_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_441146442577_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_441146442577_div_7
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_441146442577_div_23
  · have : q = 131 := (Nat.prime_dvd_prime_iff_eq hq prime_131).mp hdf
    subst this; exact prime_441146442577_div_131
  · have : q = 8893 := (Nat.prime_dvd_prime_iff_eq hq prime_8893).mp hdf
    subst this; exact prime_441146442577_div_8893
private lemma prime_45383381426551453_sub1 : (45383381426551453 - 1 : ℕ) = 2 ^ 2 * 3 * 8573 * 441146442577 := by norm_num
private lemma prime_45383381426551453_pow : (2 : ZMod 45383381426551453) ^ (45383381426551453 - 1) = 1 := by
  reduce_mod_char
private lemma prime_45383381426551453_div_2 : (2 : ZMod 45383381426551453) ^ ((45383381426551453 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45383381426551453_div_3 : (2 : ZMod 45383381426551453) ^ ((45383381426551453 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45383381426551453_div_8573 : (2 : ZMod 45383381426551453) ^ ((45383381426551453 - 1) / 8573) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45383381426551453_div_441146442577 : (2 : ZMod 45383381426551453) ^ ((45383381426551453 - 1) / 441146442577) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_45383381426551453 : Nat.Prime 45383381426551453 := by
  refine lucas_primality 45383381426551453 (2 : ZMod 45383381426551453) prime_45383381426551453_pow ?_
  intro q hq hqd
  rw [prime_45383381426551453_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 8573, 441146442577].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_45383381426551453_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_45383381426551453_div_3
  · have : q = 8573 := (Nat.prime_dvd_prime_iff_eq hq prime_8573).mp hdf
    subst this; exact prime_45383381426551453_div_8573
  · have : q = 441146442577 := (Nat.prime_dvd_prime_iff_eq hq prime_441146442577).mp hdf
    subst this; exact prime_45383381426551453_div_441146442577
private lemma prime_29953031741523958981_sub1 : (29953031741523958981 - 1 : ℕ) = 2 ^ 2 * 3 * 5 * 11 * 45383381426551453 := by norm_num
private lemma prime_29953031741523958981_pow : (6 : ZMod 29953031741523958981) ^ (29953031741523958981 - 1) = 1 := by
  reduce_mod_char
private lemma prime_29953031741523958981_div_2 : (6 : ZMod 29953031741523958981) ^ ((29953031741523958981 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29953031741523958981_div_3 : (6 : ZMod 29953031741523958981) ^ ((29953031741523958981 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29953031741523958981_div_5 : (6 : ZMod 29953031741523958981) ^ ((29953031741523958981 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29953031741523958981_div_11 : (6 : ZMod 29953031741523958981) ^ ((29953031741523958981 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29953031741523958981_div_45383381426551453 : (6 : ZMod 29953031741523958981) ^ ((29953031741523958981 - 1) / 45383381426551453) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_29953031741523958981 : Nat.Prime 29953031741523958981 := by
  refine lucas_primality 29953031741523958981 (6 : ZMod 29953031741523958981) prime_29953031741523958981_pow ?_
  intro q hq hqd
  rw [prime_29953031741523958981_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 5, 11, 45383381426551453].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_29953031741523958981_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_29953031741523958981_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_29953031741523958981_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_29953031741523958981_div_11
  · have : q = 45383381426551453 := (Nat.prime_dvd_prime_iff_eq hq prime_45383381426551453).mp hdf
    subst this; exact prime_29953031741523958981_div_45383381426551453
private lemma prime_110826217443638648229701_sub1 : (110826217443638648229701 - 1 : ℕ) = 2 ^ 2 * 5 ^ 2 * 37 * 29953031741523958981 := by norm_num
private lemma prime_110826217443638648229701_pow : (2 : ZMod 110826217443638648229701) ^ (110826217443638648229701 - 1) = 1 := by
  reduce_mod_char
private lemma prime_110826217443638648229701_div_2 : (2 : ZMod 110826217443638648229701) ^ ((110826217443638648229701 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_110826217443638648229701_div_5 : (2 : ZMod 110826217443638648229701) ^ ((110826217443638648229701 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_110826217443638648229701_div_37 : (2 : ZMod 110826217443638648229701) ^ ((110826217443638648229701 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_110826217443638648229701_div_29953031741523958981 : (2 : ZMod 110826217443638648229701) ^ ((110826217443638648229701 - 1) / 29953031741523958981) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_110826217443638648229701 : Nat.Prime 110826217443638648229701 := by
  refine lucas_primality 110826217443638648229701 (2 : ZMod 110826217443638648229701) prime_110826217443638648229701_pow ?_
  intro q hq hqd
  rw [prime_110826217443638648229701_sub1] at hqd
  have : q ∣ [2 ^ 2, 5 ^ 2, 37, 29953031741523958981].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_110826217443638648229701_div_2
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_110826217443638648229701_div_5
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_110826217443638648229701_div_37
  · have : q = 29953031741523958981 := (Nat.prime_dvd_prime_iff_eq hq prime_29953031741523958981).mp hdf
    subst this; exact prime_110826217443638648229701_div_29953031741523958981
private lemma prime_7895259730684817299883899241_sub1 : (7895259730684817299883899241 - 1 : ℕ) = 2 ^ 3 * 5 * 13 * 137 * 110826217443638648229701 := by norm_num
private lemma prime_7895259730684817299883899241_pow : (3 : ZMod 7895259730684817299883899241) ^ (7895259730684817299883899241 - 1) = 1 := by
  reduce_mod_char
private lemma prime_7895259730684817299883899241_div_2 : (3 : ZMod 7895259730684817299883899241) ^ ((7895259730684817299883899241 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7895259730684817299883899241_div_5 : (3 : ZMod 7895259730684817299883899241) ^ ((7895259730684817299883899241 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7895259730684817299883899241_div_13 : (3 : ZMod 7895259730684817299883899241) ^ ((7895259730684817299883899241 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7895259730684817299883899241_div_137 : (3 : ZMod 7895259730684817299883899241) ^ ((7895259730684817299883899241 - 1) / 137) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7895259730684817299883899241_div_110826217443638648229701 : (3 : ZMod 7895259730684817299883899241) ^ ((7895259730684817299883899241 - 1) / 110826217443638648229701) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7895259730684817299883899241 : Nat.Prime 7895259730684817299883899241 := by
  refine lucas_primality 7895259730684817299883899241 (3 : ZMod 7895259730684817299883899241) prime_7895259730684817299883899241_pow ?_
  intro q hq hqd
  rw [prime_7895259730684817299883899241_sub1] at hqd
  have : q ∣ [2 ^ 3, 5, 13, 137, 110826217443638648229701].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_7895259730684817299883899241_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_7895259730684817299883899241_div_5
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_7895259730684817299883899241_div_13
  · have : q = 137 := (Nat.prime_dvd_prime_iff_eq hq prime_137).mp hdf
    subst this; exact prime_7895259730684817299883899241_div_137
  · have : q = 110826217443638648229701 := (Nat.prime_dvd_prime_iff_eq hq prime_110826217443638648229701).mp hdf
    subst this; exact prime_7895259730684817299883899241_div_110826217443638648229701
private lemma prime_2876888052074839662333662809689700327_sub1 : (2876888052074839662333662809689700327 - 1 : ℕ) = 2 * 3 ^ 3 * 23 * 397 * 739 * 7895259730684817299883899241 := by norm_num
private lemma prime_2876888052074839662333662809689700327_pow : (3 : ZMod 2876888052074839662333662809689700327) ^ (2876888052074839662333662809689700327 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2876888052074839662333662809689700327_div_2 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327_div_3 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327_div_23 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327_div_397 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 397) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327_div_739 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 739) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327_div_7895259730684817299883899241 : (3 : ZMod 2876888052074839662333662809689700327) ^ ((2876888052074839662333662809689700327 - 1) / 7895259730684817299883899241) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2876888052074839662333662809689700327 : Nat.Prime 2876888052074839662333662809689700327 := by
  refine lucas_primality 2876888052074839662333662809689700327 (3 : ZMod 2876888052074839662333662809689700327) prime_2876888052074839662333662809689700327_pow ?_
  intro q hq hqd
  rw [prime_2876888052074839662333662809689700327_sub1] at hqd
  have : q ∣ [2, 3 ^ 3, 23, 397, 739, 7895259730684817299883899241].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_3
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_23
  · have : q = 397 := (Nat.prime_dvd_prime_iff_eq hq prime_397).mp hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_397
  · have : q = 739 := (Nat.prime_dvd_prime_iff_eq hq prime_739).mp hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_739
  · have : q = 7895259730684817299883899241 := (Nat.prime_dvd_prime_iff_eq hq prime_7895259730684817299883899241).mp hdf
    subst this; exact prime_2876888052074839662333662809689700327_div_7895259730684817299883899241
private lemma prime_A_76_sub1 : (137878017165136616150796664575183430072206928816041017475071 - 1 : ℕ) = 2 * 5 * 53 * 90426598981058814497 * 2876888052074839662333662809689700327 := by norm_num
private lemma prime_A_76_pow : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ (137878017165136616150796664575183430072206928816041017475071 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_76_div_2 : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ ((137878017165136616150796664575183430072206928816041017475071 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_76_div_5 : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ ((137878017165136616150796664575183430072206928816041017475071 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_76_div_53 : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ ((137878017165136616150796664575183430072206928816041017475071 - 1) / 53) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_76_div_90426598981058814497 : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ ((137878017165136616150796664575183430072206928816041017475071 - 1) / 90426598981058814497) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_76_div_2876888052074839662333662809689700327 : (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) ^ ((137878017165136616150796664575183430072206928816041017475071 - 1) / 2876888052074839662333662809689700327) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_76 : Nat.Prime 137878017165136616150796664575183430072206928816041017475071 := by
  refine lucas_primality 137878017165136616150796664575183430072206928816041017475071 (29 : ZMod 137878017165136616150796664575183430072206928816041017475071) prime_A_76_pow ?_
  intro q hq hqd
  rw [prime_A_76_sub1] at hqd
  have : q ∣ [2, 5, 53, 90426598981058814497, 2876888052074839662333662809689700327].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_76_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_76_div_5
  · have : q = 53 := (Nat.prime_dvd_prime_iff_eq hq prime_53).mp hdf
    subst this; exact prime_A_76_div_53
  · have : q = 90426598981058814497 := (Nat.prime_dvd_prime_iff_eq hq prime_90426598981058814497).mp hdf
    subst this; exact prime_A_76_div_90426598981058814497
  · have : q = 2876888052074839662333662809689700327 := (Nat.prime_dvd_prime_iff_eq hq prime_2876888052074839662333662809689700327).mp hdf
    subst this; exact prime_A_76_div_2876888052074839662333662809689700327
private lemma prime_2097097 : Nat.Prime 2097097 := by norm_num
private lemma prime_2350207 : Nat.Prime 2350207 := by norm_num
private lemma prime_394834777_sub1 : (394834777 - 1 : ℕ) = 2 ^ 3 * 3 * 7 * 2350207 := by norm_num
private lemma prime_394834777_pow : (10 : ZMod 394834777) ^ (394834777 - 1) = 1 := by
  reduce_mod_char
private lemma prime_394834777_div_2 : (10 : ZMod 394834777) ^ ((394834777 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_394834777_div_3 : (10 : ZMod 394834777) ^ ((394834777 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_394834777_div_7 : (10 : ZMod 394834777) ^ ((394834777 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_394834777_div_2350207 : (10 : ZMod 394834777) ^ ((394834777 - 1) / 2350207) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_394834777 : Nat.Prime 394834777 := by
  refine lucas_primality 394834777 (10 : ZMod 394834777) prime_394834777_pow ?_
  intro q hq hqd
  rw [prime_394834777_sub1] at hqd
  have : q ∣ [2 ^ 3, 3, 7, 2350207].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_394834777_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_394834777_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_394834777_div_7
  · have : q = 2350207 := (Nat.prime_dvd_prime_iff_eq hq prime_2350207).mp hdf
    subst this; exact prime_394834777_div_2350207
private lemma prime_401 : Nat.Prime 401 := by norm_num
private lemma prime_47 : Nat.Prime 47 := by norm_num
private lemma prime_231943 : Nat.Prime 231943 := by norm_num
private lemma prime_218026421_sub1 : (218026421 - 1 : ℕ) = 2 ^ 2 * 5 * 47 * 231943 := by norm_num
private lemma prime_218026421_pow : (2 : ZMod 218026421) ^ (218026421 - 1) = 1 := by
  reduce_mod_char
private lemma prime_218026421_div_2 : (2 : ZMod 218026421) ^ ((218026421 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_218026421_div_5 : (2 : ZMod 218026421) ^ ((218026421 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_218026421_div_47 : (2 : ZMod 218026421) ^ ((218026421 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_218026421_div_231943 : (2 : ZMod 218026421) ^ ((218026421 - 1) / 231943) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_218026421 : Nat.Prime 218026421 := by
  refine lucas_primality 218026421 (2 : ZMod 218026421) prime_218026421_pow ?_
  intro q hq hqd
  rw [prime_218026421_sub1] at hqd
  have : q ∣ [2 ^ 2, 5, 47, 231943].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_218026421_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_218026421_div_5
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_218026421_div_47
  · have : q = 231943 := (Nat.prime_dvd_prime_iff_eq hq prime_231943).mp hdf
    subst this; exact prime_218026421_div_231943
private lemma prime_436052843_sub1 : (436052843 - 1 : ℕ) = 2 * 218026421 := by norm_num
private lemma prime_436052843_pow : (2 : ZMod 436052843) ^ (436052843 - 1) = 1 := by
  reduce_mod_char
private lemma prime_436052843_div_2 : (2 : ZMod 436052843) ^ ((436052843 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_436052843_div_218026421 : (2 : ZMod 436052843) ^ ((436052843 - 1) / 218026421) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_436052843 : Nat.Prime 436052843 := by
  refine lucas_primality 436052843 (2 : ZMod 436052843) prime_436052843_pow ?_
  intro q hq hqd
  rw [prime_436052843_sub1] at hqd
  have : q ∣ [2, 218026421].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_436052843_div_2
  · have : q = 218026421 := (Nat.prime_dvd_prime_iff_eq hq prime_218026421).mp hdf
    subst this; exact prime_436052843_div_218026421
private lemma prime_872105687_sub1 : (872105687 - 1 : ℕ) = 2 * 436052843 := by norm_num
private lemma prime_872105687_pow : (5 : ZMod 872105687) ^ (872105687 - 1) = 1 := by
  reduce_mod_char
private lemma prime_872105687_div_2 : (5 : ZMod 872105687) ^ ((872105687 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_872105687_div_436052843 : (5 : ZMod 872105687) ^ ((872105687 - 1) / 436052843) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_872105687 : Nat.Prime 872105687 := by
  refine lucas_primality 872105687 (5 : ZMod 872105687) prime_872105687_pow ?_
  intro q hq hqd
  rw [prime_872105687_sub1] at hqd
  have : q ∣ [2, 436052843].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_872105687_div_2
  · have : q = 436052843 := (Nat.prime_dvd_prime_iff_eq hq prime_436052843).mp hdf
    subst this; exact prime_872105687_div_436052843
private lemma prime_16786290263377_sub1 : (16786290263377 - 1 : ℕ) = 2 ^ 4 * 3 * 401 * 872105687 := by norm_num
private lemma prime_16786290263377_pow : (7 : ZMod 16786290263377) ^ (16786290263377 - 1) = 1 := by
  reduce_mod_char
private lemma prime_16786290263377_div_2 : (7 : ZMod 16786290263377) ^ ((16786290263377 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_16786290263377_div_3 : (7 : ZMod 16786290263377) ^ ((16786290263377 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_16786290263377_div_401 : (7 : ZMod 16786290263377) ^ ((16786290263377 - 1) / 401) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_16786290263377_div_872105687 : (7 : ZMod 16786290263377) ^ ((16786290263377 - 1) / 872105687) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_16786290263377 : Nat.Prime 16786290263377 := by
  refine lucas_primality 16786290263377 (7 : ZMod 16786290263377) prime_16786290263377_pow ?_
  intro q hq hqd
  rw [prime_16786290263377_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 401, 872105687].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_16786290263377_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_16786290263377_div_3
  · have : q = 401 := (Nat.prime_dvd_prime_iff_eq hq prime_401).mp hdf
    subst this; exact prime_16786290263377_div_401
  · have : q = 872105687 := (Nat.prime_dvd_prime_iff_eq hq prime_872105687).mp hdf
    subst this; exact prime_16786290263377_div_872105687
private lemma prime_79533734073572748743149_sub1 : (79533734073572748743149 - 1 : ℕ) = 2 ^ 2 * 3 * 394834777 * 16786290263377 := by norm_num
private lemma prime_79533734073572748743149_pow : (2 : ZMod 79533734073572748743149) ^ (79533734073572748743149 - 1) = 1 := by
  reduce_mod_char
private lemma prime_79533734073572748743149_div_2 : (2 : ZMod 79533734073572748743149) ^ ((79533734073572748743149 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79533734073572748743149_div_3 : (2 : ZMod 79533734073572748743149) ^ ((79533734073572748743149 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79533734073572748743149_div_394834777 : (2 : ZMod 79533734073572748743149) ^ ((79533734073572748743149 - 1) / 394834777) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79533734073572748743149_div_16786290263377 : (2 : ZMod 79533734073572748743149) ^ ((79533734073572748743149 - 1) / 16786290263377) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79533734073572748743149 : Nat.Prime 79533734073572748743149 := by
  refine lucas_primality 79533734073572748743149 (2 : ZMod 79533734073572748743149) prime_79533734073572748743149_pow ?_
  intro q hq hqd
  rw [prime_79533734073572748743149_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 394834777, 16786290263377].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_79533734073572748743149_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_79533734073572748743149_div_3
  · have : q = 394834777 := (Nat.prime_dvd_prime_iff_eq hq prime_394834777).mp hdf
    subst this; exact prime_79533734073572748743149_div_394834777
  · have : q = 16786290263377 := (Nat.prime_dvd_prime_iff_eq hq prime_16786290263377).mp hdf
    subst this; exact prime_79533734073572748743149_div_16786290263377
private lemma prime_B_76_sub1 : (137878017165136616150796664575183430072206928816041017475073 - 1 : ℕ) = 2 ^ 76 * 3 * 13 * 23 * 12197 * 2097097 * 79533734073572748743149 := by norm_num
private lemma prime_B_76_pow : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ (137878017165136616150796664575183430072206928816041017475073 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_76_div_2 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_3 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_13 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_23 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_12197 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 12197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_2097097 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 2097097) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76_div_79533734073572748743149 : (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) ^ ((137878017165136616150796664575183430072206928816041017475073 - 1) / 79533734073572748743149) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_76 : Nat.Prime 137878017165136616150796664575183430072206928816041017475073 := by
  refine lucas_primality 137878017165136616150796664575183430072206928816041017475073 (5 : ZMod 137878017165136616150796664575183430072206928816041017475073) prime_B_76_pow ?_
  intro q hq hqd
  rw [prime_B_76_sub1] at hqd
  have : q ∣ [2 ^ 76, 3, 13, 23, 12197, 2097097, 79533734073572748743149].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_76_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_76_div_3
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_B_76_div_13
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_B_76_div_23
  · have : q = 12197 := (Nat.prime_dvd_prime_iff_eq hq prime_12197).mp hdf
    subst this; exact prime_B_76_div_12197
  · have : q = 2097097 := (Nat.prime_dvd_prime_iff_eq hq prime_2097097).mp hdf
    subst this; exact prime_B_76_div_2097097
  · have : q = 79533734073572748743149 := (Nat.prime_dvd_prime_iff_eq hq prime_79533734073572748743149).mp hdf
    subst this; exact prime_B_76_div_79533734073572748743149
private lemma pair_76 :
    Nat.Prime ((3 ^ 76 - 744) * (2 ^ 76) - 1) ∧
    Nat.Prime ((3 ^ 76 - 744) * (2 ^ 76) + 1) := by
  constructor
  · convert prime_A_76
  · convert prime_B_76
