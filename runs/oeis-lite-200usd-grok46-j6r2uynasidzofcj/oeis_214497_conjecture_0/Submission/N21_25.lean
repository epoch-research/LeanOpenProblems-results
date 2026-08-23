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

/- Pair for n = 21 -/
private lemma prime_79 : Nat.Prime 79 := by norm_num
private lemma prime_2389901 : Nat.Prime 2389901 := by norm_num
private lemma prime_58095061 : Nat.Prime 58095061 := by norm_num
private lemma prime_A_21_sub1 : (21936948211875839 - 1 : ℕ) = 2 * 79 * 2389901 * 58095061 := by norm_num
private lemma prime_A_21_pow : (14 : ZMod 21936948211875839) ^ (21936948211875839 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_21_div_2 : (14 : ZMod 21936948211875839) ^ ((21936948211875839 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_21_div_79 : (14 : ZMod 21936948211875839) ^ ((21936948211875839 - 1) / 79) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_21_div_2389901 : (14 : ZMod 21936948211875839) ^ ((21936948211875839 - 1) / 2389901) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_21_div_58095061 : (14 : ZMod 21936948211875839) ^ ((21936948211875839 - 1) / 58095061) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_21 : Nat.Prime 21936948211875839 := by
  refine lucas_primality 21936948211875839 (14 : ZMod 21936948211875839) prime_A_21_pow ?_
  intro q hq hqd
  rw [prime_A_21_sub1] at hqd
  have : q ∣ [2, 79, 2389901, 58095061].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_21_div_2
  · have : q = 79 := (Nat.prime_dvd_prime_iff_eq hq prime_79).mp hdf
    subst this; exact prime_A_21_div_79
  · have : q = 2389901 := (Nat.prime_dvd_prime_iff_eq hq prime_2389901).mp hdf
    subst this; exact prime_A_21_div_2389901
  · have : q = 58095061 := (Nat.prime_dvd_prime_iff_eq hq prime_58095061).mp hdf
    subst this; exact prime_A_21_div_58095061
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_149 : Nat.Prime 149 := by norm_num
private lemma prime_1423 : Nat.Prime 1423 := by norm_num
private lemma prime_B_21_sub1 : (21936948211875841 - 1 : ℕ) = 2 ^ 21 * 3 * 5 * 11 * 13 * 23 * 149 * 1423 := by norm_num
private lemma prime_B_21_pow : (17 : ZMod 21936948211875841) ^ (21936948211875841 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_21_div_2 : (17 : ZMod 21936948211875841) ^ ((21936948211875841 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_21_div_3 : (17 : ZMod 21936948211875841) ^ ((21936948211875841 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_21_div_5 : (17 : ZMod 21936948211875841) ^ ((21936948211875841 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_21_div_11 : (17 : ZMod 21936948211875841) ^ ((21936948211875841 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_21_div_13 : (17 : ZMod 21936948211875841) ^ ((21936948211875841 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_21_div_23 : (17 : ZMod 21936948211875841) ^ ((21936948211875841 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_21_div_149 : (17 : ZMod 21936948211875841) ^ ((21936948211875841 - 1) / 149) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_21_div_1423 : (17 : ZMod 21936948211875841) ^ ((21936948211875841 - 1) / 1423) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_21 : Nat.Prime 21936948211875841 := by
  refine lucas_primality 21936948211875841 (17 : ZMod 21936948211875841) prime_B_21_pow ?_
  intro q hq hqd
  rw [prime_B_21_sub1] at hqd
  have : q ∣ [2 ^ 21, 3, 5, 11, 13, 23, 149, 1423].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_21_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_21_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_21_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_21_div_11
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_B_21_div_13
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_B_21_div_23
  · have : q = 149 := (Nat.prime_dvd_prime_iff_eq hq prime_149).mp hdf
    subst this; exact prime_B_21_div_149
  · have : q = 1423 := (Nat.prime_dvd_prime_iff_eq hq prime_1423).mp hdf
    subst this; exact prime_B_21_div_1423
private lemma pair_21 :
    Nat.Prime ((3 ^ 21 - 1158) * (2 ^ 21) - 1) ∧
    Nat.Prime ((3 ^ 21 - 1158) * (2 ^ 21) + 1) := by
  constructor
  · convert prime_A_21
  · convert prime_B_21

/- Pair for n = 22 -/
private lemma prime_607 : Nat.Prime 607 := by norm_num
private lemma prime_83 : Nat.Prime 83 := by norm_num
private lemma prime_3455723 : Nat.Prime 3455723 := by norm_num
private lemma prime_870842197_sub1 : (870842197 - 1 : ℕ) = 2 ^ 2 * 3 ^ 2 * 7 * 3455723 := by norm_num
private lemma prime_870842197_pow : (2 : ZMod 870842197) ^ (870842197 - 1) = 1 := by
  reduce_mod_char
private lemma prime_870842197_div_2 : (2 : ZMod 870842197) ^ ((870842197 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_870842197_div_3 : (2 : ZMod 870842197) ^ ((870842197 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_870842197_div_7 : (2 : ZMod 870842197) ^ ((870842197 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_870842197_div_3455723 : (2 : ZMod 870842197) ^ ((870842197 - 1) / 3455723) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_870842197 : Nat.Prime 870842197 := by
  refine lucas_primality 870842197 (2 : ZMod 870842197) prime_870842197_pow ?_
  intro q hq hqd
  rw [prime_870842197_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 2, 7, 3455723].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_870842197_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_870842197_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_870842197_div_7
  · have : q = 3455723 := (Nat.prime_dvd_prime_iff_eq hq prime_3455723).mp hdf
    subst this; exact prime_870842197_div_3455723
private lemma prime_867358828213_sub1 : (867358828213 - 1 : ℕ) = 2 ^ 2 * 3 * 83 * 870842197 := by norm_num
private lemma prime_867358828213_pow : (2 : ZMod 867358828213) ^ (867358828213 - 1) = 1 := by
  reduce_mod_char
private lemma prime_867358828213_div_2 : (2 : ZMod 867358828213) ^ ((867358828213 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_867358828213_div_3 : (2 : ZMod 867358828213) ^ ((867358828213 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_867358828213_div_83 : (2 : ZMod 867358828213) ^ ((867358828213 - 1) / 83) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_867358828213_div_870842197 : (2 : ZMod 867358828213) ^ ((867358828213 - 1) / 870842197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_867358828213 : Nat.Prime 867358828213 := by
  refine lucas_primality 867358828213 (2 : ZMod 867358828213) prime_867358828213_pow ?_
  intro q hq hqd
  rw [prime_867358828213_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 83, 870842197].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_867358828213_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_867358828213_div_3
  · have : q = 83 := (Nat.prime_dvd_prime_iff_eq hq prime_83).mp hdf
    subst this; exact prime_867358828213_div_83
  · have : q = 870842197 := (Nat.prime_dvd_prime_iff_eq hq prime_870842197).mp hdf
    subst this; exact prime_867358828213_div_870842197
private lemma prime_A_22_sub1 : (131621702181322751 - 1 : ℕ) = 2 * 5 ^ 3 * 607 * 867358828213 := by norm_num
private lemma prime_A_22_pow : (17 : ZMod 131621702181322751) ^ (131621702181322751 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_22_div_2 : (17 : ZMod 131621702181322751) ^ ((131621702181322751 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_22_div_5 : (17 : ZMod 131621702181322751) ^ ((131621702181322751 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_22_div_607 : (17 : ZMod 131621702181322751) ^ ((131621702181322751 - 1) / 607) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_22_div_867358828213 : (17 : ZMod 131621702181322751) ^ ((131621702181322751 - 1) / 867358828213) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_22 : Nat.Prime 131621702181322751 := by
  refine lucas_primality 131621702181322751 (17 : ZMod 131621702181322751) prime_A_22_pow ?_
  intro q hq hqd
  rw [prime_A_22_sub1] at hqd
  have : q ∣ [2, 5 ^ 3, 607, 867358828213].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_22_div_2
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_A_22_div_5
  · have : q = 607 := (Nat.prime_dvd_prime_iff_eq hq prime_607).mp hdf
    subst this; exact prime_A_22_div_607
  · have : q = 867358828213 := (Nat.prime_dvd_prime_iff_eq hq prime_867358828213).mp hdf
    subst this; exact prime_A_22_div_867358828213
private lemma prime_8941 : Nat.Prime 8941 := by norm_num
private lemma prime_55711 : Nat.Prime 55711 := by norm_num
private lemma prime_B_22_sub1 : (131621702181322753 - 1 : ℕ) = 2 ^ 22 * 3 ^ 2 * 7 * 8941 * 55711 := by norm_num
private lemma prime_B_22_pow : (5 : ZMod 131621702181322753) ^ (131621702181322753 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_22_div_2 : (5 : ZMod 131621702181322753) ^ ((131621702181322753 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_22_div_3 : (5 : ZMod 131621702181322753) ^ ((131621702181322753 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_22_div_7 : (5 : ZMod 131621702181322753) ^ ((131621702181322753 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_22_div_8941 : (5 : ZMod 131621702181322753) ^ ((131621702181322753 - 1) / 8941) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_22_div_55711 : (5 : ZMod 131621702181322753) ^ ((131621702181322753 - 1) / 55711) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_22 : Nat.Prime 131621702181322753 := by
  refine lucas_primality 131621702181322753 (5 : ZMod 131621702181322753) prime_B_22_pow ?_
  intro q hq hqd
  rw [prime_B_22_sub1] at hqd
  have : q ∣ [2 ^ 22, 3 ^ 2, 7, 8941, 55711].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_22_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_22_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_B_22_div_7
  · have : q = 8941 := (Nat.prime_dvd_prime_iff_eq hq prime_8941).mp hdf
    subst this; exact prime_B_22_div_8941
  · have : q = 55711 := (Nat.prime_dvd_prime_iff_eq hq prime_55711).mp hdf
    subst this; exact prime_B_22_div_55711
private lemma pair_22 :
    Nat.Prime ((3 ^ 22 - 396) * (2 ^ 22) - 1) ∧
    Nat.Prime ((3 ^ 22 - 396) * (2 ^ 22) + 1) := by
  constructor
  · convert prime_A_22
  · convert prime_B_22

/- Pair for n = 23 -/
private lemma prime_2939 : Nat.Prime 2939 := by norm_num
private lemma prime_4980961 : Nat.Prime 4980961 := by norm_num
private lemma prime_26973421 : Nat.Prime 26973421 := by norm_num
private lemma prime_A_23_sub1 : (789730214144901119 - 1 : ℕ) = 2 * 2939 * 4980961 * 26973421 := by norm_num
private lemma prime_A_23_pow : (19 : ZMod 789730214144901119) ^ (789730214144901119 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_23_div_2 : (19 : ZMod 789730214144901119) ^ ((789730214144901119 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_23_div_2939 : (19 : ZMod 789730214144901119) ^ ((789730214144901119 - 1) / 2939) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_23_div_4980961 : (19 : ZMod 789730214144901119) ^ ((789730214144901119 - 1) / 4980961) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_23_div_26973421 : (19 : ZMod 789730214144901119) ^ ((789730214144901119 - 1) / 26973421) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_23 : Nat.Prime 789730214144901119 := by
  refine lucas_primality 789730214144901119 (19 : ZMod 789730214144901119) prime_A_23_pow ?_
  intro q hq hqd
  rw [prime_A_23_sub1] at hqd
  have : q ∣ [2, 2939, 4980961, 26973421].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_23_div_2
  · have : q = 2939 := (Nat.prime_dvd_prime_iff_eq hq prime_2939).mp hdf
    subst this; exact prime_A_23_div_2939
  · have : q = 4980961 := (Nat.prime_dvd_prime_iff_eq hq prime_4980961).mp hdf
    subst this; exact prime_A_23_div_4980961
  · have : q = 26973421 := (Nat.prime_dvd_prime_iff_eq hq prime_26973421).mp hdf
    subst this; exact prime_A_23_div_26973421
private lemma prime_977 : Nat.Prime 977 := by norm_num
private lemma prime_23531 : Nat.Prime 23531 := by norm_num
private lemma prime_B_23_sub1 : (789730214144901121 - 1 : ℕ) = 2 ^ 23 * 3 ^ 2 * 5 * 7 * 13 * 977 * 23531 := by norm_num
private lemma prime_B_23_pow : (17 : ZMod 789730214144901121) ^ (789730214144901121 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_23_div_2 : (17 : ZMod 789730214144901121) ^ ((789730214144901121 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_23_div_3 : (17 : ZMod 789730214144901121) ^ ((789730214144901121 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_23_div_5 : (17 : ZMod 789730214144901121) ^ ((789730214144901121 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_23_div_7 : (17 : ZMod 789730214144901121) ^ ((789730214144901121 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_23_div_13 : (17 : ZMod 789730214144901121) ^ ((789730214144901121 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_23_div_977 : (17 : ZMod 789730214144901121) ^ ((789730214144901121 - 1) / 977) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_23_div_23531 : (17 : ZMod 789730214144901121) ^ ((789730214144901121 - 1) / 23531) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_23 : Nat.Prime 789730214144901121 := by
  refine lucas_primality 789730214144901121 (17 : ZMod 789730214144901121) prime_B_23_pow ?_
  intro q hq hqd
  rw [prime_B_23_sub1] at hqd
  have : q ∣ [2 ^ 23, 3 ^ 2, 5, 7, 13, 977, 23531].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_23_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_23_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_23_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_B_23_div_7
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_B_23_div_13
  · have : q = 977 := (Nat.prime_dvd_prime_iff_eq hq prime_977).mp hdf
    subst this; exact prime_B_23_div_977
  · have : q = 23531 := (Nat.prime_dvd_prime_iff_eq hq prime_23531).mp hdf
    subst this; exact prime_B_23_div_23531
private lemma pair_23 :
    Nat.Prime ((3 ^ 23 - 1062) * (2 ^ 23) - 1) ∧
    Nat.Prime ((3 ^ 23 - 1062) * (2 ^ 23) + 1) := by
  constructor
  · convert prime_A_23
  · convert prime_B_23

/- Pair for n = 24 -/
private lemma prime_1181 : Nat.Prime 1181 := by norm_num
private lemma prime_20639 : Nat.Prime 20639 := by norm_num
private lemma prime_59 : Nat.Prime 59 := by norm_num
private lemma prime_67 : Nat.Prime 67 := by norm_num
private lemma prime_48787 : Nat.Prime 48787 := by norm_num
private lemma prime_1157130067_sub1 : (1157130067 - 1 : ℕ) = 2 * 3 * 59 * 67 * 48787 := by norm_num
private lemma prime_1157130067_pow : (2 : ZMod 1157130067) ^ (1157130067 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1157130067_div_2 : (2 : ZMod 1157130067) ^ ((1157130067 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1157130067_div_3 : (2 : ZMod 1157130067) ^ ((1157130067 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1157130067_div_59 : (2 : ZMod 1157130067) ^ ((1157130067 - 1) / 59) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1157130067_div_67 : (2 : ZMod 1157130067) ^ ((1157130067 - 1) / 67) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1157130067_div_48787 : (2 : ZMod 1157130067) ^ ((1157130067 - 1) / 48787) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1157130067 : Nat.Prime 1157130067 := by
  refine lucas_primality 1157130067 (2 : ZMod 1157130067) prime_1157130067_pow ?_
  intro q hq hqd
  rw [prime_1157130067_sub1] at hqd
  have : q ∣ [2, 3, 59, 67, 48787].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1157130067_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1157130067_div_3
  · have : q = 59 := (Nat.prime_dvd_prime_iff_eq hq prime_59).mp hdf
    subst this; exact prime_1157130067_div_59
  · have : q = 67 := (Nat.prime_dvd_prime_iff_eq hq prime_67).mp hdf
    subst this; exact prime_1157130067_div_67
  · have : q = 48787 := (Nat.prime_dvd_prime_iff_eq hq prime_48787).mp hdf
    subst this; exact prime_1157130067_div_48787
private lemma prime_286584089433757_sub1 : (286584089433757 - 1 : ℕ) = 2 ^ 2 * 3 * 20639 * 1157130067 := by norm_num
private lemma prime_286584089433757_pow : (2 : ZMod 286584089433757) ^ (286584089433757 - 1) = 1 := by
  reduce_mod_char
private lemma prime_286584089433757_div_2 : (2 : ZMod 286584089433757) ^ ((286584089433757 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_286584089433757_div_3 : (2 : ZMod 286584089433757) ^ ((286584089433757 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_286584089433757_div_20639 : (2 : ZMod 286584089433757) ^ ((286584089433757 - 1) / 20639) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_286584089433757_div_1157130067 : (2 : ZMod 286584089433757) ^ ((286584089433757 - 1) / 1157130067) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_286584089433757 : Nat.Prime 286584089433757 := by
  refine lucas_primality 286584089433757 (2 : ZMod 286584089433757) prime_286584089433757_pow ?_
  intro q hq hqd
  rw [prime_286584089433757_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 20639, 1157130067].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_286584089433757_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_286584089433757_div_3
  · have : q = 20639 := (Nat.prime_dvd_prime_iff_eq hq prime_20639).mp hdf
    subst this; exact prime_286584089433757_div_20639
  · have : q = 1157130067 := (Nat.prime_dvd_prime_iff_eq hq prime_1157130067).mp hdf
    subst this; exact prime_286584089433757_div_1157130067
private lemma prime_A_24_sub1 : (4738381334697738239 - 1 : ℕ) = 2 * 7 * 1181 * 286584089433757 := by norm_num
private lemma prime_A_24_pow : (7 : ZMod 4738381334697738239) ^ (4738381334697738239 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_24_div_2 : (7 : ZMod 4738381334697738239) ^ ((4738381334697738239 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_24_div_7 : (7 : ZMod 4738381334697738239) ^ ((4738381334697738239 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_24_div_1181 : (7 : ZMod 4738381334697738239) ^ ((4738381334697738239 - 1) / 1181) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_24_div_286584089433757 : (7 : ZMod 4738381334697738239) ^ ((4738381334697738239 - 1) / 286584089433757) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_24 : Nat.Prime 4738381334697738239 := by
  refine lucas_primality 4738381334697738239 (7 : ZMod 4738381334697738239) prime_A_24_pow ?_
  intro q hq hqd
  rw [prime_A_24_sub1] at hqd
  have : q ∣ [2, 7, 1181, 286584089433757].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_24_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_24_div_7
  · have : q = 1181 := (Nat.prime_dvd_prime_iff_eq hq prime_1181).mp hdf
    subst this; exact prime_A_24_div_1181
  · have : q = 286584089433757 := (Nat.prime_dvd_prime_iff_eq hq prime_286584089433757).mp hdf
    subst this; exact prime_A_24_div_286584089433757
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_4787347 : Nat.Prime 4787347 := by norm_num
private lemma prime_B_24_sub1 : (4738381334697738241 - 1 : ℕ) = 2 ^ 24 * 3 ^ 3 * 5 * 19 * 23 * 4787347 := by norm_num
private lemma prime_B_24_pow : (11 : ZMod 4738381334697738241) ^ (4738381334697738241 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_24_div_2 : (11 : ZMod 4738381334697738241) ^ ((4738381334697738241 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_24_div_3 : (11 : ZMod 4738381334697738241) ^ ((4738381334697738241 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_24_div_5 : (11 : ZMod 4738381334697738241) ^ ((4738381334697738241 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_24_div_19 : (11 : ZMod 4738381334697738241) ^ ((4738381334697738241 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_24_div_23 : (11 : ZMod 4738381334697738241) ^ ((4738381334697738241 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_24_div_4787347 : (11 : ZMod 4738381334697738241) ^ ((4738381334697738241 - 1) / 4787347) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_24 : Nat.Prime 4738381334697738241 := by
  refine lucas_primality 4738381334697738241 (11 : ZMod 4738381334697738241) prime_B_24_pow ?_
  intro q hq hqd
  rw [prime_B_24_sub1] at hqd
  have : q ∣ [2 ^ 24, 3 ^ 3, 5, 19, 23, 4787347].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_24_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_24_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_24_div_5
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_B_24_div_19
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_B_24_div_23
  · have : q = 4787347 := (Nat.prime_dvd_prime_iff_eq hq prime_4787347).mp hdf
    subst this; exact prime_B_24_div_4787347
private lemma pair_24 :
    Nat.Prime ((3 ^ 24 - 216) * (2 ^ 24) - 1) ∧
    Nat.Prime ((3 ^ 24 - 216) * (2 ^ 24) + 1) := by
  constructor
  · convert prime_A_24
  · convert prime_B_24

/- Pair for n = 25 -/
private lemma prime_409 : Nat.Prime 409 := by norm_num
private lemma prime_2713 : Nat.Prime 2713 := by norm_num
private lemma prime_1873 : Nat.Prime 1873 := by norm_num
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_20116919 : Nat.Prime 20116919 := by norm_num
private lemma prime_3419876231_sub1 : (3419876231 - 1 : ℕ) = 2 * 5 * 17 * 20116919 := by norm_num
private lemma prime_3419876231_pow : (7 : ZMod 3419876231) ^ (3419876231 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3419876231_div_2 : (7 : ZMod 3419876231) ^ ((3419876231 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3419876231_div_5 : (7 : ZMod 3419876231) ^ ((3419876231 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3419876231_div_17 : (7 : ZMod 3419876231) ^ ((3419876231 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3419876231_div_20116919 : (7 : ZMod 3419876231) ^ ((3419876231 - 1) / 20116919) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3419876231 : Nat.Prime 3419876231 := by
  refine lucas_primality 3419876231 (7 : ZMod 3419876231) prime_3419876231_pow ?_
  intro q hq hqd
  rw [prime_3419876231_sub1] at hqd
  have : q ∣ [2, 5, 17, 20116919].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3419876231_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_3419876231_div_5
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_3419876231_div_17
  · have : q = 20116919 := (Nat.prime_dvd_prime_iff_eq hq prime_20116919).mp hdf
    subst this; exact prime_3419876231_div_20116919
private lemma prime_12810856361327_sub1 : (12810856361327 - 1 : ℕ) = 2 * 1873 * 3419876231 := by norm_num
private lemma prime_12810856361327_pow : (5 : ZMod 12810856361327) ^ (12810856361327 - 1) = 1 := by
  reduce_mod_char
private lemma prime_12810856361327_div_2 : (5 : ZMod 12810856361327) ^ ((12810856361327 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12810856361327_div_1873 : (5 : ZMod 12810856361327) ^ ((12810856361327 - 1) / 1873) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12810856361327_div_3419876231 : (5 : ZMod 12810856361327) ^ ((12810856361327 - 1) / 3419876231) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12810856361327 : Nat.Prime 12810856361327 := by
  refine lucas_primality 12810856361327 (5 : ZMod 12810856361327) prime_12810856361327_pow ?_
  intro q hq hqd
  rw [prime_12810856361327_sub1] at hqd
  have : q ∣ [2, 1873, 3419876231].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_12810856361327_div_2
  · have : q = 1873 := (Nat.prime_dvd_prime_iff_eq hq prime_1873).mp hdf
    subst this; exact prime_12810856361327_div_1873
  · have : q = 3419876231 := (Nat.prime_dvd_prime_iff_eq hq prime_3419876231).mp hdf
    subst this; exact prime_12810856361327_div_3419876231
private lemma prime_A_25_sub1 : (28430288006173163519 - 1 : ℕ) = 2 * 409 * 2713 * 12810856361327 := by norm_num
private lemma prime_A_25_pow : (13 : ZMod 28430288006173163519) ^ (28430288006173163519 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_25_div_2 : (13 : ZMod 28430288006173163519) ^ ((28430288006173163519 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_25_div_409 : (13 : ZMod 28430288006173163519) ^ ((28430288006173163519 - 1) / 409) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_25_div_2713 : (13 : ZMod 28430288006173163519) ^ ((28430288006173163519 - 1) / 2713) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_25_div_12810856361327 : (13 : ZMod 28430288006173163519) ^ ((28430288006173163519 - 1) / 12810856361327) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_25 : Nat.Prime 28430288006173163519 := by
  refine lucas_primality 28430288006173163519 (13 : ZMod 28430288006173163519) prime_A_25_pow ?_
  intro q hq hqd
  rw [prime_A_25_sub1] at hqd
  have : q ∣ [2, 409, 2713, 12810856361327].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_25_div_2
  · have : q = 409 := (Nat.prime_dvd_prime_iff_eq hq prime_409).mp hdf
    subst this; exact prime_A_25_div_409
  · have : q = 2713 := (Nat.prime_dvd_prime_iff_eq hq prime_2713).mp hdf
    subst this; exact prime_A_25_div_2713
  · have : q = 12810856361327 := (Nat.prime_dvd_prime_iff_eq hq prime_12810856361327).mp hdf
    subst this; exact prime_A_25_div_12810856361327
private lemma prime_38329 : Nat.Prime 38329 := by norm_num
private lemma prime_92107 : Nat.Prime 92107 := by norm_num
private lemma prime_56485907249_sub1 : (56485907249 - 1 : ℕ) = 2 ^ 4 * 38329 * 92107 := by norm_num
private lemma prime_56485907249_pow : (3 : ZMod 56485907249) ^ (56485907249 - 1) = 1 := by
  reduce_mod_char
private lemma prime_56485907249_div_2 : (3 : ZMod 56485907249) ^ ((56485907249 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_56485907249_div_38329 : (3 : ZMod 56485907249) ^ ((56485907249 - 1) / 38329) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_56485907249_div_92107 : (3 : ZMod 56485907249) ^ ((56485907249 - 1) / 92107) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_56485907249 : Nat.Prime 56485907249 := by
  refine lucas_primality 56485907249 (3 : ZMod 56485907249) prime_56485907249_pow ?_
  intro q hq hqd
  rw [prime_56485907249_sub1] at hqd
  have : q ∣ [2 ^ 4, 38329, 92107].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_56485907249_div_2
  · have : q = 38329 := (Nat.prime_dvd_prime_iff_eq hq prime_38329).mp hdf
    subst this; exact prime_56485907249_div_38329
  · have : q = 92107 := (Nat.prime_dvd_prime_iff_eq hq prime_92107).mp hdf
    subst this; exact prime_56485907249_div_92107
private lemma prime_B_25_sub1 : (28430288006173163521 - 1 : ℕ) = 2 ^ 25 * 3 * 5 * 56485907249 := by norm_num
private lemma prime_B_25_pow : (14 : ZMod 28430288006173163521) ^ (28430288006173163521 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_25_div_2 : (14 : ZMod 28430288006173163521) ^ ((28430288006173163521 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_25_div_3 : (14 : ZMod 28430288006173163521) ^ ((28430288006173163521 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_25_div_5 : (14 : ZMod 28430288006173163521) ^ ((28430288006173163521 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_25_div_56485907249 : (14 : ZMod 28430288006173163521) ^ ((28430288006173163521 - 1) / 56485907249) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_25 : Nat.Prime 28430288006173163521 := by
  refine lucas_primality 28430288006173163521 (14 : ZMod 28430288006173163521) prime_B_25_pow ?_
  intro q hq hqd
  rw [prime_B_25_sub1] at hqd
  have : q ∣ [2 ^ 25, 3, 5, 56485907249].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_25_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_25_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_25_div_5
  · have : q = 56485907249 := (Nat.prime_dvd_prime_iff_eq hq prime_56485907249).mp hdf
    subst this; exact prime_B_25_div_56485907249
private lemma pair_25 :
    Nat.Prime ((3 ^ 25 - 708) * (2 ^ 25) - 1) ∧
    Nat.Prime ((3 ^ 25 - 708) * (2 ^ 25) + 1) := by
  constructor
  · convert prime_A_25
  · convert prime_B_25
