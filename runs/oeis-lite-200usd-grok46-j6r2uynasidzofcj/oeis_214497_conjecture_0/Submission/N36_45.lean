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

/- Pair for n = 36 -/
private lemma prime_433 : Nat.Prime 433 := by norm_num
private lemma prime_29 : Nat.Prime 29 := by norm_num
private lemma prime_113 : Nat.Prime 113 := by norm_num
private lemma prime_139 : Nat.Prime 139 := by norm_num
private lemma prime_322591 : Nat.Prime 322591 := by norm_num
private lemma prime_47651801 : Nat.Prime 47651801 := by norm_num
private lemma prime_1429554031_sub1 : (1429554031 - 1 : ℕ) = 2 * 3 * 5 * 47651801 := by norm_num
private lemma prime_1429554031_pow : (15 : ZMod 1429554031) ^ (1429554031 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1429554031_div_2 : (15 : ZMod 1429554031) ^ ((1429554031 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1429554031_div_3 : (15 : ZMod 1429554031) ^ ((1429554031 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1429554031_div_5 : (15 : ZMod 1429554031) ^ ((1429554031 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1429554031_div_47651801 : (15 : ZMod 1429554031) ^ ((1429554031 - 1) / 47651801) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1429554031 : Nat.Prime 1429554031 := by
  refine lucas_primality 1429554031 (15 : ZMod 1429554031) prime_1429554031_pow ?_
  intro q hq hqd
  rw [prime_1429554031_sub1] at hqd
  have : q ∣ [2, 3, 5, 47651801].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1429554031_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1429554031_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_1429554031_div_5
  · have : q = 47651801 := (Nat.prime_dvd_prime_iff_eq hq prime_47651801).mp hdf
    subst this; exact prime_1429554031_div_47651801
private lemma prime_8214083617496609099899_sub1 : (8214083617496609099899 - 1 : ℕ) = 2 * 3 ^ 4 * 7 * 113 * 139 * 322591 * 1429554031 := by norm_num
private lemma prime_8214083617496609099899_pow : (3 : ZMod 8214083617496609099899) ^ (8214083617496609099899 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8214083617496609099899_div_2 : (3 : ZMod 8214083617496609099899) ^ ((8214083617496609099899 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8214083617496609099899_div_3 : (3 : ZMod 8214083617496609099899) ^ ((8214083617496609099899 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8214083617496609099899_div_7 : (3 : ZMod 8214083617496609099899) ^ ((8214083617496609099899 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8214083617496609099899_div_113 : (3 : ZMod 8214083617496609099899) ^ ((8214083617496609099899 - 1) / 113) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8214083617496609099899_div_139 : (3 : ZMod 8214083617496609099899) ^ ((8214083617496609099899 - 1) / 139) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8214083617496609099899_div_322591 : (3 : ZMod 8214083617496609099899) ^ ((8214083617496609099899 - 1) / 322591) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8214083617496609099899_div_1429554031 : (3 : ZMod 8214083617496609099899) ^ ((8214083617496609099899 - 1) / 1429554031) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8214083617496609099899 : Nat.Prime 8214083617496609099899 := by
  refine lucas_primality 8214083617496609099899 (3 : ZMod 8214083617496609099899) prime_8214083617496609099899_pow ?_
  intro q hq hqd
  rw [prime_8214083617496609099899_sub1] at hqd
  have : q ∣ [2, 3 ^ 4, 7, 113, 139, 322591, 1429554031].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_8214083617496609099899_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_8214083617496609099899_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_8214083617496609099899_div_7
  · have : q = 113 := (Nat.prime_dvd_prime_iff_eq hq prime_113).mp hdf
    subst this; exact prime_8214083617496609099899_div_113
  · have : q = 139 := (Nat.prime_dvd_prime_iff_eq hq prime_139).mp hdf
    subst this; exact prime_8214083617496609099899_div_139
  · have : q = 322591 := (Nat.prime_dvd_prime_iff_eq hq prime_322591).mp hdf
    subst this; exact prime_8214083617496609099899_div_322591
  · have : q = 1429554031 := (Nat.prime_dvd_prime_iff_eq hq prime_1429554031).mp hdf
    subst this; exact prime_8214083617496609099899_div_1429554031
private lemma prime_11910421245370083194853551_sub1 : (11910421245370083194853551 - 1 : ℕ) = 2 * 5 ^ 2 * 29 * 8214083617496609099899 := by norm_num
private lemma prime_11910421245370083194853551_pow : (13 : ZMod 11910421245370083194853551) ^ (11910421245370083194853551 - 1) = 1 := by
  reduce_mod_char
private lemma prime_11910421245370083194853551_div_2 : (13 : ZMod 11910421245370083194853551) ^ ((11910421245370083194853551 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11910421245370083194853551_div_5 : (13 : ZMod 11910421245370083194853551) ^ ((11910421245370083194853551 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11910421245370083194853551_div_29 : (13 : ZMod 11910421245370083194853551) ^ ((11910421245370083194853551 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11910421245370083194853551_div_8214083617496609099899 : (13 : ZMod 11910421245370083194853551) ^ ((11910421245370083194853551 - 1) / 8214083617496609099899) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11910421245370083194853551 : Nat.Prime 11910421245370083194853551 := by
  refine lucas_primality 11910421245370083194853551 (13 : ZMod 11910421245370083194853551) prime_11910421245370083194853551_pow ?_
  intro q hq hqd
  rw [prime_11910421245370083194853551_sub1] at hqd
  have : q ∣ [2, 5 ^ 2, 29, 8214083617496609099899].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_11910421245370083194853551_div_2
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_11910421245370083194853551_div_5
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_11910421245370083194853551_div_29
  · have : q = 8214083617496609099899 := (Nat.prime_dvd_prime_iff_eq hq prime_8214083617496609099899).mp hdf
    subst this; exact prime_11910421245370083194853551_div_8214083617496609099899
private lemma prime_A_36_sub1 : (10314424798490492046743175167 - 1 : ℕ) = 2 * 433 * 11910421245370083194853551 := by norm_num
private lemma prime_A_36_pow : (5 : ZMod 10314424798490492046743175167) ^ (10314424798490492046743175167 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_36_div_2 : (5 : ZMod 10314424798490492046743175167) ^ ((10314424798490492046743175167 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_36_div_433 : (5 : ZMod 10314424798490492046743175167) ^ ((10314424798490492046743175167 - 1) / 433) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_36_div_11910421245370083194853551 : (5 : ZMod 10314424798490492046743175167) ^ ((10314424798490492046743175167 - 1) / 11910421245370083194853551) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_36 : Nat.Prime 10314424798490492046743175167 := by
  refine lucas_primality 10314424798490492046743175167 (5 : ZMod 10314424798490492046743175167) prime_A_36_pow ?_
  intro q hq hqd
  rw [prime_A_36_sub1] at hqd
  have : q ∣ [2, 433, 11910421245370083194853551].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_36_div_2
  · have : q = 433 := (Nat.prime_dvd_prime_iff_eq hq prime_433).mp hdf
    subst this; exact prime_A_36_div_433
  · have : q = 11910421245370083194853551 := (Nat.prime_dvd_prime_iff_eq hq prime_11910421245370083194853551).mp hdf
    subst this; exact prime_A_36_div_11910421245370083194853551
private lemma prime_131 : Nat.Prime 131 := by norm_num
private lemma prime_1822021 : Nat.Prime 1822021 := by norm_num
private lemma prime_26201687 : Nat.Prime 26201687 := by norm_num
private lemma prime_B_36_sub1 : (10314424798490492046743175169 - 1 : ℕ) = 2 ^ 39 * 3 * 131 * 1822021 * 26201687 := by norm_num
private lemma prime_B_36_pow : (11 : ZMod 10314424798490492046743175169) ^ (10314424798490492046743175169 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_36_div_2 : (11 : ZMod 10314424798490492046743175169) ^ ((10314424798490492046743175169 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_36_div_3 : (11 : ZMod 10314424798490492046743175169) ^ ((10314424798490492046743175169 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_36_div_131 : (11 : ZMod 10314424798490492046743175169) ^ ((10314424798490492046743175169 - 1) / 131) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_36_div_1822021 : (11 : ZMod 10314424798490492046743175169) ^ ((10314424798490492046743175169 - 1) / 1822021) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_36_div_26201687 : (11 : ZMod 10314424798490492046743175169) ^ ((10314424798490492046743175169 - 1) / 26201687) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_36 : Nat.Prime 10314424798490492046743175169 := by
  refine lucas_primality 10314424798490492046743175169 (11 : ZMod 10314424798490492046743175169) prime_B_36_pow ?_
  intro q hq hqd
  rw [prime_B_36_sub1] at hqd
  have : q ∣ [2 ^ 39, 3, 131, 1822021, 26201687].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_36_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_36_div_3
  · have : q = 131 := (Nat.prime_dvd_prime_iff_eq hq prime_131).mp hdf
    subst this; exact prime_B_36_div_131
  · have : q = 1822021 := (Nat.prime_dvd_prime_iff_eq hq prime_1822021).mp hdf
    subst this; exact prime_B_36_div_1822021
  · have : q = 26201687 := (Nat.prime_dvd_prime_iff_eq hq prime_26201687).mp hdf
    subst this; exact prime_B_36_div_26201687
private lemma pair_36 :
    Nat.Prime ((3 ^ 36 - 633) * (2 ^ 36) - 1) ∧
    Nat.Prime ((3 ^ 36 - 633) * (2 ^ 36) + 1) := by
  constructor
  · convert prime_A_36
  · convert prime_B_36

/- Pair for n = 37 -/
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_1759 : Nat.Prime 1759 := by norm_num
private lemma prime_3767 : Nat.Prime 3767 := by norm_num
private lemma prime_301319 : Nat.Prime 301319 := by norm_num
private lemma prime_4759 : Nat.Prime 4759 := by norm_num
private lemma prime_7723 : Nat.Prime 7723 := by norm_num
private lemma prime_11491 : Nat.Prime 11491 := by norm_num
private lemma prime_49342216109_sub1 : (49342216109 - 1 : ℕ) = 2 ^ 2 * 139 * 7723 * 11491 := by norm_num
private lemma prime_49342216109_pow : (2 : ZMod 49342216109) ^ (49342216109 - 1) = 1 := by
  reduce_mod_char
private lemma prime_49342216109_div_2 : (2 : ZMod 49342216109) ^ ((49342216109 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_49342216109_div_139 : (2 : ZMod 49342216109) ^ ((49342216109 - 1) / 139) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_49342216109_div_7723 : (2 : ZMod 49342216109) ^ ((49342216109 - 1) / 7723) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_49342216109_div_11491 : (2 : ZMod 49342216109) ^ ((49342216109 - 1) / 11491) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_49342216109 : Nat.Prime 49342216109 := by
  refine lucas_primality 49342216109 (2 : ZMod 49342216109) prime_49342216109_pow ?_
  intro q hq hqd
  rw [prime_49342216109_sub1] at hqd
  have : q ∣ [2 ^ 2, 139, 7723, 11491].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_49342216109_div_2
  · have : q = 139 := (Nat.prime_dvd_prime_iff_eq hq prime_139).mp hdf
    subst this; exact prime_49342216109_div_139
  · have : q = 7723 := (Nat.prime_dvd_prime_iff_eq hq prime_7723).mp hdf
    subst this; exact prime_49342216109_div_7723
  · have : q = 11491 := (Nat.prime_dvd_prime_iff_eq hq prime_11491).mp hdf
    subst this; exact prime_49342216109_div_11491
private lemma prime_1408917638776387_sub1 : (1408917638776387 - 1 : ℕ) = 2 * 3 * 4759 * 49342216109 := by norm_num
private lemma prime_1408917638776387_pow : (2 : ZMod 1408917638776387) ^ (1408917638776387 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1408917638776387_div_2 : (2 : ZMod 1408917638776387) ^ ((1408917638776387 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1408917638776387_div_3 : (2 : ZMod 1408917638776387) ^ ((1408917638776387 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1408917638776387_div_4759 : (2 : ZMod 1408917638776387) ^ ((1408917638776387 - 1) / 4759) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1408917638776387_div_49342216109 : (2 : ZMod 1408917638776387) ^ ((1408917638776387 - 1) / 49342216109) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1408917638776387 : Nat.Prime 1408917638776387 := by
  refine lucas_primality 1408917638776387 (2 : ZMod 1408917638776387) prime_1408917638776387_pow ?_
  intro q hq hqd
  rw [prime_1408917638776387_sub1] at hqd
  have : q ∣ [2, 3, 4759, 49342216109].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1408917638776387_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1408917638776387_div_3
  · have : q = 4759 := (Nat.prime_dvd_prime_iff_eq hq prime_4759).mp hdf
    subst this; exact prime_1408917638776387_div_4759
  · have : q = 49342216109 := (Nat.prime_dvd_prime_iff_eq hq prime_49342216109).mp hdf
    subst this; exact prime_1408917638776387_div_49342216109
private lemma prime_A_37_sub1 : (61886548790943184002534604799 - 1 : ℕ) = 2 * 11 * 1759 * 3767 * 301319 * 1408917638776387 := by norm_num
private lemma prime_A_37_pow : (11 : ZMod 61886548790943184002534604799) ^ (61886548790943184002534604799 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_37_div_2 : (11 : ZMod 61886548790943184002534604799) ^ ((61886548790943184002534604799 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_37_div_11 : (11 : ZMod 61886548790943184002534604799) ^ ((61886548790943184002534604799 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_37_div_1759 : (11 : ZMod 61886548790943184002534604799) ^ ((61886548790943184002534604799 - 1) / 1759) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_37_div_3767 : (11 : ZMod 61886548790943184002534604799) ^ ((61886548790943184002534604799 - 1) / 3767) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_37_div_301319 : (11 : ZMod 61886548790943184002534604799) ^ ((61886548790943184002534604799 - 1) / 301319) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_37_div_1408917638776387 : (11 : ZMod 61886548790943184002534604799) ^ ((61886548790943184002534604799 - 1) / 1408917638776387) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_37 : Nat.Prime 61886548790943184002534604799 := by
  refine lucas_primality 61886548790943184002534604799 (11 : ZMod 61886548790943184002534604799) prime_A_37_pow ?_
  intro q hq hqd
  rw [prime_A_37_sub1] at hqd
  have : q ∣ [2, 11, 1759, 3767, 301319, 1408917638776387].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_37_div_2
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_A_37_div_11
  · have : q = 1759 := (Nat.prime_dvd_prime_iff_eq hq prime_1759).mp hdf
    subst this; exact prime_A_37_div_1759
  · have : q = 3767 := (Nat.prime_dvd_prime_iff_eq hq prime_3767).mp hdf
    subst this; exact prime_A_37_div_3767
  · have : q = 301319 := (Nat.prime_dvd_prime_iff_eq hq prime_301319).mp hdf
    subst this; exact prime_A_37_div_301319
  · have : q = 1408917638776387 := (Nat.prime_dvd_prime_iff_eq hq prime_1408917638776387).mp hdf
    subst this; exact prime_A_37_div_1408917638776387
private lemma prime_883 : Nat.Prime 883 := by norm_num
private lemma prime_2371 : Nat.Prime 2371 := by norm_num
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_79087 : Nat.Prime 79087 := by norm_num
private lemma prime_204835331_sub1 : (204835331 - 1 : ℕ) = 2 * 5 * 7 * 37 * 79087 := by norm_num
private lemma prime_204835331_pow : (2 : ZMod 204835331) ^ (204835331 - 1) = 1 := by
  reduce_mod_char
private lemma prime_204835331_div_2 : (2 : ZMod 204835331) ^ ((204835331 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_204835331_div_5 : (2 : ZMod 204835331) ^ ((204835331 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_204835331_div_7 : (2 : ZMod 204835331) ^ ((204835331 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_204835331_div_37 : (2 : ZMod 204835331) ^ ((204835331 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_204835331_div_79087 : (2 : ZMod 204835331) ^ ((204835331 - 1) / 79087) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_204835331 : Nat.Prime 204835331 := by
  refine lucas_primality 204835331 (2 : ZMod 204835331) prime_204835331_pow ?_
  intro q hq hqd
  rw [prime_204835331_sub1] at hqd
  have : q ∣ [2, 5, 7, 37, 79087].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_204835331_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_204835331_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_204835331_div_7
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_204835331_div_37
  · have : q = 79087 := (Nat.prime_dvd_prime_iff_eq hq prime_79087).mp hdf
    subst this; exact prime_204835331_div_79087
private lemma prime_B_37_sub1 : (61886548790943184002534604801 - 1 : ℕ) = 2 ^ 38 * 3 * 5 ^ 2 * 7 * 883 * 2371 * 204835331 := by norm_num
private lemma prime_B_37_pow : (19 : ZMod 61886548790943184002534604801) ^ (61886548790943184002534604801 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_37_div_2 : (19 : ZMod 61886548790943184002534604801) ^ ((61886548790943184002534604801 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_37_div_3 : (19 : ZMod 61886548790943184002534604801) ^ ((61886548790943184002534604801 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_37_div_5 : (19 : ZMod 61886548790943184002534604801) ^ ((61886548790943184002534604801 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_37_div_7 : (19 : ZMod 61886548790943184002534604801) ^ ((61886548790943184002534604801 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_37_div_883 : (19 : ZMod 61886548790943184002534604801) ^ ((61886548790943184002534604801 - 1) / 883) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_37_div_2371 : (19 : ZMod 61886548790943184002534604801) ^ ((61886548790943184002534604801 - 1) / 2371) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_37_div_204835331 : (19 : ZMod 61886548790943184002534604801) ^ ((61886548790943184002534604801 - 1) / 204835331) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_37 : Nat.Prime 61886548790943184002534604801 := by
  refine lucas_primality 61886548790943184002534604801 (19 : ZMod 61886548790943184002534604801) prime_B_37_pow ?_
  intro q hq hqd
  rw [prime_B_37_sub1] at hqd
  have : q ∣ [2 ^ 38, 3, 5 ^ 2, 7, 883, 2371, 204835331].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_37_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_37_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_B_37_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_B_37_div_7
  · have : q = 883 := (Nat.prime_dvd_prime_iff_eq hq prime_883).mp hdf
    subst this; exact prime_B_37_div_883
  · have : q = 2371 := (Nat.prime_dvd_prime_iff_eq hq prime_2371).mp hdf
    subst this; exact prime_B_37_div_2371
  · have : q = 204835331 := (Nat.prime_dvd_prime_iff_eq hq prime_204835331).mp hdf
    subst this; exact prime_B_37_div_204835331
private lemma pair_37 :
    Nat.Prime ((3 ^ 37 - 213) * (2 ^ 37) - 1) ∧
    Nat.Prime ((3 ^ 37 - 213) * (2 ^ 37) + 1) := by
  constructor
  · convert prime_A_37
  · convert prime_B_37

/- Pair for n = 38 -/
private lemma prime_157 : Nat.Prime 157 := by norm_num
private lemma prime_74077 : Nat.Prime 74077 := by norm_num
private lemma prime_1449017 : Nat.Prime 1449017 := by norm_num
private lemma prime_37123351 : Nat.Prime 37123351 := by norm_num
private lemma prime_59353157 : Nat.Prime 59353157 := by norm_num
private lemma prime_A_38_sub1 : (371319292745658519349899558911 - 1 : ℕ) = 2 * 5 * 157 * 74077 * 1449017 * 37123351 * 59353157 := by norm_num
private lemma prime_A_38_pow : (13 : ZMod 371319292745658519349899558911) ^ (371319292745658519349899558911 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_38_div_2 : (13 : ZMod 371319292745658519349899558911) ^ ((371319292745658519349899558911 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_38_div_5 : (13 : ZMod 371319292745658519349899558911) ^ ((371319292745658519349899558911 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_38_div_157 : (13 : ZMod 371319292745658519349899558911) ^ ((371319292745658519349899558911 - 1) / 157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_38_div_74077 : (13 : ZMod 371319292745658519349899558911) ^ ((371319292745658519349899558911 - 1) / 74077) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_38_div_1449017 : (13 : ZMod 371319292745658519349899558911) ^ ((371319292745658519349899558911 - 1) / 1449017) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_38_div_37123351 : (13 : ZMod 371319292745658519349899558911) ^ ((371319292745658519349899558911 - 1) / 37123351) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_38_div_59353157 : (13 : ZMod 371319292745658519349899558911) ^ ((371319292745658519349899558911 - 1) / 59353157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_38 : Nat.Prime 371319292745658519349899558911 := by
  refine lucas_primality 371319292745658519349899558911 (13 : ZMod 371319292745658519349899558911) prime_A_38_pow ?_
  intro q hq hqd
  rw [prime_A_38_sub1] at hqd
  have : q ∣ [2, 5, 157, 74077, 1449017, 37123351, 59353157].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_38_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_38_div_5
  · have : q = 157 := (Nat.prime_dvd_prime_iff_eq hq prime_157).mp hdf
    subst this; exact prime_A_38_div_157
  · have : q = 74077 := (Nat.prime_dvd_prime_iff_eq hq prime_74077).mp hdf
    subst this; exact prime_A_38_div_74077
  · have : q = 1449017 := (Nat.prime_dvd_prime_iff_eq hq prime_1449017).mp hdf
    subst this; exact prime_A_38_div_1449017
  · have : q = 37123351 := (Nat.prime_dvd_prime_iff_eq hq prime_37123351).mp hdf
    subst this; exact prime_A_38_div_37123351
  · have : q = 59353157 := (Nat.prime_dvd_prime_iff_eq hq prime_59353157).mp hdf
    subst this; exact prime_A_38_div_59353157
private lemma prime_63395401 : Nat.Prime 63395401 := by norm_num
private lemma prime_21523591 : Nat.Prime 21523591 := by norm_num
private lemma prime_645707731_sub1 : (645707731 - 1 : ℕ) = 2 * 3 * 5 * 21523591 := by norm_num
private lemma prime_645707731_pow : (2 : ZMod 645707731) ^ (645707731 - 1) = 1 := by
  reduce_mod_char
private lemma prime_645707731_div_2 : (2 : ZMod 645707731) ^ ((645707731 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_645707731_div_3 : (2 : ZMod 645707731) ^ ((645707731 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_645707731_div_5 : (2 : ZMod 645707731) ^ ((645707731 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_645707731_div_21523591 : (2 : ZMod 645707731) ^ ((645707731 - 1) / 21523591) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_645707731 : Nat.Prime 645707731 := by
  refine lucas_primality 645707731 (2 : ZMod 645707731) prime_645707731_pow ?_
  intro q hq hqd
  rw [prime_645707731_sub1] at hqd
  have : q ∣ [2, 3, 5, 21523591].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_645707731_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_645707731_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_645707731_div_5
  · have : q = 21523591 := (Nat.prime_dvd_prime_iff_eq hq prime_21523591).mp hdf
    subst this; exact prime_645707731_div_21523591
private lemma prime_B_38_sub1 : (371319292745658519349899558913 - 1 : ℕ) = 2 ^ 38 * 3 * 11 * 63395401 * 645707731 := by norm_num
private lemma prime_B_38_pow : (7 : ZMod 371319292745658519349899558913) ^ (371319292745658519349899558913 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_38_div_2 : (7 : ZMod 371319292745658519349899558913) ^ ((371319292745658519349899558913 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_38_div_3 : (7 : ZMod 371319292745658519349899558913) ^ ((371319292745658519349899558913 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_38_div_11 : (7 : ZMod 371319292745658519349899558913) ^ ((371319292745658519349899558913 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_38_div_63395401 : (7 : ZMod 371319292745658519349899558913) ^ ((371319292745658519349899558913 - 1) / 63395401) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_38_div_645707731 : (7 : ZMod 371319292745658519349899558913) ^ ((371319292745658519349899558913 - 1) / 645707731) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_38 : Nat.Prime 371319292745658519349899558913 := by
  refine lucas_primality 371319292745658519349899558913 (7 : ZMod 371319292745658519349899558913) prime_B_38_pow ?_
  intro q hq hqd
  rw [prime_B_38_sub1] at hqd
  have : q ∣ [2 ^ 38, 3, 11, 63395401, 645707731].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_38_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_38_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_38_div_11
  · have : q = 63395401 := (Nat.prime_dvd_prime_iff_eq hq prime_63395401).mp hdf
    subst this; exact prime_B_38_div_63395401
  · have : q = 645707731 := (Nat.prime_dvd_prime_iff_eq hq prime_645707731).mp hdf
    subst this; exact prime_B_38_div_645707731
private lemma pair_38 :
    Nat.Prime ((3 ^ 38 - 2766) * (2 ^ 38) - 1) ∧
    Nat.Prime ((3 ^ 38 - 2766) * (2 ^ 38) + 1) := by
  constructor
  · convert prime_A_38
  · convert prime_B_38

/- Pair for n = 39 -/
private lemma prime_1103 : Nat.Prime 1103 := by norm_num
private lemma prime_91097 : Nat.Prime 91097 := by norm_num
private lemma prime_4481 : Nat.Prime 4481 := by norm_num
private lemma prime_14879 : Nat.Prime 14879 := by norm_num
private lemma prime_666727991_sub1 : (666727991 - 1 : ℕ) = 2 * 5 * 4481 * 14879 := by norm_num
private lemma prime_666727991_pow : (13 : ZMod 666727991) ^ (666727991 - 1) = 1 := by
  reduce_mod_char
private lemma prime_666727991_div_2 : (13 : ZMod 666727991) ^ ((666727991 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_666727991_div_5 : (13 : ZMod 666727991) ^ ((666727991 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_666727991_div_4481 : (13 : ZMod 666727991) ^ ((666727991 - 1) / 4481) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_666727991_div_14879 : (13 : ZMod 666727991) ^ ((666727991 - 1) / 14879) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_666727991 : Nat.Prime 666727991 := by
  refine lucas_primality 666727991 (13 : ZMod 666727991) prime_666727991_pow ?_
  intro q hq hqd
  rw [prime_666727991_sub1] at hqd
  have : q ∣ [2, 5, 4481, 14879].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_666727991_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_666727991_div_5
  · have : q = 4481 := (Nat.prime_dvd_prime_iff_eq hq prime_4481).mp hdf
    subst this; exact prime_666727991_div_4481
  · have : q = 14879 := (Nat.prime_dvd_prime_iff_eq hq prime_14879).mp hdf
    subst this; exact prime_666727991_div_14879
private lemma prime_41 : Nat.Prime 41 := by norm_num
private lemma prime_257 : Nat.Prime 257 := by norm_num
private lemma prime_797 : Nat.Prime 797 := by norm_num
private lemma prime_251939671_sub1 : (251939671 - 1 : ℕ) = 2 * 3 * 5 * 41 * 257 * 797 := by norm_num
private lemma prime_251939671_pow : (3 : ZMod 251939671) ^ (251939671 - 1) = 1 := by
  reduce_mod_char
private lemma prime_251939671_div_2 : (3 : ZMod 251939671) ^ ((251939671 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251939671_div_3 : (3 : ZMod 251939671) ^ ((251939671 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251939671_div_5 : (3 : ZMod 251939671) ^ ((251939671 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251939671_div_41 : (3 : ZMod 251939671) ^ ((251939671 - 1) / 41) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251939671_div_257 : (3 : ZMod 251939671) ^ ((251939671 - 1) / 257) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251939671_div_797 : (3 : ZMod 251939671) ^ ((251939671 - 1) / 797) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251939671 : Nat.Prime 251939671 := by
  refine lucas_primality 251939671 (3 : ZMod 251939671) prime_251939671_pow ?_
  intro q hq hqd
  rw [prime_251939671_sub1] at hqd
  have : q ∣ [2, 3, 5, 41, 257, 797].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_251939671_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_251939671_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_251939671_div_5
  · have : q = 41 := (Nat.prime_dvd_prime_iff_eq hq prime_41).mp hdf
    subst this; exact prime_251939671_div_41
  · have : q = 257 := (Nat.prime_dvd_prime_iff_eq hq prime_257).mp hdf
    subst this; exact prime_251939671_div_257
  · have : q = 797 := (Nat.prime_dvd_prime_iff_eq hq prime_797).mp hdf
    subst this; exact prime_251939671_div_797
private lemma prime_12093104209_sub1 : (12093104209 - 1 : ℕ) = 2 ^ 4 * 3 * 251939671 := by norm_num
private lemma prime_12093104209_pow : (11 : ZMod 12093104209) ^ (12093104209 - 1) = 1 := by
  reduce_mod_char
private lemma prime_12093104209_div_2 : (11 : ZMod 12093104209) ^ ((12093104209 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12093104209_div_3 : (11 : ZMod 12093104209) ^ ((12093104209 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12093104209_div_251939671 : (11 : ZMod 12093104209) ^ ((12093104209 - 1) / 251939671) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_12093104209 : Nat.Prime 12093104209 := by
  refine lucas_primality 12093104209 (11 : ZMod 12093104209) prime_12093104209_pow ?_
  intro q hq hqd
  rw [prime_12093104209_sub1] at hqd
  have : q ∣ [2 ^ 4, 3, 251939671].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_12093104209_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_12093104209_div_3
  · have : q = 251939671 := (Nat.prime_dvd_prime_iff_eq hq prime_251939671).mp hdf
    subst this; exact prime_12093104209_div_251939671
private lemma prime_A_39_sub1 : (2227915756473955478411780554751 - 1 : ℕ) = 2 * 5 ^ 3 * 11 * 1103 * 91097 * 666727991 * 12093104209 := by norm_num
private lemma prime_A_39_pow : (11 : ZMod 2227915756473955478411780554751) ^ (2227915756473955478411780554751 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_39_div_2 : (11 : ZMod 2227915756473955478411780554751) ^ ((2227915756473955478411780554751 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_39_div_5 : (11 : ZMod 2227915756473955478411780554751) ^ ((2227915756473955478411780554751 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_39_div_11 : (11 : ZMod 2227915756473955478411780554751) ^ ((2227915756473955478411780554751 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_39_div_1103 : (11 : ZMod 2227915756473955478411780554751) ^ ((2227915756473955478411780554751 - 1) / 1103) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_39_div_91097 : (11 : ZMod 2227915756473955478411780554751) ^ ((2227915756473955478411780554751 - 1) / 91097) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_39_div_666727991 : (11 : ZMod 2227915756473955478411780554751) ^ ((2227915756473955478411780554751 - 1) / 666727991) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_39_div_12093104209 : (11 : ZMod 2227915756473955478411780554751) ^ ((2227915756473955478411780554751 - 1) / 12093104209) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_39 : Nat.Prime 2227915756473955478411780554751 := by
  refine lucas_primality 2227915756473955478411780554751 (11 : ZMod 2227915756473955478411780554751) prime_A_39_pow ?_
  intro q hq hqd
  rw [prime_A_39_sub1] at hqd
  have : q ∣ [2, 5 ^ 3, 11, 1103, 91097, 666727991, 12093104209].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_39_div_2
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_A_39_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_A_39_div_11
  · have : q = 1103 := (Nat.prime_dvd_prime_iff_eq hq prime_1103).mp hdf
    subst this; exact prime_A_39_div_1103
  · have : q = 91097 := (Nat.prime_dvd_prime_iff_eq hq prime_91097).mp hdf
    subst this; exact prime_A_39_div_91097
  · have : q = 666727991 := (Nat.prime_dvd_prime_iff_eq hq prime_666727991).mp hdf
    subst this; exact prime_A_39_div_666727991
  · have : q = 12093104209 := (Nat.prime_dvd_prime_iff_eq hq prime_12093104209).mp hdf
    subst this; exact prime_A_39_div_12093104209
private lemma prime_408959 : Nat.Prime 408959 := by norm_num
private lemma prime_72641341 : Nat.Prime 72641341 := by norm_num
private lemma prime_B_39_sub1 : (2227915756473955478411780554753 - 1 : ℕ) = 2 ^ 44 * 3 * 7 ^ 2 * 29 * 408959 * 72641341 := by norm_num
private lemma prime_B_39_pow : (15 : ZMod 2227915756473955478411780554753) ^ (2227915756473955478411780554753 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_39_div_2 : (15 : ZMod 2227915756473955478411780554753) ^ ((2227915756473955478411780554753 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_39_div_3 : (15 : ZMod 2227915756473955478411780554753) ^ ((2227915756473955478411780554753 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_39_div_7 : (15 : ZMod 2227915756473955478411780554753) ^ ((2227915756473955478411780554753 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_39_div_29 : (15 : ZMod 2227915756473955478411780554753) ^ ((2227915756473955478411780554753 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_39_div_408959 : (15 : ZMod 2227915756473955478411780554753) ^ ((2227915756473955478411780554753 - 1) / 408959) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_39_div_72641341 : (15 : ZMod 2227915756473955478411780554753) ^ ((2227915756473955478411780554753 - 1) / 72641341) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_39 : Nat.Prime 2227915756473955478411780554753 := by
  refine lucas_primality 2227915756473955478411780554753 (15 : ZMod 2227915756473955478411780554753) prime_B_39_pow ?_
  intro q hq hqd
  rw [prime_B_39_sub1] at hqd
  have : q ∣ [2 ^ 44, 3, 7 ^ 2, 29, 408959, 72641341].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_39_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_39_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_B_39_div_7
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_B_39_div_29
  · have : q = 408959 := (Nat.prime_dvd_prime_iff_eq hq prime_408959).mp hdf
    subst this; exact prime_B_39_div_408959
  · have : q = 72641341 := (Nat.prime_dvd_prime_iff_eq hq prime_72641341).mp hdf
    subst this; exact prime_B_39_div_72641341
private lemma pair_39 :
    Nat.Prime ((3 ^ 39 - 363) * (2 ^ 39) - 1) ∧
    Nat.Prime ((3 ^ 39 - 363) * (2 ^ 39) + 1) := by
  constructor
  · convert prime_A_39
  · convert prime_B_39

/- Pair for n = 40 -/
private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_7498459 : Nat.Prime 7498459 := by norm_num
private lemma prime_61 : Nat.Prime 61 := by norm_num
private lemma prime_7823 : Nat.Prime 7823 := by norm_num
private lemma prime_80209 : Nat.Prime 80209 := by norm_num
private lemma prime_126461 : Nat.Prime 126461 := by norm_num
private lemma prime_730318345129_sub1 : (730318345129 - 1 : ℕ) = 2 ^ 3 * 3 ^ 2 * 80209 * 126461 := by norm_num
private lemma prime_730318345129_pow : (17 : ZMod 730318345129) ^ (730318345129 - 1) = 1 := by
  reduce_mod_char
private lemma prime_730318345129_div_2 : (17 : ZMod 730318345129) ^ ((730318345129 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_730318345129_div_3 : (17 : ZMod 730318345129) ^ ((730318345129 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_730318345129_div_80209 : (17 : ZMod 730318345129) ^ ((730318345129 - 1) / 80209) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_730318345129_div_126461 : (17 : ZMod 730318345129) ^ ((730318345129 - 1) / 126461) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_730318345129 : Nat.Prime 730318345129 := by
  refine lucas_primality 730318345129 (17 : ZMod 730318345129) prime_730318345129_pow ?_
  intro q hq hqd
  rw [prime_730318345129_sub1] at hqd
  have : q ∣ [2 ^ 3, 3 ^ 2, 80209, 126461].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_730318345129_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_730318345129_div_3
  · have : q = 80209 := (Nat.prime_dvd_prime_iff_eq hq prime_80209).mp hdf
    subst this; exact prime_730318345129_div_80209
  · have : q = 126461 := (Nat.prime_dvd_prime_iff_eq hq prime_126461).mp hdf
    subst this; exact prime_730318345129_div_126461
private lemma prime_1624227999566897_sub1 : (1624227999566897 - 1 : ℕ) = 2 ^ 4 * 139 * 730318345129 := by norm_num
private lemma prime_1624227999566897_pow : (3 : ZMod 1624227999566897) ^ (1624227999566897 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1624227999566897_div_2 : (3 : ZMod 1624227999566897) ^ ((1624227999566897 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1624227999566897_div_139 : (3 : ZMod 1624227999566897) ^ ((1624227999566897 - 1) / 139) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1624227999566897_div_730318345129 : (3 : ZMod 1624227999566897) ^ ((1624227999566897 - 1) / 730318345129) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1624227999566897 : Nat.Prime 1624227999566897 := by
  refine lucas_primality 1624227999566897 (3 : ZMod 1624227999566897) prime_1624227999566897_pow ?_
  intro q hq hqd
  rw [prime_1624227999566897_sub1] at hqd
  have : q ∣ [2 ^ 4, 139, 730318345129].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1624227999566897_div_2
  · have : q = 139 := (Nat.prime_dvd_prime_iff_eq hq prime_139).mp hdf
    subst this; exact prime_1624227999566897_div_139
  · have : q = 730318345129 := (Nat.prime_dvd_prime_iff_eq hq prime_730318345129).mp hdf
    subst this; exact prime_1624227999566897_div_730318345129
private lemma prime_7750864740773219490911_sub1 : (7750864740773219490911 - 1 : ℕ) = 2 * 5 * 61 * 7823 * 1624227999566897 := by norm_num
private lemma prime_7750864740773219490911_pow : (17 : ZMod 7750864740773219490911) ^ (7750864740773219490911 - 1) = 1 := by
  reduce_mod_char
private lemma prime_7750864740773219490911_div_2 : (17 : ZMod 7750864740773219490911) ^ ((7750864740773219490911 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7750864740773219490911_div_5 : (17 : ZMod 7750864740773219490911) ^ ((7750864740773219490911 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7750864740773219490911_div_61 : (17 : ZMod 7750864740773219490911) ^ ((7750864740773219490911 - 1) / 61) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7750864740773219490911_div_7823 : (17 : ZMod 7750864740773219490911) ^ ((7750864740773219490911 - 1) / 7823) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7750864740773219490911_div_1624227999566897 : (17 : ZMod 7750864740773219490911) ^ ((7750864740773219490911 - 1) / 1624227999566897) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7750864740773219490911 : Nat.Prime 7750864740773219490911 := by
  refine lucas_primality 7750864740773219490911 (17 : ZMod 7750864740773219490911) prime_7750864740773219490911_pow ?_
  intro q hq hqd
  rw [prime_7750864740773219490911_sub1] at hqd
  have : q ∣ [2, 5, 61, 7823, 1624227999566897].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_7750864740773219490911_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_7750864740773219490911_div_5
  · have : q = 61 := (Nat.prime_dvd_prime_iff_eq hq prime_61).mp hdf
    subst this; exact prime_7750864740773219490911_div_61
  · have : q = 7823 := (Nat.prime_dvd_prime_iff_eq hq prime_7823).mp hdf
    subst this; exact prime_7750864740773219490911_div_7823
  · have : q = 1624227999566897 := (Nat.prime_dvd_prime_iff_eq hq prime_1624227999566897).mp hdf
    subst this; exact prime_7750864740773219490911_div_1624227999566897
private lemma prime_A_40_sub1 : (13367494538843731369637311414271 - 1 : ℕ) = 2 * 5 * 23 * 7498459 * 7750864740773219490911 := by norm_num
private lemma prime_A_40_pow : (23 : ZMod 13367494538843731369637311414271) ^ (13367494538843731369637311414271 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_40_div_2 : (23 : ZMod 13367494538843731369637311414271) ^ ((13367494538843731369637311414271 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_40_div_5 : (23 : ZMod 13367494538843731369637311414271) ^ ((13367494538843731369637311414271 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_40_div_23 : (23 : ZMod 13367494538843731369637311414271) ^ ((13367494538843731369637311414271 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_40_div_7498459 : (23 : ZMod 13367494538843731369637311414271) ^ ((13367494538843731369637311414271 - 1) / 7498459) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_40_div_7750864740773219490911 : (23 : ZMod 13367494538843731369637311414271) ^ ((13367494538843731369637311414271 - 1) / 7750864740773219490911) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_40 : Nat.Prime 13367494538843731369637311414271 := by
  refine lucas_primality 13367494538843731369637311414271 (23 : ZMod 13367494538843731369637311414271) prime_A_40_pow ?_
  intro q hq hqd
  rw [prime_A_40_sub1] at hqd
  have : q ∣ [2, 5, 23, 7498459, 7750864740773219490911].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_40_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_40_div_5
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_A_40_div_23
  · have : q = 7498459 := (Nat.prime_dvd_prime_iff_eq hq prime_7498459).mp hdf
    subst this; exact prime_A_40_div_7498459
  · have : q = 7750864740773219490911 := (Nat.prime_dvd_prime_iff_eq hq prime_7750864740773219490911).mp hdf
    subst this; exact prime_A_40_div_7750864740773219490911
private lemma prime_53 : Nat.Prime 53 := by norm_num
private lemma prime_2927 : Nat.Prime 2927 := by norm_num
private lemma prime_26573 : Nat.Prime 26573 := by norm_num
private lemma prime_12767299 : Nat.Prime 12767299 := by norm_num
private lemma prime_B_40_sub1 : (13367494538843731369637311414273 - 1 : ℕ) = 2 ^ 40 * 3 * 7 * 11 * 53 * 2927 * 26573 * 12767299 := by norm_num
private lemma prime_B_40_pow : (5 : ZMod 13367494538843731369637311414273) ^ (13367494538843731369637311414273 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_40_div_2 : (5 : ZMod 13367494538843731369637311414273) ^ ((13367494538843731369637311414273 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_40_div_3 : (5 : ZMod 13367494538843731369637311414273) ^ ((13367494538843731369637311414273 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_40_div_7 : (5 : ZMod 13367494538843731369637311414273) ^ ((13367494538843731369637311414273 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_40_div_11 : (5 : ZMod 13367494538843731369637311414273) ^ ((13367494538843731369637311414273 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_40_div_53 : (5 : ZMod 13367494538843731369637311414273) ^ ((13367494538843731369637311414273 - 1) / 53) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_40_div_2927 : (5 : ZMod 13367494538843731369637311414273) ^ ((13367494538843731369637311414273 - 1) / 2927) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_40_div_26573 : (5 : ZMod 13367494538843731369637311414273) ^ ((13367494538843731369637311414273 - 1) / 26573) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_40_div_12767299 : (5 : ZMod 13367494538843731369637311414273) ^ ((13367494538843731369637311414273 - 1) / 12767299) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_40 : Nat.Prime 13367494538843731369637311414273 := by
  refine lucas_primality 13367494538843731369637311414273 (5 : ZMod 13367494538843731369637311414273) prime_B_40_pow ?_
  intro q hq hqd
  rw [prime_B_40_sub1] at hqd
  have : q ∣ [2 ^ 40, 3, 7, 11, 53, 2927, 26573, 12767299].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_40_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_40_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_B_40_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_40_div_11
  · have : q = 53 := (Nat.prime_dvd_prime_iff_eq hq prime_53).mp hdf
    subst this; exact prime_B_40_div_53
  · have : q = 2927 := (Nat.prime_dvd_prime_iff_eq hq prime_2927).mp hdf
    subst this; exact prime_B_40_div_2927
  · have : q = 26573 := (Nat.prime_dvd_prime_iff_eq hq prime_26573).mp hdf
    subst this; exact prime_B_40_div_26573
  · have : q = 12767299 := (Nat.prime_dvd_prime_iff_eq hq prime_12767299).mp hdf
    subst this; exact prime_B_40_div_12767299
private lemma pair_40 :
    Nat.Prime ((3 ^ 40 - 2454) * (2 ^ 40) - 1) ∧
    Nat.Prime ((3 ^ 40 - 2454) * (2 ^ 40) + 1) := by
  constructor
  · convert prime_A_40
  · convert prime_B_40

/- Pair for n = 41 -/
private lemma prime_89 : Nat.Prime 89 := by norm_num
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_321829993_sub1 : (321829993 - 1 : ℕ) = 2 ^ 3 * 3 ^ 2 * 11 ^ 2 * 17 * 41 * 53 := by norm_num
private lemma prime_321829993_pow : (15 : ZMod 321829993) ^ (321829993 - 1) = 1 := by
  reduce_mod_char
private lemma prime_321829993_div_2 : (15 : ZMod 321829993) ^ ((321829993 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_321829993_div_3 : (15 : ZMod 321829993) ^ ((321829993 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_321829993_div_11 : (15 : ZMod 321829993) ^ ((321829993 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_321829993_div_17 : (15 : ZMod 321829993) ^ ((321829993 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_321829993_div_41 : (15 : ZMod 321829993) ^ ((321829993 - 1) / 41) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_321829993_div_53 : (15 : ZMod 321829993) ^ ((321829993 - 1) / 53) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_321829993 : Nat.Prime 321829993 := by
  refine lucas_primality 321829993 (15 : ZMod 321829993) prime_321829993_pow ?_
  intro q hq hqd
  rw [prime_321829993_sub1] at hqd
  have : q ∣ [2 ^ 3, 3 ^ 2, 11 ^ 2, 17, 41, 53].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_321829993_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_321829993_div_3
  · have : q = 11 := prime_eq_of_dvd_prime_pow hq prime_11 hdf
    subst this; exact prime_321829993_div_11
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_321829993_div_17
  · have : q = 41 := (Nat.prime_dvd_prime_iff_eq hq prime_41).mp hdf
    subst this; exact prime_321829993_div_41
  · have : q = 53 := (Nat.prime_dvd_prime_iff_eq hq prime_53).mp hdf
    subst this; exact prime_321829993_div_53
private lemma prime_1493 : Nat.Prime 1493 := by norm_num
private lemma prime_1697 : Nat.Prime 1697 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_197 : Nat.Prime 197 := by norm_num
private lemma prime_73883 : Nat.Prime 73883 := by norm_num
private lemma prime_174659413_sub1 : (174659413 - 1 : ℕ) = 2 ^ 2 * 3 * 197 * 73883 := by norm_num
private lemma prime_174659413_pow : (2 : ZMod 174659413) ^ (174659413 - 1) = 1 := by
  reduce_mod_char
private lemma prime_174659413_div_2 : (2 : ZMod 174659413) ^ ((174659413 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174659413_div_3 : (2 : ZMod 174659413) ^ ((174659413 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174659413_div_197 : (2 : ZMod 174659413) ^ ((174659413 - 1) / 197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174659413_div_73883 : (2 : ZMod 174659413) ^ ((174659413 - 1) / 73883) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_174659413 : Nat.Prime 174659413 := by
  refine lucas_primality 174659413 (2 : ZMod 174659413) prime_174659413_pow ?_
  intro q hq hqd
  rw [prime_174659413_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 197, 73883].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_174659413_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_174659413_div_3
  · have : q = 197 := (Nat.prime_dvd_prime_iff_eq hq prime_197).mp hdf
    subst this; exact prime_174659413_div_197
  · have : q = 73883 := (Nat.prime_dvd_prime_iff_eq hq prime_73883).mp hdf
    subst this; exact prime_174659413_div_73883
private lemma prime_9082289477_sub1 : (9082289477 - 1 : ℕ) = 2 ^ 2 * 13 * 174659413 := by norm_num
private lemma prime_9082289477_pow : (2 : ZMod 9082289477) ^ (9082289477 - 1) = 1 := by
  reduce_mod_char
private lemma prime_9082289477_div_2 : (2 : ZMod 9082289477) ^ ((9082289477 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_9082289477_div_13 : (2 : ZMod 9082289477) ^ ((9082289477 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_9082289477_div_174659413 : (2 : ZMod 9082289477) ^ ((9082289477 - 1) / 174659413) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_9082289477 : Nat.Prime 9082289477 := by
  refine lucas_primality 9082289477 (2 : ZMod 9082289477) prime_9082289477_pow ?_
  intro q hq hqd
  rw [prime_9082289477_sub1] at hqd
  have : q ∣ [2 ^ 2, 13, 174659413].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_9082289477_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_9082289477_div_13
  · have : q = 174659413 := (Nat.prime_dvd_prime_iff_eq hq prime_174659413).mp hdf
    subst this; exact prime_9082289477_div_174659413
private lemma prime_3773817012909019589_sub1 : (3773817012909019589 - 1 : ℕ) = 2 ^ 2 * 41 * 1493 * 1697 * 9082289477 := by norm_num
private lemma prime_3773817012909019589_pow : (2 : ZMod 3773817012909019589) ^ (3773817012909019589 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3773817012909019589_div_2 : (2 : ZMod 3773817012909019589) ^ ((3773817012909019589 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3773817012909019589_div_41 : (2 : ZMod 3773817012909019589) ^ ((3773817012909019589 - 1) / 41) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3773817012909019589_div_1493 : (2 : ZMod 3773817012909019589) ^ ((3773817012909019589 - 1) / 1493) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3773817012909019589_div_1697 : (2 : ZMod 3773817012909019589) ^ ((3773817012909019589 - 1) / 1697) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3773817012909019589_div_9082289477 : (2 : ZMod 3773817012909019589) ^ ((3773817012909019589 - 1) / 9082289477) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3773817012909019589 : Nat.Prime 3773817012909019589 := by
  refine lucas_primality 3773817012909019589 (2 : ZMod 3773817012909019589) prime_3773817012909019589_pow ?_
  intro q hq hqd
  rw [prime_3773817012909019589_sub1] at hqd
  have : q ∣ [2 ^ 2, 41, 1493, 1697, 9082289477].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_3773817012909019589_div_2
  · have : q = 41 := (Nat.prime_dvd_prime_iff_eq hq prime_41).mp hdf
    subst this; exact prime_3773817012909019589_div_41
  · have : q = 1493 := (Nat.prime_dvd_prime_iff_eq hq prime_1493).mp hdf
    subst this; exact prime_3773817012909019589_div_1493
  · have : q = 1697 := (Nat.prime_dvd_prime_iff_eq hq prime_1697).mp hdf
    subst this; exact prime_3773817012909019589_div_1697
  · have : q = 9082289477 := (Nat.prime_dvd_prime_iff_eq hq prime_9082289477).mp hdf
    subst this; exact prime_3773817012909019589_div_9082289477
private lemma prime_A_41_sub1 : (80204967233062401187663029731327 - 1 : ℕ) = 2 * 7 * 53 * 89 * 321829993 * 3773817012909019589 := by norm_num
private lemma prime_A_41_pow : (5 : ZMod 80204967233062401187663029731327) ^ (80204967233062401187663029731327 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_41_div_2 : (5 : ZMod 80204967233062401187663029731327) ^ ((80204967233062401187663029731327 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_41_div_7 : (5 : ZMod 80204967233062401187663029731327) ^ ((80204967233062401187663029731327 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_41_div_53 : (5 : ZMod 80204967233062401187663029731327) ^ ((80204967233062401187663029731327 - 1) / 53) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_41_div_89 : (5 : ZMod 80204967233062401187663029731327) ^ ((80204967233062401187663029731327 - 1) / 89) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_41_div_321829993 : (5 : ZMod 80204967233062401187663029731327) ^ ((80204967233062401187663029731327 - 1) / 321829993) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_41_div_3773817012909019589 : (5 : ZMod 80204967233062401187663029731327) ^ ((80204967233062401187663029731327 - 1) / 3773817012909019589) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_41 : Nat.Prime 80204967233062401187663029731327 := by
  refine lucas_primality 80204967233062401187663029731327 (5 : ZMod 80204967233062401187663029731327) prime_A_41_pow ?_
  intro q hq hqd
  rw [prime_A_41_sub1] at hqd
  have : q ∣ [2, 7, 53, 89, 321829993, 3773817012909019589].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_41_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_41_div_7
  · have : q = 53 := (Nat.prime_dvd_prime_iff_eq hq prime_53).mp hdf
    subst this; exact prime_A_41_div_53
  · have : q = 89 := (Nat.prime_dvd_prime_iff_eq hq prime_89).mp hdf
    subst this; exact prime_A_41_div_89
  · have : q = 321829993 := (Nat.prime_dvd_prime_iff_eq hq prime_321829993).mp hdf
    subst this; exact prime_A_41_div_321829993
  · have : q = 3773817012909019589 := (Nat.prime_dvd_prime_iff_eq hq prime_3773817012909019589).mp hdf
    subst this; exact prime_A_41_div_3773817012909019589
private lemma prime_109 : Nat.Prime 109 := by norm_num
private lemma prime_258611 : Nat.Prime 258611 := by norm_num
private lemma prime_16189837 : Nat.Prime 16189837 := by norm_num
private lemma prime_971390221_sub1 : (971390221 - 1 : ℕ) = 2 ^ 2 * 3 * 5 * 16189837 := by norm_num
private lemma prime_971390221_pow : (2 : ZMod 971390221) ^ (971390221 - 1) = 1 := by
  reduce_mod_char
private lemma prime_971390221_div_2 : (2 : ZMod 971390221) ^ ((971390221 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_971390221_div_3 : (2 : ZMod 971390221) ^ ((971390221 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_971390221_div_5 : (2 : ZMod 971390221) ^ ((971390221 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_971390221_div_16189837 : (2 : ZMod 971390221) ^ ((971390221 - 1) / 16189837) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_971390221 : Nat.Prime 971390221 := by
  refine lucas_primality 971390221 (2 : ZMod 971390221) prime_971390221_pow ?_
  intro q hq hqd
  rw [prime_971390221_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 5, 16189837].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_971390221_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_971390221_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_971390221_div_5
  · have : q = 16189837 := (Nat.prime_dvd_prime_iff_eq hq prime_16189837).mp hdf
    subst this; exact prime_971390221_div_16189837
private lemma prime_328585552947484549_sub1 : (328585552947484549 - 1 : ℕ) = 2 ^ 2 * 3 * 109 * 258611 * 971390221 := by norm_num
private lemma prime_328585552947484549_pow : (6 : ZMod 328585552947484549) ^ (328585552947484549 - 1) = 1 := by
  reduce_mod_char
private lemma prime_328585552947484549_div_2 : (6 : ZMod 328585552947484549) ^ ((328585552947484549 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_328585552947484549_div_3 : (6 : ZMod 328585552947484549) ^ ((328585552947484549 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_328585552947484549_div_109 : (6 : ZMod 328585552947484549) ^ ((328585552947484549 - 1) / 109) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_328585552947484549_div_258611 : (6 : ZMod 328585552947484549) ^ ((328585552947484549 - 1) / 258611) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_328585552947484549_div_971390221 : (6 : ZMod 328585552947484549) ^ ((328585552947484549 - 1) / 971390221) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_328585552947484549 : Nat.Prime 328585552947484549 := by
  refine lucas_primality 328585552947484549 (6 : ZMod 328585552947484549) prime_328585552947484549_pow ?_
  intro q hq hqd
  rw [prime_328585552947484549_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 109, 258611, 971390221].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_328585552947484549_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_328585552947484549_div_3
  · have : q = 109 := (Nat.prime_dvd_prime_iff_eq hq prime_109).mp hdf
    subst this; exact prime_328585552947484549_div_109
  · have : q = 258611 := (Nat.prime_dvd_prime_iff_eq hq prime_258611).mp hdf
    subst this; exact prime_328585552947484549_div_258611
  · have : q = 971390221 := (Nat.prime_dvd_prime_iff_eq hq prime_971390221).mp hdf
    subst this; exact prime_328585552947484549_div_971390221
private lemma prime_B_41_sub1 : (80204967233062401187663029731329 - 1 : ℕ) = 2 ^ 41 * 3 * 37 * 328585552947484549 := by norm_num
private lemma prime_B_41_pow : (7 : ZMod 80204967233062401187663029731329) ^ (80204967233062401187663029731329 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_41_div_2 : (7 : ZMod 80204967233062401187663029731329) ^ ((80204967233062401187663029731329 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_41_div_3 : (7 : ZMod 80204967233062401187663029731329) ^ ((80204967233062401187663029731329 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_41_div_37 : (7 : ZMod 80204967233062401187663029731329) ^ ((80204967233062401187663029731329 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_41_div_328585552947484549 : (7 : ZMod 80204967233062401187663029731329) ^ ((80204967233062401187663029731329 - 1) / 328585552947484549) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_41 : Nat.Prime 80204967233062401187663029731329 := by
  refine lucas_primality 80204967233062401187663029731329 (7 : ZMod 80204967233062401187663029731329) prime_B_41_pow ?_
  intro q hq hqd
  rw [prime_B_41_sub1] at hqd
  have : q ∣ [2 ^ 41, 3, 37, 328585552947484549].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_41_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_41_div_3
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_B_41_div_37
  · have : q = 328585552947484549 := (Nat.prime_dvd_prime_iff_eq hq prime_328585552947484549).mp hdf
    subst this; exact prime_B_41_div_328585552947484549
private lemma pair_41 :
    Nat.Prime ((3 ^ 41 - 1464) * (2 ^ 41) - 1) ∧
    Nat.Prime ((3 ^ 41 - 1464) * (2 ^ 41) + 1) := by
  constructor
  · convert prime_A_41
  · convert prime_B_41

/- Pair for n = 42 -/
private lemma prime_31 : Nat.Prime 31 := by norm_num
private lemma prime_47 : Nat.Prime 47 := by norm_num
private lemma prime_79 : Nat.Prime 79 := by norm_num
private lemma prime_14021671 : Nat.Prime 14021671 := by norm_num
private lemma prime_813256919_sub1 : (813256919 - 1 : ℕ) = 2 * 29 * 14021671 := by norm_num
private lemma prime_813256919_pow : (13 : ZMod 813256919) ^ (813256919 - 1) = 1 := by
  reduce_mod_char
private lemma prime_813256919_div_2 : (13 : ZMod 813256919) ^ ((813256919 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_813256919_div_29 : (13 : ZMod 813256919) ^ ((813256919 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_813256919_div_14021671 : (13 : ZMod 813256919) ^ ((813256919 - 1) / 14021671) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_813256919 : Nat.Prime 813256919 := by
  refine lucas_primality 813256919 (13 : ZMod 813256919) prime_813256919_pow ?_
  intro q hq hqd
  rw [prime_813256919_sub1] at hqd
  have : q ∣ [2, 29, 14021671].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_813256919_div_2
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_813256919_div_29
  · have : q = 14021671 := (Nat.prime_dvd_prime_iff_eq hq prime_14021671).mp hdf
    subst this; exact prime_813256919_div_14021671
private lemma prime_127 : Nat.Prime 127 := by norm_num
private lemma prime_307 : Nat.Prime 307 := by norm_num
private lemma prime_3203 : Nat.Prime 3203 := by norm_num
private lemma prime_8193877 : Nat.Prime 8193877 := by norm_num
private lemma prime_8186126706725273_sub1 : (8186126706725273 - 1 : ℕ) = 2 ^ 3 * 127 * 307 * 3203 * 8193877 := by norm_num
private lemma prime_8186126706725273_pow : (3 : ZMod 8186126706725273) ^ (8186126706725273 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8186126706725273_div_2 : (3 : ZMod 8186126706725273) ^ ((8186126706725273 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8186126706725273_div_127 : (3 : ZMod 8186126706725273) ^ ((8186126706725273 - 1) / 127) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8186126706725273_div_307 : (3 : ZMod 8186126706725273) ^ ((8186126706725273 - 1) / 307) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8186126706725273_div_3203 : (3 : ZMod 8186126706725273) ^ ((8186126706725273 - 1) / 3203) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8186126706725273_div_8193877 : (3 : ZMod 8186126706725273) ^ ((8186126706725273 - 1) / 8193877) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8186126706725273 : Nat.Prime 8186126706725273 := by
  refine lucas_primality 8186126706725273 (3 : ZMod 8186126706725273) prime_8186126706725273_pow ?_
  intro q hq hqd
  rw [prime_8186126706725273_sub1] at hqd
  have : q ∣ [2 ^ 3, 127, 307, 3203, 8193877].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_8186126706725273_div_2
  · have : q = 127 := (Nat.prime_dvd_prime_iff_eq hq prime_127).mp hdf
    subst this; exact prime_8186126706725273_div_127
  · have : q = 307 := (Nat.prime_dvd_prime_iff_eq hq prime_307).mp hdf
    subst this; exact prime_8186126706725273_div_307
  · have : q = 3203 := (Nat.prime_dvd_prime_iff_eq hq prime_3203).mp hdf
    subst this; exact prime_8186126706725273_div_3203
  · have : q = 8193877 := (Nat.prime_dvd_prime_iff_eq hq prime_8193877).mp hdf
    subst this; exact prime_8186126706725273_div_8193877
private lemma prime_16372253413450547_sub1 : (16372253413450547 - 1 : ℕ) = 2 * 8186126706725273 := by norm_num
private lemma prime_16372253413450547_pow : (2 : ZMod 16372253413450547) ^ (16372253413450547 - 1) = 1 := by
  reduce_mod_char
private lemma prime_16372253413450547_div_2 : (2 : ZMod 16372253413450547) ^ ((16372253413450547 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_16372253413450547_div_8186126706725273 : (2 : ZMod 16372253413450547) ^ ((16372253413450547 - 1) / 8186126706725273) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_16372253413450547 : Nat.Prime 16372253413450547 := by
  refine lucas_primality 16372253413450547 (2 : ZMod 16372253413450547) prime_16372253413450547_pow ?_
  intro q hq hqd
  rw [prime_16372253413450547_sub1] at hqd
  have : q ∣ [2, 8186126706725273].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_16372253413450547_div_2
  · have : q = 8186126706725273 := (Nat.prime_dvd_prime_iff_eq hq prime_8186126706725273).mp hdf
    subst this; exact prime_16372253413450547_div_8186126706725273
private lemma prime_A_42_sub1 : (481229803398374417615319107371007 - 1 : ℕ) = 2 * 31 * 47 * 79 * 157 * 813256919 * 16372253413450547 := by norm_num
private lemma prime_A_42_pow : (5 : ZMod 481229803398374417615319107371007) ^ (481229803398374417615319107371007 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_42_div_2 : (5 : ZMod 481229803398374417615319107371007) ^ ((481229803398374417615319107371007 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_42_div_31 : (5 : ZMod 481229803398374417615319107371007) ^ ((481229803398374417615319107371007 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_42_div_47 : (5 : ZMod 481229803398374417615319107371007) ^ ((481229803398374417615319107371007 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_42_div_79 : (5 : ZMod 481229803398374417615319107371007) ^ ((481229803398374417615319107371007 - 1) / 79) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_42_div_157 : (5 : ZMod 481229803398374417615319107371007) ^ ((481229803398374417615319107371007 - 1) / 157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_42_div_813256919 : (5 : ZMod 481229803398374417615319107371007) ^ ((481229803398374417615319107371007 - 1) / 813256919) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_42_div_16372253413450547 : (5 : ZMod 481229803398374417615319107371007) ^ ((481229803398374417615319107371007 - 1) / 16372253413450547) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_42 : Nat.Prime 481229803398374417615319107371007 := by
  refine lucas_primality 481229803398374417615319107371007 (5 : ZMod 481229803398374417615319107371007) prime_A_42_pow ?_
  intro q hq hqd
  rw [prime_A_42_sub1] at hqd
  have : q ∣ [2, 31, 47, 79, 157, 813256919, 16372253413450547].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_42_div_2
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_A_42_div_31
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_A_42_div_47
  · have : q = 79 := (Nat.prime_dvd_prime_iff_eq hq prime_79).mp hdf
    subst this; exact prime_A_42_div_79
  · have : q = 157 := (Nat.prime_dvd_prime_iff_eq hq prime_157).mp hdf
    subst this; exact prime_A_42_div_157
  · have : q = 813256919 := (Nat.prime_dvd_prime_iff_eq hq prime_813256919).mp hdf
    subst this; exact prime_A_42_div_813256919
  · have : q = 16372253413450547 := (Nat.prime_dvd_prime_iff_eq hq prime_16372253413450547).mp hdf
    subst this; exact prime_A_42_div_16372253413450547
private lemma prime_1278113 : Nat.Prime 1278113 := by norm_num
private lemma prime_8737 : Nat.Prime 8737 := by norm_num
private lemma prime_18506224129_sub1 : (18506224129 - 1 : ℕ) = 2 ^ 9 * 3 * 7 * 197 * 8737 := by norm_num
private lemma prime_18506224129_pow : (11 : ZMod 18506224129) ^ (18506224129 - 1) = 1 := by
  reduce_mod_char
private lemma prime_18506224129_div_2 : (11 : ZMod 18506224129) ^ ((18506224129 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18506224129_div_3 : (11 : ZMod 18506224129) ^ ((18506224129 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18506224129_div_7 : (11 : ZMod 18506224129) ^ ((18506224129 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18506224129_div_197 : (11 : ZMod 18506224129) ^ ((18506224129 - 1) / 197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18506224129_div_8737 : (11 : ZMod 18506224129) ^ ((18506224129 - 1) / 8737) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_18506224129 : Nat.Prime 18506224129 := by
  refine lucas_primality 18506224129 (11 : ZMod 18506224129) prime_18506224129_pow ?_
  intro q hq hqd
  rw [prime_18506224129_sub1] at hqd
  have : q ∣ [2 ^ 9, 3, 7, 197, 8737].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_18506224129_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_18506224129_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_18506224129_div_7
  · have : q = 197 := (Nat.prime_dvd_prime_iff_eq hq prime_197).mp hdf
    subst this; exact prime_18506224129_div_197
  · have : q = 8737 := (Nat.prime_dvd_prime_iff_eq hq prime_8737).mp hdf
    subst this; exact prime_18506224129_div_8737
private lemma prime_B_42_sub1 : (481229803398374417615319107371009 - 1 : ℕ) = 2 ^ 43 * 3 ^ 2 * 257 * 1278113 * 18506224129 := by norm_num
private lemma prime_B_42_pow : (11 : ZMod 481229803398374417615319107371009) ^ (481229803398374417615319107371009 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_42_div_2 : (11 : ZMod 481229803398374417615319107371009) ^ ((481229803398374417615319107371009 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_42_div_3 : (11 : ZMod 481229803398374417615319107371009) ^ ((481229803398374417615319107371009 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_42_div_257 : (11 : ZMod 481229803398374417615319107371009) ^ ((481229803398374417615319107371009 - 1) / 257) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_42_div_1278113 : (11 : ZMod 481229803398374417615319107371009) ^ ((481229803398374417615319107371009 - 1) / 1278113) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_42_div_18506224129 : (11 : ZMod 481229803398374417615319107371009) ^ ((481229803398374417615319107371009 - 1) / 18506224129) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_42 : Nat.Prime 481229803398374417615319107371009 := by
  refine lucas_primality 481229803398374417615319107371009 (11 : ZMod 481229803398374417615319107371009) prime_B_42_pow ?_
  intro q hq hqd
  rw [prime_B_42_sub1] at hqd
  have : q ∣ [2 ^ 43, 3 ^ 2, 257, 1278113, 18506224129].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_42_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_42_div_3
  · have : q = 257 := (Nat.prime_dvd_prime_iff_eq hq prime_257).mp hdf
    subst this; exact prime_B_42_div_257
  · have : q = 1278113 := (Nat.prime_dvd_prime_iff_eq hq prime_1278113).mp hdf
    subst this; exact prime_B_42_div_1278113
  · have : q = 18506224129 := (Nat.prime_dvd_prime_iff_eq hq prime_18506224129).mp hdf
    subst this; exact prime_B_42_div_18506224129
private lemma pair_42 :
    Nat.Prime ((3 ^ 42 - 2007) * (2 ^ 42) - 1) ∧
    Nat.Prime ((3 ^ 42 - 2007) * (2 ^ 42) + 1) := by
  constructor
  · convert prime_A_42
  · convert prime_B_42

/- Pair for n = 43 -/
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_10253 : Nat.Prime 10253 := by norm_num
private lemma prime_290663 : Nat.Prime 290663 := by norm_num
private lemma prime_59 : Nat.Prime 59 := by norm_num
private lemma prime_1609 : Nat.Prime 1609 := by norm_num
private lemma prime_10639 : Nat.Prime 10639 := by norm_num
private lemma prime_259339 : Nat.Prime 259339 := by norm_num
private lemma prime_560172241_sub1 : (560172241 - 1 : ℕ) = 2 ^ 4 * 3 ^ 3 * 5 * 259339 := by norm_num
private lemma prime_560172241_pow : (14 : ZMod 560172241) ^ (560172241 - 1) = 1 := by
  reduce_mod_char
private lemma prime_560172241_div_2 : (14 : ZMod 560172241) ^ ((560172241 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_560172241_div_3 : (14 : ZMod 560172241) ^ ((560172241 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_560172241_div_5 : (14 : ZMod 560172241) ^ ((560172241 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_560172241_div_259339 : (14 : ZMod 560172241) ^ ((560172241 - 1) / 259339) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_560172241 : Nat.Prime 560172241 := by
  refine lucas_primality 560172241 (14 : ZMod 560172241) prime_560172241_pow ?_
  intro q hq hqd
  rw [prime_560172241_sub1] at hqd
  have : q ∣ [2 ^ 4, 3 ^ 3, 5, 259339].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_560172241_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_560172241_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_560172241_div_5
  · have : q = 259339 := (Nat.prime_dvd_prime_iff_eq hq prime_259339).mp hdf
    subst this; exact prime_560172241_div_259339
private lemma prime_879187415200729805227_sub1 : (879187415200729805227 - 1 : ℕ) = 2 * 3 * 7 * 37 * 59 * 1609 * 10639 * 560172241 := by norm_num
private lemma prime_879187415200729805227_pow : (3 : ZMod 879187415200729805227) ^ (879187415200729805227 - 1) = 1 := by
  reduce_mod_char
private lemma prime_879187415200729805227_div_2 : (3 : ZMod 879187415200729805227) ^ ((879187415200729805227 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_879187415200729805227_div_3 : (3 : ZMod 879187415200729805227) ^ ((879187415200729805227 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_879187415200729805227_div_7 : (3 : ZMod 879187415200729805227) ^ ((879187415200729805227 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_879187415200729805227_div_37 : (3 : ZMod 879187415200729805227) ^ ((879187415200729805227 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_879187415200729805227_div_59 : (3 : ZMod 879187415200729805227) ^ ((879187415200729805227 - 1) / 59) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_879187415200729805227_div_1609 : (3 : ZMod 879187415200729805227) ^ ((879187415200729805227 - 1) / 1609) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_879187415200729805227_div_10639 : (3 : ZMod 879187415200729805227) ^ ((879187415200729805227 - 1) / 10639) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_879187415200729805227_div_560172241 : (3 : ZMod 879187415200729805227) ^ ((879187415200729805227 - 1) / 560172241) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_879187415200729805227 : Nat.Prime 879187415200729805227 := by
  refine lucas_primality 879187415200729805227 (3 : ZMod 879187415200729805227) prime_879187415200729805227_pow ?_
  intro q hq hqd
  rw [prime_879187415200729805227_sub1] at hqd
  have : q ∣ [2, 3, 7, 37, 59, 1609, 10639, 560172241].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_879187415200729805227_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_879187415200729805227_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_879187415200729805227_div_7
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_879187415200729805227_div_37
  · have : q = 59 := (Nat.prime_dvd_prime_iff_eq hq prime_59).mp hdf
    subst this; exact prime_879187415200729805227_div_59
  · have : q = 1609 := (Nat.prime_dvd_prime_iff_eq hq prime_1609).mp hdf
    subst this; exact prime_879187415200729805227_div_1609
  · have : q = 10639 := (Nat.prime_dvd_prime_iff_eq hq prime_10639).mp hdf
    subst this; exact prime_879187415200729805227_div_10639
  · have : q = 560172241 := (Nat.prime_dvd_prime_iff_eq hq prime_560172241).mp hdf
    subst this; exact prime_879187415200729805227_div_560172241
private lemma prime_A_43_sub1 : (2887378820390246518622171386871807 - 1 : ℕ) = 2 * 19 * 29 * 10253 * 290663 * 879187415200729805227 := by norm_num
private lemma prime_A_43_pow : (5 : ZMod 2887378820390246518622171386871807) ^ (2887378820390246518622171386871807 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_43_div_2 : (5 : ZMod 2887378820390246518622171386871807) ^ ((2887378820390246518622171386871807 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_43_div_19 : (5 : ZMod 2887378820390246518622171386871807) ^ ((2887378820390246518622171386871807 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_43_div_29 : (5 : ZMod 2887378820390246518622171386871807) ^ ((2887378820390246518622171386871807 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_43_div_10253 : (5 : ZMod 2887378820390246518622171386871807) ^ ((2887378820390246518622171386871807 - 1) / 10253) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_43_div_290663 : (5 : ZMod 2887378820390246518622171386871807) ^ ((2887378820390246518622171386871807 - 1) / 290663) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_43_div_879187415200729805227 : (5 : ZMod 2887378820390246518622171386871807) ^ ((2887378820390246518622171386871807 - 1) / 879187415200729805227) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_43 : Nat.Prime 2887378820390246518622171386871807 := by
  refine lucas_primality 2887378820390246518622171386871807 (5 : ZMod 2887378820390246518622171386871807) prime_A_43_pow ?_
  intro q hq hqd
  rw [prime_A_43_sub1] at hqd
  have : q ∣ [2, 19, 29, 10253, 290663, 879187415200729805227].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_43_div_2
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_A_43_div_19
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_A_43_div_29
  · have : q = 10253 := (Nat.prime_dvd_prime_iff_eq hq prime_10253).mp hdf
    subst this; exact prime_A_43_div_10253
  · have : q = 290663 := (Nat.prime_dvd_prime_iff_eq hq prime_290663).mp hdf
    subst this; exact prime_A_43_div_290663
  · have : q = 879187415200729805227 := (Nat.prime_dvd_prime_iff_eq hq prime_879187415200729805227).mp hdf
    subst this; exact prime_A_43_div_879187415200729805227
private lemma prime_107 : Nat.Prime 107 := by norm_num
private lemma prime_349 : Nat.Prime 349 := by norm_num
private lemma prime_340979 : Nat.Prime 340979 := by norm_num
private lemma prime_238003343_sub1 : (238003343 - 1 : ℕ) = 2 * 349 * 340979 := by norm_num
private lemma prime_238003343_pow : (5 : ZMod 238003343) ^ (238003343 - 1) = 1 := by
  reduce_mod_char
private lemma prime_238003343_div_2 : (5 : ZMod 238003343) ^ ((238003343 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_238003343_div_349 : (5 : ZMod 238003343) ^ ((238003343 - 1) / 349) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_238003343_div_340979 : (5 : ZMod 238003343) ^ ((238003343 - 1) / 340979) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_238003343 : Nat.Prime 238003343 := by
  refine lucas_primality 238003343 (5 : ZMod 238003343) prime_238003343_pow ?_
  intro q hq hqd
  rw [prime_238003343_sub1] at hqd
  have : q ∣ [2, 349, 340979].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_238003343_div_2
  · have : q = 349 := (Nat.prime_dvd_prime_iff_eq hq prime_349).mp hdf
    subst this; exact prime_238003343_div_349
  · have : q = 340979 := (Nat.prime_dvd_prime_iff_eq hq prime_340979).mp hdf
    subst this; exact prime_238003343_div_340979
private lemma prime_59675129 : Nat.Prime 59675129 := by norm_num
private lemma prime_1074152323_sub1 : (1074152323 - 1 : ℕ) = 2 * 3 ^ 2 * 59675129 := by norm_num
private lemma prime_1074152323_pow : (14 : ZMod 1074152323) ^ (1074152323 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1074152323_div_2 : (14 : ZMod 1074152323) ^ ((1074152323 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1074152323_div_3 : (14 : ZMod 1074152323) ^ ((1074152323 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1074152323_div_59675129 : (14 : ZMod 1074152323) ^ ((1074152323 - 1) / 59675129) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1074152323 : Nat.Prime 1074152323 := by
  refine lucas_primality 1074152323 (14 : ZMod 1074152323) prime_1074152323_pow ?_
  intro q hq hqd
  rw [prime_1074152323_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 59675129].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1074152323_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_1074152323_div_3
  · have : q = 59675129 := (Nat.prime_dvd_prime_iff_eq hq prime_59675129).mp hdf
    subst this; exact prime_1074152323_div_59675129
private lemma prime_B_43_sub1 : (2887378820390246518622171386871809 - 1 : ℕ) = 2 ^ 45 * 3 * 107 * 238003343 * 1074152323 := by norm_num
private lemma prime_B_43_pow : (7 : ZMod 2887378820390246518622171386871809) ^ (2887378820390246518622171386871809 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_43_div_2 : (7 : ZMod 2887378820390246518622171386871809) ^ ((2887378820390246518622171386871809 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_43_div_3 : (7 : ZMod 2887378820390246518622171386871809) ^ ((2887378820390246518622171386871809 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_43_div_107 : (7 : ZMod 2887378820390246518622171386871809) ^ ((2887378820390246518622171386871809 - 1) / 107) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_43_div_238003343 : (7 : ZMod 2887378820390246518622171386871809) ^ ((2887378820390246518622171386871809 - 1) / 238003343) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_43_div_1074152323 : (7 : ZMod 2887378820390246518622171386871809) ^ ((2887378820390246518622171386871809 - 1) / 1074152323) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_43 : Nat.Prime 2887378820390246518622171386871809 := by
  refine lucas_primality 2887378820390246518622171386871809 (7 : ZMod 2887378820390246518622171386871809) prime_B_43_pow ?_
  intro q hq hqd
  rw [prime_B_43_sub1] at hqd
  have : q ∣ [2 ^ 45, 3, 107, 238003343, 1074152323].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_43_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_43_div_3
  · have : q = 107 := (Nat.prime_dvd_prime_iff_eq hq prime_107).mp hdf
    subst this; exact prime_B_43_div_107
  · have : q = 238003343 := (Nat.prime_dvd_prime_iff_eq hq prime_238003343).mp hdf
    subst this; exact prime_B_43_div_238003343
  · have : q = 1074152323 := (Nat.prime_dvd_prime_iff_eq hq prime_1074152323).mp hdf
    subst this; exact prime_B_43_div_1074152323
private lemma pair_43 :
    Nat.Prime ((3 ^ 43 - 4551) * (2 ^ 43) - 1) ∧
    Nat.Prime ((3 ^ 43 - 4551) * (2 ^ 43) + 1) := by
  constructor
  · convert prime_A_43
  · convert prime_B_43

/- Pair for n = 44 -/
private lemma prime_1223 : Nat.Prime 1223 := by norm_num
private lemma prime_1148219 : Nat.Prime 1148219 := by norm_num
private lemma prime_36528103 : Nat.Prime 36528103 := by norm_num
private lemma prime_7905143 : Nat.Prime 7905143 := by norm_num
private lemma prime_4534579748233_sub1 : (4534579748233 - 1 : ℕ) = 2 ^ 3 * 3 ^ 2 * 31 * 257 * 7905143 := by norm_num
private lemma prime_4534579748233_pow : (5 : ZMod 4534579748233) ^ (4534579748233 - 1) = 1 := by
  reduce_mod_char
private lemma prime_4534579748233_div_2 : (5 : ZMod 4534579748233) ^ ((4534579748233 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4534579748233_div_3 : (5 : ZMod 4534579748233) ^ ((4534579748233 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4534579748233_div_31 : (5 : ZMod 4534579748233) ^ ((4534579748233 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4534579748233_div_257 : (5 : ZMod 4534579748233) ^ ((4534579748233 - 1) / 257) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4534579748233_div_7905143 : (5 : ZMod 4534579748233) ^ ((4534579748233 - 1) / 7905143) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_4534579748233 : Nat.Prime 4534579748233 := by
  refine lucas_primality 4534579748233 (5 : ZMod 4534579748233) prime_4534579748233_pow ?_
  intro q hq hqd
  rw [prime_4534579748233_sub1] at hqd
  have : q ∣ [2 ^ 3, 3 ^ 2, 31, 257, 7905143].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_4534579748233_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_4534579748233_div_3
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_4534579748233_div_31
  · have : q = 257 := (Nat.prime_dvd_prime_iff_eq hq prime_257).mp hdf
    subst this; exact prime_4534579748233_div_257
  · have : q = 7905143 := (Nat.prime_dvd_prime_iff_eq hq prime_7905143).mp hdf
    subst this; exact prime_4534579748233_div_7905143
private lemma prime_1269682329505241_sub1 : (1269682329505241 - 1 : ℕ) = 2 ^ 3 * 5 * 7 * 4534579748233 := by norm_num
private lemma prime_1269682329505241_pow : (3 : ZMod 1269682329505241) ^ (1269682329505241 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1269682329505241_div_2 : (3 : ZMod 1269682329505241) ^ ((1269682329505241 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1269682329505241_div_5 : (3 : ZMod 1269682329505241) ^ ((1269682329505241 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1269682329505241_div_7 : (3 : ZMod 1269682329505241) ^ ((1269682329505241 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1269682329505241_div_4534579748233 : (3 : ZMod 1269682329505241) ^ ((1269682329505241 - 1) / 4534579748233) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1269682329505241 : Nat.Prime 1269682329505241 := by
  refine lucas_primality 1269682329505241 (3 : ZMod 1269682329505241) prime_1269682329505241_pow ?_
  intro q hq hqd
  rw [prime_1269682329505241_sub1] at hqd
  have : q ∣ [2 ^ 3, 5, 7, 4534579748233].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1269682329505241_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_1269682329505241_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_1269682329505241_div_7
  · have : q = 4534579748233 := (Nat.prime_dvd_prime_iff_eq hq prime_4534579748233).mp hdf
    subst this; exact prime_1269682329505241_div_4534579748233
private lemma prime_A_44_sub1 : (17324272922341479295923216206266367 - 1 : ℕ) = 2 * 7 * 19 * 1223 * 1148219 * 36528103 * 1269682329505241 := by norm_num
private lemma prime_A_44_pow : (5 : ZMod 17324272922341479295923216206266367) ^ (17324272922341479295923216206266367 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_44_div_2 : (5 : ZMod 17324272922341479295923216206266367) ^ ((17324272922341479295923216206266367 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_44_div_7 : (5 : ZMod 17324272922341479295923216206266367) ^ ((17324272922341479295923216206266367 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_44_div_19 : (5 : ZMod 17324272922341479295923216206266367) ^ ((17324272922341479295923216206266367 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_44_div_1223 : (5 : ZMod 17324272922341479295923216206266367) ^ ((17324272922341479295923216206266367 - 1) / 1223) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_44_div_1148219 : (5 : ZMod 17324272922341479295923216206266367) ^ ((17324272922341479295923216206266367 - 1) / 1148219) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_44_div_36528103 : (5 : ZMod 17324272922341479295923216206266367) ^ ((17324272922341479295923216206266367 - 1) / 36528103) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_44_div_1269682329505241 : (5 : ZMod 17324272922341479295923216206266367) ^ ((17324272922341479295923216206266367 - 1) / 1269682329505241) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_44 : Nat.Prime 17324272922341479295923216206266367 := by
  refine lucas_primality 17324272922341479295923216206266367 (5 : ZMod 17324272922341479295923216206266367) prime_A_44_pow ?_
  intro q hq hqd
  rw [prime_A_44_sub1] at hqd
  have : q ∣ [2, 7, 19, 1223, 1148219, 36528103, 1269682329505241].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_44_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_44_div_7
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_A_44_div_19
  · have : q = 1223 := (Nat.prime_dvd_prime_iff_eq hq prime_1223).mp hdf
    subst this; exact prime_A_44_div_1223
  · have : q = 1148219 := (Nat.prime_dvd_prime_iff_eq hq prime_1148219).mp hdf
    subst this; exact prime_A_44_div_1148219
  · have : q = 36528103 := (Nat.prime_dvd_prime_iff_eq hq prime_36528103).mp hdf
    subst this; exact prime_A_44_div_36528103
  · have : q = 1269682329505241 := (Nat.prime_dvd_prime_iff_eq hq prime_1269682329505241).mp hdf
    subst this; exact prime_A_44_div_1269682329505241
private lemma prime_277 : Nat.Prime 277 := by norm_num
private lemma prime_439 : Nat.Prime 439 := by norm_num
private lemma prime_67 : Nat.Prime 67 := by norm_num
private lemma prime_37561 : Nat.Prime 37561 := by norm_num
private lemma prime_1434023 : Nat.Prime 1434023 := by norm_num
private lemma prime_7217687279003_sub1 : (7217687279003 - 1 : ℕ) = 2 * 67 * 37561 * 1434023 := by norm_num
private lemma prime_7217687279003_pow : (2 : ZMod 7217687279003) ^ (7217687279003 - 1) = 1 := by
  reduce_mod_char
private lemma prime_7217687279003_div_2 : (2 : ZMod 7217687279003) ^ ((7217687279003 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7217687279003_div_67 : (2 : ZMod 7217687279003) ^ ((7217687279003 - 1) / 67) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7217687279003_div_37561 : (2 : ZMod 7217687279003) ^ ((7217687279003 - 1) / 37561) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7217687279003_div_1434023 : (2 : ZMod 7217687279003) ^ ((7217687279003 - 1) / 1434023) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7217687279003 : Nat.Prime 7217687279003 := by
  refine lucas_primality 7217687279003 (2 : ZMod 7217687279003) prime_7217687279003_pow ?_
  intro q hq hqd
  rw [prime_7217687279003_sub1] at hqd
  have : q ∣ [2, 67, 37561, 1434023].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_7217687279003_div_2
  · have : q = 67 := (Nat.prime_dvd_prime_iff_eq hq prime_67).mp hdf
    subst this; exact prime_7217687279003_div_67
  · have : q = 37561 := (Nat.prime_dvd_prime_iff_eq hq prime_37561).mp hdf
    subst this; exact prime_7217687279003_div_37561
  · have : q = 1434023 := (Nat.prime_dvd_prime_iff_eq hq prime_1434023).mp hdf
    subst this; exact prime_7217687279003_div_1434023
private lemma prime_B_44_sub1 : (17324272922341479295923216206266369 - 1 : ℕ) = 2 ^ 45 * 3 * 11 * 17 * 277 * 439 * 7217687279003 := by norm_num
private lemma prime_B_44_pow : (7 : ZMod 17324272922341479295923216206266369) ^ (17324272922341479295923216206266369 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_44_div_2 : (7 : ZMod 17324272922341479295923216206266369) ^ ((17324272922341479295923216206266369 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_44_div_3 : (7 : ZMod 17324272922341479295923216206266369) ^ ((17324272922341479295923216206266369 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_44_div_11 : (7 : ZMod 17324272922341479295923216206266369) ^ ((17324272922341479295923216206266369 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_44_div_17 : (7 : ZMod 17324272922341479295923216206266369) ^ ((17324272922341479295923216206266369 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_44_div_277 : (7 : ZMod 17324272922341479295923216206266369) ^ ((17324272922341479295923216206266369 - 1) / 277) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_44_div_439 : (7 : ZMod 17324272922341479295923216206266369) ^ ((17324272922341479295923216206266369 - 1) / 439) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_44_div_7217687279003 : (7 : ZMod 17324272922341479295923216206266369) ^ ((17324272922341479295923216206266369 - 1) / 7217687279003) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_44 : Nat.Prime 17324272922341479295923216206266369 := by
  refine lucas_primality 17324272922341479295923216206266369 (7 : ZMod 17324272922341479295923216206266369) prime_B_44_pow ?_
  intro q hq hqd
  rw [prime_B_44_sub1] at hqd
  have : q ∣ [2 ^ 45, 3, 11, 17, 277, 439, 7217687279003].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_44_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_44_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_44_div_11
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_B_44_div_17
  · have : q = 277 := (Nat.prime_dvd_prime_iff_eq hq prime_277).mp hdf
    subst this; exact prime_B_44_div_277
  · have : q = 439 := (Nat.prime_dvd_prime_iff_eq hq prime_439).mp hdf
    subst this; exact prime_B_44_div_439
  · have : q = 7217687279003 := (Nat.prime_dvd_prime_iff_eq hq prime_7217687279003).mp hdf
    subst this; exact prime_B_44_div_7217687279003
private lemma pair_44 :
    Nat.Prime ((3 ^ 44 - 3183) * (2 ^ 44) - 1) ∧
    Nat.Prime ((3 ^ 44 - 3183) * (2 ^ 44) + 1) := by
  constructor
  · convert prime_A_44
  · convert prime_B_44

/- Pair for n = 45 -/
private lemma prime_10011403 : Nat.Prime 10011403 := by norm_num
private lemma prime_240273673_sub1 : (240273673 - 1 : ℕ) = 2 ^ 3 * 3 * 10011403 := by norm_num
private lemma prime_240273673_pow : (10 : ZMod 240273673) ^ (240273673 - 1) = 1 := by
  reduce_mod_char
private lemma prime_240273673_div_2 : (10 : ZMod 240273673) ^ ((240273673 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_240273673_div_3 : (10 : ZMod 240273673) ^ ((240273673 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_240273673_div_10011403 : (10 : ZMod 240273673) ^ ((240273673 - 1) / 10011403) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_240273673 : Nat.Prime 240273673 := by
  refine lucas_primality 240273673 (10 : ZMod 240273673) prime_240273673_pow ?_
  intro q hq hqd
  rw [prime_240273673_sub1] at hqd
  have : q ∣ [2 ^ 3, 3, 10011403].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_240273673_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_240273673_div_3
  · have : q = 10011403 := (Nat.prime_dvd_prime_iff_eq hq prime_10011403).mp hdf
    subst this; exact prime_240273673_div_10011403
private lemma prime_5197 : Nat.Prime 5197 := by norm_num
private lemma prime_1062869653_sub1 : (1062869653 - 1 : ℕ) = 2 ^ 2 * 3 ^ 2 * 13 * 19 * 23 * 5197 := by norm_num
private lemma prime_1062869653_pow : (5 : ZMod 1062869653) ^ (1062869653 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1062869653_div_2 : (5 : ZMod 1062869653) ^ ((1062869653 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1062869653_div_3 : (5 : ZMod 1062869653) ^ ((1062869653 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1062869653_div_13 : (5 : ZMod 1062869653) ^ ((1062869653 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1062869653_div_19 : (5 : ZMod 1062869653) ^ ((1062869653 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1062869653_div_23 : (5 : ZMod 1062869653) ^ ((1062869653 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1062869653_div_5197 : (5 : ZMod 1062869653) ^ ((1062869653 - 1) / 5197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1062869653 : Nat.Prime 1062869653 := by
  refine lucas_primality 1062869653 (5 : ZMod 1062869653) prime_1062869653_pow ?_
  intro q hq hqd
  rw [prime_1062869653_sub1] at hqd
  have : q ∣ [2 ^ 2, 3 ^ 2, 13, 19, 23, 5197].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1062869653_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_1062869653_div_3
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_1062869653_div_13
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_1062869653_div_19
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_1062869653_div_23
  · have : q = 5197 := (Nat.prime_dvd_prime_iff_eq hq prime_5197).mp hdf
    subst this; exact prime_1062869653_div_5197
private lemma prime_55269221957_sub1 : (55269221957 - 1 : ℕ) = 2 ^ 2 * 13 * 1062869653 := by norm_num
private lemma prime_55269221957_pow : (2 : ZMod 55269221957) ^ (55269221957 - 1) = 1 := by
  reduce_mod_char
private lemma prime_55269221957_div_2 : (2 : ZMod 55269221957) ^ ((55269221957 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_55269221957_div_13 : (2 : ZMod 55269221957) ^ ((55269221957 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_55269221957_div_1062869653 : (2 : ZMod 55269221957) ^ ((55269221957 - 1) / 1062869653) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_55269221957 : Nat.Prime 55269221957 := by
  refine lucas_primality 55269221957 (2 : ZMod 55269221957) prime_55269221957_pow ?_
  intro q hq hqd
  rw [prime_55269221957_sub1] at hqd
  have : q ∣ [2 ^ 2, 13, 1062869653].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_55269221957_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_55269221957_div_13
  · have : q = 1062869653 := (Nat.prime_dvd_prime_iff_eq hq prime_1062869653).mp hdf
    subst this; exact prime_55269221957_div_1062869653
private lemma prime_43 : Nat.Prime 43 := by norm_num
private lemma prime_20939 : Nat.Prime 20939 := by norm_num
private lemma prime_174989 : Nat.Prime 174989 := by norm_num
private lemma prime_34032111304249_sub1 : (34032111304249 - 1 : ℕ) = 2 ^ 3 * 3 ^ 3 * 43 * 20939 * 174989 := by norm_num
private lemma prime_34032111304249_pow : (23 : ZMod 34032111304249) ^ (34032111304249 - 1) = 1 := by
  reduce_mod_char
private lemma prime_34032111304249_div_2 : (23 : ZMod 34032111304249) ^ ((34032111304249 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_34032111304249_div_3 : (23 : ZMod 34032111304249) ^ ((34032111304249 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_34032111304249_div_43 : (23 : ZMod 34032111304249) ^ ((34032111304249 - 1) / 43) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_34032111304249_div_20939 : (23 : ZMod 34032111304249) ^ ((34032111304249 - 1) / 20939) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_34032111304249_div_174989 : (23 : ZMod 34032111304249) ^ ((34032111304249 - 1) / 174989) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_34032111304249 : Nat.Prime 34032111304249 := by
  refine lucas_primality 34032111304249 (23 : ZMod 34032111304249) prime_34032111304249_pow ?_
  intro q hq hqd
  rw [prime_34032111304249_sub1] at hqd
  have : q ∣ [2 ^ 3, 3 ^ 3, 43, 20939, 174989].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_34032111304249_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_34032111304249_div_3
  · have : q = 43 := (Nat.prime_dvd_prime_iff_eq hq prime_43).mp hdf
    subst this; exact prime_34032111304249_div_43
  · have : q = 20939 := (Nat.prime_dvd_prime_iff_eq hq prime_20939).mp hdf
    subst this; exact prime_34032111304249_div_20939
  · have : q = 174989 := (Nat.prime_dvd_prime_iff_eq hq prime_174989).mp hdf
    subst this; exact prime_34032111304249_div_174989
private lemma prime_A_45_sub1 : (103945637534048876058843861296873471 - 1 : ℕ) = 2 * 5 * 23 * 240273673 * 55269221957 * 34032111304249 := by norm_num
private lemma prime_A_45_pow : (13 : ZMod 103945637534048876058843861296873471) ^ (103945637534048876058843861296873471 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_45_div_2 : (13 : ZMod 103945637534048876058843861296873471) ^ ((103945637534048876058843861296873471 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_45_div_5 : (13 : ZMod 103945637534048876058843861296873471) ^ ((103945637534048876058843861296873471 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_45_div_23 : (13 : ZMod 103945637534048876058843861296873471) ^ ((103945637534048876058843861296873471 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_45_div_240273673 : (13 : ZMod 103945637534048876058843861296873471) ^ ((103945637534048876058843861296873471 - 1) / 240273673) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_45_div_55269221957 : (13 : ZMod 103945637534048876058843861296873471) ^ ((103945637534048876058843861296873471 - 1) / 55269221957) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_45_div_34032111304249 : (13 : ZMod 103945637534048876058843861296873471) ^ ((103945637534048876058843861296873471 - 1) / 34032111304249) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_45 : Nat.Prime 103945637534048876058843861296873471 := by
  refine lucas_primality 103945637534048876058843861296873471 (13 : ZMod 103945637534048876058843861296873471) prime_A_45_pow ?_
  intro q hq hqd
  rw [prime_A_45_sub1] at hqd
  have : q ∣ [2, 5, 23, 240273673, 55269221957, 34032111304249].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_45_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_45_div_5
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_A_45_div_23
  · have : q = 240273673 := (Nat.prime_dvd_prime_iff_eq hq prime_240273673).mp hdf
    subst this; exact prime_A_45_div_240273673
  · have : q = 55269221957 := (Nat.prime_dvd_prime_iff_eq hq prime_55269221957).mp hdf
    subst this; exact prime_A_45_div_55269221957
  · have : q = 34032111304249 := (Nat.prime_dvd_prime_iff_eq hq prime_34032111304249).mp hdf
    subst this; exact prime_A_45_div_34032111304249
private lemma prime_281 : Nat.Prime 281 := by norm_num
private lemma prime_1319 : Nat.Prime 1319 := by norm_num
private lemma prime_2437 : Nat.Prime 2437 := by norm_num
private lemma prime_5569 : Nat.Prime 5569 := by norm_num
private lemma prime_181607 : Nat.Prime 181607 := by norm_num
private lemma prime_B_45_sub1 : (103945637534048876058843861296873473 - 1 : ℕ) = 2 ^ 46 * 3 * 7 ^ 2 * 11 * 281 * 1319 * 2437 * 5569 * 181607 := by norm_num
private lemma prime_B_45_pow : (10 : ZMod 103945637534048876058843861296873473) ^ (103945637534048876058843861296873473 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_45_div_2 : (10 : ZMod 103945637534048876058843861296873473) ^ ((103945637534048876058843861296873473 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_45_div_3 : (10 : ZMod 103945637534048876058843861296873473) ^ ((103945637534048876058843861296873473 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_45_div_7 : (10 : ZMod 103945637534048876058843861296873473) ^ ((103945637534048876058843861296873473 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_45_div_11 : (10 : ZMod 103945637534048876058843861296873473) ^ ((103945637534048876058843861296873473 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_45_div_281 : (10 : ZMod 103945637534048876058843861296873473) ^ ((103945637534048876058843861296873473 - 1) / 281) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_45_div_1319 : (10 : ZMod 103945637534048876058843861296873473) ^ ((103945637534048876058843861296873473 - 1) / 1319) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_45_div_2437 : (10 : ZMod 103945637534048876058843861296873473) ^ ((103945637534048876058843861296873473 - 1) / 2437) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_45_div_5569 : (10 : ZMod 103945637534048876058843861296873473) ^ ((103945637534048876058843861296873473 - 1) / 5569) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_45_div_181607 : (10 : ZMod 103945637534048876058843861296873473) ^ ((103945637534048876058843861296873473 - 1) / 181607) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_45 : Nat.Prime 103945637534048876058843861296873473 := by
  refine lucas_primality 103945637534048876058843861296873473 (10 : ZMod 103945637534048876058843861296873473) prime_B_45_pow ?_
  intro q hq hqd
  rw [prime_B_45_sub1] at hqd
  have : q ∣ [2 ^ 46, 3, 7 ^ 2, 11, 281, 1319, 2437, 5569, 181607].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_45_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_45_div_3
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_B_45_div_7
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_45_div_11
  · have : q = 281 := (Nat.prime_dvd_prime_iff_eq hq prime_281).mp hdf
    subst this; exact prime_B_45_div_281
  · have : q = 1319 := (Nat.prime_dvd_prime_iff_eq hq prime_1319).mp hdf
    subst this; exact prime_B_45_div_1319
  · have : q = 2437 := (Nat.prime_dvd_prime_iff_eq hq prime_2437).mp hdf
    subst this; exact prime_B_45_div_2437
  · have : q = 5569 := (Nat.prime_dvd_prime_iff_eq hq prime_5569).mp hdf
    subst this; exact prime_B_45_div_5569
  · have : q = 181607 := (Nat.prime_dvd_prime_iff_eq hq prime_181607).mp hdf
    subst this; exact prime_B_45_div_181607
private lemma pair_45 :
    Nat.Prime ((3 ^ 45 - 1497) * (2 ^ 45) - 1) ∧
    Nat.Prime ((3 ^ 45 - 1497) * (2 ^ 45) + 1) := by
  constructor
  · convert prime_A_45
  · convert prime_B_45
