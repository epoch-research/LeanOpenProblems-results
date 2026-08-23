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

/- Pair for n = 61 -/
private lemma prime_431 : Nat.Prime 431 := by norm_num
private lemma prime_342467 : Nat.Prime 342467 := by norm_num
private lemma prime_51445049 : Nat.Prime 51445049 := by norm_num
private lemma prime_61 : Nat.Prime 61 := by norm_num
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_99809747 : Nat.Prime 99809747 := by norm_num
private lemma prime_11378311159_sub1 : (11378311159 - 1 : ℕ) = 2 * 3 * 19 * 99809747 := by norm_num
private lemma prime_11378311159_pow : (6 : ZMod 11378311159) ^ (11378311159 - 1) = 1 := by
  reduce_mod_char
private lemma prime_11378311159_div_2 : (6 : ZMod 11378311159) ^ ((11378311159 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11378311159_div_3 : (6 : ZMod 11378311159) ^ ((11378311159 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11378311159_div_19 : (6 : ZMod 11378311159) ^ ((11378311159 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11378311159_div_99809747 : (6 : ZMod 11378311159) ^ ((11378311159 - 1) / 99809747) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11378311159 : Nat.Prime 11378311159 := by
  refine lucas_primality 11378311159 (6 : ZMod 11378311159) prime_11378311159_pow ?_
  intro q hq hqd
  rw [prime_11378311159_sub1] at hqd
  have : q ∣ [2, 3, 19, 99809747].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_11378311159_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_11378311159_div_3
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_11378311159_div_19
  · have : q = 99809747 := (Nat.prime_dvd_prime_iff_eq hq prime_99809747).mp hdf
    subst this; exact prime_11378311159_div_99809747
private lemma prime_6940769806991_sub1 : (6940769806991 - 1 : ℕ) = 2 * 5 * 61 * 11378311159 := by norm_num
private lemma prime_6940769806991_pow : (11 : ZMod 6940769806991) ^ (6940769806991 - 1) = 1 := by
  reduce_mod_char
private lemma prime_6940769806991_div_2 : (11 : ZMod 6940769806991) ^ ((6940769806991 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6940769806991_div_5 : (11 : ZMod 6940769806991) ^ ((6940769806991 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6940769806991_div_61 : (11 : ZMod 6940769806991) ^ ((6940769806991 - 1) / 61) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6940769806991_div_11378311159 : (11 : ZMod 6940769806991) ^ ((6940769806991 - 1) / 11378311159) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_6940769806991 : Nat.Prime 6940769806991 := by
  refine lucas_primality 6940769806991 (11 : ZMod 6940769806991) prime_6940769806991_pow ?_
  intro q hq hqd
  rw [prime_6940769806991_sub1] at hqd
  have : q ∣ [2, 5, 61, 11378311159].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_6940769806991_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_6940769806991_div_5
  · have : q = 61 := (Nat.prime_dvd_prime_iff_eq hq prime_61).mp hdf
    subst this; exact prime_6940769806991_div_61
  · have : q = 11378311159 := (Nat.prime_dvd_prime_iff_eq hq prime_11378311159).mp hdf
    subst this; exact prime_6940769806991_div_11378311159
private lemma prime_46577197 : Nat.Prime 46577197 := by norm_num
private lemma prime_31 : Nat.Prime 31 := by norm_num
private lemma prime_151 : Nat.Prime 151 := by norm_num
private lemma prime_284417561_sub1 : (284417561 - 1 : ℕ) = 2 ^ 3 * 5 * 7 ^ 2 * 31 ^ 2 * 151 := by norm_num
private lemma prime_284417561_pow : (3 : ZMod 284417561) ^ (284417561 - 1) = 1 := by
  reduce_mod_char
private lemma prime_284417561_div_2 : (3 : ZMod 284417561) ^ ((284417561 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_284417561_div_5 : (3 : ZMod 284417561) ^ ((284417561 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_284417561_div_7 : (3 : ZMod 284417561) ^ ((284417561 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_284417561_div_31 : (3 : ZMod 284417561) ^ ((284417561 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_284417561_div_151 : (3 : ZMod 284417561) ^ ((284417561 - 1) / 151) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_284417561 : Nat.Prime 284417561 := by
  refine lucas_primality 284417561 (3 : ZMod 284417561) prime_284417561_pow ?_
  intro q hq hqd
  rw [prime_284417561_sub1] at hqd
  have : q ∣ [2 ^ 3, 5, 7 ^ 2, 31 ^ 2, 151].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_284417561_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_284417561_div_5
  · have : q = 7 := prime_eq_of_dvd_prime_pow hq Nat.prime_seven hdf
    subst this; exact prime_284417561_div_7
  · have : q = 31 := prime_eq_of_dvd_prime_pow hq prime_31 hdf
    subst this; exact prime_284417561_div_31
  · have : q = 151 := (Nat.prime_dvd_prime_iff_eq hq prime_151).mp hdf
    subst this; exact prime_284417561_div_151
private lemma prime_79484236613739103_sub1 : (79484236613739103 - 1 : ℕ) = 2 * 3 * 46577197 * 284417561 := by norm_num
private lemma prime_79484236613739103_pow : (3 : ZMod 79484236613739103) ^ (79484236613739103 - 1) = 1 := by
  reduce_mod_char
private lemma prime_79484236613739103_div_2 : (3 : ZMod 79484236613739103) ^ ((79484236613739103 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79484236613739103_div_3 : (3 : ZMod 79484236613739103) ^ ((79484236613739103 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79484236613739103_div_46577197 : (3 : ZMod 79484236613739103) ^ ((79484236613739103 - 1) / 46577197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79484236613739103_div_284417561 : (3 : ZMod 79484236613739103) ^ ((79484236613739103 - 1) / 284417561) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_79484236613739103 : Nat.Prime 79484236613739103 := by
  refine lucas_primality 79484236613739103 (3 : ZMod 79484236613739103) prime_79484236613739103_pow ?_
  intro q hq hqd
  rw [prime_79484236613739103_sub1] at hqd
  have : q ∣ [2, 3, 46577197, 284417561].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_79484236613739103_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_79484236613739103_div_3
  · have : q = 46577197 := (Nat.prime_dvd_prime_iff_eq hq prime_46577197).mp hdf
    subst this; exact prime_79484236613739103_div_46577197
  · have : q = 284417561 := (Nat.prime_dvd_prime_iff_eq hq prime_284417561).mp hdf
    subst this; exact prime_79484236613739103_div_284417561
private lemma prime_A_61_sub1 : (293242067884135544935936504276313319767940268031 - 1 : ℕ) = 2 * 5 * 7 * 431 * 342467 * 51445049 * 6940769806991 * 79484236613739103 := by norm_num
private lemma prime_A_61_pow : (13 : ZMod 293242067884135544935936504276313319767940268031) ^ (293242067884135544935936504276313319767940268031 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_61_div_2 : (13 : ZMod 293242067884135544935936504276313319767940268031) ^ ((293242067884135544935936504276313319767940268031 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_61_div_5 : (13 : ZMod 293242067884135544935936504276313319767940268031) ^ ((293242067884135544935936504276313319767940268031 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_61_div_7 : (13 : ZMod 293242067884135544935936504276313319767940268031) ^ ((293242067884135544935936504276313319767940268031 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_61_div_431 : (13 : ZMod 293242067884135544935936504276313319767940268031) ^ ((293242067884135544935936504276313319767940268031 - 1) / 431) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_61_div_342467 : (13 : ZMod 293242067884135544935936504276313319767940268031) ^ ((293242067884135544935936504276313319767940268031 - 1) / 342467) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_61_div_51445049 : (13 : ZMod 293242067884135544935936504276313319767940268031) ^ ((293242067884135544935936504276313319767940268031 - 1) / 51445049) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_61_div_6940769806991 : (13 : ZMod 293242067884135544935936504276313319767940268031) ^ ((293242067884135544935936504276313319767940268031 - 1) / 6940769806991) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_61_div_79484236613739103 : (13 : ZMod 293242067884135544935936504276313319767940268031) ^ ((293242067884135544935936504276313319767940268031 - 1) / 79484236613739103) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_61 : Nat.Prime 293242067884135544935936504276313319767940268031 := by
  refine lucas_primality 293242067884135544935936504276313319767940268031 (13 : ZMod 293242067884135544935936504276313319767940268031) prime_A_61_pow ?_
  intro q hq hqd
  rw [prime_A_61_sub1] at hqd
  have : q ∣ [2, 5, 7, 431, 342467, 51445049, 6940769806991, 79484236613739103].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_61_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_61_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_61_div_7
  · have : q = 431 := (Nat.prime_dvd_prime_iff_eq hq prime_431).mp hdf
    subst this; exact prime_A_61_div_431
  · have : q = 342467 := (Nat.prime_dvd_prime_iff_eq hq prime_342467).mp hdf
    subst this; exact prime_A_61_div_342467
  · have : q = 51445049 := (Nat.prime_dvd_prime_iff_eq hq prime_51445049).mp hdf
    subst this; exact prime_A_61_div_51445049
  · have : q = 6940769806991 := (Nat.prime_dvd_prime_iff_eq hq prime_6940769806991).mp hdf
    subst this; exact prime_A_61_div_6940769806991
  · have : q = 79484236613739103 := (Nat.prime_dvd_prime_iff_eq hq prime_79484236613739103).mp hdf
    subst this; exact prime_A_61_div_79484236613739103
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_197 : Nat.Prime 197 := by norm_num
private lemma prime_1879 : Nat.Prime 1879 := by norm_num
private lemma prime_161233 : Nat.Prime 161233 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_227 : Nat.Prime 227 := by norm_num
private lemma prime_73063 : Nat.Prime 73063 := by norm_num
private lemma prime_7881073 : Nat.Prime 7881073 := by norm_num
private lemma prime_64570724146538663_sub1 : (64570724146538663 - 1 : ℕ) = 2 * 13 * 19 * 227 * 73063 * 7881073 := by norm_num
private lemma prime_64570724146538663_pow : (5 : ZMod 64570724146538663) ^ (64570724146538663 - 1) = 1 := by
  reduce_mod_char
private lemma prime_64570724146538663_div_2 : (5 : ZMod 64570724146538663) ^ ((64570724146538663 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_64570724146538663_div_13 : (5 : ZMod 64570724146538663) ^ ((64570724146538663 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_64570724146538663_div_19 : (5 : ZMod 64570724146538663) ^ ((64570724146538663 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_64570724146538663_div_227 : (5 : ZMod 64570724146538663) ^ ((64570724146538663 - 1) / 227) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_64570724146538663_div_73063 : (5 : ZMod 64570724146538663) ^ ((64570724146538663 - 1) / 73063) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_64570724146538663_div_7881073 : (5 : ZMod 64570724146538663) ^ ((64570724146538663 - 1) / 7881073) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_64570724146538663 : Nat.Prime 64570724146538663 := by
  refine lucas_primality 64570724146538663 (5 : ZMod 64570724146538663) prime_64570724146538663_pow ?_
  intro q hq hqd
  rw [prime_64570724146538663_sub1] at hqd
  have : q ∣ [2, 13, 19, 227, 73063, 7881073].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_64570724146538663_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_64570724146538663_div_13
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_64570724146538663_div_19
  · have : q = 227 := (Nat.prime_dvd_prime_iff_eq hq prime_227).mp hdf
    subst this; exact prime_64570724146538663_div_227
  · have : q = 73063 := (Nat.prime_dvd_prime_iff_eq hq prime_73063).mp hdf
    subst this; exact prime_64570724146538663_div_73063
  · have : q = 7881073 := (Nat.prime_dvd_prime_iff_eq hq prime_7881073).mp hdf
    subst this; exact prime_64570724146538663_div_7881073
private lemma prime_B_61_sub1 : (293242067884135544935936504276313319767940268033 - 1 : ℕ) = 2 ^ 61 * 3 * 11 * 197 * 1879 * 161233 * 64570724146538663 := by norm_num
private lemma prime_B_61_pow : (5 : ZMod 293242067884135544935936504276313319767940268033) ^ (293242067884135544935936504276313319767940268033 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_61_div_2 : (5 : ZMod 293242067884135544935936504276313319767940268033) ^ ((293242067884135544935936504276313319767940268033 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_61_div_3 : (5 : ZMod 293242067884135544935936504276313319767940268033) ^ ((293242067884135544935936504276313319767940268033 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_61_div_11 : (5 : ZMod 293242067884135544935936504276313319767940268033) ^ ((293242067884135544935936504276313319767940268033 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_61_div_197 : (5 : ZMod 293242067884135544935936504276313319767940268033) ^ ((293242067884135544935936504276313319767940268033 - 1) / 197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_61_div_1879 : (5 : ZMod 293242067884135544935936504276313319767940268033) ^ ((293242067884135544935936504276313319767940268033 - 1) / 1879) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_61_div_161233 : (5 : ZMod 293242067884135544935936504276313319767940268033) ^ ((293242067884135544935936504276313319767940268033 - 1) / 161233) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_61_div_64570724146538663 : (5 : ZMod 293242067884135544935936504276313319767940268033) ^ ((293242067884135544935936504276313319767940268033 - 1) / 64570724146538663) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_61 : Nat.Prime 293242067884135544935936504276313319767940268033 := by
  refine lucas_primality 293242067884135544935936504276313319767940268033 (5 : ZMod 293242067884135544935936504276313319767940268033) prime_B_61_pow ?_
  intro q hq hqd
  rw [prime_B_61_sub1] at hqd
  have : q ∣ [2 ^ 61, 3, 11, 197, 1879, 161233, 64570724146538663].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_61_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_61_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_B_61_div_11
  · have : q = 197 := (Nat.prime_dvd_prime_iff_eq hq prime_197).mp hdf
    subst this; exact prime_B_61_div_197
  · have : q = 1879 := (Nat.prime_dvd_prime_iff_eq hq prime_1879).mp hdf
    subst this; exact prime_B_61_div_1879
  · have : q = 161233 := (Nat.prime_dvd_prime_iff_eq hq prime_161233).mp hdf
    subst this; exact prime_B_61_div_161233
  · have : q = 64570724146538663 := (Nat.prime_dvd_prime_iff_eq hq prime_64570724146538663).mp hdf
    subst this; exact prime_B_61_div_64570724146538663
private lemma pair_61 :
    Nat.Prime ((3 ^ 61 - 4062) * (2 ^ 61) - 1) ∧
    Nat.Prime ((3 ^ 61 - 4062) * (2 ^ 61) + 1) := by
  constructor
  · convert prime_A_61
  · convert prime_B_61

/- Pair for n = 62 -/
private lemma prime_17 : Nat.Prime 17 := by norm_num
private lemma prime_47 : Nat.Prime 47 := by norm_num
private lemma prime_241 : Nat.Prime 241 := by norm_num
private lemma prime_719 : Nat.Prime 719 := by norm_num
private lemma prime_3941750693_sub1 : (3941750693 - 1 : ℕ) = 2 ^ 2 * 11 ^ 2 * 47 * 241 * 719 := by norm_num
private lemma prime_3941750693_pow : (2 : ZMod 3941750693) ^ (3941750693 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3941750693_div_2 : (2 : ZMod 3941750693) ^ ((3941750693 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3941750693_div_11 : (2 : ZMod 3941750693) ^ ((3941750693 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3941750693_div_47 : (2 : ZMod 3941750693) ^ ((3941750693 - 1) / 47) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3941750693_div_241 : (2 : ZMod 3941750693) ^ ((3941750693 - 1) / 241) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3941750693_div_719 : (2 : ZMod 3941750693) ^ ((3941750693 - 1) / 719) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3941750693 : Nat.Prime 3941750693 := by
  refine lucas_primality 3941750693 (2 : ZMod 3941750693) prime_3941750693_pow ?_
  intro q hq hqd
  rw [prime_3941750693_sub1] at hqd
  have : q ∣ [2 ^ 2, 11 ^ 2, 47, 241, 719].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_3941750693_div_2
  · have : q = 11 := prime_eq_of_dvd_prime_pow hq prime_11 hdf
    subst this; exact prime_3941750693_div_11
  · have : q = 47 := (Nat.prime_dvd_prime_iff_eq hq prime_47).mp hdf
    subst this; exact prime_3941750693_div_47
  · have : q = 241 := (Nat.prime_dvd_prime_iff_eq hq prime_241).mp hdf
    subst this; exact prime_3941750693_div_241
  · have : q = 719 := (Nat.prime_dvd_prime_iff_eq hq prime_719).mp hdf
    subst this; exact prime_3941750693_div_719
private lemma prime_354757562371_sub1 : (354757562371 - 1 : ℕ) = 2 * 3 ^ 2 * 5 * 3941750693 := by norm_num
private lemma prime_354757562371_pow : (3 : ZMod 354757562371) ^ (354757562371 - 1) = 1 := by
  reduce_mod_char
private lemma prime_354757562371_div_2 : (3 : ZMod 354757562371) ^ ((354757562371 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_354757562371_div_3 : (3 : ZMod 354757562371) ^ ((354757562371 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_354757562371_div_5 : (3 : ZMod 354757562371) ^ ((354757562371 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_354757562371_div_3941750693 : (3 : ZMod 354757562371) ^ ((354757562371 - 1) / 3941750693) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_354757562371 : Nat.Prime 354757562371 := by
  refine lucas_primality 354757562371 (3 : ZMod 354757562371) prime_354757562371_pow ?_
  intro q hq hqd
  rw [prime_354757562371_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 5, 3941750693].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_354757562371_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_354757562371_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_354757562371_div_5
  · have : q = 3941750693 := (Nat.prime_dvd_prime_iff_eq hq prime_3941750693).mp hdf
    subst this; exact prime_354757562371_div_3941750693
private lemma prime_26961574740197_sub1 : (26961574740197 - 1 : ℕ) = 2 ^ 2 * 19 * 354757562371 := by norm_num
private lemma prime_26961574740197_pow : (2 : ZMod 26961574740197) ^ (26961574740197 - 1) = 1 := by
  reduce_mod_char
private lemma prime_26961574740197_div_2 : (2 : ZMod 26961574740197) ^ ((26961574740197 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_26961574740197_div_19 : (2 : ZMod 26961574740197) ^ ((26961574740197 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_26961574740197_div_354757562371 : (2 : ZMod 26961574740197) ^ ((26961574740197 - 1) / 354757562371) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_26961574740197 : Nat.Prime 26961574740197 := by
  refine lucas_primality 26961574740197 (2 : ZMod 26961574740197) prime_26961574740197_pow ?_
  intro q hq hqd
  rw [prime_26961574740197_sub1] at hqd
  have : q ∣ [2 ^ 2, 19, 354757562371].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_26961574740197_div_2
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_26961574740197_div_19
  · have : q = 354757562371 := (Nat.prime_dvd_prime_iff_eq hq prime_354757562371).mp hdf
    subst this; exact prime_26961574740197_div_354757562371
private lemma prime_2081 : Nat.Prime 2081 := by norm_num
private lemma prime_26573 : Nat.Prime 26573 := by norm_num
private lemma prime_75083 : Nat.Prime 75083 := by norm_num
private lemma prime_7980722237_sub1 : (7980722237 - 1 : ℕ) = 2 ^ 2 * 26573 * 75083 := by norm_num
private lemma prime_7980722237_pow : (2 : ZMod 7980722237) ^ (7980722237 - 1) = 1 := by
  reduce_mod_char
private lemma prime_7980722237_div_2 : (2 : ZMod 7980722237) ^ ((7980722237 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7980722237_div_26573 : (2 : ZMod 7980722237) ^ ((7980722237 - 1) / 26573) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7980722237_div_75083 : (2 : ZMod 7980722237) ^ ((7980722237 - 1) / 75083) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_7980722237 : Nat.Prime 7980722237 := by
  refine lucas_primality 7980722237 (2 : ZMod 7980722237) prime_7980722237_pow ?_
  intro q hq hqd
  rw [prime_7980722237_sub1] at hqd
  have : q ∣ [2 ^ 2, 26573, 75083].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_7980722237_div_2
  · have : q = 26573 := (Nat.prime_dvd_prime_iff_eq hq prime_26573).mp hdf
    subst this; exact prime_7980722237_div_26573
  · have : q = 75083 := (Nat.prime_dvd_prime_iff_eq hq prime_75083).mp hdf
    subst this; exact prime_7980722237_div_75083
private lemma prime_166078829751971_sub1 : (166078829751971 - 1 : ℕ) = 2 * 5 * 2081 * 7980722237 := by norm_num
private lemma prime_166078829751971_pow : (2 : ZMod 166078829751971) ^ (166078829751971 - 1) = 1 := by
  reduce_mod_char
private lemma prime_166078829751971_div_2 : (2 : ZMod 166078829751971) ^ ((166078829751971 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_166078829751971_div_5 : (2 : ZMod 166078829751971) ^ ((166078829751971 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_166078829751971_div_2081 : (2 : ZMod 166078829751971) ^ ((166078829751971 - 1) / 2081) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_166078829751971_div_7980722237 : (2 : ZMod 166078829751971) ^ ((166078829751971 - 1) / 7980722237) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_166078829751971 : Nat.Prime 166078829751971 := by
  refine lucas_primality 166078829751971 (2 : ZMod 166078829751971) prime_166078829751971_pow ?_
  intro q hq hqd
  rw [prime_166078829751971_sub1] at hqd
  have : q ∣ [2, 5, 2081, 7980722237].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_166078829751971_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_166078829751971_div_5
  · have : q = 2081 := (Nat.prime_dvd_prime_iff_eq hq prime_2081).mp hdf
    subst this; exact prime_166078829751971_div_2081
  · have : q = 7980722237 := (Nat.prime_dvd_prime_iff_eq hq prime_7980722237).mp hdf
    subst this; exact prime_166078829751971_div_7980722237
private lemma prime_16108117 : Nat.Prime 16108117 := by norm_num
private lemma prime_43 : Nat.Prime 43 := by norm_num
private lemma prime_141073 : Nat.Prime 141073 := by norm_num
private lemma prime_169851893_sub1 : (169851893 - 1 : ℕ) = 2 ^ 2 * 7 * 43 * 141073 := by norm_num
private lemma prime_169851893_pow : (2 : ZMod 169851893) ^ (169851893 - 1) = 1 := by
  reduce_mod_char
private lemma prime_169851893_div_2 : (2 : ZMod 169851893) ^ ((169851893 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_169851893_div_7 : (2 : ZMod 169851893) ^ ((169851893 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_169851893_div_43 : (2 : ZMod 169851893) ^ ((169851893 - 1) / 43) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_169851893_div_141073 : (2 : ZMod 169851893) ^ ((169851893 - 1) / 141073) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_169851893 : Nat.Prime 169851893 := by
  refine lucas_primality 169851893 (2 : ZMod 169851893) prime_169851893_pow ?_
  intro q hq hqd
  rw [prime_169851893_sub1] at hqd
  have : q ∣ [2 ^ 2, 7, 43, 141073].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_169851893_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_169851893_div_7
  · have : q = 43 := (Nat.prime_dvd_prime_iff_eq hq prime_43).mp hdf
    subst this; exact prime_169851893_div_43
  · have : q = 141073 := (Nat.prime_dvd_prime_iff_eq hq prime_141073).mp hdf
    subst this; exact prime_169851893_div_141073
private lemma prime_5471988330230963_sub1 : (5471988330230963 - 1 : ℕ) = 2 * 16108117 * 169851893 := by norm_num
private lemma prime_5471988330230963_pow : (2 : ZMod 5471988330230963) ^ (5471988330230963 - 1) = 1 := by
  reduce_mod_char
private lemma prime_5471988330230963_div_2 : (2 : ZMod 5471988330230963) ^ ((5471988330230963 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5471988330230963_div_16108117 : (2 : ZMod 5471988330230963) ^ ((5471988330230963 - 1) / 16108117) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5471988330230963_div_169851893 : (2 : ZMod 5471988330230963) ^ ((5471988330230963 - 1) / 169851893) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5471988330230963 : Nat.Prime 5471988330230963 := by
  refine lucas_primality 5471988330230963 (2 : ZMod 5471988330230963) prime_5471988330230963_pow ?_
  intro q hq hqd
  rw [prime_5471988330230963_sub1] at hqd
  have : q ∣ [2, 16108117, 169851893].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_5471988330230963_div_2
  · have : q = 16108117 := (Nat.prime_dvd_prime_iff_eq hq prime_16108117).mp hdf
    subst this; exact prime_5471988330230963_div_16108117
  · have : q = 169851893 := (Nat.prime_dvd_prime_iff_eq hq prime_169851893).mp hdf
    subst this; exact prime_5471988330230963_div_169851893
private lemma prime_11556839353447793857_sub1 : (11556839353447793857 - 1 : ℕ) = 2 ^ 6 * 3 * 11 * 5471988330230963 := by norm_num
private lemma prime_11556839353447793857_pow : (10 : ZMod 11556839353447793857) ^ (11556839353447793857 - 1) = 1 := by
  reduce_mod_char
private lemma prime_11556839353447793857_div_2 : (10 : ZMod 11556839353447793857) ^ ((11556839353447793857 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11556839353447793857_div_3 : (10 : ZMod 11556839353447793857) ^ ((11556839353447793857 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11556839353447793857_div_11 : (10 : ZMod 11556839353447793857) ^ ((11556839353447793857 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11556839353447793857_div_5471988330230963 : (10 : ZMod 11556839353447793857) ^ ((11556839353447793857 - 1) / 5471988330230963) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_11556839353447793857 : Nat.Prime 11556839353447793857 := by
  refine lucas_primality 11556839353447793857 (10 : ZMod 11556839353447793857) prime_11556839353447793857_pow ?_
  intro q hq hqd
  rw [prime_11556839353447793857_sub1] at hqd
  have : q ∣ [2 ^ 6, 3, 11, 5471988330230963].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_11556839353447793857_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_11556839353447793857_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_11556839353447793857_div_11
  · have : q = 5471988330230963 := (Nat.prime_dvd_prime_iff_eq hq prime_5471988330230963).mp hdf
    subst this; exact prime_11556839353447793857_div_5471988330230963
private lemma prime_A_62_sub1 : (1759452407304813269615619061186309004572238020607 - 1 : ℕ) = 2 * 17 * 26961574740197 * 166078829751971 * 11556839353447793857 := by norm_num
private lemma prime_A_62_pow : (5 : ZMod 1759452407304813269615619061186309004572238020607) ^ (1759452407304813269615619061186309004572238020607 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_62_div_2 : (5 : ZMod 1759452407304813269615619061186309004572238020607) ^ ((1759452407304813269615619061186309004572238020607 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_62_div_17 : (5 : ZMod 1759452407304813269615619061186309004572238020607) ^ ((1759452407304813269615619061186309004572238020607 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_62_div_26961574740197 : (5 : ZMod 1759452407304813269615619061186309004572238020607) ^ ((1759452407304813269615619061186309004572238020607 - 1) / 26961574740197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_62_div_166078829751971 : (5 : ZMod 1759452407304813269615619061186309004572238020607) ^ ((1759452407304813269615619061186309004572238020607 - 1) / 166078829751971) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_62_div_11556839353447793857 : (5 : ZMod 1759452407304813269615619061186309004572238020607) ^ ((1759452407304813269615619061186309004572238020607 - 1) / 11556839353447793857) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_62 : Nat.Prime 1759452407304813269615619061186309004572238020607 := by
  refine lucas_primality 1759452407304813269615619061186309004572238020607 (5 : ZMod 1759452407304813269615619061186309004572238020607) prime_A_62_pow ?_
  intro q hq hqd
  rw [prime_A_62_sub1] at hqd
  have : q ∣ [2, 17, 26961574740197, 166078829751971, 11556839353447793857].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_62_div_2
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_A_62_div_17
  · have : q = 26961574740197 := (Nat.prime_dvd_prime_iff_eq hq prime_26961574740197).mp hdf
    subst this; exact prime_A_62_div_26961574740197
  · have : q = 166078829751971 := (Nat.prime_dvd_prime_iff_eq hq prime_166078829751971).mp hdf
    subst this; exact prime_A_62_div_166078829751971
  · have : q = 11556839353447793857 := (Nat.prime_dvd_prime_iff_eq hq prime_11556839353447793857).mp hdf
    subst this; exact prime_A_62_div_11556839353447793857
private lemma prime_193 : Nat.Prime 193 := by norm_num
private lemma prime_8389 : Nat.Prime 8389 := by norm_num
private lemma prime_336437 : Nat.Prime 336437 := by norm_num
private lemma prime_1430647 : Nat.Prime 1430647 := by norm_num
private lemma prime_4744163 : Nat.Prime 4744163 := by norm_num
private lemma prime_3705823519649707_sub1 : (3705823519649707 - 1 : ℕ) = 2 * 3 * 7 * 13 * 1430647 * 4744163 := by norm_num
private lemma prime_3705823519649707_pow : (3 : ZMod 3705823519649707) ^ (3705823519649707 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3705823519649707_div_2 : (3 : ZMod 3705823519649707) ^ ((3705823519649707 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3705823519649707_div_3 : (3 : ZMod 3705823519649707) ^ ((3705823519649707 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3705823519649707_div_7 : (3 : ZMod 3705823519649707) ^ ((3705823519649707 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3705823519649707_div_13 : (3 : ZMod 3705823519649707) ^ ((3705823519649707 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3705823519649707_div_1430647 : (3 : ZMod 3705823519649707) ^ ((3705823519649707 - 1) / 1430647) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3705823519649707_div_4744163 : (3 : ZMod 3705823519649707) ^ ((3705823519649707 - 1) / 4744163) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3705823519649707 : Nat.Prime 3705823519649707 := by
  refine lucas_primality 3705823519649707 (3 : ZMod 3705823519649707) prime_3705823519649707_pow ?_
  intro q hq hqd
  rw [prime_3705823519649707_sub1] at hqd
  have : q ∣ [2, 3, 7, 13, 1430647, 4744163].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3705823519649707_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_3705823519649707_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_3705823519649707_div_7
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_3705823519649707_div_13
  · have : q = 1430647 := (Nat.prime_dvd_prime_iff_eq hq prime_1430647).mp hdf
    subst this; exact prime_3705823519649707_div_1430647
  · have : q = 4744163 := (Nat.prime_dvd_prime_iff_eq hq prime_4744163).mp hdf
    subst this; exact prime_3705823519649707_div_4744163
private lemma prime_B_62_sub1 : (1759452407304813269615619061186309004572238020609 - 1 : ℕ) = 2 ^ 62 * 3 ^ 3 * 7 * 193 * 8389 * 336437 * 3705823519649707 := by norm_num
private lemma prime_B_62_pow : (22 : ZMod 1759452407304813269615619061186309004572238020609) ^ (1759452407304813269615619061186309004572238020609 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_62_div_2 : (22 : ZMod 1759452407304813269615619061186309004572238020609) ^ ((1759452407304813269615619061186309004572238020609 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_62_div_3 : (22 : ZMod 1759452407304813269615619061186309004572238020609) ^ ((1759452407304813269615619061186309004572238020609 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_62_div_7 : (22 : ZMod 1759452407304813269615619061186309004572238020609) ^ ((1759452407304813269615619061186309004572238020609 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_62_div_193 : (22 : ZMod 1759452407304813269615619061186309004572238020609) ^ ((1759452407304813269615619061186309004572238020609 - 1) / 193) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_62_div_8389 : (22 : ZMod 1759452407304813269615619061186309004572238020609) ^ ((1759452407304813269615619061186309004572238020609 - 1) / 8389) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_62_div_336437 : (22 : ZMod 1759452407304813269615619061186309004572238020609) ^ ((1759452407304813269615619061186309004572238020609 - 1) / 336437) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_62_div_3705823519649707 : (22 : ZMod 1759452407304813269615619061186309004572238020609) ^ ((1759452407304813269615619061186309004572238020609 - 1) / 3705823519649707) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_62 : Nat.Prime 1759452407304813269615619061186309004572238020609 := by
  refine lucas_primality 1759452407304813269615619061186309004572238020609 (22 : ZMod 1759452407304813269615619061186309004572238020609) prime_B_62_pow ?_
  intro q hq hqd
  rw [prime_B_62_sub1] at hqd
  have : q ∣ [2 ^ 62, 3 ^ 3, 7, 193, 8389, 336437, 3705823519649707].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_62_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_62_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_B_62_div_7
  · have : q = 193 := (Nat.prime_dvd_prime_iff_eq hq prime_193).mp hdf
    subst this; exact prime_B_62_div_193
  · have : q = 8389 := (Nat.prime_dvd_prime_iff_eq hq prime_8389).mp hdf
    subst this; exact prime_B_62_div_8389
  · have : q = 336437 := (Nat.prime_dvd_prime_iff_eq hq prime_336437).mp hdf
    subst this; exact prime_B_62_div_336437
  · have : q = 3705823519649707 := (Nat.prime_dvd_prime_iff_eq hq prime_3705823519649707).mp hdf
    subst this; exact prime_B_62_div_3705823519649707
private lemma pair_62 :
    Nat.Prime ((3 ^ 62 - 4482) * (2 ^ 62) - 1) ∧
    Nat.Prime ((3 ^ 62 - 4482) * (2 ^ 62) + 1) := by
  constructor
  · convert prime_A_62
  · convert prime_B_62

/- Pair for n = 63 -/
private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_97 : Nat.Prime 97 := by norm_num
private lemma prime_27259 : Nat.Prime 27259 := by norm_num
private lemma prime_2786905643_sub1 : (2786905643 - 1 : ℕ) = 2 * 17 * 31 * 97 * 27259 := by norm_num
private lemma prime_2786905643_pow : (2 : ZMod 2786905643) ^ (2786905643 - 1) = 1 := by
  reduce_mod_char
private lemma prime_2786905643_div_2 : (2 : ZMod 2786905643) ^ ((2786905643 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2786905643_div_17 : (2 : ZMod 2786905643) ^ ((2786905643 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2786905643_div_31 : (2 : ZMod 2786905643) ^ ((2786905643 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2786905643_div_97 : (2 : ZMod 2786905643) ^ ((2786905643 - 1) / 97) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2786905643_div_27259 : (2 : ZMod 2786905643) ^ ((2786905643 - 1) / 27259) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_2786905643 : Nat.Prime 2786905643 := by
  refine lucas_primality 2786905643 (2 : ZMod 2786905643) prime_2786905643_pow ?_
  intro q hq hqd
  rw [prime_2786905643_sub1] at hqd
  have : q ∣ [2, 17, 31, 97, 27259].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_2786905643_div_2
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_2786905643_div_17
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_2786905643_div_31
  · have : q = 97 := (Nat.prime_dvd_prime_iff_eq hq prime_97).mp hdf
    subst this; exact prime_2786905643_div_97
  · have : q = 27259 := (Nat.prime_dvd_prime_iff_eq hq prime_27259).mp hdf
    subst this; exact prime_2786905643_div_27259
private lemma prime_283 : Nat.Prime 283 := by norm_num
private lemma prime_70522873 : Nat.Prime 70522873 := by norm_num
private lemma prime_14809803331_sub1 : (14809803331 - 1 : ℕ) = 2 * 3 * 5 * 7 * 70522873 := by norm_num
private lemma prime_14809803331_pow : (3 : ZMod 14809803331) ^ (14809803331 - 1) = 1 := by
  reduce_mod_char
private lemma prime_14809803331_div_2 : (3 : ZMod 14809803331) ^ ((14809803331 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_14809803331_div_3 : (3 : ZMod 14809803331) ^ ((14809803331 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_14809803331_div_5 : (3 : ZMod 14809803331) ^ ((14809803331 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_14809803331_div_7 : (3 : ZMod 14809803331) ^ ((14809803331 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_14809803331_div_70522873 : (3 : ZMod 14809803331) ^ ((14809803331 - 1) / 70522873) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_14809803331 : Nat.Prime 14809803331 := by
  refine lucas_primality 14809803331 (3 : ZMod 14809803331) prime_14809803331_pow ?_
  intro q hq hqd
  rw [prime_14809803331_sub1] at hqd
  have : q ∣ [2, 3, 5, 7, 70522873].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_14809803331_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_14809803331_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_14809803331_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_14809803331_div_7
  · have : q = 70522873 := (Nat.prime_dvd_prime_iff_eq hq prime_70522873).mp hdf
    subst this; exact prime_14809803331_div_70522873
private lemma prime_251470460560381_sub1 : (251470460560381 - 1 : ℕ) = 2 ^ 2 * 3 * 5 * 283 * 14809803331 := by norm_num
private lemma prime_251470460560381_pow : (10 : ZMod 251470460560381) ^ (251470460560381 - 1) = 1 := by
  reduce_mod_char
private lemma prime_251470460560381_div_2 : (10 : ZMod 251470460560381) ^ ((251470460560381 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251470460560381_div_3 : (10 : ZMod 251470460560381) ^ ((251470460560381 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251470460560381_div_5 : (10 : ZMod 251470460560381) ^ ((251470460560381 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251470460560381_div_283 : (10 : ZMod 251470460560381) ^ ((251470460560381 - 1) / 283) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251470460560381_div_14809803331 : (10 : ZMod 251470460560381) ^ ((251470460560381 - 1) / 14809803331) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_251470460560381 : Nat.Prime 251470460560381 := by
  refine lucas_primality 251470460560381 (10 : ZMod 251470460560381) prime_251470460560381_pow ?_
  intro q hq hqd
  rw [prime_251470460560381_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 5, 283, 14809803331].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_251470460560381_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_251470460560381_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_251470460560381_div_5
  · have : q = 283 := (Nat.prime_dvd_prime_iff_eq hq prime_283).mp hdf
    subst this; exact prime_251470460560381_div_283
  · have : q = 14809803331 := (Nat.prime_dvd_prime_iff_eq hq prime_14809803331).mp hdf
    subst this; exact prime_251470460560381_div_14809803331
private lemma prime_359 : Nat.Prime 359 := by norm_num
private lemma prime_2473 : Nat.Prime 2473 := by norm_num
private lemma prime_73 : Nat.Prime 73 := by norm_num
private lemma prime_16831 : Nat.Prime 16831 := by norm_num
private lemma prime_3133090651_sub1 : (3133090651 - 1 : ℕ) = 2 * 3 * 5 ^ 2 * 17 * 73 * 16831 := by norm_num
private lemma prime_3133090651_pow : (2 : ZMod 3133090651) ^ (3133090651 - 1) = 1 := by
  reduce_mod_char
private lemma prime_3133090651_div_2 : (2 : ZMod 3133090651) ^ ((3133090651 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3133090651_div_3 : (2 : ZMod 3133090651) ^ ((3133090651 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3133090651_div_5 : (2 : ZMod 3133090651) ^ ((3133090651 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3133090651_div_17 : (2 : ZMod 3133090651) ^ ((3133090651 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3133090651_div_73 : (2 : ZMod 3133090651) ^ ((3133090651 - 1) / 73) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3133090651_div_16831 : (2 : ZMod 3133090651) ^ ((3133090651 - 1) / 16831) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_3133090651 : Nat.Prime 3133090651 := by
  refine lucas_primality 3133090651 (2 : ZMod 3133090651) prime_3133090651_pow ?_
  intro q hq hqd
  rw [prime_3133090651_sub1] at hqd
  have : q ∣ [2, 3, 5 ^ 2, 17, 73, 16831].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_3133090651_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_3133090651_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_3133090651_div_5
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_3133090651_div_17
  · have : q = 73 := (Nat.prime_dvd_prime_iff_eq hq prime_73).mp hdf
    subst this; exact prime_3133090651_div_73
  · have : q = 16831 := (Nat.prime_dvd_prime_iff_eq hq prime_16831).mp hdf
    subst this; exact prime_3133090651_div_16831
private lemma prime_150205309825987279_sub1 : (150205309825987279 - 1 : ℕ) = 2 * 3 ^ 3 * 359 * 2473 * 3133090651 := by norm_num
private lemma prime_150205309825987279_pow : (6 : ZMod 150205309825987279) ^ (150205309825987279 - 1) = 1 := by
  reduce_mod_char
private lemma prime_150205309825987279_div_2 : (6 : ZMod 150205309825987279) ^ ((150205309825987279 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150205309825987279_div_3 : (6 : ZMod 150205309825987279) ^ ((150205309825987279 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150205309825987279_div_359 : (6 : ZMod 150205309825987279) ^ ((150205309825987279 - 1) / 359) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150205309825987279_div_2473 : (6 : ZMod 150205309825987279) ^ ((150205309825987279 - 1) / 2473) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150205309825987279_div_3133090651 : (6 : ZMod 150205309825987279) ^ ((150205309825987279 - 1) / 3133090651) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_150205309825987279 : Nat.Prime 150205309825987279 := by
  refine lucas_primality 150205309825987279 (6 : ZMod 150205309825987279) prime_150205309825987279_pow ?_
  intro q hq hqd
  rw [prime_150205309825987279_sub1] at hqd
  have : q ∣ [2, 3 ^ 3, 359, 2473, 3133090651].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_150205309825987279_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_150205309825987279_div_3
  · have : q = 359 := (Nat.prime_dvd_prime_iff_eq hq prime_359).mp hdf
    subst this; exact prime_150205309825987279_div_359
  · have : q = 2473 := (Nat.prime_dvd_prime_iff_eq hq prime_2473).mp hdf
    subst this; exact prime_150205309825987279_div_2473
  · have : q = 3133090651 := (Nat.prime_dvd_prime_iff_eq hq prime_3133090651).mp hdf
    subst this; exact prime_150205309825987279_div_3133090651
private lemma prime_117160141664270077621_sub1 : (117160141664270077621 - 1 : ℕ) = 2 ^ 2 * 3 * 5 * 13 * 150205309825987279 := by norm_num
private lemma prime_117160141664270077621_pow : (6 : ZMod 117160141664270077621) ^ (117160141664270077621 - 1) = 1 := by
  reduce_mod_char
private lemma prime_117160141664270077621_div_2 : (6 : ZMod 117160141664270077621) ^ ((117160141664270077621 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_117160141664270077621_div_3 : (6 : ZMod 117160141664270077621) ^ ((117160141664270077621 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_117160141664270077621_div_5 : (6 : ZMod 117160141664270077621) ^ ((117160141664270077621 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_117160141664270077621_div_13 : (6 : ZMod 117160141664270077621) ^ ((117160141664270077621 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_117160141664270077621_div_150205309825987279 : (6 : ZMod 117160141664270077621) ^ ((117160141664270077621 - 1) / 150205309825987279) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_117160141664270077621 : Nat.Prime 117160141664270077621 := by
  refine lucas_primality 117160141664270077621 (6 : ZMod 117160141664270077621) prime_117160141664270077621_pow ?_
  intro q hq hqd
  rw [prime_117160141664270077621_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 5, 13, 150205309825987279].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_117160141664270077621_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_117160141664270077621_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_117160141664270077621_div_5
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_117160141664270077621_div_13
  · have : q = 150205309825987279 := (Nat.prime_dvd_prime_iff_eq hq prime_150205309825987279).mp hdf
    subst this; exact prime_117160141664270077621_div_150205309825987279
private lemma prime_A_63_sub1 : (10556714443828879617693714437981021386588670656511 - 1 : ℕ) = 2 * 5 * 13 * 23 * 43 * 2786905643 * 251470460560381 * 117160141664270077621 := by norm_num
private lemma prime_A_63_pow : (19 : ZMod 10556714443828879617693714437981021386588670656511) ^ (10556714443828879617693714437981021386588670656511 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_63_div_2 : (19 : ZMod 10556714443828879617693714437981021386588670656511) ^ ((10556714443828879617693714437981021386588670656511 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_63_div_5 : (19 : ZMod 10556714443828879617693714437981021386588670656511) ^ ((10556714443828879617693714437981021386588670656511 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_63_div_13 : (19 : ZMod 10556714443828879617693714437981021386588670656511) ^ ((10556714443828879617693714437981021386588670656511 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_63_div_23 : (19 : ZMod 10556714443828879617693714437981021386588670656511) ^ ((10556714443828879617693714437981021386588670656511 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_63_div_43 : (19 : ZMod 10556714443828879617693714437981021386588670656511) ^ ((10556714443828879617693714437981021386588670656511 - 1) / 43) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_63_div_2786905643 : (19 : ZMod 10556714443828879617693714437981021386588670656511) ^ ((10556714443828879617693714437981021386588670656511 - 1) / 2786905643) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_63_div_251470460560381 : (19 : ZMod 10556714443828879617693714437981021386588670656511) ^ ((10556714443828879617693714437981021386588670656511 - 1) / 251470460560381) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_63_div_117160141664270077621 : (19 : ZMod 10556714443828879617693714437981021386588670656511) ^ ((10556714443828879617693714437981021386588670656511 - 1) / 117160141664270077621) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_63 : Nat.Prime 10556714443828879617693714437981021386588670656511 := by
  refine lucas_primality 10556714443828879617693714437981021386588670656511 (19 : ZMod 10556714443828879617693714437981021386588670656511) prime_A_63_pow ?_
  intro q hq hqd
  rw [prime_A_63_sub1] at hqd
  have : q ∣ [2, 5, 13, 23, 43, 2786905643, 251470460560381, 117160141664270077621].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_63_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_63_div_5
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_A_63_div_13
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_A_63_div_23
  · have : q = 43 := (Nat.prime_dvd_prime_iff_eq hq prime_43).mp hdf
    subst this; exact prime_A_63_div_43
  · have : q = 2786905643 := (Nat.prime_dvd_prime_iff_eq hq prime_2786905643).mp hdf
    subst this; exact prime_A_63_div_2786905643
  · have : q = 251470460560381 := (Nat.prime_dvd_prime_iff_eq hq prime_251470460560381).mp hdf
    subst this; exact prime_A_63_div_251470460560381
  · have : q = 117160141664270077621 := (Nat.prime_dvd_prime_iff_eq hq prime_117160141664270077621).mp hdf
    subst this; exact prime_A_63_div_117160141664270077621
private lemma prime_107 : Nat.Prime 107 := by norm_num
private lemma prime_2383 : Nat.Prime 2383 := by norm_num
private lemma prime_29 : Nat.Prime 29 := by norm_num
private lemma prime_1097189 : Nat.Prime 1097189 := by norm_num
private lemma prime_1463650127_sub1 : (1463650127 - 1 : ℕ) = 2 * 23 * 29 * 1097189 := by norm_num
private lemma prime_1463650127_pow : (5 : ZMod 1463650127) ^ (1463650127 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1463650127_div_2 : (5 : ZMod 1463650127) ^ ((1463650127 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1463650127_div_23 : (5 : ZMod 1463650127) ^ ((1463650127 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1463650127_div_29 : (5 : ZMod 1463650127) ^ ((1463650127 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1463650127_div_1097189 : (5 : ZMod 1463650127) ^ ((1463650127 - 1) / 1097189) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1463650127 : Nat.Prime 1463650127 := by
  refine lucas_primality 1463650127 (5 : ZMod 1463650127) prime_1463650127_pow ?_
  intro q hq hqd
  rw [prime_1463650127_sub1] at hqd
  have : q ∣ [2, 23, 29, 1097189].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1463650127_div_2
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_1463650127_div_23
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_1463650127_div_29
  · have : q = 1097189 := (Nat.prime_dvd_prime_iff_eq hq prime_1097189).mp hdf
    subst this; exact prime_1463650127_div_1097189
private lemma prime_20927269515847_sub1 : (20927269515847 - 1 : ℕ) = 2 * 3 * 2383 * 1463650127 := by norm_num
private lemma prime_20927269515847_pow : (3 : ZMod 20927269515847) ^ (20927269515847 - 1) = 1 := by
  reduce_mod_char
private lemma prime_20927269515847_div_2 : (3 : ZMod 20927269515847) ^ ((20927269515847 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_20927269515847_div_3 : (3 : ZMod 20927269515847) ^ ((20927269515847 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_20927269515847_div_2383 : (3 : ZMod 20927269515847) ^ ((20927269515847 - 1) / 2383) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_20927269515847_div_1463650127 : (3 : ZMod 20927269515847) ^ ((20927269515847 - 1) / 1463650127) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_20927269515847 : Nat.Prime 20927269515847 := by
  refine lucas_primality 20927269515847 (3 : ZMod 20927269515847) prime_20927269515847_pow ?_
  intro q hq hqd
  rw [prime_20927269515847_sub1] at hqd
  have : q ∣ [2, 3, 2383, 1463650127].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_20927269515847_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_20927269515847_div_3
  · have : q = 2383 := (Nat.prime_dvd_prime_iff_eq hq prime_2383).mp hdf
    subst this; exact prime_20927269515847_div_2383
  · have : q = 1463650127 := (Nat.prime_dvd_prime_iff_eq hq prime_1463650127).mp hdf
    subst this; exact prime_20927269515847_div_1463650127
private lemma prime_367 : Nat.Prime 367 := by norm_num
private lemma prime_5167 : Nat.Prime 5167 := by norm_num
private lemma prime_1706815111_sub1 : (1706815111 - 1 : ℕ) = 2 * 3 * 5 * 7 * 11 ^ 2 * 13 * 5167 := by norm_num
private lemma prime_1706815111_pow : (3 : ZMod 1706815111) ^ (1706815111 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1706815111_div_2 : (3 : ZMod 1706815111) ^ ((1706815111 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1706815111_div_3 : (3 : ZMod 1706815111) ^ ((1706815111 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1706815111_div_5 : (3 : ZMod 1706815111) ^ ((1706815111 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1706815111_div_7 : (3 : ZMod 1706815111) ^ ((1706815111 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1706815111_div_11 : (3 : ZMod 1706815111) ^ ((1706815111 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1706815111_div_13 : (3 : ZMod 1706815111) ^ ((1706815111 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1706815111_div_5167 : (3 : ZMod 1706815111) ^ ((1706815111 - 1) / 5167) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1706815111 : Nat.Prime 1706815111 := by
  refine lucas_primality 1706815111 (3 : ZMod 1706815111) prime_1706815111_pow ?_
  intro q hq hqd
  rw [prime_1706815111_sub1] at hqd
  have : q ∣ [2, 3, 5, 7, 11 ^ 2, 13, 5167].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_1706815111_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1706815111_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_1706815111_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_1706815111_div_7
  · have : q = 11 := prime_eq_of_dvd_prime_pow hq prime_11 hdf
    subst this; exact prime_1706815111_div_11
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_1706815111_div_13
  · have : q = 5167 := (Nat.prime_dvd_prime_iff_eq hq prime_5167).mp hdf
    subst this; exact prime_1706815111_div_5167
private lemma prime_21297638955059_sub1 : (21297638955059 - 1 : ℕ) = 2 * 17 * 367 * 1706815111 := by norm_num
private lemma prime_21297638955059_pow : (2 : ZMod 21297638955059) ^ (21297638955059 - 1) = 1 := by
  reduce_mod_char
private lemma prime_21297638955059_div_2 : (2 : ZMod 21297638955059) ^ ((21297638955059 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_21297638955059_div_17 : (2 : ZMod 21297638955059) ^ ((21297638955059 - 1) / 17) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_21297638955059_div_367 : (2 : ZMod 21297638955059) ^ ((21297638955059 - 1) / 367) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_21297638955059_div_1706815111 : (2 : ZMod 21297638955059) ^ ((21297638955059 - 1) / 1706815111) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_21297638955059 : Nat.Prime 21297638955059 := by
  refine lucas_primality 21297638955059 (2 : ZMod 21297638955059) prime_21297638955059_pow ?_
  intro q hq hqd
  rw [prime_21297638955059_sub1] at hqd
  have : q ∣ [2, 17, 367, 1706815111].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_21297638955059_div_2
  · have : q = 17 := (Nat.prime_dvd_prime_iff_eq hq prime_17).mp hdf
    subst this; exact prime_21297638955059_div_17
  · have : q = 367 := (Nat.prime_dvd_prime_iff_eq hq prime_367).mp hdf
    subst this; exact prime_21297638955059_div_367
  · have : q = 1706815111 := (Nat.prime_dvd_prime_iff_eq hq prime_1706815111).mp hdf
    subst this; exact prime_21297638955059_div_1706815111
private lemma prime_B_63_sub1 : (10556714443828879617693714437981021386588670656513 - 1 : ℕ) = 2 ^ 66 * 3 * 107 * 20927269515847 * 21297638955059 := by norm_num
private lemma prime_B_63_pow : (5 : ZMod 10556714443828879617693714437981021386588670656513) ^ (10556714443828879617693714437981021386588670656513 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_63_div_2 : (5 : ZMod 10556714443828879617693714437981021386588670656513) ^ ((10556714443828879617693714437981021386588670656513 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_63_div_3 : (5 : ZMod 10556714443828879617693714437981021386588670656513) ^ ((10556714443828879617693714437981021386588670656513 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_63_div_107 : (5 : ZMod 10556714443828879617693714437981021386588670656513) ^ ((10556714443828879617693714437981021386588670656513 - 1) / 107) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_63_div_20927269515847 : (5 : ZMod 10556714443828879617693714437981021386588670656513) ^ ((10556714443828879617693714437981021386588670656513 - 1) / 20927269515847) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_63_div_21297638955059 : (5 : ZMod 10556714443828879617693714437981021386588670656513) ^ ((10556714443828879617693714437981021386588670656513 - 1) / 21297638955059) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_63 : Nat.Prime 10556714443828879617693714437981021386588670656513 := by
  refine lucas_primality 10556714443828879617693714437981021386588670656513 (5 : ZMod 10556714443828879617693714437981021386588670656513) prime_B_63_pow ?_
  intro q hq hqd
  rw [prime_B_63_sub1] at hqd
  have : q ∣ [2 ^ 66, 3, 107, 20927269515847, 21297638955059].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_63_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_63_div_3
  · have : q = 107 := (Nat.prime_dvd_prime_iff_eq hq prime_107).mp hdf
    subst this; exact prime_B_63_div_107
  · have : q = 20927269515847 := (Nat.prime_dvd_prime_iff_eq hq prime_20927269515847).mp hdf
    subst this; exact prime_B_63_div_20927269515847
  · have : q = 21297638955059 := (Nat.prime_dvd_prime_iff_eq hq prime_21297638955059).mp hdf
    subst this; exact prime_B_63_div_21297638955059
private lemma pair_63 :
    Nat.Prime ((3 ^ 63 - 5763) * (2 ^ 63) - 1) ∧
    Nat.Prime ((3 ^ 63 - 5763) * (2 ^ 63) + 1) := by
  constructor
  · convert prime_A_63
  · convert prime_B_63

/- Pair for n = 64 -/
private lemma prime_157 : Nat.Prime 157 := by norm_num
private lemma prime_1381 : Nat.Prime 1381 := by norm_num
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_37186309 : Nat.Prime 37186309 := by norm_num
private lemma prime_2228867 : Nat.Prime 2228867 := by norm_num
private lemma prime_196837 : Nat.Prime 196837 := by norm_num
private lemma prime_1063 : Nat.Prime 1063 := by norm_num
private lemma prime_148243 : Nat.Prime 148243 := by norm_num
private lemma prime_63082351 : Nat.Prime 63082351 := by norm_num
private lemma prime_39762650110913837_sub1 : (39762650110913837 - 1 : ℕ) = 2 ^ 2 * 1063 * 148243 * 63082351 := by norm_num
private lemma prime_39762650110913837_pow : (2 : ZMod 39762650110913837) ^ (39762650110913837 - 1) = 1 := by
  reduce_mod_char
private lemma prime_39762650110913837_div_2 : (2 : ZMod 39762650110913837) ^ ((39762650110913837 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_39762650110913837_div_1063 : (2 : ZMod 39762650110913837) ^ ((39762650110913837 - 1) / 1063) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_39762650110913837_div_148243 : (2 : ZMod 39762650110913837) ^ ((39762650110913837 - 1) / 148243) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_39762650110913837_div_63082351 : (2 : ZMod 39762650110913837) ^ ((39762650110913837 - 1) / 63082351) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_39762650110913837 : Nat.Prime 39762650110913837 := by
  refine lucas_primality 39762650110913837 (2 : ZMod 39762650110913837) prime_39762650110913837_pow ?_
  intro q hq hqd
  rw [prime_39762650110913837_sub1] at hqd
  have : q ∣ [2 ^ 2, 1063, 148243, 63082351].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_39762650110913837_div_2
  · have : q = 1063 := (Nat.prime_dvd_prime_iff_eq hq prime_1063).mp hdf
    subst this; exact prime_39762650110913837_div_1063
  · have : q = 148243 := (Nat.prime_dvd_prime_iff_eq hq prime_148243).mp hdf
    subst this; exact prime_39762650110913837_div_148243
  · have : q = 63082351 := (Nat.prime_dvd_prime_iff_eq hq prime_63082351).mp hdf
    subst this; exact prime_39762650110913837_div_63082351
private lemma prime_62614086079055575468553_sub1 : (62614086079055575468553 - 1 : ℕ) = 2 ^ 3 * 196837 * 39762650110913837 := by norm_num
private lemma prime_62614086079055575468553_pow : (3 : ZMod 62614086079055575468553) ^ (62614086079055575468553 - 1) = 1 := by
  reduce_mod_char
private lemma prime_62614086079055575468553_div_2 : (3 : ZMod 62614086079055575468553) ^ ((62614086079055575468553 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_62614086079055575468553_div_196837 : (3 : ZMod 62614086079055575468553) ^ ((62614086079055575468553 - 1) / 196837) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_62614086079055575468553_div_39762650110913837 : (3 : ZMod 62614086079055575468553) ^ ((62614086079055575468553 - 1) / 39762650110913837) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_62614086079055575468553 : Nat.Prime 62614086079055575468553 := by
  refine lucas_primality 62614086079055575468553 (3 : ZMod 62614086079055575468553) prime_62614086079055575468553_pow ?_
  intro q hq hqd
  rw [prime_62614086079055575468553_sub1] at hqd
  have : q ∣ [2 ^ 3, 196837, 39762650110913837].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_62614086079055575468553_div_2
  · have : q = 196837 := (Nat.prime_dvd_prime_iff_eq hq prime_196837).mp hdf
    subst this; exact prime_62614086079055575468553_div_196837
  · have : q = 39762650110913837 := (Nat.prime_dvd_prime_iff_eq hq prime_39762650110913837).mp hdf
    subst this; exact prime_62614086079055575468553_div_39762650110913837
private lemma prime_13397613138889570879475262667297_sub1 : (13397613138889570879475262667297 - 1 : ℕ) = 2 ^ 5 * 3 * 2228867 * 62614086079055575468553 := by norm_num
private lemma prime_13397613138889570879475262667297_pow : (5 : ZMod 13397613138889570879475262667297) ^ (13397613138889570879475262667297 - 1) = 1 := by
  reduce_mod_char
private lemma prime_13397613138889570879475262667297_div_2 : (5 : ZMod 13397613138889570879475262667297) ^ ((13397613138889570879475262667297 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13397613138889570879475262667297_div_3 : (5 : ZMod 13397613138889570879475262667297) ^ ((13397613138889570879475262667297 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13397613138889570879475262667297_div_2228867 : (5 : ZMod 13397613138889570879475262667297) ^ ((13397613138889570879475262667297 - 1) / 2228867) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13397613138889570879475262667297_div_62614086079055575468553 : (5 : ZMod 13397613138889570879475262667297) ^ ((13397613138889570879475262667297 - 1) / 62614086079055575468553) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_13397613138889570879475262667297 : Nat.Prime 13397613138889570879475262667297 := by
  refine lucas_primality 13397613138889570879475262667297 (5 : ZMod 13397613138889570879475262667297) prime_13397613138889570879475262667297_pow ?_
  intro q hq hqd
  rw [prime_13397613138889570879475262667297_sub1] at hqd
  have : q ∣ [2 ^ 5, 3, 2228867, 62614086079055575468553].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_13397613138889570879475262667297_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_13397613138889570879475262667297_div_3
  · have : q = 2228867 := (Nat.prime_dvd_prime_iff_eq hq prime_2228867).mp hdf
    subst this; exact prime_13397613138889570879475262667297_div_2228867
  · have : q = 62614086079055575468553 := (Nat.prime_dvd_prime_iff_eq hq prime_62614086079055575468553).mp hdf
    subst this; exact prime_13397613138889570879475262667297_div_62614086079055575468553
private lemma prime_516143262198834969587225354916752172496829_sub1 : (516143262198834969587225354916752172496829 - 1 : ℕ) = 2 ^ 2 * 7 * 37 * 37186309 * 13397613138889570879475262667297 := by norm_num
private lemma prime_516143262198834969587225354916752172496829_pow : (2 : ZMod 516143262198834969587225354916752172496829) ^ (516143262198834969587225354916752172496829 - 1) = 1 := by
  reduce_mod_char
private lemma prime_516143262198834969587225354916752172496829_div_2 : (2 : ZMod 516143262198834969587225354916752172496829) ^ ((516143262198834969587225354916752172496829 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_516143262198834969587225354916752172496829_div_7 : (2 : ZMod 516143262198834969587225354916752172496829) ^ ((516143262198834969587225354916752172496829 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_516143262198834969587225354916752172496829_div_37 : (2 : ZMod 516143262198834969587225354916752172496829) ^ ((516143262198834969587225354916752172496829 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_516143262198834969587225354916752172496829_div_37186309 : (2 : ZMod 516143262198834969587225354916752172496829) ^ ((516143262198834969587225354916752172496829 - 1) / 37186309) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_516143262198834969587225354916752172496829_div_13397613138889570879475262667297 : (2 : ZMod 516143262198834969587225354916752172496829) ^ ((516143262198834969587225354916752172496829 - 1) / 13397613138889570879475262667297) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_516143262198834969587225354916752172496829 : Nat.Prime 516143262198834969587225354916752172496829 := by
  refine lucas_primality 516143262198834969587225354916752172496829 (2 : ZMod 516143262198834969587225354916752172496829) prime_516143262198834969587225354916752172496829_pow ?_
  intro q hq hqd
  rw [prime_516143262198834969587225354916752172496829_sub1] at hqd
  have : q ∣ [2 ^ 2, 7, 37, 37186309, 13397613138889570879475262667297].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_516143262198834969587225354916752172496829_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_516143262198834969587225354916752172496829_div_7
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_516143262198834969587225354916752172496829_div_37
  · have : q = 37186309 := (Nat.prime_dvd_prime_iff_eq hq prime_37186309).mp hdf
    subst this; exact prime_516143262198834969587225354916752172496829_div_37186309
  · have : q = 13397613138889570879475262667297 := (Nat.prime_dvd_prime_iff_eq hq prime_13397613138889570879475262667297).mp hdf
    subst this; exact prime_516143262198834969587225354916752172496829_div_13397613138889570879475262667297
private lemma prime_A_64_sub1 : (63340286662973277706162286913773767973882654883839 - 1 : ℕ) = 2 * 157 * 283 * 1381 * 516143262198834969587225354916752172496829 := by norm_num
private lemma prime_A_64_pow : (7 : ZMod 63340286662973277706162286913773767973882654883839) ^ (63340286662973277706162286913773767973882654883839 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_64_div_2 : (7 : ZMod 63340286662973277706162286913773767973882654883839) ^ ((63340286662973277706162286913773767973882654883839 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_64_div_157 : (7 : ZMod 63340286662973277706162286913773767973882654883839) ^ ((63340286662973277706162286913773767973882654883839 - 1) / 157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_64_div_283 : (7 : ZMod 63340286662973277706162286913773767973882654883839) ^ ((63340286662973277706162286913773767973882654883839 - 1) / 283) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_64_div_1381 : (7 : ZMod 63340286662973277706162286913773767973882654883839) ^ ((63340286662973277706162286913773767973882654883839 - 1) / 1381) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_64_div_516143262198834969587225354916752172496829 : (7 : ZMod 63340286662973277706162286913773767973882654883839) ^ ((63340286662973277706162286913773767973882654883839 - 1) / 516143262198834969587225354916752172496829) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_64 : Nat.Prime 63340286662973277706162286913773767973882654883839 := by
  refine lucas_primality 63340286662973277706162286913773767973882654883839 (7 : ZMod 63340286662973277706162286913773767973882654883839) prime_A_64_pow ?_
  intro q hq hqd
  rw [prime_A_64_sub1] at hqd
  have : q ∣ [2, 157, 283, 1381, 516143262198834969587225354916752172496829].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_64_div_2
  · have : q = 157 := (Nat.prime_dvd_prime_iff_eq hq prime_157).mp hdf
    subst this; exact prime_A_64_div_157
  · have : q = 283 := (Nat.prime_dvd_prime_iff_eq hq prime_283).mp hdf
    subst this; exact prime_A_64_div_283
  · have : q = 1381 := (Nat.prime_dvd_prime_iff_eq hq prime_1381).mp hdf
    subst this; exact prime_A_64_div_1381
  · have : q = 516143262198834969587225354916752172496829 := (Nat.prime_dvd_prime_iff_eq hq prime_516143262198834969587225354916752172496829).mp hdf
    subst this; exact prime_A_64_div_516143262198834969587225354916752172496829
private lemma prime_59 : Nat.Prime 59 := by norm_num
private lemma prime_953 : Nat.Prime 953 := by norm_num
private lemma prime_1901 : Nat.Prime 1901 := by norm_num
private lemma prime_8627 : Nat.Prime 8627 := by norm_num
private lemma prime_263 : Nat.Prime 263 := by norm_num
private lemma prime_1429367 : Nat.Prime 1429367 := by norm_num
private lemma prime_63155151529_sub1 : (63155151529 - 1 : ℕ) = 2 ^ 3 * 3 * 7 * 263 * 1429367 := by norm_num
private lemma prime_63155151529_pow : (11 : ZMod 63155151529) ^ (63155151529 - 1) = 1 := by
  reduce_mod_char
private lemma prime_63155151529_div_2 : (11 : ZMod 63155151529) ^ ((63155151529 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_63155151529_div_3 : (11 : ZMod 63155151529) ^ ((63155151529 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_63155151529_div_7 : (11 : ZMod 63155151529) ^ ((63155151529 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_63155151529_div_263 : (11 : ZMod 63155151529) ^ ((63155151529 - 1) / 263) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_63155151529_div_1429367 : (11 : ZMod 63155151529) ^ ((63155151529 - 1) / 1429367) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_63155151529 : Nat.Prime 63155151529 := by
  refine lucas_primality 63155151529 (11 : ZMod 63155151529) prime_63155151529_pow ?_
  intro q hq hqd
  rw [prime_63155151529_sub1] at hqd
  have : q ∣ [2 ^ 3, 3, 7, 263, 1429367].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_63155151529_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_63155151529_div_3
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_63155151529_div_7
  · have : q = 263 := (Nat.prime_dvd_prime_iff_eq hq prime_263).mp hdf
    subst this; exact prime_63155151529_div_263
  · have : q = 1429367 := (Nat.prime_dvd_prime_iff_eq hq prime_1429367).mp hdf
    subst this; exact prime_63155151529_div_1429367
private lemma prime_646644787249060731573982879_sub1 : (646644787249060731573982879 - 1 : ℕ) = 2 * 3 * 13 * 37 * 227 * 953 * 1901 * 8627 * 63155151529 := by norm_num
private lemma prime_646644787249060731573982879_pow : (3 : ZMod 646644787249060731573982879) ^ (646644787249060731573982879 - 1) = 1 := by
  reduce_mod_char
private lemma prime_646644787249060731573982879_div_2 : (3 : ZMod 646644787249060731573982879) ^ ((646644787249060731573982879 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_646644787249060731573982879_div_3 : (3 : ZMod 646644787249060731573982879) ^ ((646644787249060731573982879 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_646644787249060731573982879_div_13 : (3 : ZMod 646644787249060731573982879) ^ ((646644787249060731573982879 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_646644787249060731573982879_div_37 : (3 : ZMod 646644787249060731573982879) ^ ((646644787249060731573982879 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_646644787249060731573982879_div_227 : (3 : ZMod 646644787249060731573982879) ^ ((646644787249060731573982879 - 1) / 227) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_646644787249060731573982879_div_953 : (3 : ZMod 646644787249060731573982879) ^ ((646644787249060731573982879 - 1) / 953) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_646644787249060731573982879_div_1901 : (3 : ZMod 646644787249060731573982879) ^ ((646644787249060731573982879 - 1) / 1901) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_646644787249060731573982879_div_8627 : (3 : ZMod 646644787249060731573982879) ^ ((646644787249060731573982879 - 1) / 8627) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_646644787249060731573982879_div_63155151529 : (3 : ZMod 646644787249060731573982879) ^ ((646644787249060731573982879 - 1) / 63155151529) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_646644787249060731573982879 : Nat.Prime 646644787249060731573982879 := by
  refine lucas_primality 646644787249060731573982879 (3 : ZMod 646644787249060731573982879) prime_646644787249060731573982879_pow ?_
  intro q hq hqd
  rw [prime_646644787249060731573982879_sub1] at hqd
  have : q ∣ [2, 3, 13, 37, 227, 953, 1901, 8627, 63155151529].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_646644787249060731573982879_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_646644787249060731573982879_div_3
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_646644787249060731573982879_div_13
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_646644787249060731573982879_div_37
  · have : q = 227 := (Nat.prime_dvd_prime_iff_eq hq prime_227).mp hdf
    subst this; exact prime_646644787249060731573982879_div_227
  · have : q = 953 := (Nat.prime_dvd_prime_iff_eq hq prime_953).mp hdf
    subst this; exact prime_646644787249060731573982879_div_953
  · have : q = 1901 := (Nat.prime_dvd_prime_iff_eq hq prime_1901).mp hdf
    subst this; exact prime_646644787249060731573982879_div_1901
  · have : q = 8627 := (Nat.prime_dvd_prime_iff_eq hq prime_8627).mp hdf
    subst this; exact prime_646644787249060731573982879_div_8627
  · have : q = 63155151529 := (Nat.prime_dvd_prime_iff_eq hq prime_63155151529).mp hdf
    subst this; exact prime_646644787249060731573982879_div_63155151529
private lemma prime_B_64_sub1 : (63340286662973277706162286913773767973882654883841 - 1 : ℕ) = 2 ^ 65 * 3 ^ 2 * 5 * 59 * 646644787249060731573982879 := by norm_num
private lemma prime_B_64_pow : (13 : ZMod 63340286662973277706162286913773767973882654883841) ^ (63340286662973277706162286913773767973882654883841 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_64_div_2 : (13 : ZMod 63340286662973277706162286913773767973882654883841) ^ ((63340286662973277706162286913773767973882654883841 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_64_div_3 : (13 : ZMod 63340286662973277706162286913773767973882654883841) ^ ((63340286662973277706162286913773767973882654883841 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_64_div_5 : (13 : ZMod 63340286662973277706162286913773767973882654883841) ^ ((63340286662973277706162286913773767973882654883841 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_64_div_59 : (13 : ZMod 63340286662973277706162286913773767973882654883841) ^ ((63340286662973277706162286913773767973882654883841 - 1) / 59) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_64_div_646644787249060731573982879 : (13 : ZMod 63340286662973277706162286913773767973882654883841) ^ ((63340286662973277706162286913773767973882654883841 - 1) / 646644787249060731573982879) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_64 : Nat.Prime 63340286662973277706162286913773767973882654883841 := by
  refine lucas_primality 63340286662973277706162286913773767973882654883841 (13 : ZMod 63340286662973277706162286913773767973882654883841) prime_B_64_pow ?_
  intro q hq hqd
  rw [prime_B_64_sub1] at hqd
  have : q ∣ [2 ^ 65, 3 ^ 2, 5, 59, 646644787249060731573982879].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_64_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_64_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_64_div_5
  · have : q = 59 := (Nat.prime_dvd_prime_iff_eq hq prime_59).mp hdf
    subst this; exact prime_B_64_div_59
  · have : q = 646644787249060731573982879 := (Nat.prime_dvd_prime_iff_eq hq prime_646644787249060731573982879).mp hdf
    subst this; exact prime_B_64_div_646644787249060731573982879
private lemma pair_64 :
    Nat.Prime ((3 ^ 64 - 1791) * (2 ^ 64) - 1) ∧
    Nat.Prime ((3 ^ 64 - 1791) * (2 ^ 64) + 1) := by
  constructor
  · convert prime_A_64
  · convert prime_B_64

/- Pair for n = 65 -/
private lemma prime_1993 : Nat.Prime 1993 := by norm_num
private lemma prime_40699 : Nat.Prime 40699 := by norm_num
private lemma prime_869291 : Nat.Prime 869291 := by norm_num
private lemma prime_71 : Nat.Prime 71 := by norm_num
private lemma prime_19188569 : Nat.Prime 19188569 := by norm_num
private lemma prime_41058389 : Nat.Prime 41058389 := by norm_num
private lemma prime_23993 : Nat.Prime 23993 := by norm_num
private lemma prime_13352389 : Nat.Prime 13352389 := by norm_num
private lemma prime_63432046116847_sub1 : (63432046116847 - 1 : ℕ) = 2 * 3 ^ 2 * 11 * 23993 * 13352389 := by norm_num
private lemma prime_63432046116847_pow : (3 : ZMod 63432046116847) ^ (63432046116847 - 1) = 1 := by
  reduce_mod_char
private lemma prime_63432046116847_div_2 : (3 : ZMod 63432046116847) ^ ((63432046116847 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_63432046116847_div_3 : (3 : ZMod 63432046116847) ^ ((63432046116847 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_63432046116847_div_11 : (3 : ZMod 63432046116847) ^ ((63432046116847 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_63432046116847_div_23993 : (3 : ZMod 63432046116847) ^ ((63432046116847 - 1) / 23993) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_63432046116847_div_13352389 : (3 : ZMod 63432046116847) ^ ((63432046116847 - 1) / 13352389) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_63432046116847 : Nat.Prime 63432046116847 := by
  refine lucas_primality 63432046116847 (3 : ZMod 63432046116847) prime_63432046116847_pow ?_
  intro q hq hqd
  rw [prime_63432046116847_sub1] at hqd
  have : q ∣ [2, 3 ^ 2, 11, 23993, 13352389].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_63432046116847_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_63432046116847_div_3
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_63432046116847_div_11
  · have : q = 23993 := (Nat.prime_dvd_prime_iff_eq hq prime_23993).mp hdf
    subst this; exact prime_63432046116847_div_23993
  · have : q = 13352389 := (Nat.prime_dvd_prime_iff_eq hq prime_13352389).mp hdf
    subst this; exact prime_63432046116847_div_13352389
private lemma prime_27782628041674040334905574426724111_sub1 : (27782628041674040334905574426724111 - 1 : ℕ) = 2 * 3 ^ 3 * 5 * 29 * 71 * 19188569 * 41058389 * 63432046116847 := by norm_num
private lemma prime_27782628041674040334905574426724111_pow : (6 : ZMod 27782628041674040334905574426724111) ^ (27782628041674040334905574426724111 - 1) = 1 := by
  reduce_mod_char
private lemma prime_27782628041674040334905574426724111_div_2 : (6 : ZMod 27782628041674040334905574426724111) ^ ((27782628041674040334905574426724111 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27782628041674040334905574426724111_div_3 : (6 : ZMod 27782628041674040334905574426724111) ^ ((27782628041674040334905574426724111 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27782628041674040334905574426724111_div_5 : (6 : ZMod 27782628041674040334905574426724111) ^ ((27782628041674040334905574426724111 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27782628041674040334905574426724111_div_29 : (6 : ZMod 27782628041674040334905574426724111) ^ ((27782628041674040334905574426724111 - 1) / 29) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27782628041674040334905574426724111_div_71 : (6 : ZMod 27782628041674040334905574426724111) ^ ((27782628041674040334905574426724111 - 1) / 71) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27782628041674040334905574426724111_div_19188569 : (6 : ZMod 27782628041674040334905574426724111) ^ ((27782628041674040334905574426724111 - 1) / 19188569) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27782628041674040334905574426724111_div_41058389 : (6 : ZMod 27782628041674040334905574426724111) ^ ((27782628041674040334905574426724111 - 1) / 41058389) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27782628041674040334905574426724111_div_63432046116847 : (6 : ZMod 27782628041674040334905574426724111) ^ ((27782628041674040334905574426724111 - 1) / 63432046116847) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_27782628041674040334905574426724111 : Nat.Prime 27782628041674040334905574426724111 := by
  refine lucas_primality 27782628041674040334905574426724111 (6 : ZMod 27782628041674040334905574426724111) prime_27782628041674040334905574426724111_pow ?_
  intro q hq hqd
  rw [prime_27782628041674040334905574426724111_sub1] at hqd
  have : q ∣ [2, 3 ^ 3, 5, 29, 71, 19188569, 41058389, 63432046116847].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_27782628041674040334905574426724111_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_27782628041674040334905574426724111_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_27782628041674040334905574426724111_div_5
  · have : q = 29 := (Nat.prime_dvd_prime_iff_eq hq prime_29).mp hdf
    subst this; exact prime_27782628041674040334905574426724111_div_29
  · have : q = 71 := (Nat.prime_dvd_prime_iff_eq hq prime_71).mp hdf
    subst this; exact prime_27782628041674040334905574426724111_div_71
  · have : q = 19188569 := (Nat.prime_dvd_prime_iff_eq hq prime_19188569).mp hdf
    subst this; exact prime_27782628041674040334905574426724111_div_19188569
  · have : q = 41058389 := (Nat.prime_dvd_prime_iff_eq hq prime_41058389).mp hdf
    subst this; exact prime_27782628041674040334905574426724111_div_41058389
  · have : q = 63432046116847 := (Nat.prime_dvd_prime_iff_eq hq prime_63432046116847).mp hdf
    subst this; exact prime_27782628041674040334905574426724111_div_63432046116847
private lemma prime_A_65_sub1 : (380041719977839666236973721603837716407567683420159 - 1 : ℕ) = 2 * 97 * 1993 * 40699 * 869291 * 27782628041674040334905574426724111 := by norm_num
private lemma prime_A_65_pow : (7 : ZMod 380041719977839666236973721603837716407567683420159) ^ (380041719977839666236973721603837716407567683420159 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_65_div_2 : (7 : ZMod 380041719977839666236973721603837716407567683420159) ^ ((380041719977839666236973721603837716407567683420159 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_65_div_97 : (7 : ZMod 380041719977839666236973721603837716407567683420159) ^ ((380041719977839666236973721603837716407567683420159 - 1) / 97) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_65_div_1993 : (7 : ZMod 380041719977839666236973721603837716407567683420159) ^ ((380041719977839666236973721603837716407567683420159 - 1) / 1993) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_65_div_40699 : (7 : ZMod 380041719977839666236973721603837716407567683420159) ^ ((380041719977839666236973721603837716407567683420159 - 1) / 40699) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_65_div_869291 : (7 : ZMod 380041719977839666236973721603837716407567683420159) ^ ((380041719977839666236973721603837716407567683420159 - 1) / 869291) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_65_div_27782628041674040334905574426724111 : (7 : ZMod 380041719977839666236973721603837716407567683420159) ^ ((380041719977839666236973721603837716407567683420159 - 1) / 27782628041674040334905574426724111) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_65 : Nat.Prime 380041719977839666236973721603837716407567683420159 := by
  refine lucas_primality 380041719977839666236973721603837716407567683420159 (7 : ZMod 380041719977839666236973721603837716407567683420159) prime_A_65_pow ?_
  intro q hq hqd
  rw [prime_A_65_sub1] at hqd
  have : q ∣ [2, 97, 1993, 40699, 869291, 27782628041674040334905574426724111].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_65_div_2
  · have : q = 97 := (Nat.prime_dvd_prime_iff_eq hq prime_97).mp hdf
    subst this; exact prime_A_65_div_97
  · have : q = 1993 := (Nat.prime_dvd_prime_iff_eq hq prime_1993).mp hdf
    subst this; exact prime_A_65_div_1993
  · have : q = 40699 := (Nat.prime_dvd_prime_iff_eq hq prime_40699).mp hdf
    subst this; exact prime_A_65_div_40699
  · have : q = 869291 := (Nat.prime_dvd_prime_iff_eq hq prime_869291).mp hdf
    subst this; exact prime_A_65_div_869291
  · have : q = 27782628041674040334905574426724111 := (Nat.prime_dvd_prime_iff_eq hq prime_27782628041674040334905574426724111).mp hdf
    subst this; exact prime_A_65_div_27782628041674040334905574426724111
private lemma prime_26855573 : Nat.Prime 26855573 := by norm_num
private lemma prime_2129579 : Nat.Prime 2129579 := by norm_num
private lemma prime_29007157 : Nat.Prime 29007157 := by norm_num
private lemma prime_68993107 : Nat.Prime 68993107 := by norm_num
private lemma prime_8523826867747990295243_sub1 : (8523826867747990295243 - 1 : ℕ) = 2 * 2129579 * 29007157 * 68993107 := by norm_num
private lemma prime_8523826867747990295243_pow : (2 : ZMod 8523826867747990295243) ^ (8523826867747990295243 - 1) = 1 := by
  reduce_mod_char
private lemma prime_8523826867747990295243_div_2 : (2 : ZMod 8523826867747990295243) ^ ((8523826867747990295243 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8523826867747990295243_div_2129579 : (2 : ZMod 8523826867747990295243) ^ ((8523826867747990295243 - 1) / 2129579) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8523826867747990295243_div_29007157 : (2 : ZMod 8523826867747990295243) ^ ((8523826867747990295243 - 1) / 29007157) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8523826867747990295243_div_68993107 : (2 : ZMod 8523826867747990295243) ^ ((8523826867747990295243 - 1) / 68993107) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_8523826867747990295243 : Nat.Prime 8523826867747990295243 := by
  refine lucas_primality 8523826867747990295243 (2 : ZMod 8523826867747990295243) prime_8523826867747990295243_pow ?_
  intro q hq hqd
  rw [prime_8523826867747990295243_sub1] at hqd
  have : q ∣ [2, 2129579, 29007157, 68993107].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_8523826867747990295243_div_2
  · have : q = 2129579 := (Nat.prime_dvd_prime_iff_eq hq prime_2129579).mp hdf
    subst this; exact prime_8523826867747990295243_div_2129579
  · have : q = 29007157 := (Nat.prime_dvd_prime_iff_eq hq prime_29007157).mp hdf
    subst this; exact prime_8523826867747990295243_div_29007157
  · have : q = 68993107 := (Nat.prime_dvd_prime_iff_eq hq prime_68993107).mp hdf
    subst this; exact prime_8523826867747990295243_div_68993107
private lemma prime_B_65_sub1 : (380041719977839666236973721603837716407567683420161 - 1 : ℕ) = 2 ^ 65 * 3 ^ 2 * 5 * 26855573 * 8523826867747990295243 := by norm_num
private lemma prime_B_65_pow : (13 : ZMod 380041719977839666236973721603837716407567683420161) ^ (380041719977839666236973721603837716407567683420161 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_65_div_2 : (13 : ZMod 380041719977839666236973721603837716407567683420161) ^ ((380041719977839666236973721603837716407567683420161 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_65_div_3 : (13 : ZMod 380041719977839666236973721603837716407567683420161) ^ ((380041719977839666236973721603837716407567683420161 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_65_div_5 : (13 : ZMod 380041719977839666236973721603837716407567683420161) ^ ((380041719977839666236973721603837716407567683420161 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_65_div_26855573 : (13 : ZMod 380041719977839666236973721603837716407567683420161) ^ ((380041719977839666236973721603837716407567683420161 - 1) / 26855573) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_65_div_8523826867747990295243 : (13 : ZMod 380041719977839666236973721603837716407567683420161) ^ ((380041719977839666236973721603837716407567683420161 - 1) / 8523826867747990295243) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_65 : Nat.Prime 380041719977839666236973721603837716407567683420161 := by
  refine lucas_primality 380041719977839666236973721603837716407567683420161 (13 : ZMod 380041719977839666236973721603837716407567683420161) prime_B_65_pow ?_
  intro q hq hqd
  rw [prime_B_65_sub1] at hqd
  have : q ∣ [2 ^ 65, 3 ^ 2, 5, 26855573, 8523826867747990295243].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_65_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_65_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_65_div_5
  · have : q = 26855573 := (Nat.prime_dvd_prime_iff_eq hq prime_26855573).mp hdf
    subst this; exact prime_B_65_div_26855573
  · have : q = 8523826867747990295243 := (Nat.prime_dvd_prime_iff_eq hq prime_8523826867747990295243).mp hdf
    subst this; exact prime_B_65_div_8523826867747990295243
private lemma pair_65 :
    Nat.Prime ((3 ^ 65 - 2088) * (2 ^ 65) - 1) ∧
    Nat.Prime ((3 ^ 65 - 2088) * (2 ^ 65) + 1) := by
  constructor
  · convert prime_A_65
  · convert prime_B_65
