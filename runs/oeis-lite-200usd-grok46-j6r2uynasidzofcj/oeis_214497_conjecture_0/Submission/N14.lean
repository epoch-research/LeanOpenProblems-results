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
private lemma prime_23 : Nat.Prime 23 := by norm_num
private lemma prime_233 : Nat.Prime 233 := by norm_num
private lemma prime_2437 : Nat.Prime 2437 := by norm_num
private lemma prime_1703463001_sub1 : (1703463001 - 1 : ℕ) = 2 ^ 3 * 3 * 5 ^ 3 * 233 * 2437 := by norm_num
private lemma prime_1703463001_pow : (13 : ZMod 1703463001) ^ (1703463001 - 1) = 1 := by
  reduce_mod_char
private lemma prime_1703463001_div_2 : (13 : ZMod 1703463001) ^ ((1703463001 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1703463001_div_3 : (13 : ZMod 1703463001) ^ ((1703463001 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1703463001_div_5 : (13 : ZMod 1703463001) ^ ((1703463001 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1703463001_div_233 : (13 : ZMod 1703463001) ^ ((1703463001 - 1) / 233) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1703463001_div_2437 : (13 : ZMod 1703463001) ^ ((1703463001 - 1) / 2437) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_1703463001 : Nat.Prime 1703463001 := by
  refine lucas_primality 1703463001 (13 : ZMod 1703463001) prime_1703463001_pow ?_
  intro q hq hqd
  rw [prime_1703463001_sub1] at hqd
  have : q ∣ [2 ^ 3, 3, 5 ^ 3, 233, 2437].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_1703463001_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_1703463001_div_3
  · have : q = 5 := prime_eq_of_dvd_prime_pow hq Nat.prime_five hdf
    subst this; exact prime_1703463001_div_5
  · have : q = 233 := (Nat.prime_dvd_prime_iff_eq hq prime_233).mp hdf
    subst this; exact prime_1703463001_div_233
  · have : q = 2437 := (Nat.prime_dvd_prime_iff_eq hq prime_2437).mp hdf
    subst this; exact prime_1703463001_div_2437
private lemma prime_A_14_sub1 : (78359298047 - 1 : ℕ) = 2 * 23 * 1703463001 := by norm_num
private lemma prime_A_14_pow : (5 : ZMod 78359298047) ^ (78359298047 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_14_div_2 : (5 : ZMod 78359298047) ^ ((78359298047 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_14_div_23 : (5 : ZMod 78359298047) ^ ((78359298047 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_14_div_1703463001 : (5 : ZMod 78359298047) ^ ((78359298047 - 1) / 1703463001) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_14 : Nat.Prime 78359298047 := by
  refine lucas_primality 78359298047 (5 : ZMod 78359298047) prime_A_14_pow ?_
  intro q hq hqd
  rw [prime_A_14_sub1] at hqd
  have : q ∣ [2, 23, 1703463001].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_14_div_2
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_A_14_div_23
  · have : q = 1703463001 := (Nat.prime_dvd_prime_iff_eq hq prime_1703463001).mp hdf
    subst this; exact prime_A_14_div_1703463001
private lemma prime_11071 : Nat.Prime 11071 := by norm_num
private lemma prime_B_14_sub1 : (78359298049 - 1 : ℕ) = 2 ^ 18 * 3 ^ 3 * 11071 := by norm_num
private lemma prime_B_14_pow : (11 : ZMod 78359298049) ^ (78359298049 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_14_div_2 : (11 : ZMod 78359298049) ^ ((78359298049 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_14_div_3 : (11 : ZMod 78359298049) ^ ((78359298049 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_14_div_11071 : (11 : ZMod 78359298049) ^ ((78359298049 - 1) / 11071) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_14 : Nat.Prime 78359298049 := by
  refine lucas_primality 78359298049 (11 : ZMod 78359298049) prime_B_14_pow ?_
  intro q hq hqd
  rw [prime_B_14_sub1] at hqd
  have : q ∣ [2 ^ 18, 3 ^ 3, 11071].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_14_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_14_div_3
  · have : q = 11071 := (Nat.prime_dvd_prime_iff_eq hq prime_11071).mp hdf
    subst this; exact prime_B_14_div_11071
private lemma pair_14 :
    Nat.Prime ((3 ^ 14 - 297) * (2 ^ 14) - 1) ∧
    Nat.Prime ((3 ^ 14 - 297) * (2 ^ 14) + 1) := by
  constructor
  · convert prime_A_14
  · convert prime_B_14

