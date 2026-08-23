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
private lemma prime_31 : Nat.Prime 31 := by norm_num
private lemma prime_97 : Nat.Prime 97 := by norm_num
private lemma prime_78175169 : Nat.Prime 78175169 := by norm_num
private lemma prime_A_15_sub1 : (470145466367 - 1 : ℕ) = 2 * 31 * 97 * 78175169 := by norm_num
private lemma prime_A_15_pow : (5 : ZMod 470145466367) ^ (470145466367 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_15_div_2 : (5 : ZMod 470145466367) ^ ((470145466367 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_15_div_31 : (5 : ZMod 470145466367) ^ ((470145466367 - 1) / 31) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_15_div_97 : (5 : ZMod 470145466367) ^ ((470145466367 - 1) / 97) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_15_div_78175169 : (5 : ZMod 470145466367) ^ ((470145466367 - 1) / 78175169) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_15 : Nat.Prime 470145466367 := by
  refine lucas_primality 470145466367 (5 : ZMod 470145466367) prime_A_15_pow ?_
  intro q hq hqd
  rw [prime_A_15_sub1] at hqd
  have : q ∣ [2, 31, 97, 78175169].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_15_div_2
  · have : q = 31 := (Nat.prime_dvd_prime_iff_eq hq prime_31).mp hdf
    subst this; exact prime_A_15_div_31
  · have : q = 97 := (Nat.prime_dvd_prime_iff_eq hq prime_97).mp hdf
    subst this; exact prime_A_15_div_97
  · have : q = 78175169 := (Nat.prime_dvd_prime_iff_eq hq prime_78175169).mp hdf
    subst this; exact prime_A_15_div_78175169
private lemma prime_199 : Nat.Prime 199 := by norm_num
private lemma prime_8011 : Nat.Prime 8011 := by norm_num
private lemma prime_B_15_sub1 : (470145466369 - 1 : ℕ) = 2 ^ 15 * 3 ^ 2 * 199 * 8011 := by norm_num
private lemma prime_B_15_pow : (7 : ZMod 470145466369) ^ (470145466369 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_15_div_2 : (7 : ZMod 470145466369) ^ ((470145466369 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_15_div_3 : (7 : ZMod 470145466369) ^ ((470145466369 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_15_div_199 : (7 : ZMod 470145466369) ^ ((470145466369 - 1) / 199) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_15_div_8011 : (7 : ZMod 470145466369) ^ ((470145466369 - 1) / 8011) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_15 : Nat.Prime 470145466369 := by
  refine lucas_primality 470145466369 (7 : ZMod 470145466369) prime_B_15_pow ?_
  intro q hq hqd
  rw [prime_B_15_sub1] at hqd
  have : q ∣ [2 ^ 15, 3 ^ 2, 199, 8011].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_15_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_15_div_3
  · have : q = 199 := (Nat.prime_dvd_prime_iff_eq hq prime_199).mp hdf
    subst this; exact prime_B_15_div_199
  · have : q = 8011 := (Nat.prime_dvd_prime_iff_eq hq prime_8011).mp hdf
    subst this; exact prime_B_15_div_8011
private lemma pair_15 :
    Nat.Prime ((3 ^ 15 - 1206) * (2 ^ 15) - 1) ∧
    Nat.Prime ((3 ^ 15 - 1206) * (2 ^ 15) + 1) := by
  constructor
  · convert prime_A_15
  · convert prime_B_15

