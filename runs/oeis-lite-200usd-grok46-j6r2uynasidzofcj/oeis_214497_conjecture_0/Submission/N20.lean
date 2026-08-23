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
private lemma prime_14221 : Nat.Prime 14221 := by norm_num
private lemma prime_5021 : Nat.Prime 5021 := by norm_num
private lemma prime_92761 : Nat.Prime 92761 := by norm_num
private lemma prime_5589035773_sub1 : (5589035773 - 1 : ℕ) = 2 ^ 2 * 3 * 5021 * 92761 := by norm_num
private lemma prime_5589035773_pow : (2 : ZMod 5589035773) ^ (5589035773 - 1) = 1 := by
  reduce_mod_char
private lemma prime_5589035773_div_2 : (2 : ZMod 5589035773) ^ ((5589035773 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5589035773_div_3 : (2 : ZMod 5589035773) ^ ((5589035773 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5589035773_div_5021 : (2 : ZMod 5589035773) ^ ((5589035773 - 1) / 5021) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5589035773_div_92761 : (2 : ZMod 5589035773) ^ ((5589035773 - 1) / 92761) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_5589035773 : Nat.Prime 5589035773 := by
  refine lucas_primality 5589035773 (2 : ZMod 5589035773) prime_5589035773_pow ?_
  intro q hq hqd
  rw [prime_5589035773_sub1] at hqd
  have : q ∣ [2 ^ 2, 3, 5021, 92761].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_5589035773_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_5589035773_div_3
  · have : q = 5021 := (Nat.prime_dvd_prime_iff_eq hq prime_5021).mp hdf
    subst this; exact prime_5589035773_div_5021
  · have : q = 92761 := (Nat.prime_dvd_prime_iff_eq hq prime_92761).mp hdf
    subst this; exact prime_5589035773_div_92761
private lemma prime_A_20_sub1 : (3656157175480319 - 1 : ℕ) = 2 * 23 * 14221 * 5589035773 := by norm_num
private lemma prime_A_20_pow : (11 : ZMod 3656157175480319) ^ (3656157175480319 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_20_div_2 : (11 : ZMod 3656157175480319) ^ ((3656157175480319 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_20_div_23 : (11 : ZMod 3656157175480319) ^ ((3656157175480319 - 1) / 23) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_20_div_14221 : (11 : ZMod 3656157175480319) ^ ((3656157175480319 - 1) / 14221) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_20_div_5589035773 : (11 : ZMod 3656157175480319) ^ ((3656157175480319 - 1) / 5589035773) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_20 : Nat.Prime 3656157175480319 := by
  refine lucas_primality 3656157175480319 (11 : ZMod 3656157175480319) prime_A_20_pow ?_
  intro q hq hqd
  rw [prime_A_20_sub1] at hqd
  have : q ∣ [2, 23, 14221, 5589035773].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_20_div_2
  · have : q = 23 := (Nat.prime_dvd_prime_iff_eq hq prime_23).mp hdf
    subst this; exact prime_A_20_div_23
  · have : q = 14221 := (Nat.prime_dvd_prime_iff_eq hq prime_14221).mp hdf
    subst this; exact prime_A_20_div_14221
  · have : q = 5589035773 := (Nat.prime_dvd_prime_iff_eq hq prime_5589035773).mp hdf
    subst this; exact prime_A_20_div_5589035773
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_582587 : Nat.Prime 582587 := by norm_num
private lemma prime_B_20_sub1 : (3656157175480321 - 1 : ℕ) = 2 ^ 20 * 3 ^ 2 * 5 * 7 * 19 * 582587 := by norm_num
private lemma prime_B_20_pow : (11 : ZMod 3656157175480321) ^ (3656157175480321 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_20_div_2 : (11 : ZMod 3656157175480321) ^ ((3656157175480321 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_20_div_3 : (11 : ZMod 3656157175480321) ^ ((3656157175480321 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_20_div_5 : (11 : ZMod 3656157175480321) ^ ((3656157175480321 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_20_div_7 : (11 : ZMod 3656157175480321) ^ ((3656157175480321 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_20_div_19 : (11 : ZMod 3656157175480321) ^ ((3656157175480321 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_20_div_582587 : (11 : ZMod 3656157175480321) ^ ((3656157175480321 - 1) / 582587) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_20 : Nat.Prime 3656157175480321 := by
  refine lucas_primality 3656157175480321 (11 : ZMod 3656157175480321) prime_B_20_pow ?_
  intro q hq hqd
  rw [prime_B_20_sub1] at hqd
  have : q ∣ [2 ^ 20, 3 ^ 2, 5, 7, 19, 582587].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_20_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_20_div_3
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_B_20_div_5
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_B_20_div_7
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_B_20_div_19
  · have : q = 582587 := (Nat.prime_dvd_prime_iff_eq hq prime_582587).mp hdf
    subst this; exact prime_B_20_div_582587
private lemma pair_20 :
    Nat.Prime ((3 ^ 20 - 1206) * (2 ^ 20) - 1) ∧
    Nat.Prime ((3 ^ 20 - 1206) * (2 ^ 20) + 1) := by
  constructor
  · convert prime_A_20
  · convert prime_B_20

