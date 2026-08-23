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
private lemma prime_19 : Nat.Prime 19 := by norm_num
private lemma prime_37 : Nat.Prime 37 := by norm_num
private lemma prime_103 : Nat.Prime 103 := by norm_num
private lemma prime_37569299 : Nat.Prime 37569299 := by norm_num
private lemma prime_286353196979_sub1 : (286353196979 - 1 : ℕ) = 2 * 37 * 103 * 37569299 := by norm_num
private lemma prime_286353196979_pow : (2 : ZMod 286353196979) ^ (286353196979 - 1) = 1 := by
  reduce_mod_char
private lemma prime_286353196979_div_2 : (2 : ZMod 286353196979) ^ ((286353196979 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_286353196979_div_37 : (2 : ZMod 286353196979) ^ ((286353196979 - 1) / 37) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_286353196979_div_103 : (2 : ZMod 286353196979) ^ ((286353196979 - 1) / 103) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_286353196979_div_37569299 : (2 : ZMod 286353196979) ^ ((286353196979 - 1) / 37569299) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_286353196979 : Nat.Prime 286353196979 := by
  refine lucas_primality 286353196979 (2 : ZMod 286353196979) prime_286353196979_pow ?_
  intro q hq hqd
  rw [prime_286353196979_sub1] at hqd
  have : q ∣ [2, 37, 103, 37569299].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_286353196979_div_2
  · have : q = 37 := (Nat.prime_dvd_prime_iff_eq hq prime_37).mp hdf
    subst this; exact prime_286353196979_div_37
  · have : q = 103 := (Nat.prime_dvd_prime_iff_eq hq prime_103).mp hdf
    subst this; exact prime_286353196979_div_103
  · have : q = 37569299 := (Nat.prime_dvd_prime_iff_eq hq prime_37569299).mp hdf
    subst this; exact prime_286353196979_div_37569299
private lemma prime_43525685940809_sub1 : (43525685940809 - 1 : ℕ) = 2 ^ 3 * 19 * 286353196979 := by norm_num
private lemma prime_43525685940809_pow : (3 : ZMod 43525685940809) ^ (43525685940809 - 1) = 1 := by
  reduce_mod_char
private lemma prime_43525685940809_div_2 : (3 : ZMod 43525685940809) ^ ((43525685940809 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_43525685940809_div_19 : (3 : ZMod 43525685940809) ^ ((43525685940809 - 1) / 19) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_43525685940809_div_286353196979 : (3 : ZMod 43525685940809) ^ ((43525685940809 - 1) / 286353196979) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_43525685940809 : Nat.Prime 43525685940809 := by
  refine lucas_primality 43525685940809 (3 : ZMod 43525685940809) prime_43525685940809_pow ?_
  intro q hq hqd
  rw [prime_43525685940809_sub1] at hqd
  have : q ∣ [2 ^ 3, 19, 286353196979].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_43525685940809_div_2
  · have : q = 19 := (Nat.prime_dvd_prime_iff_eq hq prime_19).mp hdf
    subst this; exact prime_43525685940809_div_19
  · have : q = 286353196979 := (Nat.prime_dvd_prime_iff_eq hq prime_286353196979).mp hdf
    subst this; exact prime_43525685940809_div_286353196979
private lemma prime_A_19_sub1 : (609359603171327 - 1 : ℕ) = 2 * 7 * 43525685940809 := by norm_num
private lemma prime_A_19_pow : (5 : ZMod 609359603171327) ^ (609359603171327 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_19_div_2 : (5 : ZMod 609359603171327) ^ ((609359603171327 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_19_div_7 : (5 : ZMod 609359603171327) ^ ((609359603171327 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_19_div_43525685940809 : (5 : ZMod 609359603171327) ^ ((609359603171327 - 1) / 43525685940809) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_19 : Nat.Prime 609359603171327 := by
  refine lucas_primality 609359603171327 (5 : ZMod 609359603171327) prime_A_19_pow ?_
  intro q hq hqd
  rw [prime_A_19_sub1] at hqd
  have : q ∣ [2, 7, 43525685940809].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_19_div_2
  · have : q = 7 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_seven).mp hdf
    subst this; exact prime_A_19_div_7
  · have : q = 43525685940809 := (Nat.prime_dvd_prime_iff_eq hq prime_43525685940809).mp hdf
    subst this; exact prime_A_19_div_43525685940809
private lemma prime_64570067 : Nat.Prime 64570067 := by norm_num
private lemma prime_B_19_sub1 : (609359603171329 - 1 : ℕ) = 2 ^ 20 * 3 ^ 2 * 64570067 := by norm_num
private lemma prime_B_19_pow : (7 : ZMod 609359603171329) ^ (609359603171329 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_19_div_2 : (7 : ZMod 609359603171329) ^ ((609359603171329 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_19_div_3 : (7 : ZMod 609359603171329) ^ ((609359603171329 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_19_div_64570067 : (7 : ZMod 609359603171329) ^ ((609359603171329 - 1) / 64570067) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_19 : Nat.Prime 609359603171329 := by
  refine lucas_primality 609359603171329 (7 : ZMod 609359603171329) prime_B_19_pow ?_
  intro q hq hqd
  rw [prime_B_19_sub1] at hqd
  have : q ∣ [2 ^ 20, 3 ^ 2, 64570067].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_19_div_2
  · have : q = 3 := prime_eq_of_dvd_prime_pow hq Nat.prime_three hdf
    subst this; exact prime_B_19_div_3
  · have : q = 64570067 := (Nat.prime_dvd_prime_iff_eq hq prime_64570067).mp hdf
    subst this; exact prime_B_19_div_64570067
private lemma pair_19 :
    Nat.Prime ((3 ^ 19 - 261) * (2 ^ 19) - 1) ∧
    Nat.Prime ((3 ^ 19 - 261) * (2 ^ 19) + 1) := by
  constructor
  · convert prime_A_19
  · convert prime_B_19

