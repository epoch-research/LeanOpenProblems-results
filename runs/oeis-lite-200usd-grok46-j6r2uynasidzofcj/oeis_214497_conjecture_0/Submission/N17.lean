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
private lemma prime_11 : Nat.Prime 11 := by norm_num
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_73 : Nat.Prime 73 := by norm_num
private lemma prime_555301 : Nat.Prime 555301 := by norm_num
private lemma prime_162147893_sub1 : (162147893 - 1 : ℕ) = 2 ^ 2 * 73 * 555301 := by norm_num
private lemma prime_162147893_pow : (2 : ZMod 162147893) ^ (162147893 - 1) = 1 := by
  reduce_mod_char
private lemma prime_162147893_div_2 : (2 : ZMod 162147893) ^ ((162147893 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_162147893_div_73 : (2 : ZMod 162147893) ^ ((162147893 - 1) / 73) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_162147893_div_555301 : (2 : ZMod 162147893) ^ ((162147893 - 1) / 555301) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_162147893 : Nat.Prime 162147893 := by
  refine lucas_primality 162147893 (2 : ZMod 162147893) prime_162147893_pow ?_
  intro q hq hqd
  rw [prime_162147893_sub1] at hqd
  have : q ∣ [2 ^ 2, 73, 555301].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_162147893_div_2
  · have : q = 73 := (Nat.prime_dvd_prime_iff_eq hq prime_73).mp hdf
    subst this; exact prime_162147893_div_73
  · have : q = 555301 := (Nat.prime_dvd_prime_iff_eq hq prime_555301).mp hdf
    subst this; exact prime_162147893_div_555301
private lemma prime_A_17_sub1 : (16926618550271 - 1 : ℕ) = 2 * 5 * 11 * 13 * 73 * 162147893 := by norm_num
private lemma prime_A_17_pow : (11 : ZMod 16926618550271) ^ (16926618550271 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_17_div_2 : (11 : ZMod 16926618550271) ^ ((16926618550271 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_17_div_5 : (11 : ZMod 16926618550271) ^ ((16926618550271 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_17_div_11 : (11 : ZMod 16926618550271) ^ ((16926618550271 - 1) / 11) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_17_div_13 : (11 : ZMod 16926618550271) ^ ((16926618550271 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_17_div_73 : (11 : ZMod 16926618550271) ^ ((16926618550271 - 1) / 73) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_17_div_162147893 : (11 : ZMod 16926618550271) ^ ((16926618550271 - 1) / 162147893) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_17 : Nat.Prime 16926618550271 := by
  refine lucas_primality 16926618550271 (11 : ZMod 16926618550271) prime_A_17_pow ?_
  intro q hq hqd
  rw [prime_A_17_sub1] at hqd
  have : q ∣ [2, 5, 11, 13, 73, 162147893].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_17_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_17_div_5
  · have : q = 11 := (Nat.prime_dvd_prime_iff_eq hq prime_11).mp hdf
    subst this; exact prime_A_17_div_11
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_A_17_div_13
  · have : q = 73 := (Nat.prime_dvd_prime_iff_eq hq prime_73).mp hdf
    subst this; exact prime_A_17_div_73
  · have : q = 162147893 := (Nat.prime_dvd_prime_iff_eq hq prime_162147893).mp hdf
    subst this; exact prime_A_17_div_162147893
private lemma prime_43046617 : Nat.Prime 43046617 := by norm_num
private lemma prime_B_17_sub1 : (16926618550273 - 1 : ℕ) = 2 ^ 17 * 3 * 43046617 := by norm_num
private lemma prime_B_17_pow : (7 : ZMod 16926618550273) ^ (16926618550273 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_17_div_2 : (7 : ZMod 16926618550273) ^ ((16926618550273 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_17_div_3 : (7 : ZMod 16926618550273) ^ ((16926618550273 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_17_div_43046617 : (7 : ZMod 16926618550273) ^ ((16926618550273 - 1) / 43046617) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_17 : Nat.Prime 16926618550273 := by
  refine lucas_primality 16926618550273 (7 : ZMod 16926618550273) prime_B_17_pow ?_
  intro q hq hqd
  rw [prime_B_17_sub1] at hqd
  have : q ∣ [2 ^ 17, 3, 43046617].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_17_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_17_div_3
  · have : q = 43046617 := (Nat.prime_dvd_prime_iff_eq hq prime_43046617).mp hdf
    subst this; exact prime_B_17_div_43046617
private lemma pair_17 :
    Nat.Prime ((3 ^ 17 - 312) * (2 ^ 17) - 1) ∧
    Nat.Prime ((3 ^ 17 - 312) * (2 ^ 17) + 1) := by
  constructor
  · convert prime_A_17
  · convert prime_B_17

