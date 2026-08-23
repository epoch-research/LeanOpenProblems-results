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
private lemma prime_13 : Nat.Prime 13 := by norm_num
private lemma prime_264977 : Nat.Prime 264977 := by norm_num
private lemma prime_409483 : Nat.Prime 409483 := by norm_num
private lemma prime_A_16_sub1 : (2821092999167 - 1 : ℕ) = 2 * 13 * 264977 * 409483 := by norm_num
private lemma prime_A_16_pow : (5 : ZMod 2821092999167) ^ (2821092999167 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_16_div_2 : (5 : ZMod 2821092999167) ^ ((2821092999167 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_16_div_13 : (5 : ZMod 2821092999167) ^ ((2821092999167 - 1) / 13) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_16_div_264977 : (5 : ZMod 2821092999167) ^ ((2821092999167 - 1) / 264977) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_16_div_409483 : (5 : ZMod 2821092999167) ^ ((2821092999167 - 1) / 409483) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_16 : Nat.Prime 2821092999167 := by
  refine lucas_primality 2821092999167 (5 : ZMod 2821092999167) prime_A_16_pow ?_
  intro q hq hqd
  rw [prime_A_16_sub1] at hqd
  have : q ∣ [2, 13, 264977, 409483].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_16_div_2
  · have : q = 13 := (Nat.prime_dvd_prime_iff_eq hq prime_13).mp hdf
    subst this; exact prime_A_16_div_13
  · have : q = 264977 := (Nat.prime_dvd_prime_iff_eq hq prime_264977).mp hdf
    subst this; exact prime_A_16_div_264977
  · have : q = 409483 := (Nat.prime_dvd_prime_iff_eq hq prime_409483).mp hdf
    subst this; exact prime_A_16_div_409483
private lemma prime_593 : Nat.Prime 593 := by norm_num
private lemma prime_24197 : Nat.Prime 24197 := by norm_num
private lemma prime_B_16_sub1 : (2821092999169 - 1 : ℕ) = 2 ^ 16 * 3 * 593 * 24197 := by norm_num
private lemma prime_B_16_pow : (19 : ZMod 2821092999169) ^ (2821092999169 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_16_div_2 : (19 : ZMod 2821092999169) ^ ((2821092999169 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_16_div_3 : (19 : ZMod 2821092999169) ^ ((2821092999169 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_16_div_593 : (19 : ZMod 2821092999169) ^ ((2821092999169 - 1) / 593) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_16_div_24197 : (19 : ZMod 2821092999169) ^ ((2821092999169 - 1) / 24197) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_16 : Nat.Prime 2821092999169 := by
  refine lucas_primality 2821092999169 (19 : ZMod 2821092999169) prime_B_16_pow ?_
  intro q hq hqd
  rw [prime_B_16_sub1] at hqd
  have : q ∣ [2 ^ 16, 3, 593, 24197].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_16_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_16_div_3
  · have : q = 593 := (Nat.prime_dvd_prime_iff_eq hq prime_593).mp hdf
    subst this; exact prime_B_16_div_593
  · have : q = 24197 := (Nat.prime_dvd_prime_iff_eq hq prime_24197).mp hdf
    subst this; exact prime_B_16_div_24197
private lemma pair_16 :
    Nat.Prime ((3 ^ 16 - 258) * (2 ^ 16) - 1) ∧
    Nat.Prime ((3 ^ 16 - 258) * (2 ^ 16) + 1) := by
  constructor
  · convert prime_A_16
  · convert prime_B_16

