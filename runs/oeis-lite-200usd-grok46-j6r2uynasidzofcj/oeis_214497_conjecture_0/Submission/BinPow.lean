import FormalConjectures.Util.ProblemImports

open Nat List

lemma prime_dvd_list_prod {q : ℕ} (hq : q.Prime) :
    ∀ (ps : List ℕ), q ∣ ps.prod → ∃ p ∈ ps, q ∣ p
  | [], h => by
    simp at h
    exact (hq.ne_one h).elim
  | p :: ps, h => by
    rw [prod_cons] at h
    rcases hq.dvd_mul.mp h with h | h
    · exact ⟨p, mem_cons_self, h⟩
    · obtain ⟨p', hp', hq'⟩ := prime_dvd_list_prod hq ps h
      exact ⟨p', mem_cons_of_mem _ hp', hq'⟩

lemma prime_eq_of_dvd_prime_pow {q p : ℕ} {e : ℕ} (hq : q.Prime) (hp : p.Prime)
    (h : q ∣ p ^ e) : q = p :=
  (prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)

-- Test
lemma prime_7591 : Nat.Prime 7591 := by norm_num

lemma B_eq : (13058949121 - 1 : ℕ) = 2 ^ 14 * 3 * 5 * 7 * 7591 := by norm_num

lemma B_pow : (17 : ZMod 13058949121) ^ (13058949121 - 1) = 1 := by
  reduce_mod_char

lemma B_div2 : (17 : ZMod 13058949121) ^ ((13058949121 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
lemma B_div3 : (17 : ZMod 13058949121) ^ ((13058949121 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
lemma B_div5 : (17 : ZMod 13058949121) ^ ((13058949121 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
lemma B_div7 : (17 : ZMod 13058949121) ^ ((13058949121 - 1) / 7) ≠ 1 := by
  reduce_mod_char; decide
lemma B_div7591 : (17 : ZMod 13058949121) ^ ((13058949121 - 1) / 7591) ≠ 1 := by
  reduce_mod_char; decide

lemma prime_B : Nat.Prime 13058949121 := by
  refine lucas_primality 13058949121 (17 : ZMod 13058949121) B_pow ?_
  intro q hq hqd
  rw [B_eq] at hqd
  have : q ∣ [2 ^ 14, 3, 5, 7, 7591].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [mem_cons, not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq prime_two hdf
    subst this; exact B_div2
  · have : q = 3 := (prime_dvd_prime_iff_eq hq prime_three).mp hdf
    subst this; exact B_div3
  · have : q = 5 := (prime_dvd_prime_iff_eq hq prime_five).mp hdf
    subst this; exact B_div5
  · have : q = 7 := (prime_dvd_prime_iff_eq hq prime_seven).mp hdf
    subst this; exact B_div7
  · have : q = 7591 := (prime_dvd_prime_iff_eq hq prime_7591).mp hdf
    subst this; exact B_div7591

lemma prime_6143 : Nat.Prime 6143 := by norm_num
lemma prime_1062913 : Nat.Prime 1062913 := by norm_num

lemma A_eq : (13058949119 - 1 : ℕ) = 2 * 6143 * 1062913 := by norm_num

lemma A_pow : (13 : ZMod 13058949119) ^ (13058949119 - 1) = 1 := by
  reduce_mod_char
lemma A_div2 : (13 : ZMod 13058949119) ^ ((13058949119 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
lemma A_div6143 : (13 : ZMod 13058949119) ^ ((13058949119 - 1) / 6143) ≠ 1 := by
  reduce_mod_char; decide
lemma A_div1062913 : (13 : ZMod 13058949119) ^ ((13058949119 - 1) / 1062913) ≠ 1 := by
  reduce_mod_char; decide

lemma prime_A : Nat.Prime 13058949119 := by
  refine lucas_primality 13058949119 (13 : ZMod 13058949119) A_pow ?_
  intro q hq hqd
  rw [A_eq] at hqd
  have : q ∣ [2, 6143, 1062913].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [mem_cons, not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (prime_dvd_prime_iff_eq hq prime_two).mp hdf
    subst this; exact A_div2
  · have : q = 6143 := (prime_dvd_prime_iff_eq hq prime_6143).mp hdf
    subst this; exact A_div6143
  · have : q = 1062913 := (prime_dvd_prime_iff_eq hq prime_1062913).mp hdf
    subst this; exact A_div1062913

-- n=13, k=213
example : Nat.Prime ((3 ^ 13 - 213) * (2 ^ 13) - 1) ∧
          Nat.Prime ((3 ^ 13 - 213) * (2 ^ 13) + 1) := by
  constructor
  · convert prime_A
  · convert prime_B
