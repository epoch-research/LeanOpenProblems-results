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
private lemma prime_113 : Nat.Prime 113 := by norm_num
private lemma prime_26251 : Nat.Prime 26251 := by norm_num
private lemma prime_1711859 : Nat.Prime 1711859 := by norm_num
private lemma prime_89876021219_sub1 : (89876021219 - 1 : ℕ) = 2 * 26251 * 1711859 := by norm_num
private lemma prime_89876021219_pow : (2 : ZMod 89876021219) ^ (89876021219 - 1) = 1 := by
  reduce_mod_char
private lemma prime_89876021219_div_2 : (2 : ZMod 89876021219) ^ ((89876021219 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_89876021219_div_26251 : (2 : ZMod 89876021219) ^ ((89876021219 - 1) / 26251) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_89876021219_div_1711859 : (2 : ZMod 89876021219) ^ ((89876021219 - 1) / 1711859) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_89876021219 : Nat.Prime 89876021219 := by
  refine lucas_primality 89876021219 (2 : ZMod 89876021219) prime_89876021219_pow ?_
  intro q hq hqd
  rw [prime_89876021219_sub1] at hqd
  have : q ∣ [2, 26251, 1711859].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_89876021219_div_2
  · have : q = 26251 := (Nat.prime_dvd_prime_iff_eq hq prime_26251).mp hdf
    subst this; exact prime_89876021219_div_26251
  · have : q = 1711859 := (Nat.prime_dvd_prime_iff_eq hq prime_1711859).mp hdf
    subst this; exact prime_89876021219_div_1711859
private lemma prime_A_18_sub1 : (101559903977471 - 1 : ℕ) = 2 * 5 * 113 * 89876021219 := by norm_num
private lemma prime_A_18_pow : (7 : ZMod 101559903977471) ^ (101559903977471 - 1) = 1 := by
  reduce_mod_char
private lemma prime_A_18_div_2 : (7 : ZMod 101559903977471) ^ ((101559903977471 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_18_div_5 : (7 : ZMod 101559903977471) ^ ((101559903977471 - 1) / 5) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_18_div_113 : (7 : ZMod 101559903977471) ^ ((101559903977471 - 1) / 113) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_18_div_89876021219 : (7 : ZMod 101559903977471) ^ ((101559903977471 - 1) / 89876021219) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_A_18 : Nat.Prime 101559903977471 := by
  refine lucas_primality 101559903977471 (7 : ZMod 101559903977471) prime_A_18_pow ?_
  intro q hq hqd
  rw [prime_A_18_sub1] at hqd
  have : q ∣ [2, 5, 113, 89876021219].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdf
    subst this; exact prime_A_18_div_2
  · have : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hdf
    subst this; exact prime_A_18_div_5
  · have : q = 113 := (Nat.prime_dvd_prime_iff_eq hq prime_113).mp hdf
    subst this; exact prime_A_18_div_113
  · have : q = 89876021219 := (Nat.prime_dvd_prime_iff_eq hq prime_89876021219).mp hdf
    subst this; exact prime_A_18_div_89876021219
private lemma prime_709 : Nat.Prime 709 := by norm_num
private lemma prime_1423 : Nat.Prime 1423 := by norm_num
private lemma prime_B_18_sub1 : (101559903977473 - 1 : ℕ) = 2 ^ 25 * 3 * 709 * 1423 := by norm_num
private lemma prime_B_18_pow : (5 : ZMod 101559903977473) ^ (101559903977473 - 1) = 1 := by
  reduce_mod_char
private lemma prime_B_18_div_2 : (5 : ZMod 101559903977473) ^ ((101559903977473 - 1) / 2) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_18_div_3 : (5 : ZMod 101559903977473) ^ ((101559903977473 - 1) / 3) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_18_div_709 : (5 : ZMod 101559903977473) ^ ((101559903977473 - 1) / 709) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_18_div_1423 : (5 : ZMod 101559903977473) ^ ((101559903977473 - 1) / 1423) ≠ 1 := by
  reduce_mod_char; decide
private lemma prime_B_18 : Nat.Prime 101559903977473 := by
  refine lucas_primality 101559903977473 (5 : ZMod 101559903977473) prime_B_18_pow ?_
  intro q hq hqd
  rw [prime_B_18_sub1] at hqd
  have : q ∣ [2 ^ 25, 3, 709, 1423].prod := by
    simpa [List.prod_cons, List.prod_nil] using hqd
  obtain ⟨f, hf, hdf⟩ := prime_dvd_list_prod hq _ this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · have : q = 2 := prime_eq_of_dvd_prime_pow hq Nat.prime_two hdf
    subst this; exact prime_B_18_div_2
  · have : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hdf
    subst this; exact prime_B_18_div_3
  · have : q = 709 := (Nat.prime_dvd_prime_iff_eq hq prime_709).mp hdf
    subst this; exact prime_B_18_div_709
  · have : q = 1423 := (Nat.prime_dvd_prime_iff_eq hq prime_1423).mp hdf
    subst this; exact prime_B_18_div_1423
private lemma pair_18 :
    Nat.Prime ((3 ^ 18 - 201) * (2 ^ 18) - 1) ∧
    Nat.Prime ((3 ^ 18 - 201) * (2 ^ 18) + 1) := by
  constructor
  · convert prime_A_18
  · convert prime_B_18

