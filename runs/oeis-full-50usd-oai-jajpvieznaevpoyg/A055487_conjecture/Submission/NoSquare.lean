import FormalConjectures.Util.ProblemImports
open Nat

lemma factorial_factorization_eq_one_of_half_lt {n r : ℕ} (hr : Nat.Prime r)
    (hrle : r ≤ n) (hlt : n < 2 * r) (hsq : n < r ^ 2) :
    (n !).factorization r = 1 := by
  rw [Nat.factorization_factorial hr (b := 3)]
  · norm_num [Finset.sum_Ico_succ_top]
    have hdiv1 : n / r = 1 := by
      simpa [one_mul, Nat.add_comm] using (Nat.div_eq_of_lt_le (k := 1) (n := r) (m := n) (by simpa [one_mul] using hrle) (by simpa [Nat.add_comm, two_mul] using hlt))
    have hdiv2 : n / r ^ 2 = 0 := Nat.div_eq_of_lt hsq
    rw [hdiv1, hdiv2]
  · -- log r n < 3 follows from n < r^2 < r^3 maybe
    have hn0 : n ≠ 0 := by omega
    rw [Nat.log_lt_iff_lt_pow hr.one_lt hn0]
    exact lt_trans hsq (by
      have hrpos : 0 < r := hr.pos
      calc r ^ 2 < r ^ 3 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
      )

lemma not_square_factorial_of_prime_between {n r a : ℕ} (hr : Nat.Prime r)
    (hrle : r ≤ n) (hlt : n < 2 * r) (hsq : n < r ^ 2) :
    n ! ≠ a ^ 2 := by
  intro h
  have hfac : (n !).factorization r = 1 := factorial_factorization_eq_one_of_half_lt hr hrle hlt hsq
  have hpowa : (a ^ 2).factorization r = 2 * a.factorization r := by
    rw [Nat.factorization_pow]
    rfl
  rw [h, hpowa] at hfac
  omega

lemma exists_prime_half_lt_le (n : ℕ) (hn : 2 ≤ n) :
    ∃ r, Nat.Prime r ∧ r ≤ n ∧ n < 2 * r ∧ n < r ^ 2 := by
  by_cases hn2 : n = 2
  · subst n
    exact ⟨2, Nat.prime_two, by norm_num, by norm_num, by norm_num⟩
  by_cases hn3 : n = 3
  · subst n
    exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- n >= 4 case
    have hn4 : 4 ≤ n := by omega
    let k := n / 2
    have hk0 : k ≠ 0 := by
      unfold k
      omega
    rcases Nat.exists_prime_lt_and_le_two_mul k hk0 with ⟨r, hr, hkr, hrle2⟩
    refine ⟨r, hr, ?_, ?_, ?_⟩
    · unfold k at hrle2
      omega
    · unfold k at hkr
      omega
    · have h2r : 2 * r ≤ r ^ 2 := by
        have hr2 : 2 ≤ r := hr.two_le
        nlinarith
      have hnlt : n < 2 * r := by
        unfold k at hkr
        omega
      exact lt_of_lt_of_le hnlt h2r

lemma factorial_not_square_of_two_le {n a : ℕ} (hn : 2 ≤ n) : n ! ≠ a ^ 2 := by
  rcases exists_prime_half_lt_le n hn with ⟨r, hr, hrle, hlt, hsq⟩
  exact not_square_factorial_of_prime_between hr hrle hlt hsq

