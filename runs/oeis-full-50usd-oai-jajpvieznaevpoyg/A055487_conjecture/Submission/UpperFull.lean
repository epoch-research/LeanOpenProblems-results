import FormalConjectures.Util.ProblemImports
open Set
open Nat

noncomputable def A055487 (n : ℕ) : ℕ := sInf {m : ℕ | Nat.totient m = Nat.factorial n}
def prime_candidates (n : ℕ) : Set ℕ :=
  let N := Nat.factorial n
  { p : ℕ | Nat.Prime p ∧ Nat.sqrt N < p ∧ (p - 1) ∣ N ∧ Nat.Prime (N / (p - 1) + 1) }

lemma factorial_factorization_eq_one_of_half_lt {n r : ℕ} (hr : Nat.Prime r)
    (hrle : r ≤ n) (hlt : n < 2 * r) (hsq : n < r ^ 2) :
    (n !).factorization r = 1 := by
  rw [Nat.factorization_factorial hr (b := 3)]
  · norm_num [Finset.sum_Ico_succ_top]
    have hdiv1 : n / r = 1 := by
      simpa [one_mul, Nat.add_comm] using (Nat.div_eq_of_lt_le (k := 1) (n := r) (m := n) (by simpa [one_mul] using hrle) (by simpa [Nat.add_comm, two_mul] using hlt))
    have hdiv2 : n / r ^ 2 = 0 := Nat.div_eq_of_lt hsq
    rw [hdiv1, hdiv2]
  · have hn0 : n ≠ 0 := by omega
    rw [Nat.log_lt_iff_lt_pow hr.one_lt hn0]
    exact lt_trans hsq (Nat.pow_lt_pow_right hr.one_lt (by norm_num))

lemma not_square_factorial_of_prime_between {n r a : ℕ} (hr : Nat.Prime r)
    (hrle : r ≤ n) (hlt : n < 2 * r) (hsq : n < r ^ 2) : n ! ≠ a ^ 2 := by
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
  · have hn4 : 4 ≤ n := by omega
    let k := n / 2
    have hk0 : k ≠ 0 := by unfold k; omega
    rcases Nat.exists_prime_lt_and_le_two_mul k hk0 with ⟨r, hr, hkr, hrle2⟩
    refine ⟨r, hr, ?_, ?_, ?_⟩
    · unfold k at hrle2; omega
    · unfold k at hkr; omega
    · have h2r : 2 * r ≤ r ^ 2 := by have hr2 : 2 ≤ r := hr.two_le; nlinarith
      have hnlt : n < 2 * r := by unfold k at hkr; omega
      exact lt_of_lt_of_le hnlt h2r

lemma factorial_not_square_of_two_le {n a : ℕ} (hn : 2 ≤ n) : n ! ≠ a ^ 2 := by
  rcases exists_prime_half_lt_le n hn with ⟨r, hr, hrle, hlt, hsq⟩
  exact not_square_factorial_of_prime_between hr hrle hlt hsq

lemma candidate_coprime (n : ℕ) (h_not_prime : ¬Nat.Prime (Nat.factorial n + 1))
    (h : (prime_candidates n).Nonempty) :
    (sInf (prime_candidates n)).Coprime (Nat.factorial n / (sInf (prime_candidates n) - 1) + 1) := by
  let p := sInf (prime_candidates n)
  let q := Nat.factorial n / (p - 1) + 1
  have hp_mem : p ∈ prime_candidates n := by simpa [p] using (Nat.sInf_mem h)
  have hp : Nat.Prime p := hp_mem.1
  have hq : Nat.Prime q := by simpa [prime_candidates, p, q] using hp_mem.2.2.2
  have hpne : p ≠ q := by
    intro hpq
    have hdvd : p - 1 ∣ Nat.factorial n := hp_mem.2.2.1
    have hdiv : Nat.factorial n / (p - 1) = p - 1 := by
      unfold q at hpq
      have hp1 : 1 ≤ p := hp.one_le
      omega
    have hsquare : Nat.factorial n = (p - 1) ^ 2 := by
      calc Nat.factorial n = (p - 1) * (Nat.factorial n / (p - 1)) := (Nat.mul_div_cancel' hdvd).symm
        _ = (p - 1) ^ 2 := by rw [hdiv, pow_two]
    by_cases hn2 : 2 ≤ n
    · exact factorial_not_square_of_two_le (a := p - 1) hn2 hsquare
    · have hnsmall : n = 0 ∨ n = 1 := by omega
      rcases hnsmall with rfl | rfl
      · norm_num at h_not_prime
      · norm_num at h_not_prime
  exact (Nat.coprime_primes hp hq).mpr hpne

lemma A055487_le_candidate (n : ℕ) (h_not_prime : ¬Nat.Prime (Nat.factorial n + 1))
    (h : (prime_candidates n).Nonempty) :
    A055487 n ≤
      let N := Nat.factorial n
      let p := sInf (prime_candidates n)
      p * (N / (p - 1) + 1) := by
  unfold A055487
  let p := sInf (prime_candidates n)
  let q := Nat.factorial n / (p - 1) + 1
  have hp_mem : p ∈ prime_candidates n := by simpa [p] using (Nat.sInf_mem h)
  have hp : Nat.Prime p := hp_mem.1
  have hdvd : p - 1 ∣ Nat.factorial n := hp_mem.2.2.1
  have hq : Nat.Prime q := by simpa [prime_candidates, p, q] using hp_mem.2.2.2
  have hc : p.Coprime q := by simpa [p, q] using candidate_coprime n h_not_prime h
  apply Nat.sInf_le
  change Nat.totient (p * q) = Nat.factorial n
  rw [Nat.totient_mul hc, Nat.totient_prime hp, Nat.totient_prime hq]
  have hqsub : q - 1 = Nat.factorial n / (p - 1) := by unfold q; exact Nat.add_one_sub_one _
  rw [hqsub]
  exact Nat.mul_div_cancel' hdvd
