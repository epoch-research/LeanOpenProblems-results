import FormalConjectures.Util.ProblemImports
open Set
open Nat

/--
A055487: Least $m$ such that $\phi(m) = n!$.
The sequence $a(n)$ is the smallest natural number $m$ such that Euler's totient function
$\phi(m)$ equals $n!$.
-/
noncomputable def A055487 (n : ℕ) : ℕ :=
  sInf {m : ℕ | Nat.totient m = Nat.factorial n}

/-- The set of primes $p > \sqrt{n!}$ such that $p-1$ divides $n!$ and $n!/(p-1) + 1$ is also prime. -/
def prime_candidates (n : ℕ) : Set ℕ :=
  let N := Nat.factorial n
  -- Note: Nat.Prime p implies p ≥ 2, so p - 1 ≥ 1.
  { p : ℕ | Nat.Prime p ∧ Nat.sqrt N < p ∧ (p - 1) ∣ N ∧ Nat.Prime (N / (p - 1) + 1) }

/-- Auxiliary fact: for `n ≥ 2`, `n!` is not a perfect square. -/
theorem factorial_not_isSquare (n : ℕ) (hn : 2 ≤ n) : ¬ IsSquare (Nat.factorial n) := by
  obtain ⟨P, hP, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  have hPn : P ≤ n := le_trans hhi (by omega)
  have h2P : n < 2 * P := by omega
  have hlog : Nat.log P n < 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    calc n < 2 * P := h2P
    _ ≤ P * P := by nlinarith [hP.two_le]
    _ = P ^ 2 := by ring
  have hfact : (Nat.factorial n).factorization P = 1 := by
    rw [Nat.factorization_factorial hP hlog]
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_Ico_succ_top (by norm_num)]
    simp only [Finset.Ico_self, Finset.sum_empty, zero_add, pow_one]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  intro hsq
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by rintro rfl; simp [Nat.factorial_ne_zero] at hr
  have : (Nat.factorial n).factorization P = 2 * r.factorization P := by
    rw [hr, Nat.factorization_mul hr0 hr0]; simp [two_mul]
  omega

/-- The provable direction: the construction is a genuine totient-inverse of `n!`. -/
theorem construction_le (n : ℕ)
    (h_not_prime : ¬Nat.Prime (Nat.factorial n + 1))
    (h_solvable : (prime_candidates n).Nonempty) :
    A055487 n ≤
      let N := Nat.factorial n
      let p := sInf (prime_candidates n)
      p * (N / (p - 1) + 1) := by
  simp only
  set N := Nat.factorial n with hN
  set p := sInf (prime_candidates n) with hp
  have hmem : p ∈ prime_candidates n := Nat.sInf_mem h_solvable
  obtain ⟨hp_prime, hp_sqrt, hp_dvd, hq_prime⟩ := hmem
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp_all [Nat.factorial]
    · exact h
  have hNsq : ¬ IsSquare N := factorial_not_isSquare n hn2
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hdivcancel : (p - 1) * (N / (p - 1)) = N := Nat.mul_div_cancel' hp_dvd
  have hpne : p ≠ N / (p - 1) + 1 := by
    intro h
    have hpeq : p - 1 = N / (p - 1) := by omega
    have hNsq2 : N = (p - 1) * (p - 1) := by
      have hc := hdivcancel
      rw [← hpeq] at hc
      exact hc.symm
    exact hNsq ⟨p - 1, hNsq2⟩
  have hphi : Nat.totient (p * (N / (p - 1) + 1)) = N := by
    have hcop : Nat.Coprime p (N / (p - 1) + 1) :=
      (Nat.coprime_primes hp_prime hq_prime).mpr hpne
    rw [Nat.totient_mul hcop, Nat.totient_prime hp_prime, Nat.totient_prime hq_prime,
      Nat.add_sub_cancel, hdivcancel]
  exact Nat.sInf_le hphi

/--
A055487 Conjecture: Unless n!+1 is prime (i.e., n in A002981), a(n)=pq where p is the least prime > sqrt(n!) such that (p-1) | n! and q=n!/(p-1)+1 is prime.
-/
theorem A055487_conjecture (n : ℕ)
    (h_not_prime : ¬Nat.Prime (Nat.factorial n + 1))
    (h_solvable : (prime_candidates n).Nonempty) :
    A055487 n =
      let N := Nat.factorial n
      let p := sInf (prime_candidates n)
      p * (N / (p - 1) + 1) :=
  by
    refine le_antisymm (construction_le n h_not_prime h_solvable) ?_
    sorry
