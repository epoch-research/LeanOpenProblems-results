import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

lemma a_eq_two_of_prime {p : ℕ} (hp : Nat.Prime p) : a p = 2 := by
  unfold a
  have hset : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) = {1, p} := by
    ext k
    constructor
    · intro hk
      rw [mem_filter, mem_Icc] at hk
      rcases hk with ⟨⟨h1k, hkp⟩, hsub⟩
      by_cases hk1 : k = 1
      · simp [hk1]
      · have hk0 : k ≠ 0 := by omega
        obtain ⟨q, hqprime, hqdiv⟩ := Nat.exists_prime_and_dvd hk1
        have hqmem : q ∈ primeFactors k := by
          rw [Nat.mem_primeFactors]
          exact ⟨hqprime, hqdiv, hk0⟩
        have hqmem_p : q ∈ primeFactors p := hsub hqmem
        rw [hp.primeFactors] at hqmem_p
        have hqp : q = p := by simpa using hqmem_p
        have hpdivk : p ∣ k := by
          rwa [← hqp]
        have hpk : p ≤ k := Nat.le_of_dvd (by omega) hpdivk
        have hkp_eq : k = p := le_antisymm hkp hpk
        simp [hkp_eq]
    · intro hk
      rcases (by simpa using hk : k = 1 ∨ k = p) with rfl | rfl
      · rw [mem_filter, mem_Icc]
        constructor
        · constructor
          · norm_num
          · exact Nat.Prime.one_le hp
        · rw [Nat.primeFactors_one, hp.primeFactors]
          exact empty_subset {p}
      · rw [mem_filter, mem_Icc]
        constructor
        · constructor
          · exact Nat.Prime.one_le hp
          · exact le_rfl
        · rw [hp.primeFactors]
  rw [hset]
  exact card_pair (Ne.symm hp.ne_one)

/--
Granville's ABC-Conjecture implies that for any $\epsilon > 0$,
the function $a(n)$ is bounded below by $(\log n)^{1 - \epsilon}$ for sufficiently large $n$.
This is a formalization of a claim implied by the context:
OEIS C: "This function of n appears in an ABC-conjecture by Andrew Granville. See Goldfeld."
Granville (via Goldfeld) showed that ABC conjecture $\iff$ $\forall \epsilon > 0, \exists N, \forall n > N, a(n) \ge (\log n)^{1-\epsilon}$.
-/
theorem oeis_a010846_granville_conjecture.disproof :
  ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n) := by
  intro h
  rcases h (1 / 2 : ℝ) (by norm_num) with ⟨N, hN⟩
  let M : ℕ := max N (Nat.ceil (Real.exp 4) + 1)
  obtain ⟨p, hpM, hpprime⟩ := Nat.exists_infinite_primes M
  have hpN : N ≤ p := le_trans (le_max_left N (Nat.ceil (Real.exp 4) + 1)) hpM
  have hceille : Real.exp 4 ≤ (Nat.ceil (Real.exp 4) : ℝ) := Nat.le_ceil (Real.exp 4)
  have hceillt : Real.exp 4 < (Nat.ceil (Real.exp 4) + 1 : ℕ) := by
    norm_num [Nat.cast_add]
    linarith
  have hpexp : Real.exp 4 < (p : ℝ) := by
    have hMceil : Nat.ceil (Real.exp 4) + 1 ≤ M := le_max_right N (Nat.ceil (Real.exp 4) + 1)
    have hnat : Nat.ceil (Real.exp 4) + 1 ≤ p := le_trans hMceil hpM
    exact lt_of_lt_of_le hceillt (by exact_mod_cast hnat)
  have hp_pos_real : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hlog : (4 : ℝ) < Real.log p := by
    have hexp_lt : Real.exp 4 < Real.exp (Real.log (p : ℝ)) := by
      simpa [Real.exp_log hp_pos_real] using hpexp
    exact Real.exp_lt_exp.mp hexp_lt
  have hsqrt : (2 : ℝ) < √(Real.log (p : ℝ)) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    exact hlog
  have hrpow : (2 : ℝ) < (Real.log (p : ℝ)) ^ (1 - (1 / 2 : ℝ)) := by
    norm_num
    simpa [Real.sqrt_eq_rpow] using hsqrt
  have hbound := hN p hpN
  rw [a_eq_two_of_prime hpprime] at hbound
  norm_num at hbound
  linarith
