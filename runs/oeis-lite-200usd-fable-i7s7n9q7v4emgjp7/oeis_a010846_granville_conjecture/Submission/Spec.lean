import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

/-- For a prime `p`, only `1` and `p` among `1, …, p` have all prime factors in `{p}`,
so `a p ≤ 2`. -/
lemma a_prime_le_two {p : ℕ} (hp : p.Prime) : a p ≤ 2 := by
  have hsub : (Icc 1 p).filter (fun k => k.primeFactors ⊆ p.primeFactors) ⊆ {1, p} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hkp⟩, hkf⟩ := hk
    rw [hp.primeFactors] at hkf
    rcases eq_or_lt_of_le hk1 with h1 | h1
    · simp [← h1]
    · obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
      have hq_mem : q ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqk, by omega⟩
      have hqp : q = p := by simpa using hkf hq_mem
      subst hqp
      have hle : q ≤ k := Nat.le_of_dvd (by omega) hqk
      have hkq : k = q := le_antisymm hkp hle
      simp [hkq]
  calc a p ≤ ({1, p} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)

theorem oeis_a010846_granville_conjecture.disproof :
  ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n) := by
  intro h
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (max N 81)
  have hN' : N ≤ p := le_trans (le_max_left _ _) hp_ge
  have h81 : (81 : ℕ) ≤ p := le_trans (le_max_right _ _) hp_ge
  have key := hN p hN'
  have ha : (a p : ℝ) ≤ 2 := by exact_mod_cast a_prime_le_two hp
  -- `log p > 4` since `p ≥ 81 = 3⁴ > e⁴`
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_lt_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith
  have hlog81 : (4 : ℝ) < Real.log 81 := by
    have h81eq : Real.log 81 = 4 * Real.log 3 := by
      rw [show (81:ℝ) = 3 ^ (4:ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [h81eq]; linarith
  have hlogp : (4 : ℝ) < Real.log p := by
    have hle : Real.log 81 ≤ Real.log p := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast h81
    linarith
  -- hence `(log p) ^ (1 - 1/2) = √(log p) > 2 ≥ a p`, contradiction
  have hexp : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  rw [hexp, ← Real.sqrt_eq_rpow] at key
  have h2 : (2 : ℝ) < Real.sqrt (Real.log p) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  linarith
