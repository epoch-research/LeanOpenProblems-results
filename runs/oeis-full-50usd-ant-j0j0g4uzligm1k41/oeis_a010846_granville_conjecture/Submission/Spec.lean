import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

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
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 55)
  have hpN' : N ≤ p := le_trans (le_max_left _ _) hpN
  have hp55 : 55 ≤ p := le_trans (le_max_right _ _) hpN
  -- For a prime `p`, the only `k ≤ p` whose prime factors divide `p` are `1` and `p`,
  -- so `a p ≤ 2`.
  have hap : a p ≤ 2 := by
    unfold a
    have hsub : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) ⊆ ({1, p} : Finset ℕ) := by
      intro k hk
      rw [mem_filter, mem_Icc] at hk
      obtain ⟨⟨hk1, hkp⟩, hksub⟩ := hk
      rw [hp.primeFactors] at hksub
      simp only [mem_insert, mem_singleton]
      by_cases hk1' : k = 1
      · left; exact hk1'
      · right
        have hk2 : 1 < k := lt_of_le_of_ne hk1 (Ne.symm hk1')
        obtain ⟨q, hq⟩ := Nat.nonempty_primeFactors.mpr hk2
        have hqp : q = p := by have := hksub hq; simpa using this
        rw [hqp] at hq
        rw [Nat.mem_primeFactors] at hq
        have hpk : p ∣ k := hq.2.1
        have : p ≤ k := Nat.le_of_dvd (by omega) hpk
        omega
    have h2 : ({1, p} : Finset ℕ).card ≤ 2 := by
      apply le_trans (card_insert_le _ _); simp
    exact le_trans (card_le_card hsub) h2
  -- But `4 < log p` since `p ≥ 55 > e^4`.
  have hlog : (4:ℝ) < Real.log p := by
    have hexp4 : Real.exp 4 < 55 := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h4]
      have hpos : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
      calc Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
        _ < 55 := by norm_num
    have hp55' : (55:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp55
    have hpos : (0:ℝ) < (p:ℝ) := by linarith
    rw [Real.lt_log_iff_exp_lt hpos]
    linarith
  -- Hence `(log p)^(1 - 1/2) = (log p)^(1/2) > 4^(1/2) = 2 ≥ a p`, contradiction.
  have hkey : (2:ℝ) < (Real.log p) ^ (1 - (1/2:ℝ)) := by
    have e : (1 - (1/2:ℝ)) = (1/2:ℝ) := by norm_num
    rw [e]
    have h4half : (4:ℝ) ^ (1/2:ℝ) = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, ← Real.rpow_natCast 2 2, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (2:ℝ) = (4:ℝ) ^ (1/2:ℝ) := h4half.symm
      _ < (Real.log p) ^ (1/2:ℝ) := by
          apply Real.rpow_lt_rpow (by norm_num) hlog (by norm_num)
  have hh := hN p hpN'
  have hap' : (a p : ℝ) ≤ 2 := by exact_mod_cast hap
  linarith

