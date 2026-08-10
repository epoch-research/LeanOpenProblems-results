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
  have hpge : N ≤ p := le_trans (le_max_left _ _) hpN
  have hp55 : 55 ≤ p := le_trans (le_max_right _ _) hpN
  -- `a p ≤ 2` : for prime `p` only `k = 1` and `k = p` have prime factors ⊆ {p}.
  have hap : a p ≤ 2 := by
    unfold a
    have hsub : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) ⊆ ({1, p} : Finset ℕ) := by
      intro k hk
      simp only [mem_filter, mem_Icc] at hk
      obtain ⟨⟨hk1, hkp⟩, hksub⟩ := hk
      simp only [mem_insert, mem_singleton]
      rcases eq_or_lt_of_le hk1 with h1 | h2
      · left; exact h1.symm
      · right
        have hkpos : k ≠ 0 := by omega
        obtain ⟨q, hq⟩ := (Nat.exists_prime_and_dvd (n := k) (by omega))
        have hqmem : q ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hq.1, hq.2, hkpos⟩
        have hqp : q ∈ p.primeFactors := hksub hqmem
        rw [hp.primeFactors] at hqp
        simp only [mem_singleton] at hqp
        have hpk : p ∣ k := hqp ▸ hq.2
        have := Nat.le_of_dvd (by omega) hpk
        omega
    calc ((Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p)).card
          ≤ ({1, p} : Finset ℕ).card := card_le_card hsub
      _ ≤ 2 := (card_insert_le _ _).trans (by simp)
  -- `log p > 4` since `p ≥ 55 > e^4`.
  have hlog : (4:ℝ) < Real.log p := by
    have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by
      have := Real.exp_nat_mul 1 4
      simp only [Nat.cast_ofNat, mul_one] at this
      exact this
    have hexp4 : Real.exp 4 < 55 := by
      rw [h1]
      have : Real.exp 1 ^ 4 < (2.7182818286:ℝ) ^ 4 := by gcongr; exact Real.exp_one_lt_d9
      linarith [this, (by norm_num : (2.7182818286:ℝ)^4 < 55)]
    have hpr : (55:ℝ) ≤ p := by exact_mod_cast hp55
    calc (4:ℝ) = Real.log (Real.exp 4) := (Real.log_exp 4).symm
      _ < Real.log 55 := Real.log_lt_log (by positivity) hexp4
      _ ≤ Real.log p := Real.log_le_log (by norm_num) hpr
  -- `(log p)^(1 - 1/2) = √(log p) > 2`.
  have hgt : (2:ℝ) < (Real.log p) ^ (1 - (1/2:ℝ)) := by
    have e : (1 - (1/2:ℝ)) = 1/2 := by norm_num
    rw [e, ← Real.sqrt_eq_rpow]
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2^2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hlog
  -- Contradiction: the conjecture forces `(log p)^(1-1/2) ≤ a p ≤ 2 < (log p)^(1-1/2)`.
  have hle : (Real.log p) ^ (1 - (1/2:ℝ)) ≤ (a p : ℝ) := hN p hpge
  have hap2 : (a p : ℝ) ≤ 2 := by exact_mod_cast hap
  linarith [hgt, hle, hap2]
