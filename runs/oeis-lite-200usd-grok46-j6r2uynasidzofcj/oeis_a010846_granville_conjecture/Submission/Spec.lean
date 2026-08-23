import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

/-- For a prime `p`, the only numbers `k ≤ p` with `primeFactors k ⊆ primeFactors p` are `1` and `p`. -/
lemma a_prime {p : ℕ} (hp : p.Prime) : a p = 2 := by
  have hset : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) = {1, p} := by
    ext k
    simp only [mem_filter, mem_Icc, hp.primeFactors, mem_insert, mem_singleton]
    constructor
    · intro ⟨⟨hk1, hkp⟩, hsub⟩
      by_cases hk : k = 1
      · exact Or.inl hk
      · have hkgt : 1 < k := lt_of_le_of_ne hk1 (Ne.symm hk)
        have hne : (primeFactors k).Nonempty := nonempty_primeFactors.mpr hkgt
        obtain ⟨q, hq⟩ := hne
        have hqeq : q = p := by
          simpa using hsub hq
        have hpdvd : p ∣ k := by
          rw [← hqeq]
          exact dvd_of_mem_primeFactors hq
        exact Or.inr (le_antisymm hkp (Nat.le_of_dvd (by omega) hpdvd))
    · intro h
      rcases h with rfl | rfl
      · exact ⟨⟨le_rfl, hp.one_lt.le⟩, by simp [primeFactors_one]⟩
      · refine ⟨⟨hp.one_lt.le, le_rfl⟩, ?_⟩
        rw [hp.primeFactors]
  have hne : (1 : ℕ) ≠ p := hp.ne_one.symm
  rw [a, hset, card_pair hne]

/--
The claimed lower bound `a(n) ≥ (log n)^{1-ε}` fails for all large primes, where `a(p) = 2`.
-/
theorem oeis_a010846_granville_conjecture.disproof :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n) := by
  push_neg
  refine ⟨(1 / 2 : ℝ), by positivity, ?_⟩
  intro N
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 81)
  refine ⟨p, le_of_max_le_left hpN, ?_⟩
  have ha : a p = 2 := a_prime hp
  have hp81 : 81 ≤ p := le_of_max_le_right hpN
  have hexp4 : Real.exp 4 < 81 := by
    calc
      Real.exp 4 = Real.exp 1 ^ 4 := (Real.exp_one_pow 4).symm
      _ < (3 : ℝ) ^ 4 :=
        pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by decide)
      _ = 81 := by norm_num
  have hlog : (4 : ℝ) < Real.log p := by
    rw [Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr hp.pos)]
    exact hexp4.trans_le (Nat.cast_le.mpr hp81)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsqrt4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
  have hpow : (2 : ℝ) < (Real.log p) ^ (1 / 2 : ℝ) := by
    calc
      (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := hsqrt4.symm
      _ < (Real.log p) ^ (1 / 2 : ℝ) := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 4) hlog hhalf
  rw [ha]
  have hε : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hε]
  exact hpow
