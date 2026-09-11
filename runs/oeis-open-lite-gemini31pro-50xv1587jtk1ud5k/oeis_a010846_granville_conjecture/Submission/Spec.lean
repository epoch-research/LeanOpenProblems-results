import FormalConjectures.Util.ProblemImports
open Filter Topology Nat Finset

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
theorem oeis_a010846_granville_conjecture :
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n :=
by sorry

lemma a_prime_le_two {p : ℕ} (hp : p.Prime) : a p ≤ 2 := by
  have H : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) ⊆ {1, p} := by
    intro k hk
    rw [mem_filter, mem_Icc] at hk
    rcases hk with ⟨⟨h1, hpk⟩, hsub⟩
    rw [hp.primeFactors] at hsub
    rw [mem_insert, mem_singleton]
    by_cases hk1 : k = 1
    · left; exact hk1
    · right
      have hk_gt1 : 1 < k := lt_of_le_of_ne h1 (Ne.symm hk1)
      have h_nonempty : k.primeFactors.Nonempty := nonempty_primeFactors.mpr hk_gt1
      rcases h_nonempty with ⟨q, hq⟩
      have hqp : q = p := by
        have := hsub hq
        rwa [mem_singleton] at this
      rw [hqp] at hq
      have p_le_k : p ≤ k := le_of_mem_primeFactors hq
      exact le_antisymm hpk p_le_k
  have H2 := card_le_card H
  have H3 : ({1, p} : Finset ℕ).card ≤ 2 := by
    have h4 : ({1, p} : Finset ℕ) = insert 1 {p} := rfl
    rw [h4]
    calc (insert 1 {p} : Finset ℕ).card
      _ ≤ ({p} : Finset ℕ).card + 1 := card_insert_le 1 {p}
      _ = 1 + 1 := by rw [card_singleton]
      _ = 2 := rfl
  exact le_trans H2 H3

lemma tendsto_log_rpow : Tendsto (fun x : ℝ => (Real.log x) ^ (1/2 : ℝ)) atTop atTop :=
  Tendsto.comp (tendsto_rpow_atTop (by norm_num)) Real.tendsto_log_atTop

lemma exists_M : ∃ M : ℝ, ∀ x ≥ M, 2 < (Real.log x) ^ (1/2 : ℝ) := by
  have h := tendsto_log_rpow.eventually (eventually_gt_atTop 2)
  rw [eventually_atTop] at h
  exact h

lemma get_prime (N : ℕ) (M : ℝ) : ∃ p : ℕ, p.Prime ∧ N ≤ p ∧ M ≤ (p : ℝ) := by
  have hM : ∃ m : ℕ, M ≤ m := ⟨Nat.ceil M, Nat.le_ceil M⟩
  rcases hM with ⟨m, hm⟩
  have h_prime := Nat.exists_infinite_primes (max N m)
  rcases h_prime with ⟨p, hp_ge, hp_prime⟩
  use p
  refine ⟨hp_prime, ?_, ?_⟩
  · exact le_trans (le_max_left N m) hp_ge
  · have : (m : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr (le_trans (le_max_right N m) hp_ge)
    exact le_trans hm this

theorem oeis_a010846_granville_conjecture.disproof : ¬ (type_of% @oeis_a010846_granville_conjecture) := by
  intro h
  have h_half := h (1/2) (by norm_num)
  rcases h_half with ⟨N, hN⟩
  rcases exists_M with ⟨M, hM⟩
  rcases get_prime N M with ⟨p, hp_prime, hp_ge_N, hp_ge_M⟩
  have h_ineq := hN p hp_ge_N
  have h_log := hM p hp_ge_M
  have h_a_le := a_prime_le_two hp_prime
  have h_a_real : (a p : ℝ) ≤ 2 := by exact Nat.cast_le.mpr h_a_le
  have h1 : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  rw [h1] at h_ineq
  have h_contra : (Real.log p) ^ (1/2 : ℝ) ≤ 2 := le_trans h_ineq h_a_real
  linarith
