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
lemma helper (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k ∈ Icc 1 p) (h_sub : k.primeFactors ⊆ p.primeFactors) :
    k = 1 ∨ k = p := by
  by_cases hk1 : k = 1
  · left; exact hk1
  · right
    have hk_gt : 1 < k := by
      have : k ≥ 1 := (mem_Icc.1 hk).1
      omega
    have h_nonempty : k.primeFactors.Nonempty := nonempty_primeFactors.2 hk_gt
    obtain ⟨q, hq⟩ := h_nonempty
    have hp_factors : p.primeFactors = {p} := by
      have h_pow : (p ^ 1).primeFactors = {p} := primeFactors_prime_pow (k := 1) (by decide) hp
      have : p ^ 1 = p := by ring
      rwa [this] at h_pow
    rw [hp_factors] at h_sub
    have hq_mem : q ∈ ({p} : Finset ℕ) := h_sub hq
    have hq_eq : q = p := mem_singleton.1 hq_mem
    rw [hq_eq] at hq
    have hp_dvd : p ∣ k := dvd_of_mem_primeFactors hq
    have hk_le : k ≤ p := (mem_Icc.1 hk).2
    have hp_le : p ≤ k := le_of_dvd (by omega) hp_dvd
    omega

lemma filter_primeFactors_eq (p : ℕ) (hp : p.Prime) :
    (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) = {1, p} := by
  ext x
  simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
  have h_p2 : 2 ≤ p := hp.two_le
  constructor
  · rintro ⟨⟨hk1, hk2⟩, h_sub⟩
    have hk_mem : x ∈ Icc 1 p := by
      rw [mem_Icc]
      exact ⟨hk1, hk2⟩
    exact helper p hp x hk_mem h_sub
  · intro h_or
    rcases h_or with rfl | rfl
    · refine ⟨⟨by norm_num, by omega⟩, ?_⟩
      simp
    · refine ⟨⟨by omega, by rfl⟩, ?_⟩
      exact Subset.refl _

lemma a_prime (p : ℕ) (hp : p.Prime) : a p = 2 := by
  unfold a
  rw [filter_primeFactors_eq p hp]
  have h_ne : 1 ≠ p := by
    have : 2 ≤ p := hp.two_le
    omega
  exact card_pair h_ne

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
  have h_half : 0 < (1/2 : ℝ) := by norm_num
  obtain ⟨N, hN⟩ := h (1/2) h_half
  let M := N + 1000
  obtain ⟨p, hp_M, hp_prime⟩ := exists_infinite_primes M
  have hp_N : N ≤ p := by omega
  have hp_1000 : 1000 ≤ p := by omega
  have hp_pos : 0 < (p : ℝ) := by
    positivity
  have h_exp : Real.exp 4 < 1000 := by
    have h_exp_eq : Real.exp 4 = Real.exp 1 ^ 4 := by exact (Real.exp_one_pow 4).symm
    rw [h_exp_eq]
    have h1 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h2 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    have h3 : Real.exp 1 ^ 4 < (3 : ℝ) ^ 4 := by
      apply pow_lt_pow_left₀ h1 h2 (by decide)
    have h4 : (3 : ℝ) ^ 4 = 81 := by norm_num
    linarith
  have h_exp_p : Real.exp 4 < (p : ℝ) := by
    have : (1000 : ℝ) ≤ p := by exact_mod_cast hp_1000
    linarith
  have h_log_p : 4 < Real.log p := by
    rwa [Real.lt_log_iff_exp_lt hp_pos]
  have h_sqrt_log_p : 2 < (Real.log p) ^ (1 - (1/2 : ℝ)) := by
    have h1 : 1 - (1/2 : ℝ) = 1 / 2 := by norm_num
    rw [h1, ← Real.sqrt_eq_rpow]
    have h2 : (2 : ℝ) = Real.sqrt 4 := by norm_num
    rw [h2]
    have h3 : (0 : ℝ) ≤ 4 := by norm_num
    exact (Real.sqrt_lt_sqrt h3 h_log_p)
  have h_bound := hN p hp_N
  have h_ap : a p = 2 := a_prime p hp_prime
  have h_bound_r : (Real.log p) ^ (1 - (1/2 : ℝ)) ≤ (2 : ℝ) := by
    rw [h_ap] at h_bound
    exact h_bound
  linarith
