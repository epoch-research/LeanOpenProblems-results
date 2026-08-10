import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

private lemma a_prime_eq_two {p : ℕ} (hp : Nat.Prime p) : a p = 2 := by
  unfold a
  have hset : (Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p) = ({1, p} : Finset ℕ) := by
    ext k
    constructor
    · intro hk
      rw [Finset.mem_filter] at hk
      rcases hk with ⟨hkI, hsub⟩
      rw [Finset.mem_Icc] at hkI
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_cases hk1 : k = 1
      · exact Or.inl hk1
      · right
        by_contra hkp
        have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hkI.1
        have hkgt : 1 < k := lt_of_le_of_ne hkI.1 (Ne.symm hk1)
        obtain ⟨q, hqprime, hqdk⟩ := Nat.exists_prime_and_dvd (_root_.ne_of_gt hkgt)
        have hqmemk : q ∈ primeFactors k := by
          exact Nat.mem_primeFactors.mpr ⟨hqprime, hqdk, _root_.ne_of_gt hkpos⟩
        have hqmemp : q ∈ primeFactors p := hsub hqmemk
        have hqeqp : q = p := by
          simpa [hp.primeFactors] using hqmemp
        subst q
        have hple : p ≤ k := Nat.le_of_dvd hkpos hqdk
        have hkltp : k < p := lt_of_le_of_ne hkI.2 hkp
        exact (not_lt_of_ge hple) hkltp
    · intro hk
      rw [Finset.mem_filter]
      rw [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · constructor
        · simp [hp.one_le]
        · simp
      · constructor
        · simp [hp.one_le]
        · simp
  rw [hset]
  simp [Ne.symm hp.ne_one]

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
  obtain ⟨N, hN⟩ := h (1 / 2 : ℝ) (by norm_num)
  let M : ℕ := max N (⌈Real.exp 4⌉₊ + 1)
  obtain ⟨p, hpM, hpprime⟩ := Nat.exists_infinite_primes M
  have hNp : N ≤ p := le_trans (le_max_left _ _) hpM
  have hmain := hN p hNp
  have hap : a p = 2 := a_prime_eq_two hpprime
  have hexplt : Real.exp 4 < (p : ℝ) := by
    have h1 : Real.exp 4 ≤ (⌈Real.exp 4⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp 4⌉₊ : ℝ) < (⌈Real.exp 4⌉₊ + 1 : ℕ) := by norm_num
    have h3nat : ⌈Real.exp 4⌉₊ + 1 ≤ p := le_trans (le_max_right N (⌈Real.exp 4⌉₊ + 1)) hpM
    have h3 : ((⌈Real.exp 4⌉₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3nat
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)
  have hloggt : 4 < Real.log (p : ℝ) := by
    rw [Real.lt_log_iff_exp_lt]
    · exact hexplt
    · exact lt_trans (Real.exp_pos 4) hexplt
  have hsqrtgt : (2 : ℝ) < √(Real.log (p : ℝ)) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.sqrt_lt_sqrt (sq_nonneg (2 : ℝ))
    norm_num
    exact hloggt
  have hrpowgt : (2 : ℝ) < (Real.log (p : ℝ)) ^ (1 - (1 / 2 : ℝ)) := by
    rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
    simpa [Real.sqrt_eq_rpow] using hsqrtgt
  have hmain' : (Real.log (p : ℝ)) ^ (1 - (1 / 2 : ℝ)) ≤ (2 : ℝ) := by
    simpa [hap] using hmain
  exact not_lt_of_ge hmain' hrpowgt
