import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A236566: Number of ordered ways to write $2n = p + q$ with $p, q$ and $\operatorname{prime}(p + 2) + 2$ all prime.
Here $\operatorname{prime}(k)$ denotes the $k$-th prime number $p_k$.
Transcribing this to Mathlib's 0-indexed $p'_{k} = \operatorname{Nat.nth\ Nat.Prime}\ k$, we use $\operatorname{Nat.nth\ Nat.Prime}\ (p+1)$ for $\operatorname{prime}(p + 2)$.
-/
noncomputable def A236566 (n : ℕ) : ℕ :=
  Finset.card <| (Finset.range (2 * n)).filter fun p =>
    Nat.Prime p ∧
    Nat.Prime (2 * n - p) ∧
    Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)

/-- Twin Prime Conjecture: There are infinitely many primes $p$ such that $p + 2$ is prime. -/
def twin_prime_conjecture : Prop := Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}

/-- Lemoine's Conjecture (or Levy's conjecture): Every odd number $k > 5$ can be written as $p + 2q$, where $p$ and $q$ are prime numbers. -/
def lemoine_conjecture : Prop :=
  ∀ k : ℕ, Odd k → 5 < k → ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ k = p + 2 * q

/--
Conjecture A236566 part (ii):
If $n > 30$, then $2n + 1$ can be written as $2p + q$ with $p, q$ and $\operatorname{prime}(p + 2) + 2$ all prime.
Note: We interpret $\operatorname{prime}(p + 2)$ as $\operatorname{Nat.nth\ Nat.Prime}\ (p + 1)$, following the setup of A236566's Lean definition above,
where $p$ is one of the primes involved in the sum $2n+1 = 2p+q$.
-/
def a236566_conjecture_part_ii : Prop :=
  ∀ n : ℕ, 30 < n → ∃ (p q : ℕ),
    Nat.Prime p ∧
    Nat.Prime q ∧
    Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2) ∧
    2 * n + 1 = 2 * p + q

lemma lemoine_small (k : ℕ) (hk : Odd k) (h5 : 5 < k) (h61 : k ≤ 61) :
    ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ k = p + 2 * q := by
  rcases hk with ⟨m, rfl⟩
  have hm1 : 2 < m := by omega
  have hm2 : m ≤ 30 := by omega
  interval_cases m
  · use 3, 2; decide
  · use 3, 3; decide
  · use 5, 3; decide
  · use 3, 5; decide
  · use 5, 5; decide
  · use 3, 7; decide
  · use 5, 7; decide
  · use 7, 7; decide
  · use 13, 5; decide
  · use 3, 11; decide
  · use 5, 11; decide
  · use 3, 13; decide
  · use 5, 13; decide
  · use 7, 13; decide
  · use 13, 11; decide
  · use 3, 17; decide
  · use 5, 17; decide
  · use 3, 19; decide
  · use 5, 19; decide
  · use 7, 19; decide
  · use 13, 17; decide
  · use 3, 23; decide
  · use 5, 23; decide
  · use 7, 23; decide
  · use 17, 19; decide
  · use 11, 23; decide
  · use 13, 23; decide
  · use 3, 29; decide

lemma lemoine_from_a236566 (h : a236566_conjecture_part_ii) : lemoine_conjecture := by
  intro k hk h5
  by_cases h61 : k ≤ 61
  · exact lemoine_small k hk h5 h61
  · push_neg at h61
    rcases hk with ⟨n, rfl⟩
    have hn : 30 < n := by omega
    obtain ⟨p, q, hp, hq, _, heq⟩ := h n hn
    use q, p
    refine ⟨hq, hp, ?_⟩
    omega

theorem twin_prime_of_forall_exists_gt (h : ∀ a : ℕ, ∃ b, Nat.Prime b ∧ Nat.Prime (b + 2) ∧ a < b) : twin_prime_conjecture := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨b, h1, h2, h3⟩ := h a
  exact ⟨b, ⟨h1, h2⟩, h3⟩

theorem twin_prime_from_a236566 (h : a236566_conjecture_part_ii) : twin_prime_conjecture := by
  apply twin_prime_of_forall_exists_gt
  by_contra h_no_twin
  push_neg at h_no_twin
  obtain ⟨a, ha⟩ := h_no_twin
  let M := max a 30
  have hM_a : a ≤ M := le_max_left a 30
  have hM_30 : 30 ≤ M := le_max_right a 30
  let K := 2 * M + 2
  have hK_ge2 : 2 ≤ K := by omega
  let n := K ! / 2 + M + 1
  have h_div : 2 ∣ K ! := Nat.dvd_factorial (by decide) hK_ge2
  have h_eq : 2 * (K ! / 2) = K ! := Nat.mul_div_cancel' h_div
  have hn_30 : 30 < n := by omega
  obtain ⟨p, q, hp, hq, hp2, hsum⟩ := h n hn_30
  have hsum_eq : 2 * n + 1 = K ! + 2 * M + 3 := by
    calc 2 * n + 1 = 2 * (K ! / 2 + M + 1) + 1 := rfl
      _ = 2 * (K ! / 2) + 2 * M + 3 := by omega
      _ = K ! + 2 * M + 3 := by rw [h_eq]
  have h_pq_sum : 2 * p + q = K ! + 2 * M + 3 := hsum_eq ▸ hsum.symm
  have hp_le_M : p ≤ M := by
    by_contra hp_gt_M
    push_neg at hp_gt_M
    let b := Nat.nth Nat.Prime (p + 1)
    have hb_prime : Nat.Prime b := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (p + 1)
    have hb2_prime : Nat.Prime (b + 2) := hp2
    have hp_le_b : p + 1 ≤ b := by
      apply Nat.le_nth
      intro hf
      exfalso
      exact Nat.infinite_setOf_prime hf
    have ha_lt_b : a < b := by omega
    have h_le : b ≤ a := ha b hb_prime hb2_prime
    omega
  let d := 2 * M + 3 - 2 * p
  have hd_ge3 : 3 ≤ d := by omega
  have hd_le : d ≤ 2 * M - 1 := by
    have hp_ge2 : 2 ≤ p := hp.two_le
    omega
  have hd_le_K : d ≤ K := by omega
  have hd_dvd_factorial : d ∣ K ! := Nat.dvd_factorial (by omega) hd_le_K
  have hq_val : q = K ! + d := by omega
  have hd_dvd_q : d ∣ q := by
    rw [hq_val]
    exact dvd_add hd_dvd_factorial (dvd_refl d)
  have hd_lt_q : d < q := by
    rw [hq_val]
    have hK_fact_pos : 0 < K ! := Nat.factorial_pos K
    omega
  have hq_not_prime : ¬ Nat.Prime q := by
    apply Nat.not_prime_of_dvd_of_lt hd_dvd_q (by omega) hd_lt_q
  exact hq_not_prime hq

/--
A236566: Conjecture: Part (ii) implies both Lemoine's conjecture (cf. A046927) and the twin prime conjecture.
-/
theorem oeis_236566_conjecture_2 :
  a236566_conjecture_part_ii → lemoine_conjecture ∧ twin_prime_conjecture := by
  intro h
  exact ⟨lemoine_from_a236566 h, twin_prime_from_a236566 h⟩
