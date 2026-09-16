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

set_option maxRecDepth 2000000

/--
A236566: Conjecture: Part (ii) implies both Lemoine's conjecture (cf. A046927) and the twin prime conjecture.
-/

def S := {p : ℕ | Nat.Prime p ∧ Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)}

lemma S_infinite (h : a236566_conjecture_part_ii) : Set.Infinite S := by
  intro h_fin
  have h_finset : ∃ F : Finset ℕ, ∀ x, x ∈ F ↔ x ∈ S := by
    classical exact ⟨h_fin.toFinset, fun x => Set.Finite.mem_toFinset _⟩
  rcases h_finset with ⟨F, hF⟩
  let N0 := F.sup (fun x => x)
  let N := max 30 N0
  have h_le : ∀ p ∈ S, p ≤ N := by
    intro p hp
    have h1 : p ∈ F := (hF p).mpr hp
    have h2 : p ≤ N0 := Finset.le_sup (f := id) h1
    omega
  let N2 := 2 * N + 2
  let M := N2.factorial
  let n := M / 2
  have hM_even : 2 ∣ M := by
    apply Nat.dvd_factorial (by decide)
    have : N ≥ 30 := by exact le_max_left 30 N0
    omega
  have hM : M = 2 * n := by
    have : M / 2 * 2 = M := Nat.div_mul_cancel hM_even
    omega
  have hn_gt : n > 30 := by
    have hN2 : N2 ≥ 62 := by
      have : N ≥ 30 := by exact le_max_left 30 N0
      omega
    have : N2.factorial ≥ 62 := by
      apply Nat.le_trans (m := N2)
      · omega
      · apply Nat.self_le_factorial
    omega
  obtain ⟨p, q, hp, hq, hpS, heq⟩ := h n hn_gt
  have hp_in_S : p ∈ S := ⟨hp, hpS⟩
  have hp_le_N : p ≤ N := h_le p hp_in_S
  have h_2p_sub_1_gt_0 : 2 * p - 1 > 0 := by
    have : p ≥ 2 := hp.two_le
    omega
  have h_2p_sub_1_le_N2 : 2 * p - 1 ≤ N2 := by
    omega
  have h_div : 2 * p - 1 ∣ M := Nat.dvd_factorial h_2p_sub_1_gt_0 h_2p_sub_1_le_N2
  have h_q_eq : q = M - (2 * p - 1) := by
    have h1 : 2 * n + 1 = 2 * p + q := heq
    have h2 : M + 1 = 2 * p + q := by omega
    have : p ≥ 2 := hp.two_le
    omega
  have h_q_div : 2 * p - 1 ∣ q := by
    rw [h_q_eq]
    apply Nat.dvd_sub
    · exact h_div
    · exact dvd_rfl
  have h_q_gt : q > 2 * p - 1 := by
    rw [h_q_eq]
    have hp2 : p ≥ 2 := hp.two_le
    have : 2 * p - 1 ≤ 2 * N + 1 := by omega
    have hN_30 : N ≥ 30 := by exact le_max_left 30 N0
    have h_fac : M > 4 * N := by
      have h1 : 2 * N + 2 = (2 * N + 1) + 1 := by omega
      have h2 : (2 * N + 2).factorial = (2 * N + 2) * (2 * N + 1).factorial := by
        rw [h1, Nat.factorial_succ]
      have h3 : (2 * N + 1).factorial ≥ 2 := by
        apply Nat.le_trans (m := 2 * N + 1)
        · omega
        · apply Nat.self_le_factorial
      nlinarith
    omega
  have h_q_comp : ¬ Nat.Prime q := by
    intro hq_prime
    have := hq_prime.eq_one_or_self_of_dvd (2 * p - 1) h_q_div
    rcases this with h1 | h2
    · have : p ≥ 2 := hp.two_le
      omega
    · omega
  exact h_q_comp hq

lemma twin_of_part_ii (h : a236566_conjecture_part_ii) : twin_prime_conjecture := by
  have hS := S_infinite h
  let f (p : ℕ) := Nat.nth Nat.Prime (p + 1)
  have h_inj : Function.Injective f := by
    intro a b hab
    have : a + 1 = b + 1 := Nat.nth_injective Nat.infinite_setOf_prime hab
    omega
  have h_inf_img : Set.Infinite (f '' S) := hS.image h_inj.injOn
  apply Set.Infinite.mono (s := f '' S)
  · intro x hx
    rcases hx with ⟨p, hpS, rfl⟩
    exact ⟨Nat.prime_nth_prime (p + 1), hpS.2⟩
  · exact h_inf_img

lemma lemoine_of_part_ii (h : a236566_conjecture_part_ii) : lemoine_conjecture := by
  intro k hk_odd hk_gt
  by_cases hk_61 : k > 61
  · obtain ⟨n, hn⟩ : ∃ n, k = 2 * n + 1 := by
      use k / 2
      have : 2 ∣ k - 1 := by
        rcases hk_odd with ⟨m, hm⟩
        rw [hm]
        omega
      omega
    have hn30 : n > 30 := by omega
    obtain ⟨p, q, hp, hq, _, heq⟩ := h n hn30
    use q, p
    refine ⟨hq, hp, ?_⟩
    omega
  · have : ∀ k < 62, Odd k → 5 < k → ∃ p < k, ∃ q < k, Nat.Prime p ∧ Nat.Prime q ∧ k = p + 2 * q := by
      decide
    rcases this k (by omega) hk_odd hk_gt with ⟨p, _, q, _, hp, hq, heq⟩
    exact ⟨p, q, hp, hq, heq⟩

theorem oeis_236566_conjecture_2 :
  a236566_conjecture_part_ii → lemoine_conjecture ∧ twin_prime_conjecture := by
  intro h
  exact ⟨lemoine_of_part_ii h, twin_of_part_ii h⟩

theorem oeis_236566_conjecture_2.disproof : ¬ (type_of% @oeis_236566_conjecture_2) := sorry
