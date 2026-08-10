import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A227923: Number of ways to write $n = x + y$ ($x, y > 0$) such that $6x-1$ is a Sophie Germain prime and $\{6y-1, 6y+1\}$ is a twin prime pair.
-/
def A227923 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun x =>
    let y : ℕ := n - x
    -- The condition for the sum. The term (12 * x - 1).Prime checks if 2 * (6 * x - 1) + 1 is prime,
    -- which is the definition of a Sophie Germain prime when 6x-1 is prime.
    if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0

/--
The set of all Sophie Germain primes. A prime $p$ is a Sophie Germain prime if $p \ge 2$ and $2p+1$ is also prime.
-/
def SophieGermainPrimes : Set ℕ :=
  {p : ℕ | p.Prime ∧ (2 * p + 1).Prime}

/--
The set of all twin primes. A prime $p$ is a twin prime if $p+2$ is also prime.
We choose the smaller prime in the pair to represent the set.
-/
def TwinPrimes : Set ℕ :=
  {p : ℕ | p.Prime ∧ (p + 2).Prime}

lemma exists_of_A227923_pos {n : ℕ} (h : A227923 n > 0) :
  ∃ x ∈ Ico 1 n, (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime := by
  unfold A227923 at h
  have h_ne : (Ico 1 n).sum (fun x => if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime then 1 else 0) ≠ 0 := Nat.ne_of_gt h
  obtain ⟨x, hx, h_cond⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_ne
  use x, hx
  by_contra hc
  have h_if : (if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime then 1 else 0) = 0 := by
    split
    · rename_i hc2
      exact False.elim (hc hc2)
    · rfl
  exact h_cond h_if

lemma dvd_of_add_dvd_left {k a b : ℕ} (h1 : k ∣ a + b) (h2 : k ∣ b) : k ∣ a := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  use u - v
  have : a = k * u - k * v := by omega
  rw [this, Nat.mul_sub_left_distrib]

lemma dvd_of_add_dvd_right {k a b : ℕ} (h1 : k ∣ a + b) (h2 : k ∣ a) : k ∣ b := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  use u - v
  have : b = k * u - k * v := by omega
  rw [this, Nat.mul_sub_left_distrib]

lemma factorial_gt_two_mul_self {N : ℕ} (hN : N ≥ 5) : (N + 1).factorial > 2 * N := by
  have h1 : N - 1 ≥ 4 := by omega
  have h2 : (N - 1).factorial ≥ 24 := by
    have h_le := Nat.factorial_le h1
    have h4 : Nat.factorial 4 = 24 := rfl
    omega
  have h_fact : (N + 1).factorial = (N + 1) * N * (N - 1).factorial := by
    have h_succ : (N + 1).factorial = (N + 1) * N.factorial := rfl
    have h_N : N.factorial = N * (N - 1).factorial := by
      have hN1 : N = (N - 1) + 1 := by omega
      nth_rw 1 [hN1]
      change ((N - 1) + 1) * (N - 1).factorial = N * (N - 1).factorial
      rw [← hN1]
    rw [h_succ, h_N]
    ring
  rw [h_fact]
  have h_prod : (N + 1) * N * (N - 1).factorial = N * ((N + 1) * (N - 1).factorial) := by ring
  rw [h_prod]
  have h_inner : (N + 1) * (N - 1).factorial > 2 := by nlinarith
  have hN_pos : N > 0 := by omega
  have h_comm : 2 * N = N * 2 := by ring
  rw [h_comm]
  exact Nat.mul_lt_mul_of_pos_left h_inner hN_pos


/--
oeis_227923_conjecture_1: Part (i) of the conjecture implies that there are
infinitely many Sophie Germain primes, and also infinitely many twin prime pairs.
For example, if all twin primes does not exceed an integer N > 2, and (N+1)!/6 = x + y
with 6*x-1 a Sophie Germain prime and {6*y-1, 6*y+1} a twin prime pair, then
(N+1)! = (6*x-1) + (6*y+1) with 1 < 6*y+1 < N+1, hence we get a contradiction since
(N+1)! - k is composite for every k = 2..N.
-/
theorem oeis_227923_conjecture_1 :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) := by
  intro h_pos
  constructor
  · intro h_fin
    obtain ⟨M, hM⟩ := h_fin.exists_le
    let N := max 5 M
    have hN5 : N ≥ 5 := le_max_left 5 M
    have hNM : N ≥ M := le_max_right 5 M
    have h_dvd : 6 ∣ (N + 1).factorial := by
      have hN_ge : 6 ≤ N + 1 := by omega
      exact Nat.dvd_factorial (by omega) hN_ge
    let n := (N + 1).factorial / 6
    have hn_eq : 6 * n = (N + 1).factorial := Nat.mul_div_cancel' h_dvd
    have hn1 : 1 < n := by
      have h_fact : (N + 1).factorial > 2 * N := factorial_gt_two_mul_self hN5
      omega
    obtain ⟨x, hx, h_sg, h_sg_2, h_tw_1, h_tw_2⟩ := exists_of_A227923_pos (h_pos n hn1)
    rw [Finset.mem_Ico] at hx
    have h_eq_sg : 2 * (6 * x - 1) + 1 = 12 * x - 1 := by omega
    have h_in_sg : (6 * x - 1) ∈ SophieGermainPrimes := by
      simp [SophieGermainPrimes]
      refine ⟨h_sg, ?_⟩
      rw [h_eq_sg]
      exact h_sg_2
    have h_le_M : 6 * x - 1 ≤ M := hM (6 * x - 1) h_in_sg
    have h_le_N : 6 * x - 1 ≤ N := by omega
    have h_dvd_k : (6 * x - 1) ∣ (N + 1).factorial := by
      have h1 : 0 < 6 * x - 1 := by omega
      have h2 : 6 * x - 1 ≤ N + 1 := by omega
      exact Nat.dvd_factorial h1 h2
    have h_sum : (N + 1).factorial = (6 * x - 1) + (6 * (n - x) + 1) := by omega
    have h_k_dvd_S : (6 * x - 1) ∣ (6 * (n - x) + 1) := by
      have h_sum_dvd : (6 * x - 1) ∣ (6 * x - 1) + (6 * (n - x) + 1) := by
        rw [← h_sum]
        exact h_dvd_k
      exact dvd_of_add_dvd_right h_sum_dvd (dvd_refl _)
    have h_or := h_tw_2.eq_one_or_self_of_dvd (6 * x - 1) h_k_dvd_S
    have h_eq : 6 * x - 1 = 6 * (n - x) + 1 := by
      cases h_or with
      | inl h1 => omega
      | inr h2 => exact h2
    have h_contra : (N + 1).factorial ≤ 2 * N := by omega
    have h_gt : (N + 1).factorial > 2 * N := factorial_gt_two_mul_self hN5
    omega
  · intro h_fin
    obtain ⟨M, hM⟩ := h_fin.exists_le
    let N := max 5 (M + 2)
    have hN5 : N ≥ 5 := le_max_left 5 (M + 2)
    have hNM : N ≥ M + 2 := le_max_right 5 (M + 2)
    have h_dvd : 6 ∣ (N + 1).factorial := by
      have hN_ge : 6 ≤ N + 1 := by omega
      exact Nat.dvd_factorial (by omega) hN_ge
    let n := (N + 1).factorial / 6
    have hn_eq : 6 * n = (N + 1).factorial := Nat.mul_div_cancel' h_dvd
    have hn1 : 1 < n := by
      have h_fact : (N + 1).factorial > 2 * N := factorial_gt_two_mul_self hN5
      omega
    obtain ⟨x, hx, h_sg, h_sg_2, h_tw_1, h_tw_2⟩ := exists_of_A227923_pos (h_pos n hn1)
    rw [Finset.mem_Ico] at hx
    have h_eq_tw : (6 * (n - x) - 1) + 2 = 6 * (n - x) + 1 := by omega
    have h_in_tw : (6 * (n - x) - 1) ∈ TwinPrimes := by
      simp [TwinPrimes]
      refine ⟨h_tw_1, ?_⟩
      rw [h_eq_tw]
      exact h_tw_2
    have h_le_M : 6 * (n - x) - 1 ≤ M := hM (6 * (n - x) - 1) h_in_tw
    have h_le_N_plus_1 : 6 * (n - x) + 1 ≤ N := by omega
    have h_dvd_k : (6 * (n - x) + 1) ∣ (N + 1).factorial := by
      have h1 : 0 < 6 * (n - x) + 1 := by omega
      have h2 : 6 * (n - x) + 1 ≤ N + 1 := by omega
      exact Nat.dvd_factorial h1 h2
    have h_sum : (N + 1).factorial = (6 * x - 1) + (6 * (n - x) + 1) := by omega
    have h_k_dvd_S : (6 * (n - x) + 1) ∣ (6 * x - 1) := by
      have h_sum_dvd : (6 * (n - x) + 1) ∣ (6 * x - 1) + (6 * (n - x) + 1) := by
        rw [← h_sum]
        exact h_dvd_k
      exact dvd_of_add_dvd_left h_sum_dvd (dvd_refl _)
    have h_or := h_sg.eq_one_or_self_of_dvd (6 * (n - x) + 1) h_k_dvd_S
    have h_eq : 6 * (n - x) + 1 = 6 * x - 1 := by
      cases h_or with
      | inl h1 => omega
      | inr h2 => exact h2
    have h_contra : (N + 1).factorial ≤ 2 * N := by omega
    have h_gt : (N + 1).factorial > 2 * N := factorial_gt_two_mul_self hN5
    omega
















