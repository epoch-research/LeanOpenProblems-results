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

/--
oeis_227923_conjecture_1: Part (i) of the conjecture implies that there are
infinitely many Sophie Germain primes, and also infinitely many twin prime pairs.
For example, if all twin primes does not exceed an integer N > 2, and (N+1)!/6 = x + y
with 6*x-1 a Sophie Germain prime and {6*y-1, 6*y+1} a twin prime pair, then
(N+1)! = (6*x-1) + (6*y+1) with 1 < 6*y+1 < N+1, hence we get a contradiction since
(N+1)! - k is composite for every k = 2..N.
-/
lemma factorial_div_six_gt_one {N' : ℕ} (hN' : 5 ≤ N') : 1 < (N' + 1).factorial / 6 := by
  have h_le : 6 ≤ N' + 1 := by omega
  have h_fac : Nat.factorial 6 ≤ Nat.factorial (N' + 1) := Nat.factorial_le h_le
  have h_div : 720 / 6 ≤ (N' + 1).factorial / 6 := Nat.div_le_div_right h_fac
  have h_eval : 720 / 6 = 120 := by rfl
  omega

theorem oeis_227923_conjecture_1 :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) := by
  intro H
  constructor
  · rw [Set.infinite_iff_exists_gt]
    intro N
    let N' := max 5 N
    let n := (N' + 1).factorial / 6
    have hN' : 5 ≤ N' := le_max_left 5 N
    have hn_gt : 1 < n := factorial_div_six_gt_one hN'
    have h_pos : 0 < A227923 n := H n hn_gt
    have h_exists : ∃ x ∈ Ico 1 n, 0 < if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime then (1:ℕ) else 0 := by
      rwa [A227923, sum_pos_iff_of_nonneg] at h_pos
      intro a ha
      exact Nat.zero_le _
    rcases h_exists with ⟨x, hx_mem, hx_cond⟩
    have hx_all : (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime := by
      revert hx_cond
      split_ifs with h_if
      · intro _; exact h_if
      · intro h; contradiction
    rcases hx_all with ⟨hx1, hx2, hy1, hy2⟩
    have hx_ge : 1 ≤ x := (mem_Ico.mp hx_mem).1
    have hb_sg : 2 * (6 * x - 1) + 1 = 12 * x - 1 := by omega
    have hb_mem : (6 * x - 1) ∈ SophieGermainPrimes := by
      simp [SophieGermainPrimes]
      rw [hb_sg]
      exact ⟨hx1, hx2⟩
    have hx_lt_n : x < n := (mem_Ico.mp hx_mem).2
    have h_sum_eq : 6 * (n - x) + 1 + (6 * x - 1) = (N' + 1).factorial := by
      have h_dvd_6 : 6 ∣ (N' + 1).factorial := by
        apply Nat.dvd_factorial (by decide)
        omega
      have h_mul_div : 6 * n = (N' + 1).factorial := Nat.mul_div_cancel' h_dvd_6
      omega
    by_contra h_lt
    push_neg at h_lt
    have h_le_N : 6 * x - 1 ≤ N := h_lt (6 * x - 1) hb_mem
    have hN_le_N' : N ≤ N' := le_max_right 5 N
    have h_le_N' : 6 * x - 1 ≤ N' := le_trans h_le_N hN_le_N'
    have hk_dvd_fac : (6 * x - 1) ∣ (N' + 1).factorial := by
      apply Nat.dvd_factorial
      · omega
      · exact le_trans h_le_N' (Nat.le_succ N')
    have hk_dvd_other : (6 * x - 1) ∣ (6 * (n - x) + 1) := by
      have h_dvd_add : (6 * x - 1) ∣ 6 * (n - x) + 1 + (6 * x - 1) := by
        rw [h_sum_eq]
        exact hk_dvd_fac
      rwa [Nat.dvd_add_self_right] at h_dvd_add
    have h_or := hy2.eq_one_or_self_of_dvd (6 * x - 1) hk_dvd_other
    rcases h_or with h1 | h2
    · omega
    · omega
  · rw [Set.infinite_iff_exists_gt]
    intro N
    let N' := max 5 (N + 2)
    let n := (N' + 1).factorial / 6
    have hN' : 5 ≤ N' := le_max_left 5 (N + 2)
    have hn_gt : 1 < n := factorial_div_six_gt_one hN'
    have h_pos : 0 < A227923 n := H n hn_gt
    have h_exists : ∃ x ∈ Ico 1 n, 0 < if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime then (1:ℕ) else 0 := by
      rwa [A227923, sum_pos_iff_of_nonneg] at h_pos
      intro a ha
      exact Nat.zero_le _
    rcases h_exists with ⟨x, hx_mem, hx_cond⟩
    have hx_all : (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime := by
      revert hx_cond
      split_ifs with h_if
      · intro _; exact h_if
      · intro h; contradiction
    rcases hx_all with ⟨hx1, hx2, hy1, hy2⟩
    have hx_ge : 1 ≤ x := (mem_Ico.mp hx_mem).1
    have hx_lt_n : x < n := (mem_Ico.mp hx_mem).2
    have hb_mem : (6 * (n - x) - 1) ∈ TwinPrimes := by
      simp [TwinPrimes]
      have h_add : (6 * (n - x) - 1) + 2 = 6 * (n - x) + 1 := by omega
      rw [h_add]
      exact ⟨hy1, hy2⟩
    have h_sum_eq : 6 * (n - x) + 1 + (6 * x - 1) = (N' + 1).factorial := by
      have h_dvd_6 : 6 ∣ (N' + 1).factorial := by
        apply Nat.dvd_factorial (by decide)
        omega
      have h_mul_div : 6 * n = (N' + 1).factorial := Nat.mul_div_cancel' h_dvd_6
      omega
    by_contra h_lt
    push_neg at h_lt
    have h_le_N : 6 * (n - x) - 1 ≤ N := h_lt (6 * (n - x) - 1) hb_mem
    have hN_le_N' : N + 2 ≤ N' := le_max_right 5 (N + 2)
    have h_le_N' : 6 * (n - x) + 1 ≤ N' := by omega
    have hk_dvd_fac : (6 * (n - x) + 1) ∣ (N' + 1).factorial := by
      apply Nat.dvd_factorial
      · omega
      · exact le_trans h_le_N' (Nat.le_succ N')
    have hk_dvd_other : (6 * (n - x) + 1) ∣ (6 * x - 1) := by
      have h_dvd_add : (6 * (n - x) + 1) ∣ 6 * (n - x) + 1 + (6 * x - 1) := by
        rw [h_sum_eq]
        exact hk_dvd_fac
      rwa [Nat.dvd_add_self_left] at h_dvd_add
    have h_or := hx1.eq_one_or_self_of_dvd (6 * (n - x) + 1) hk_dvd_other
    rcases h_or with h1 | h2
    · omega
    · omega
