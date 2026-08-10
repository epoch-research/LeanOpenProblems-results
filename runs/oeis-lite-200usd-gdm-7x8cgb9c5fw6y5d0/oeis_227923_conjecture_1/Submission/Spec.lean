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
theorem oeis_227923_conjecture_1 :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) :=
by
  intro H
  constructor
  · rw [Set.infinite_iff_exists_gt]
    intro N
    let M := max 3 (N + 2)
    have hM1 : 4 ≤ M + 1 := by
      have : 3 ≤ M := le_max_left 3 (N + 2)
      omega
    have h_6_dvd : 6 ∣ (M + 1).factorial := by
      have hd1 : 6 ∣ Nat.factorial 4 := by decide
      have hd2 : Nat.factorial 4 ∣ Nat.factorial (M + 1) := Nat.factorial_dvd_factorial hM1
      exact Nat.dvd_trans hd1 hd2
    let n := (M + 1).factorial / 6
    have hn_eq : 6 * n = (M + 1).factorial := Nat.mul_div_cancel' h_6_dvd
    have hn1 : 1 < n := by
      change 1 < (M + 1).factorial / 6
      have h_f_le : 24 ≤ (M + 1).factorial := Nat.factorial_le hM1
      omega
    have hA := H n hn1
    have h_exists : ∃ x ∈ Ico 1 n, (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime := by
      have hne : A227923 n ≠ 0 := _root_.ne_of_gt hA
      unfold A227923 at hne
      by_contra hc
      have hzero : (Ico 1 n).sum (fun x =>
        let y : ℕ := n - x
        if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0) = 0 := by
        apply sum_eq_zero
        intro x hx
        dsimp
        split_ifs with h_cond
        · exfalso
          apply hc
          exact ⟨x, hx, h_cond⟩
        · rfl
      exact hne hzero
    rcases h_exists with ⟨x, hx, h_cond⟩
    have hx1 : 1 ≤ x := (mem_Ico.mp hx).1
    have hxn : x < n := (mem_Ico.mp hx).2
    let p := 6 * x - 1
    have hp_prime : p.Prime := h_cond.1
    have hp_sg : p ∈ SophieGermainPrimes := by
      refine ⟨hp_prime, ?_⟩
      have h_eq : 2 * p + 1 = 12 * x - 1 := by omega
      rw [h_eq]
      exact h_cond.2.1
    use p
    refine ⟨hp_sg, ?_⟩
    by_contra hp_le
    push_neg at hp_le
    -- hp_le : p ≤ N
    have hp_le_M1 : p ≤ M + 1 := by
      have : N + 2 ≤ M := le_max_right 3 (N + 2)
      omega
    have hp_pos : 0 < p := hp_prime.pos
    have hp_dvd_f : p ∣ (M + 1).factorial := Nat.dvd_factorial hp_pos hp_le_M1
    have hp_dvd_6n : p ∣ 6 * n := by
      rw [hn_eq]
      exact hp_dvd_f
    have h_sub : 6 * (n - x) + 1 = 6 * n - p := by omega
    have hp_dvd_y : p ∣ 6 * (n - x) + 1 := by
      rw [h_sub]
      exact Nat.dvd_sub hp_dvd_6n (Nat.dvd_refl p)
    have h_prime_y : (6 * (n - x) + 1).Prime := h_cond.2.2.2
    have h_cases : p = 1 ∨ p = 6 * (n - x) + 1 := h_prime_y.eq_one_or_self_of_dvd p hp_dvd_y
    rcases h_cases with h1 | h2
    · have : p > 1 := hp_prime.one_lt
      omega
    · omega
  · rw [Set.infinite_iff_exists_gt]
    intro N
    let M := max 3 (N + 2)
    have hM1 : 4 ≤ M + 1 := by
      have : 3 ≤ M := le_max_left 3 (N + 2)
      omega
    have h_6_dvd : 6 ∣ (M + 1).factorial := by
      have hd1 : 6 ∣ Nat.factorial 4 := by decide
      have hd2 : Nat.factorial 4 ∣ Nat.factorial (M + 1) := Nat.factorial_dvd_factorial hM1
      exact Nat.dvd_trans hd1 hd2
    let n := (M + 1).factorial / 6
    have hn_eq : 6 * n = (M + 1).factorial := Nat.mul_div_cancel' h_6_dvd
    have hn1 : 1 < n := by
      change 1 < (M + 1).factorial / 6
      have h_f_le : 24 ≤ (M + 1).factorial := Nat.factorial_le hM1
      omega
    have hA := H n hn1
    have h_exists : ∃ x ∈ Ico 1 n, (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime := by
      have hne : A227923 n ≠ 0 := _root_.ne_of_gt hA
      unfold A227923 at hne
      by_contra hc
      have hzero : (Ico 1 n).sum (fun x =>
        let y : ℕ := n - x
        if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0) = 0 := by
        apply sum_eq_zero
        intro x hx
        dsimp
        split_ifs with h_cond
        · exfalso
          apply hc
          exact ⟨x, hx, h_cond⟩
        · rfl
      exact hne hzero
    rcases h_exists with ⟨x, hx, h_cond⟩
    have hx1 : 1 ≤ x := (mem_Ico.mp hx).1
    have hxn : x < n := (mem_Ico.mp hx).2
    let q := 6 * (n - x) - 1
    have hq_prime : q.Prime := h_cond.2.2.1
    have hq_tp : q ∈ TwinPrimes := by
      refine ⟨hq_prime, ?_⟩
      have h_eq : q + 2 = 6 * (n - x) + 1 := by omega
      rw [h_eq]
      exact h_cond.2.2.2
    use q
    refine ⟨hq_tp, ?_⟩
    by_contra hq_le
    push_neg at hq_le
    -- hq_le : q ≤ N
    let p := 6 * (n - x) + 1
    have hp_prime : p.Prime := h_cond.2.2.2
    have hp_le_M1 : p ≤ M + 1 := by
      have : N + 2 ≤ M := le_max_right 3 (N + 2)
      omega
    have hp_pos : 0 < p := hp_prime.pos
    have hp_dvd_f : p ∣ (M + 1).factorial := Nat.dvd_factorial hp_pos hp_le_M1
    have hp_dvd_6n : p ∣ 6 * n := by
      rw [hn_eq]
      exact hp_dvd_f
    have h_sub : 6 * x - 1 = 6 * n - p := by omega
    have hp_dvd_x : p ∣ 6 * x - 1 := by
      rw [h_sub]
      exact Nat.dvd_sub hp_dvd_6n (Nat.dvd_refl p)
    have h_prime_x : (6 * x - 1).Prime := h_cond.1
    have h_cases : p = 1 ∨ p = 6 * x - 1 := h_prime_x.eq_one_or_self_of_dvd p hp_dvd_x
    rcases h_cases with h1 | h2
    · have : p > 1 := hp_prime.one_lt
      omega
    · omega










