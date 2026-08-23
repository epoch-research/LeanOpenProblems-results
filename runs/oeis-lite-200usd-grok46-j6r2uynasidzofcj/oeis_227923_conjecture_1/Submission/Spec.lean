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

/-- If `A227923 n` is positive then there is a valid splitting `n = x + y`. -/
lemma exists_of_A227923_pos {n : ℕ} (h : 0 < A227923 n) :
    ∃ x ∈ Ico 1 n,
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
        (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime := by
  have hcard :
      0 < #{x ∈ Ico 1 n |
          (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
            (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime} := by
    rwa [card_filter]
  obtain ⟨x, hx⟩ := (card_pos.mp hcard).exists_mem
  exact ⟨x, mem_filter.mp hx⟩

/-- For `m ≥ 4` one has `2 * m < m.factorial`. -/
lemma two_mul_lt_factorial {m : ℕ} (hm : 4 ≤ m) : 2 * m < m.factorial := by
  have hm0 : m ≠ 0 := by omega
  rw [← mul_factorial_pred hm0]
  have hfac : 6 ≤ (m - 1).factorial := by
    have : (3).factorial ≤ (m - 1).factorial := factorial_le (by omega)
    exact le_trans (by decide) this
  have : 2 < (m - 1).factorial := lt_of_lt_of_le (by decide) hfac
  rw [mul_comm 2 m]
  exact (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hm0)).mpr this

/-- If `4 ≤ m` and `2 ≤ k ≤ m`, then `m.factorial - k` is not prime. -/
lemma not_prime_factorial_sub {m k : ℕ} (hm : 4 ≤ m) (hk : 2 ≤ k) (hkm : k ≤ m) :
    ¬ (m.factorial - k).Prime := by
  have hkpos : 0 < k := by omega
  have hkdvd : k ∣ m.factorial := dvd_factorial hkpos hkm
  have hk_lt : k < m.factorial - k := by
    have : 2 * k < m.factorial :=
      calc
        2 * k ≤ 2 * m := Nat.mul_le_mul_left _ hkm
        _ < m.factorial := two_mul_lt_factorial hm
    omega
  have hkdvd' : k ∣ m.factorial - k := by
    rw [Nat.dvd_sub_self_right]
    exact Or.inl hkdvd
  exact not_prime_of_dvd_of_lt hkdvd' hk hk_lt

/-- `6 * n` decomposes as `(6x - 1) + (6(n - x) + 1)` for `x ∈ Ico 1 n`. -/
lemma six_mul_decomposition {n x : ℕ} (hx : x ∈ Ico 1 n) :
    6 * n = (6 * x - 1) + (6 * (n - x) + 1) := by
  have := mem_Ico.mp hx
  omega

/-- Relates the two presentations of the Sophie Germain companion. -/
lemma two_mul_six_x_sub_one {x : ℕ} (hx : 0 < x) :
    2 * (6 * x - 1) + 1 = 12 * x - 1 := by omega

/-- Relates the two presentations of the twin-prime companion. -/
lemma six_y_sub_one_add_two {y : ℕ} (hy : 0 < y) :
    (6 * y - 1) + 2 = 6 * y + 1 := by omega

/-- A convenient large multiple of `6` built from an upper bound `N ≥ 4`. -/
lemma one_lt_factorial_div_six {N : ℕ} (hN : 4 ≤ N) : 1 < (N + 2).factorial / 6 := by
  have hle : (6).factorial ≤ (N + 2).factorial := factorial_le (by omega)
  have h720 : 720 ≤ (N + 2).factorial := le_trans (by decide) hle
  exact lt_of_lt_of_le (by decide : 1 < 720 / 6) (Nat.div_le_div_right h720)

lemma six_dvd_factorial_add_two {N : ℕ} (hN : 4 ≤ N) : 6 ∣ (N + 2).factorial :=
  dvd_factorial (by decide) (by omega)

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
  intro h
  constructor
  · -- Infinitely many Sophie Germain primes.
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨N, hN4, hN⟩ := hfin.bddAbove.exists_ge 4
    set n := (N + 2).factorial / 6 with hn_def
    have hn : 1 < n := one_lt_factorial_div_six hN4
    have hpos : 0 < A227923 n := h n hn
    obtain ⟨x, hx, hx_pr, hx12, -, hy1⟩ := exists_of_A227923_pos hpos
    have hx0 : 0 < x := by
      have := mem_Ico.mp hx
      omega
    have hsg : 6 * x - 1 ∈ SophieGermainPrimes := by
      refine ⟨hx_pr, ?_⟩
      rwa [two_mul_six_x_sub_one hx0]
    have hle : 6 * x - 1 ≤ N := hN _ hsg
    have h6n : 6 * n = (N + 2).factorial := Nat.mul_div_cancel' (six_dvd_factorial_add_two hN4)
    have hde : 6 * n = (6 * x - 1) + (6 * (n - x) + 1) := six_mul_decomposition hx
    have hy1_eq : 6 * (n - x) + 1 = (N + 2).factorial - (6 * x - 1) := by
      have hsum := hde.symm.trans h6n
      have : 6 * x - 1 ≤ (N + 2).factorial := by
        have : 6 * x - 1 ≤ N := hle
        have : N ≤ N + 2 := by omega
        have : N + 2 ≤ (N + 2).factorial := self_le_factorial _
        omega
      omega
    have hnot : ¬ (6 * (n - x) + 1).Prime := by
      rw [hy1_eq]
      refine not_prime_factorial_sub (m := N + 2) (k := 6 * x - 1) ?_ ?_ ?_
      · omega
      · exact hx_pr.two_le
      · omega
    exact hnot hy1
  · -- Infinitely many twin primes.
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨N, hN4, hN⟩ := hfin.bddAbove.exists_ge 4
    set n := (N + 2).factorial / 6 with hn_def
    have hn : 1 < n := one_lt_factorial_div_six hN4
    have hpos : 0 < A227923 n := h n hn
    obtain ⟨x, hx, hx_pr, -, hy_pr, hy1⟩ := exists_of_A227923_pos hpos
    have hy0 : 0 < n - x := by
      have := mem_Ico.mp hx
      omega
    have htw : 6 * (n - x) - 1 ∈ TwinPrimes := by
      refine ⟨hy_pr, ?_⟩
      rwa [six_y_sub_one_add_two hy0]
    have hle : 6 * (n - x) - 1 ≤ N := hN _ htw
    have h6n : 6 * n = (N + 2).factorial := Nat.mul_div_cancel' (six_dvd_factorial_add_two hN4)
    have hde : 6 * n = (6 * x - 1) + (6 * (n - x) + 1) := six_mul_decomposition hx
    have hx1_eq : 6 * x - 1 = (N + 2).factorial - (6 * (n - x) + 1) := by
      have hsum := hde.symm.trans h6n
      have : 6 * (n - x) + 1 ≤ (N + 2).factorial := by
        have : 6 * (n - x) - 1 ≤ N := hle
        have : 6 * (n - x) + 1 ≤ N + 2 := by omega
        have : N + 2 ≤ (N + 2).factorial := self_le_factorial _
        omega
      omega
    have hnot : ¬ (6 * x - 1).Prime := by
      rw [hx1_eq]
      refine not_prime_factorial_sub (m := N + 2) (k := 6 * (n - x) + 1) ?_ ?_ ?_
      · omega
      · omega
      · have : 6 * (n - x) - 1 ≤ N := hle
        omega
    exact hnot hx_pr
