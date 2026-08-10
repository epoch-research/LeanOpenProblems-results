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
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) := by
  intro h
  -- Extract a witness decomposition from the positivity of the counting function.
  have key : ∀ n : ℕ, 1 < n → ∃ x y : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
    intro n hn
    have hpos := h n hn
    unfold A227923 at hpos
    obtain ⟨x, hxmem, hfx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    rw [Finset.mem_Ico] at hxmem
    dsimp only at hfx
    by_cases hc : (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
        (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime
    · obtain ⟨h1, h2, h3, h4⟩ := hc
      exact ⟨x, n - x, hxmem.1, by omega, by omega, h1, h2, h3, h4⟩
    · rw [if_neg hc] at hfx
      exact absurd rfl hfx
  -- For every N, get a decomposition of (N+4)! as (6x-1) + (6y+1) with all primality
  -- conditions.
  have main : ∀ N : ℕ, ∃ x y : ℕ, 1 ≤ x ∧ 1 ≤ y ∧
      (6 * x - 1) + (6 * y + 1) = (N + 4)! ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
    intro N
    have h6 : 6 ∣ (N + 4)! := by
      have h4 : (4 : ℕ)! ∣ (N + 4)! := Nat.factorial_dvd_factorial (by omega)
      exact dvd_trans (by norm_num [Nat.factorial]) h4
    obtain ⟨n, hn⟩ := h6
    have h24 : 24 ≤ (N + 4)! := by
      calc (24 : ℕ) = (4 : ℕ)! := by norm_num [Nat.factorial]
      _ ≤ (N + 4)! := Nat.factorial_le (by omega)
    have hn1 : 1 < n := by omega
    obtain ⟨x, y, hx, hy, hxy, hp1, hp2, hp3, hp4⟩ := key n hn1
    exact ⟨x, y, hx, hy, by omega, hp1, hp2, hp3, hp4⟩
  constructor
  · -- Infinitely many Sophie Germain primes.
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    obtain ⟨x, y, hx, hy, heq, hp1, hp2, hp3, hp4⟩ := main N
    have hmem : (6 * x - 1) ∈ SophieGermainPrimes := by
      refine ⟨hp1, ?_⟩
      have h12 : 2 * (6 * x - 1) + 1 = 12 * x - 1 := by omega
      rw [h12]; exact hp2
    have hle : 6 * x - 1 ≤ N := hN hmem
    have hdvd : (6 * x - 1) ∣ (N + 4)! := Nat.dvd_factorial (by omega) (by omega)
    rw [← heq] at hdvd
    have hdvd2 : (6 * x - 1) ∣ (6 * y + 1) := (Nat.dvd_add_right dvd_rfl).mp hdvd
    rcases hp4.eq_one_or_self_of_dvd _ hdvd2 with h1 | h2 <;> omega
  · -- Infinitely many twin primes.
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    obtain ⟨x, y, hx, hy, heq, hp1, hp2, hp3, hp4⟩ := main N
    have hmem : (6 * y - 1) ∈ TwinPrimes := by
      refine ⟨hp3, ?_⟩
      have h2 : 6 * y - 1 + 2 = 6 * y + 1 := by omega
      rw [h2]; exact hp4
    have hle : 6 * y - 1 ≤ N := hN hmem
    have hdvd : (6 * y + 1) ∣ (N + 4)! := Nat.dvd_factorial (by omega) (by omega)
    rw [← heq] at hdvd
    have hdvd2 : (6 * y + 1) ∣ (6 * x - 1) := by
      have hsub := Nat.dvd_sub hdvd (dvd_rfl (a := 6 * y + 1))
      simpa using hsub
    rcases hp1.eq_one_or_self_of_dvd _ hdvd2 with h1 | h2 <;> omega
