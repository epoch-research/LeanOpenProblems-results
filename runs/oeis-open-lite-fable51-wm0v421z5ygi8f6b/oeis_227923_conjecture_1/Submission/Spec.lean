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

lemma A227923_pos_exists (n : ℕ) (h : A227923 n > 0) :
    ∃ x y : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ x + y = n ∧ (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
      (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
  unfold A227923 at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp h)
  simp only [Finset.mem_Ico] at hx
  refine ⟨x, n - x, hx.1, by omega, by omega, ?_⟩
  by_contra hc
  apply hne
  simp only
  rw [if_neg hc]

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
  · apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    have hn : 1 < (N + 2)! := by
      have := Nat.factorial_le (show 2 ≤ N + 2 by omega)
      simp [Nat.factorial] at this ⊢
      omega
    obtain ⟨x, y, hx, hy, hxy, h1, h2, h3, h4⟩ := A227923_pos_exists _ (h _ hn)
    have hmem : 6 * x - 1 ∈ SophieGermainPrimes := by
      refine ⟨h1, ?_⟩
      have : 2 * (6 * x - 1) + 1 = 12 * x - 1 := by omega
      rw [this]; exact h2
    have hle : 6 * x - 1 ≤ N := hN hmem
    have hdvd : (6 * x - 1) ∣ (N + 2)! := Nat.dvd_factorial (by omega) (by omega)
    have hdvd6 : (6 * x - 1) ∣ (6 * x - 1) + (6 * y + 1) := by
      have : (6 * x - 1) + (6 * y + 1) = 6 * (N + 2)! := by omega
      rw [this]; exact Dvd.dvd.mul_left hdvd 6
    have hdvd' : (6 * x - 1) ∣ (6 * y + 1) := (Nat.dvd_add_right (dvd_refl _)).mp hdvd6
    rcases (Nat.Prime.eq_one_or_self_of_dvd h4 _ hdvd') with h5 | h5 <;> omega
  · apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    have hn : 1 < (N + 2)! := by
      have := Nat.factorial_le (show 2 ≤ N + 2 by omega)
      simp [Nat.factorial] at this ⊢
      omega
    obtain ⟨x, y, hx, hy, hxy, h1, h2, h3, h4⟩ := A227923_pos_exists _ (h _ hn)
    have hmem : 6 * y - 1 ∈ TwinPrimes := by
      refine ⟨h3, ?_⟩
      have : (6 * y - 1) + 2 = 6 * y + 1 := by omega
      rw [this]; exact h4
    have hle : 6 * y - 1 ≤ N := hN hmem
    have hdvd : (6 * y + 1) ∣ (N + 2)! := Nat.dvd_factorial (by omega) (by omega)
    have hdvd6 : (6 * y + 1) ∣ (6 * x - 1) + (6 * y + 1) := by
      have : (6 * x - 1) + (6 * y + 1) = 6 * (N + 2)! := by omega
      rw [this]; exact Dvd.dvd.mul_left hdvd 6
    have hdvd' : (6 * y + 1) ∣ (6 * x - 1) := (Nat.dvd_add_left (dvd_refl _)).mp hdvd6
    rcases (Nat.Prime.eq_one_or_self_of_dvd h1 _ hdvd') with h5 | h5 <;> omega

theorem oeis_227923_conjecture_1.disproof : ¬ (type_of% @oeis_227923_conjecture_1) := sorry
