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

/-- Extract a witness `x` of the sum decomposition from `A227923 n > 0`. -/
theorem A227923_extract (n : ℕ) (h : A227923 n > 0) :
    ∃ x, x ∈ Ico 1 n ∧ (6*x-1).Prime ∧ (12*x-1).Prime ∧
      (6*(n-x)-1).Prime ∧ (6*(n-x)+1).Prime := by
  have h' : A227923 n ≠ 0 := h.ne'
  simp only [A227923] at h'
  obtain ⟨x, hx, hfx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
  refine ⟨x, hx, ?_⟩
  split_ifs at hfx with hc
  · exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  · exact absurd rfl hfx

/-- The core construction: for any `N`, the hypothesis applied to `n = (6(N+1)+1)!/6`
produces a decomposition `n = x + (n-x)` satisfying the four primality conditions,
together with the key identity `6 * n = (6(N+1)+1)!`. -/
theorem A227923_core (h : ∀ n, 1 < n → A227923 n > 0) (N : ℕ) :
    ∃ x n, 1 ≤ x ∧ x < n ∧ 6 * n = (6*(N+1)+1)! ∧
      (6*x-1).Prime ∧ (12*x-1).Prime ∧ (6*(n-x)-1).Prime ∧ (6*(n-x)+1).Prime := by
  set M := 6 * (N + 1) with hM
  set n := (M+1)! / 6 with hn
  have hdvd6 : (6:ℕ) ∣ (M+1)! := by
    have : (3:ℕ)! ∣ (M+1)! := Nat.factorial_dvd_factorial (by omega)
    simpa using this
  have hfact : 6 * n = (M+1)! := by
    rw [hn, Nat.mul_div_cancel' hdvd6]
  have hbig : 5040 ≤ (M+1)! := by
    have : (7:ℕ)! ≤ (M+1)! := Nat.factorial_le (by omega)
    simpa using this
  have hn1 : 1 < n := by omega
  obtain ⟨x, hx, p1, p2, p3, p4⟩ := A227923_extract n (h n hn1)
  rw [Finset.mem_Ico] at hx
  exact ⟨x, n, hx.1, hx.2, hfact, p1, p2, p3, p4⟩

/-- Under the hypothesis, the set of twin primes is infinite. -/
theorem A227923_twin_infinite (h : ∀ n, 1 < n → A227923 n > 0) :
    Set.Infinite TwinPrimes := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  obtain ⟨x, n, hx1, hxn, hfact, p1, p2, p3, p4⟩ := A227923_core h b
  set M := 6 * (b + 1) with hM
  have hy1 : 1 ≤ n - x := by omega
  have hgt : M < 6 * (n - x) - 1 := by
    by_contra hcon
    push_neg at hcon
    have hMmod : M % 6 = 0 := by omega
    have hle : 6 * (n - x) + 1 ≤ M + 1 := by omega
    have hdvdF : (6 * (n - x) + 1) ∣ (M+1)! := Nat.dvd_factorial (by omega) hle
    have heq : 6 * x - 1 = (M+1)! - (6 * (n - x) + 1) := by
      have : x + (n - x) = n := by omega
      omega
    have hdvd2 : (6 * (n - x) + 1) ∣ (6 * x - 1) := by
      rw [heq]; exact Nat.dvd_sub hdvdF dvd_rfl
    rcases p1.eq_one_or_self_of_dvd _ hdvd2 with h1 | h2
    · omega
    · omega
  have hmem : (6 * (n - x) - 1) ∈ TwinPrimes := by
    refine ⟨p3, ?_⟩
    have he : 6 * (n - x) - 1 + 2 = 6 * (n - x) + 1 := by omega
    rw [he]; exact p4
  have := hb hmem
  omega

/-- Under the hypothesis, the set of Sophie Germain primes is infinite. -/
theorem A227923_sg_infinite (h : ∀ n, 1 < n → A227923 n > 0) :
    Set.Infinite SophieGermainPrimes := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  obtain ⟨x, n, hx1, hxn, hfact, p1, p2, p3, p4⟩ := A227923_core h b
  set M := 6 * (b + 1) with hM
  have hgt : M < 6 * x - 1 := by
    by_contra hcon
    push_neg at hcon
    have hle : 6 * x - 1 ≤ M + 1 := by omega
    have hdvdF : (6 * x - 1) ∣ (M+1)! := Nat.dvd_factorial (by omega) hle
    have heq : 6 * (n - x) + 1 = (M+1)! - (6 * x - 1) := by
      have : x + (n - x) = n := by omega
      omega
    have hdvd2 : (6 * x - 1) ∣ (6 * (n - x) + 1) := by
      rw [heq]; exact Nat.dvd_sub hdvdF dvd_rfl
    rcases p4.eq_one_or_self_of_dvd _ hdvd2 with h1 | h2
    · omega
    · omega
  have hmem : (6 * x - 1) ∈ SophieGermainPrimes := by
    refine ⟨p1, ?_⟩
    have he : 2 * (6 * x - 1) + 1 = 12 * x - 1 := by omega
    rw [he]; exact p2
  have := hb hmem
  omega

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
fun h => ⟨A227923_sg_infinite h, A227923_twin_infinite h⟩
