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
lemma extract (n : ℕ) (hpos : 0 < A227923 n) :
    ∃ x, x ∈ Ico 1 n ∧ (6*x-1).Prime ∧ (12*x-1).Prime ∧
      (6*(n-x)-1).Prime ∧ (6*(n-x)+1).Prime := by
  by_contra hc
  push_neg at hc
  rw [A227923] at hpos
  have hz : (Ico 1 n).sum (fun x =>
      let y : ℕ := n - x
      if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime
      then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only
    rw [if_neg]
    rintro ⟨h1, h2, h3, h4⟩
    exact hc x hx h1 h2 h3 h4
  omega

lemma core (h : ∀ n, 1 < n → A227923 n > 0) (N : ℕ) (hN : 3 ≤ N) :
    ∃ x y, 1 ≤ x ∧ 1 ≤ y ∧ (6*x-1).Prime ∧ (12*x-1).Prime ∧
      (6*y-1).Prime ∧ (6*y+1).Prime ∧ (6*x-1) + (6*y+1) = (N+2)! := by
  have hdvd6 : 6 ∣ (N+2)! := by
    have hd : (3)! ∣ (N+2)! := Nat.factorial_dvd_factorial (by omega)
    simpa using hd
  obtain ⟨n, hn⟩ := hdvd6
  have hFbig : (120:ℕ) ≤ (N+2)! := by
    calc (120:ℕ) = (5)! := by decide
    _ ≤ (N+2)! := Nat.factorial_le (by omega)
  have hn1 : 1 < n := by omega
  obtain ⟨x, hx, p1, p2, p3, p4⟩ := extract n (h n hn1)
  rw [Finset.mem_Ico] at hx
  refine ⟨x, n - x, by omega, by omega, p1, p2, p3, p4, by omega⟩

theorem oeis_227923_conjecture_1 :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) :=
by
  intro h
  constructor
  · -- Sophie Germain primes are infinite
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hNub⟩
    have h5 : (5 : ℕ) ∈ SophieGermainPrimes := ⟨by norm_num, by norm_num⟩
    have hN3 : 3 ≤ N := le_trans (by norm_num) (hNub h5)
    obtain ⟨x, y, hx1, hy1, p1, p2, p3, p4, heq⟩ := core h N hN3
    -- 6x-1 is a Sophie Germain prime
    have hmem : (6*x-1) ∈ SophieGermainPrimes := by
      refine ⟨p1, ?_⟩
      have : 2 * (6*x-1) + 1 = 12*x - 1 := by omega
      rw [this]; exact p2
    have hbnd : 6*x - 1 ≤ N := hNub hmem
    have hk : (6*x-1) ∣ (N+2)! := Nat.dvd_factorial (by omega) (by omega)
    have hdvd : (6*x-1) ∣ (6*y+1) := by
      have := Nat.dvd_sub hk (dvd_refl (6*x-1))
      have e : (N+2)! - (6*x-1) = 6*y+1 := by omega
      rwa [e] at this
    rcases (p4.eq_one_or_self_of_dvd (6*x-1) hdvd) with hh | hh <;> omega
  · -- Twin primes are infinite
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hNub⟩
    have h3 : (3 : ℕ) ∈ TwinPrimes := ⟨by norm_num, by norm_num⟩
    have hN3 : 3 ≤ N := hNub h3
    obtain ⟨x, y, hx1, hy1, p1, p2, p3, p4, heq⟩ := core h N hN3
    -- 6y-1 is a twin prime
    have hmem : (6*y-1) ∈ TwinPrimes := by
      refine ⟨p3, ?_⟩
      have : (6*y-1) + 2 = 6*y+1 := by omega
      rw [this]; exact p4
    have hbnd : 6*y - 1 ≤ N := hNub hmem
    have hk : (6*y+1) ∣ (N+2)! := Nat.dvd_factorial (by omega) (by omega)
    have hdvd : (6*y+1) ∣ (6*x-1) := by
      have := Nat.dvd_sub hk (dvd_refl (6*y+1))
      have e : (N+2)! - (6*y+1) = 6*x-1 := by omega
      rwa [e] at this
    rcases (p1.eq_one_or_self_of_dvd (6*y+1) hdvd) with hh | hh <;> omega
