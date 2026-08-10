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
theorem extract (n : ℕ) (h : A227923 n > 0) :
    ∃ x, 1 ≤ x ∧ x < n ∧ (6*x-1).Prime ∧ (12*x-1).Prime ∧
      (6*(n-x)-1).Prime ∧ (6*(n-x)+1).Prime := by
  unfold A227923 at h
  have hne : (Ico 1 n).sum (fun x => let y := n - x;
      if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime
        then 1 else 0) ≠ 0 := _root_.ne_of_gt h
  obtain ⟨x, hx, hfx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  simp only [Finset.mem_Ico] at hx
  refine ⟨x, hx.1, hx.2, ?_⟩
  by_contra hc
  simp only at hfx
  rw [if_neg hc] at hfx
  exact hfx rfl

theorem core (H : ∀ n, 1 < n → A227923 n > 0) (N : ℕ) (hN : 4 ≤ N) :
    ∃ x y, 1 ≤ x ∧ 1 ≤ y ∧
      (6*x-1).Prime ∧ (12*x-1).Prime ∧ (6*y-1).Prime ∧ (6*y+1).Prime ∧
      (6*x-1) + (6*y+1) = (N+2)! := by
  have h6 : (6:ℕ) ∣ (N+2)! := Nat.dvd_factorial (by norm_num) (by omega)
  obtain ⟨n, hn⟩ := h6
  have h6n : 6 * n = (N+2)! := hn.symm
  have hfac : 120 ≤ (N+2)! := by
    calc (120:ℕ) = Nat.factorial 5 := by norm_num
    _ ≤ (N+2)! := Nat.factorial_le (by omega)
  have hn1 : 1 < n := by omega
  obtain ⟨x, hx1, hxn, hp1, hp2, hp3, hp4⟩ := extract n (H n hn1)
  refine ⟨x, n - x, hx1, by omega, hp1, hp2, hp3, hp4, ?_⟩
  omega

theorem oeis_227923_conjecture_1 :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) :=
by
  intro H
  constructor
  · -- Sophie Germain primes are infinite
    intro hfin
    obtain ⟨N0, hN0⟩ := hfin.bddAbove
    obtain ⟨x, y, hx1, hy1, hp1, hp2, hp3, hp4, heq⟩ := core H (max N0 4) (le_max_right N0 4)
    have hmem : (6*x-1) ∈ SophieGermainPrimes :=
      ⟨hp1, by rw [show 2*(6*x-1)+1 = 12*x-1 from by omega]; exact hp2⟩
    have hle : 6*x-1 ≤ N0 := hN0 hmem
    have hmx : N0 ≤ max N0 4 := le_max_left N0 4
    have hdvdf : (6*x-1) ∣ (max N0 4 + 2)! := Nat.dvd_factorial (by omega) (by omega)
    have hdvd : (6*x-1) ∣ (6*y+1) := by
      have h := Nat.dvd_sub hdvdf (dvd_refl (6*x-1))
      rwa [show (max N0 4 + 2)! - (6*x-1) = 6*y+1 from by omega] at h
    rcases hp4.eq_one_or_self_of_dvd _ hdvd with h | h <;> omega
  · -- Twin primes are infinite
    intro hfin
    obtain ⟨N0, hN0⟩ := hfin.bddAbove
    obtain ⟨x, y, hx1, hy1, hp1, hp2, hp3, hp4, heq⟩ := core H (max N0 4) (le_max_right N0 4)
    have hmem : (6*y-1) ∈ TwinPrimes :=
      ⟨hp3, by rw [show 6*y-1+2 = 6*y+1 from by omega]; exact hp4⟩
    have hle : 6*y-1 ≤ N0 := hN0 hmem
    have hmx : N0 ≤ max N0 4 := le_max_left N0 4
    have hdvdf : (6*y+1) ∣ (max N0 4 + 2)! := Nat.dvd_factorial (by omega) (by omega)
    have hdvd : (6*y+1) ∣ (6*x-1) := by
      have h := Nat.dvd_sub hdvdf (dvd_refl (6*y+1))
      rwa [show (max N0 4 + 2)! - (6*y+1) = 6*x-1 from by omega] at h
    rcases hp1.eq_one_or_self_of_dvd _ hdvd with h | h <;> omega
