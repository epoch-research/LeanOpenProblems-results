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
/- The core extraction lemma: assuming the hypothesis, for any `M ≥ 7` we can find a
decomposition coming from the term `n = M!/6`. -/
private lemma A227923_key (H : ∀ n : ℕ, 1 < n → A227923 n > 0)
    (M : ℕ) (hM : 7 ≤ M) :
    ∃ x y : ℕ, 1 ≤ x ∧ 1 ≤ y ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime ∧
      (6 * x - 1) + (6 * y + 1) = M ! := by
  obtain ⟨n, hn⟩ : ∃ n, n = M ! / 6 := ⟨_, rfl⟩
  have hdvd6 : 6 ∣ M ! := Nat.dvd_factorial (by norm_num) (by omega)
  have h6n : 6 * n = M ! := by rw [hn]; exact Nat.mul_div_cancel' hdvd6
  have hfact7 : (7)! ≤ M ! := Nat.factorial_le hM
  have hn1 : 1 < n := by
    have h840 : (840 : ℕ) ≤ M ! / 6 := by
      have e : ((7)! / 6 : ℕ) = 840 := by decide
      calc (840 : ℕ) = (7)! / 6 := e.symm
        _ ≤ M ! / 6 := Nat.div_le_div_right hfact7
    rw [hn]; omega
  have hpos : 0 < (Ico 1 n).sum
      (fun x => if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
        (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime then 1 else 0) := H n hn1
  obtain ⟨x, hxmem, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  rw [Finset.mem_Ico] at hxmem
  obtain ⟨hx1, hxn⟩ := hxmem
  split_ifs at hxne with hc
  · obtain ⟨p1, p2, p3, p4⟩ := hc
    refine ⟨x, n - x, hx1, by omega, p1, p2, p3, p4, ?_⟩
    omega
  · exact absurd rfl hxne

theorem oeis_227923_conjecture_1 :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) := by
  intro H
  constructor
  · -- Infinitely many Sophie Germain primes
    intro hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨x, y, hx1, hy1, p1, p2, p3, p4, hsum⟩ := A227923_key H (B + 7) (by omega)
    have hmem : (6 * x - 1) ∈ SophieGermainPrimes := by
      refine ⟨p1, ?_⟩
      have e : 2 * (6 * x - 1) + 1 = 12 * x - 1 := by omega
      rw [e]; exact p2
    have hle : 6 * x - 1 ≤ B := hB hmem
    have hdvd : (6 * x - 1) ∣ (B + 7)! := Nat.dvd_factorial (by omega) (by omega)
    have hdvd2 : (6 * x - 1) ∣ (6 * y + 1) := by
      have e : 6 * y + 1 = (B + 7)! - (6 * x - 1) := by omega
      rw [e]; exact Nat.dvd_sub hdvd dvd_rfl
    rcases (Nat.Prime.eq_one_or_self_of_dvd p4 _ hdvd2) with h | h
    · omega
    · omega
  · -- Infinitely many twin primes
    intro hfin
    obtain ⟨B, hB⟩ := hfin.bddAbove
    obtain ⟨x, y, hx1, hy1, p1, p2, p3, p4, hsum⟩ := A227923_key H (B + 7) (by omega)
    have hmem : (6 * y - 1) ∈ TwinPrimes := by
      refine ⟨p3, ?_⟩
      have e : 6 * y - 1 + 2 = 6 * y + 1 := by omega
      rw [e]; exact p4
    have hle : 6 * y - 1 ≤ B := hB hmem
    have hdvd : (6 * y + 1) ∣ (B + 7)! := Nat.dvd_factorial (by omega) (by omega)
    have hdvd2 : (6 * y + 1) ∣ (6 * x - 1) := by
      have e : 6 * x - 1 = (B + 7)! - (6 * y + 1) := by omega
      rw [e]; exact Nat.dvd_sub hdvd dvd_rfl
    rcases (Nat.Prime.eq_one_or_self_of_dvd p1 _ hdvd2) with h | h
    · omega
    · omega
