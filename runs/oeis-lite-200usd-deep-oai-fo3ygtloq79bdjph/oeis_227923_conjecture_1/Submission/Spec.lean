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
private lemma exists_good_of_A227923_pos {n : ℕ} (h : A227923 n > 0) :
    ∃ x, x ∈ Ico 1 n ∧
      (let y : ℕ := n - x
       (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
         (6 * y - 1).Prime ∧ (6 * y + 1).Prime) := by
  unfold A227923 at h
  have hne :
      (∑ x ∈ Ico 1 n,
        (let y : ℕ := n - x
         if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
             (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0)) ≠ 0 := by
    omega
  rcases Finset.exists_ne_zero_of_sum_ne_zero hne with ⟨x, hx, hxne⟩
  refine ⟨x, hx, ?_⟩
  dsimp only at hxne ⊢
  by_cases hc : (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
      (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime
  · exact hc
  · simp [hc] at hxne

theorem oeis_227923_conjecture_1 :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) := by
  intro hA
  constructor
  · rw [← Set.not_finite]
    intro hfin
    rcases Set.Finite.bddAbove hfin with ⟨B, hB⟩
    simp [upperBounds] at hB
    let n : ℕ := (B + 3)!
    have hn_gt : 1 < n := by
      have hs : B + 3 ≤ (B + 3)! := Nat.self_le_factorial (B + 3)
      omega
    rcases exists_good_of_A227923_pos (hA n hn_gt) with ⟨x, hxmem, hgood⟩
    have hx1 : 1 ≤ x := (Finset.mem_Ico.mp hxmem).1
    have hxlt : x < n := (Finset.mem_Ico.mp hxmem).2
    let y : ℕ := n - x
    have hy1 : 1 ≤ y := by
      dsimp [y]
      omega
    have hp : (6 * x - 1).Prime := hgood.1
    have hsafe : (2 * (6 * x - 1) + 1).Prime := by
      convert hgood.2.1 using 1
      omega
    have hp_mem : 6 * x - 1 ∈ SophieGermainPrimes := by
      exact ⟨hp, hsafe⟩
    have hp_le_B : 6 * x - 1 ≤ B := hB hp_mem
    have hp_dvd_fact : 6 * x - 1 ∣ (B + 3)! := by
      exact Nat.dvd_factorial hp.pos (by omega)
    have hp_dvd_6n : 6 * x - 1 ∣ 6 * n := by
      simpa [n, mul_comm] using dvd_mul_of_dvd_right hp_dvd_fact 6
    have hsum : (6 * x - 1) + (6 * y + 1) = 6 * n := by
      dsimp [y]
      omega
    have hp_dvd_q : 6 * x - 1 ∣ 6 * y + 1 := by
      have hd := Nat.dvd_sub hp_dvd_6n (dvd_refl (6 * x - 1))
      convert hd using 1
      omega
    have hqprime : (6 * y + 1).Prime := hgood.2.2.2
    rcases (Nat.dvd_prime hqprime).1 hp_dvd_q with hp_eq_one | hp_eq_q
    · exact hp.ne_one hp_eq_one
    · have : ¬ 6 * x - 1 = 6 * y + 1 := by omega
      exact this hp_eq_q
  · rw [← Set.not_finite]
    intro hfin
    rcases Set.Finite.bddAbove hfin with ⟨B, hB⟩
    simp [upperBounds] at hB
    let n : ℕ := (B + 3)!
    have hn_gt : 1 < n := by
      have hs : B + 3 ≤ (B + 3)! := Nat.self_le_factorial (B + 3)
      omega
    rcases exists_good_of_A227923_pos (hA n hn_gt) with ⟨x, hxmem, hgood⟩
    have hx1 : 1 ≤ x := (Finset.mem_Ico.mp hxmem).1
    have hxlt : x < n := (Finset.mem_Ico.mp hxmem).2
    let y : ℕ := n - x
    have hy1 : 1 ≤ y := by
      dsimp [y]
      omega
    have htprime : (6 * y - 1).Prime := hgood.2.2.1
    have hqprime : (6 * y + 1).Prime := hgood.2.2.2
    have hsucc : (6 * y - 1 + 2).Prime := by
      convert hqprime using 1
      omega
    have ht_mem : 6 * y - 1 ∈ TwinPrimes := by
      exact ⟨htprime, hsucc⟩
    have ht_le_B : 6 * y - 1 ≤ B := hB ht_mem
    have hq_le : 6 * y + 1 ≤ B + 3 := by
      omega
    have hq_dvd_fact : 6 * y + 1 ∣ (B + 3)! := by
      exact Nat.dvd_factorial hqprime.pos hq_le
    have hq_dvd_6n : 6 * y + 1 ∣ 6 * n := by
      simpa [n, mul_comm] using dvd_mul_of_dvd_right hq_dvd_fact 6
    have hsum : (6 * x - 1) + (6 * y + 1) = 6 * n := by
      dsimp [y]
      omega
    have hq_dvd_p : 6 * y + 1 ∣ 6 * x - 1 := by
      have hd := Nat.dvd_sub hq_dvd_6n (dvd_refl (6 * y + 1))
      convert hd using 1
      omega
    have hpprime : (6 * x - 1).Prime := hgood.1
    rcases (Nat.dvd_prime hpprime).1 hq_dvd_p with hq_eq_one | hq_eq_p
    · exact hqprime.ne_one hq_eq_one
    · have : ¬ 6 * y + 1 = 6 * x - 1 := by omega
      exact this hq_eq_p
