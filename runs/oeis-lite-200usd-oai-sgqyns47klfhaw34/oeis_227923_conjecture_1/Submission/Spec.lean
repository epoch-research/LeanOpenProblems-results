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
lemma exists_good_of_A227923_pos {n : ℕ} (h : A227923 n > 0) :
    ∃ x ∈ Ico 1 n,
      (let y : ℕ := n - x
       (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime) := by
  rw [A227923] at h
  by_contra hnone
  have hzero :
      (Ico 1 n).sum (fun x =>
        let y : ℕ := n - x
        if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only
    split_ifs with hc
    · exact (hnone ⟨x, hx, hc⟩).elim
    · rfl
  omega

lemma six_mul_factorial_decomp {n x : ℕ} (hx1 : 1 ≤ x) (hx : x < n) :
    (6 * x - 1) + (6 * (n - x) + 1) = 6 * n := by
  omega

lemma twin_lower_add_two {y : ℕ} (hy : 0 < y) :
    (6 * y - 1) + 2 = 6 * y + 1 := by
  omega

lemma large_factorial_value (M : ℕ) (hM : 3 ≤ M) : 1 < M ! := by
  have hle : M ≤ M ! := Nat.self_le_factorial M
  omega

lemma right_part_large {M p r : ℕ} (hM : 3 ≤ M) (hpM : p ≤ M)
    (hsum : p + r = 6 * M !) : p < r := by
  have hle : M ≤ M ! := Nat.self_le_factorial M
  omega

lemma left_part_large {M p r : ℕ} (hM : 3 ≤ M) (hrM : r ≤ M)
    (hsum : p + r = 6 * M !) : r < p := by
  have hle : M ≤ M ! := Nat.self_le_factorial M
  omega

theorem oeis_227923_conjecture_1 :
  (∀ (n : ℕ), 1 < n → A227923 n > 0) →
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) :=
by
  intro H
  constructor
  · apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    let M : ℕ := max N 3
    have hM3 : 3 ≤ M := by
      dsimp [M]
      exact le_max_right N 3
    have hNM : N ≤ M := by
      dsimp [M]
      exact le_max_left N 3
    have hn : 1 < M ! := large_factorial_value M hM3
    obtain ⟨x, hxmem, hcond⟩ := exists_good_of_A227923_pos (H (M !) hn)
    let y : ℕ := (M !) - x
    let p : ℕ := 6 * x - 1
    let r : ℕ := 6 * y + 1
    have hx1 : 1 ≤ x := (mem_Ico.mp hxmem).1
    have hxlt : x < M ! := (mem_Ico.mp hxmem).2
    have hpprime : p.Prime := hcond.1
    have hsgprime : (2 * p + 1).Prime := by
      have h12 : 12 * x - 1 = 2 * p + 1 := by
        dsimp [p]
        omega
      simpa [h12] using hcond.2.1
    have hpS : p ∈ SophieGermainPrimes := by
      exact ⟨hpprime, hsgprime⟩
    have hpN : p ≤ N := hN hpS
    have hpM : p ≤ M := le_trans hpN hNM
    have hrprime : r.Prime := by
      simpa [r, y]
        using hcond.2.2.2
    have hsum : p + r = 6 * M ! := by
      simpa [p, r, y] using six_mul_factorial_decomp (n := M !) (x := x) hx1 hxlt
    have hp_dvd_fact : p ∣ M ! := Nat.dvd_factorial hpprime.pos hpM
    have hp_dvd_sixfact : p ∣ 6 * M ! := dvd_mul_of_dvd_right hp_dvd_fact 6
    have hp_dvd_sum : p ∣ p + r := by
      simpa [hsum] using hp_dvd_sixfact
    have hp_dvd_r : p ∣ r := (Nat.dvd_add_iff_right dvd_rfl).mpr hp_dvd_sum
    have hpeq : p = r := (Nat.prime_dvd_prime_iff_eq hpprime hrprime).mp hp_dvd_r
    have hlt : p < r := right_part_large hM3 hpM hsum
    omega
  · apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    let M : ℕ := max (N + 2) 3
    have hM3 : 3 ≤ M := by
      dsimp [M]
      exact le_max_right (N + 2) 3
    have hN2M : N + 2 ≤ M := by
      dsimp [M]
      exact le_max_left (N + 2) 3
    have hn : 1 < M ! := large_factorial_value M hM3
    obtain ⟨x, hxmem, hcond⟩ := exists_good_of_A227923_pos (H (M !) hn)
    let y : ℕ := (M !) - x
    let p : ℕ := 6 * x - 1
    let q : ℕ := 6 * y - 1
    let r : ℕ := 6 * y + 1
    have hx1 : 1 ≤ x := (mem_Ico.mp hxmem).1
    have hxlt : x < M ! := (mem_Ico.mp hxmem).2
    have hypos : 0 < y := by
      dsimp [y]
      omega
    have hpprime : p.Prime := hcond.1
    have hqprime : q.Prime := by
      simpa [q, y] using hcond.2.2.1
    have hrprime : r.Prime := by
      simpa [r, y] using hcond.2.2.2
    have hqTwin : q ∈ TwinPrimes := by
      refine ⟨hqprime, ?_⟩
      have hqr : q + 2 = r := by
        simpa [q, r] using twin_lower_add_two (y := y) hypos
      simpa [hqr] using hrprime
    have hqN : q ≤ N := hN hqTwin
    have hrM : r ≤ M := by
      have hqr : q + 2 = r := by
        simpa [q, r] using twin_lower_add_two (y := y) hypos
      omega
    have hsum : p + r = 6 * M ! := by
      simpa [p, r, y] using six_mul_factorial_decomp (n := M !) (x := x) hx1 hxlt
    have hr_dvd_fact : r ∣ M ! := Nat.dvd_factorial hrprime.pos hrM
    have hr_dvd_sixfact : r ∣ 6 * M ! := dvd_mul_of_dvd_right hr_dvd_fact 6
    have hr_dvd_sum : r ∣ p + r := by
      simpa [hsum] using hr_dvd_sixfact
    have hr_dvd_p : r ∣ p := (Nat.dvd_add_iff_left dvd_rfl).mpr hr_dvd_sum
    have hr_eq_p : r = p := (Nat.prime_dvd_prime_iff_eq hrprime hpprime).mp hr_dvd_p
    have hlt : r < p := left_part_large hM3 hrM hsum
    omega
