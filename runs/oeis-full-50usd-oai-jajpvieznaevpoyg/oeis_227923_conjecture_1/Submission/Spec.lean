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
  intro hA
  have exists_witness : ∀ {n : ℕ}, A227923 n > 0 →
      ∃ x ∈ Ico 1 n,
        let y : ℕ := n - x
        (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
          (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
    intro n hn
    unfold A227923 at hn
    have hs : (∑ x ∈ Ico 1 n,
        (let y : ℕ := n - x
         if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
              (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0)) ≠ 0 := by
      omega
    obtain ⟨x, hxmem, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    refine ⟨x, hxmem, ?_⟩
    dsimp at hxne ⊢
    by_contra hcond
    simp [hcond] at hxne
  constructor
  · refine Set.infinite_of_forall_exists_gt ?_
    intro N
    let K : ℕ := N + 6
    let n : ℕ := Nat.factorial K
    have hn : 1 < n := by
      rw [Nat.one_lt_factorial]
      omega
    obtain ⟨x, hxmem, hxcond⟩ := exists_witness (hA n hn)
    let y : ℕ := n - x
    let p : ℕ := 6 * x - 1
    let q : ℕ := 6 * y + 1
    have hp : p.Prime := hxcond.1
    have hp2 : (2 * p + 1).Prime := by
      have : 2 * p + 1 = 12 * x - 1 := by
        have hxpos : 1 ≤ x := (mem_Ico.mp hxmem).1
        omega
      simpa [this] using hxcond.2.1
    have hq : q.Prime := hxcond.2.2.2
    have hq_eq : q = 6 * n - p := by
      dsimp [q, p, y]
      have hxle : x ≤ n := le_of_lt ((mem_Ico.mp hxmem).2)
      have hxpos : 1 ≤ x := (mem_Ico.mp hxmem).1
      omega
    have hTlarge : 2 * (N + 2) < 6 * Nat.factorial K := by
      have hle : K ≤ Nat.factorial K := Nat.self_le_factorial K
      dsimp [K] at hle ⊢
      nlinarith
    have hp_gt : N < p := by
      by_contra hnot
      have hp_leN : p ≤ N := by omega
      have hp_leK : p ≤ K := by dsimp [K]; omega
      have hpT : p ∣ 6 * Nat.factorial K := by
        exact dvd_mul_of_dvd_right (Nat.dvd_factorial hp.pos hp_leK) 6
      have hp_lt_q : p < q := by
        dsimp [n] at hq_eq
        omega
      have hdiv : p ∣ q := by
        have hdiv' : p ∣ 6 * Nat.factorial K - p := Nat.dvd_sub hpT dvd_rfl
        dsimp [n] at hq_eq
        simpa [hq_eq] using hdiv'
      exact (Nat.not_prime_of_dvd_of_lt hdiv hp.two_le hp_lt_q) hq
    refine ⟨p, ?_, hp_gt⟩
    exact ⟨hp, hp2⟩
  · refine Set.infinite_of_forall_exists_gt ?_
    intro N
    let K : ℕ := N + 6
    let n : ℕ := Nat.factorial K
    have hn : 1 < n := by
      rw [Nat.one_lt_factorial]
      omega
    obtain ⟨x, hxmem, hxcond⟩ := exists_witness (hA n hn)
    let y : ℕ := n - x
    let p : ℕ := 6 * x - 1
    let r : ℕ := 6 * y + 1
    let t : ℕ := 6 * y - 1
    have hp : p.Prime := hxcond.1
    have ht : t.Prime := hxcond.2.2.1
    have hr : r.Prime := hxcond.2.2.2
    have hr_eq : r = 6 * n - p := by
      dsimp [r, p, y]
      have hxle : x ≤ n := le_of_lt ((mem_Ico.mp hxmem).2)
      have hxpos : 1 ≤ x := (mem_Ico.mp hxmem).1
      omega
    have hp_eq : p = 6 * n - r := by
      dsimp [r, p, y]
      have hxle : x ≤ n := le_of_lt ((mem_Ico.mp hxmem).2)
      have hxpos : 1 ≤ x := (mem_Ico.mp hxmem).1
      omega
    have hTlarge : 2 * (N + 2) < 6 * Nat.factorial K := by
      have hle : K ≤ Nat.factorial K := Nat.self_le_factorial K
      dsimp [K] at hle ⊢
      nlinarith
    have ht_gt : N < t := by
      by_contra hnot
      have ht_leN : t ≤ N := by omega
      have hr_le : r ≤ N + 2 := by
        dsimp [r, t] at ht_leN ⊢
        omega
      have hr_leK : r ≤ K := by dsimp [K]; omega
      have hrT : r ∣ 6 * Nat.factorial K := by
        exact dvd_mul_of_dvd_right (Nat.dvd_factorial hr.pos hr_leK) 6
      have hr_lt_p : r < p := by
        dsimp [n] at hp_eq
        omega
      have hdiv : r ∣ p := by
        have hdiv' : r ∣ 6 * Nat.factorial K - r := Nat.dvd_sub hrT dvd_rfl
        dsimp [n] at hp_eq
        simpa [hp_eq] using hdiv'
      exact (Nat.not_prime_of_dvd_of_lt hdiv hr.two_le hr_lt_p) hp
    refine ⟨t, ?_, ht_gt⟩
    refine ⟨ht, ?_⟩
    have htr : t + 2 = r := by
      dsimp [r, t]
      have hypos : 1 ≤ y := by
        dsimp [y]
        exact Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt ((mem_Ico.mp hxmem).2))
      omega
    simpa [htr] using hr
