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


lemma A227923.exists_good {n : ℕ} (hpos : A227923 n > 0) :
    ∃ x ∈ Ico 1 n,
      let y : ℕ := n - x
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
  unfold A227923 at hpos
  have hne : ((Ico 1 n).sum fun x =>
      let y : ℕ := n - x
      if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0) ≠ 0 :=
    Nat.ne_of_gt hpos
  obtain ⟨x, hxmem, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨x, hxmem, ?_⟩
  dsimp only at hxne ⊢
  by_cases hcond : (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
      (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime
  · exact hcond
  · simp [hcond] at hxne

lemma A227923.good_witness {n x : ℕ} (hxmem : x ∈ Ico 1 n) :
    let y : ℕ := n - x
    x + y = n ∧ 1 ≤ x := by
  rw [mem_Ico] at hxmem
  dsimp
  exact ⟨Nat.add_sub_of_le hxmem.2.le, hxmem.1⟩

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
  intro H
  constructor
  · apply Set.infinite_of_not_bddAbove
    rw [not_bddAbove_iff]
    intro B
    let M : ℕ := B + 6
    let n : ℕ := M ! / 6
    have hM6 : 6 ≤ M := by dsimp [M]; omega
    have h6 : 6 * n = M ! := by
      have h6dvd : 6 ∣ M ! := Nat.dvd_factorial (by norm_num) hM6
      dsimp [n]
      exact Nat.mul_div_cancel' h6dvd
    have hn : 1 < n := by
      have hfact_ge : 12 ≤ M ! := by
        have hle : 6 ! ≤ M ! := Nat.factorial_le hM6
        norm_num at hle ⊢
        omega
      have h6n_ge : 12 ≤ 6 * n := by simpa [h6] using hfact_ge
      omega
    obtain ⟨x, hxmem, hxgood⟩ := A227923.exists_good (H n hn)
    let y : ℕ := n - x
    have hxyx := A227923.good_witness hxmem
    dsimp only at hxyx
    have hxy : x + y = n := hxyx.1
    have hx1 : 1 ≤ x := hxyx.2
    dsimp only at hxgood
    have hp : (6 * x - 1).Prime := hxgood.1
    have hsp : (6 * x - 1) ∈ SophieGermainPrimes := by
      dsimp [SophieGermainPrimes]
      refine ⟨hp, ?_⟩
      have h12 : 12 * x - 1 = 2 * (6 * x - 1) + 1 := by omega
      simpa [h12] using hxgood.2.1
    refine ⟨6 * x - 1, hsp, ?_⟩
    have hfacsum : M ! = (6 * x - 1) + (6 * y + 1) := by
      have : 6 * (x + y) = M ! := by simpa [hxy] using h6
      omega
    by_contra hleB
    have hp_le_M : 6 * x - 1 ≤ M := by
      dsimp [M]
      omega
    have hdvd_fac : 6 * x - 1 ∣ M ! := hp.dvd_factorial.mpr hp_le_M
    have hdvd_sum : 6 * x - 1 ∣ (6 * x - 1) + (6 * y + 1) := by
      simpa [hfacsum] using hdvd_fac
    have hdvd_right : 6 * x - 1 ∣ 6 * y + 1 := by
      exact (Nat.dvd_add_right (dvd_refl (6 * x - 1))).mp hdvd_sum
    have hqprime : (6 * y + 1).Prime := hxgood.2.2.2
    have heq : 6 * x - 1 = 6 * y + 1 := by
      exact (Nat.dvd_prime hqprime).mp hdvd_right |>.elim (fun h1 => by
        have hp2 : 2 ≤ 6 * x - 1 := hp.two_le
        omega) id
    exact (by omega : 6 * x - 1 ≠ 6 * y + 1) heq
  · apply Set.infinite_of_not_bddAbove
    rw [not_bddAbove_iff]
    intro B
    let M : ℕ := B + 6
    let n : ℕ := M ! / 6
    have hM6 : 6 ≤ M := by dsimp [M]; omega
    have h6 : 6 * n = M ! := by
      have h6dvd : 6 ∣ M ! := Nat.dvd_factorial (by norm_num) hM6
      dsimp [n]
      exact Nat.mul_div_cancel' h6dvd
    have hn : 1 < n := by
      have hfact_ge : 12 ≤ M ! := by
        have hle : 6 ! ≤ M ! := Nat.factorial_le hM6
        norm_num at hle ⊢
        omega
      have h6n_ge : 12 ≤ 6 * n := by simpa [h6] using hfact_ge
      omega
    obtain ⟨x, hxmem, hxgood⟩ := A227923.exists_good (H n hn)
    let y : ℕ := n - x
    have hxyx := A227923.good_witness hxmem
    dsimp only at hxyx
    have hxy : x + y = n := hxyx.1
    have hx1 : 1 ≤ x := hxyx.2
    dsimp only at hxgood
    have htwin : (6 * y - 1) ∈ TwinPrimes := by
      dsimp [TwinPrimes]
      refine ⟨hxgood.2.2.1, ?_⟩
      have hsucc : 6 * y - 1 + 2 = 6 * y + 1 := by
        have hypos : 1 ≤ y := by
          have hq : (6 * y - 1).Prime := hxgood.2.2.1
          have : 2 ≤ 6 * y - 1 := hq.two_le
          omega
        omega
      simpa [hsucc] using hxgood.2.2.2
    refine ⟨6 * y - 1, htwin, ?_⟩
    have hfacsum : M ! = (6 * x - 1) + (6 * y + 1) := by
      have : 6 * (x + y) = M ! := by simpa [hxy] using h6
      omega
    by_contra hleB
    have hr_le_M : 6 * y + 1 ≤ M := by
      dsimp [M]
      omega
    have hrprime : (6 * y + 1).Prime := hxgood.2.2.2
    have hdvd_fac : 6 * y + 1 ∣ M ! := hrprime.dvd_factorial.mpr hr_le_M
    have hdvd_sum : 6 * y + 1 ∣ (6 * x - 1) + (6 * y + 1) := by
      simpa [hfacsum] using hdvd_fac
    have hdvd_left : 6 * y + 1 ∣ 6 * x - 1 := by
      exact (Nat.dvd_add_left (dvd_refl (6 * y + 1))).mp hdvd_sum
    have hpprime : (6 * x - 1).Prime := hxgood.1
    have heq : 6 * y + 1 = 6 * x - 1 := by
      exact (Nat.dvd_prime hpprime).mp hdvd_left |>.elim (fun h1 => by
        have hr2 : 2 ≤ 6 * y + 1 := hrprime.two_le
        omega) id
    have hneq : 6 * x - 1 ≠ 6 * y + 1 := by omega
    exact hneq heq.symm
