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
  intro h
  -- A prime summand of six times this factorial cannot be small.
  have large : ∀ (B p q : ℕ), p.Prime → q.Prime →
      p + q = 6 * (B + 3).factorial → B < p := by
    intro B p q hp hq heq
    by_contra hle
    have hpB : p ≤ B := by omega
    have hd : p ∣ (B + 3).factorial :=
      Nat.dvd_factorial hp.pos (by omega)
    have hsum : p ∣ p + q := by
      rw [heq]
      exact dvd_mul_of_dvd_right hd 6
    have hpq : p ∣ q := (Nat.dvd_add_iff_right (dvd_refl p)).mpr hsum
    have he : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
    have hf := Nat.self_le_factorial (B + 3)
    omega
  have both : ∀ B : ℕ, ∃ p ∈ SophieGermainPrimes, ∃ q ∈ TwinPrimes,
      B < p ∧ B < q := by
    intro B
    let n := (B + 2 + 3).factorial
    have hn : 1 < n := by
      have hf := Nat.self_le_factorial (B + 2 + 3)
      dsimp [n]
      omega
    have hs := h n hn
    unfold A227923 at hs
    obtain ⟨x, hx, hxpos⟩ := Finset.sum_pos_iff.mp hs
    have hc : (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
        (6 * (n - x) - 1).Prime ∧ (6 * (n - x) + 1).Prime := by
      by_contra hnot
      simp [hnot] at hxpos
    have hx' := Finset.mem_Ico.mp hx
    have hy : 1 ≤ n - x := by omega
    have heq : (6 * x - 1) + (6 * (n - x) + 1) = 6 * n := by omega
    have hpbig : B + 2 < 6 * x - 1 :=
      large (B + 2) _ _ hc.1 hc.2.2.2 heq
    have hqbig : B + 2 < 6 * (n - x) + 1 :=
      large (B + 2) _ _ hc.2.2.2 hc.1 (by omega)
    refine ⟨6 * x - 1, ?_, 6 * (n - x) - 1, ?_, ?_, ?_⟩
    · change (6 * x - 1).Prime ∧ (2 * (6 * x - 1) + 1).Prime
      have he : 2 * (6 * x - 1) + 1 = 12 * x - 1 := by omega
      exact ⟨hc.1, he ▸ hc.2.1⟩
    · change (6 * (n - x) - 1).Prime ∧ (6 * (n - x) - 1 + 2).Prime
      have he : 6 * (n - x) - 1 + 2 = 6 * (n - x) + 1 := by omega
      exact ⟨hc.2.2.1, he ▸ hc.2.2.2⟩
    · omega
    · omega
  constructor
  · apply Set.infinite_of_forall_exists_gt
    intro B
    obtain ⟨p, hp, q, hq, hBp, hBq⟩ := both B
    exact ⟨p, hp, hBp⟩
  · apply Set.infinite_of_forall_exists_gt
    intro B
    obtain ⟨p, hp, q, hq, hBp, hBq⟩ := both B
    exact ⟨q, hq, hBq⟩

theorem oeis_227923_conjecture_1.disproof : ¬ (type_of% @oeis_227923_conjecture_1) := sorry
