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
  (Set.Infinite SophieGermainPrimes ∧ Set.Infinite TwinPrimes) := by
  intro h
  have representation : ∀ n : ℕ, 1 < n → ∃ x ∈ Ico 1 n,
      let y := n - x
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
        (6 * y - 1).Prime ∧ (6 * y + 1).Prime := by
    intro n hn
    have hs : 0 < (Ico 1 n).sum (fun x =>
        let y := n - x
        if (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧
            (6 * y - 1).Prime ∧ (6 * y + 1).Prime then 1 else 0) := by
      simpa [A227923] using h n hn
    obtain ⟨x, hx, hxpos⟩ := Finset.sum_pos_iff.mp hs
    refine ⟨x, hx, ?_⟩
    by_contra hc
    simp [hc] at hxpos
  constructor
  · apply Set.infinite_of_forall_exists_gt
    intro B
    let m := B + 6
    let n := Nat.factorial m
    have hn : 1 < n := by
      have hm : 2 ≤ m := by simp [m]
      exact lt_of_lt_of_le (by decide : 1 < 2) (hm.trans (Nat.self_le_factorial m))
    obtain ⟨x, hx, hp, hsg, ht, htp⟩ := representation n hn
    have hx' : 1 ≤ x ∧ x < n := Finset.mem_Ico.mp hx
    let y := n - x
    refine ⟨6 * x - 1, ?_, ?_⟩
    · refine ⟨hp, ?_⟩
      convert hsg using 1 <;> omega
    · by_contra hnot
      have hpB : 6 * x - 1 ≤ B := Nat.le_of_not_lt hnot
      have hxm : 6 * x - 1 ≤ m := hpB.trans (by simp [m])
      have hppos : 0 < 6 * x - 1 := hp.pos
      have hpdvdn : 6 * x - 1 ∣ n := by
        exact Nat.dvd_factorial hppos hxm
      have hxlt : x < n := hx'.2
      have hydef : y = n - x := rfl
      have hsum : (6 * x - 1) + (6 * y + 1) = 6 * n := by
        dsimp [y]
        omega
      have hpdvdtotal : 6 * x - 1 ∣ 6 * n := dvd_mul_of_dvd_right hpdvdn 6
      have hpdvdq : 6 * x - 1 ∣ 6 * y + 1 := by
        have hd := Nat.dvd_sub hpdvdtotal (dvd_refl (6 * x - 1))
        have heq : 6 * n - (6 * x - 1) = 6 * y + 1 := by omega
        rwa [heq] at hd
      rcases htp.eq_one_or_self_of_dvd (6 * x - 1) hpdvdq with hpone | hpeq
      · exact hp.ne_one hpone
      · have hnlarge : m ≤ n := Nat.self_le_factorial m
        have hqgt : 6 * x - 1 < 6 * y + 1 := by
          omega
        exact hqgt.ne hpeq
  · apply Set.infinite_of_forall_exists_gt
    intro B
    let m := B + 6
    let n := Nat.factorial m
    have hn : 1 < n := by
      have hm : 2 ≤ m := by simp [m]
      exact lt_of_lt_of_le (by decide : 1 < 2) (hm.trans (Nat.self_le_factorial m))
    obtain ⟨x, hx, hp, hsg, ht, htp⟩ := representation n hn
    have hx' : 1 ≤ x ∧ x < n := Finset.mem_Ico.mp hx
    let y := n - x
    refine ⟨6 * y - 1, ?_, ?_⟩
    · refine ⟨ht, ?_⟩
      convert htp using 1 <;> have := ht.two_le <;> omega
    · by_contra hnot
      have htB : 6 * y - 1 ≤ B := Nat.le_of_not_lt hnot
      have hklem : 6 * y + 1 ≤ m := by
        have ht2 := ht.two_le
        dsimp [m]
        omega
      have hkpos : 0 < 6 * y + 1 := htp.pos
      have hkdvdn : 6 * y + 1 ∣ n := Nat.dvd_factorial hkpos hklem
      have hxlt : x < n := hx'.2
      have hsum : (6 * x - 1) + (6 * y + 1) = 6 * n := by
        dsimp [y]
        omega
      have hkdvdtotal : 6 * y + 1 ∣ 6 * n := dvd_mul_of_dvd_right hkdvdn 6
      have hkdivp : 6 * y + 1 ∣ 6 * x - 1 := by
        have hd := Nat.dvd_sub hkdvdtotal (dvd_refl (6 * y + 1))
        have heq : 6 * n - (6 * y + 1) = 6 * x - 1 := by omega
        rwa [heq] at hd
      rcases hp.eq_one_or_self_of_dvd (6 * y + 1) hkdivp with hkone | hkeq
      · exact htp.ne_one hkone
      · have hnlarge : m ≤ n := Nat.self_le_factorial m
        have hpgt : 6 * y + 1 < 6 * x - 1 := by
          omega
        exact hpgt.ne hkeq
