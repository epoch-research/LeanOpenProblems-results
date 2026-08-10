import FormalConjectures.Util.ProblemImports

set_option google.answer "always_true"
set_option warn.sorry false

open Nat

/--
A320146: $a(n) = 2 \cdot \operatorname{prime}(n) \pmod{\operatorname{prime}(n-1) + \operatorname{prime}(n+1)}$.
$\operatorname{prime}(k)$ is the $k$-th prime number (1-indexed). The sequence is defined for $n \ge 2$.
We use Mathlib's $P(i) = \operatorname{Nat.nth} \operatorname{Nat.Prime} i$ (0-indexed prime).
The formula translates to:
$$a(n) = \left(2 \cdot P(n-1)\right) \bmod \left(P(n-2) + P(n)\right)$$
where subtraction $n-k$ is natural number subtraction.
-/
noncomputable def A320146 (n : ℕ) : ℕ :=
  let P i : ℕ := Nat.nth Nat.Prime i
  (2 * P (n - 1)) % (P (n - 2) + P n)

-- Helper definition for the 1-indexed prime function $\operatorname{prime}(n)$ used in the conjecture.
-- This corresponds to the $n$-th prime in OEIS's 1-indexed convention.
noncomputable def prime_oeis (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)


lemma A320146_le (i : ℕ) : A320146 i ≤ 2 * prime_oeis i := by
  dsimp [A320146, prime_oeis]
  apply Nat.mod_le

lemma prime_oeis_pos (i : ℕ) : 0 < prime_oeis i := by
  dsimp [prime_oeis]
  have h_prime := Nat.prime_nth_prime (i - 1)
  exact Nat.Prime.pos h_prime

lemma denominator_pos (n : ℕ) (hn : 2 ≤ n) : 0 < Finset.sum (Finset.Icc 2 n) (fun i => (prime_oeis i : ℝ)) := by
  have h_nonempty : (Finset.Icc 2 n).Nonempty := ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩
  have h_pos : ∀ i ∈ Finset.Icc 2 n, 0 < (prime_oeis i : ℝ) := by
    intro i _hi
    exact_mod_cast prime_oeis_pos i
  exact Finset.sum_pos h_pos h_nonempty

lemma ratio_nonneg (n : ℕ) : 0 ≤ (Finset.sum (Finset.Icc 2 n) (fun i => (A320146 i : ℝ))) / (Finset.sum (Finset.Icc 2 n) (fun i => (prime_oeis i : ℝ))) := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i _hi
    exact_mod_cast Nat.zero_le (A320146 i)
  · apply Finset.sum_nonneg
    intro i _hi
    exact_mod_cast Nat.zero_le (prime_oeis i)

lemma ratio_le_two (n : ℕ) (hn : 2 ≤ n) : (Finset.sum (Finset.Icc 2 n) (fun i => (A320146 i : ℝ))) / (Finset.sum (Finset.Icc 2 n) (fun i => (prime_oeis i : ℝ))) ≤ 2 := by
  have h_den : 0 < Finset.sum (Finset.Icc 2 n) (fun i => (prime_oeis i : ℝ)) := denominator_pos n hn
  rw [div_le_iff₀ h_den]
  have h_sum : Finset.sum (Finset.Icc 2 n) (fun i => (A320146 i : ℝ)) ≤ Finset.sum (Finset.Icc 2 n) (fun i => 2 * (prime_oeis i : ℝ)) := by
    apply Finset.sum_le_sum
    intro i _hi
    have h_le := A320146_le i
    exact_mod_cast h_le
  have h_mul : Finset.sum (Finset.Icc 2 n) (fun i => 2 * (prime_oeis i : ℝ)) = 2 * Finset.sum (Finset.Icc 2 n) (fun i => (prime_oeis i : ℝ)) := by
    rw [← Finset.mul_sum]
  linarith

theorem oeis_320146_conjecture_0 :
  ∃ L : ℝ, Filter.Tendsto
    (fun n : ℕ =>
      (Finset.sum (Finset.Icc 2 n) (fun i => (A320146 i : ℝ)))
      /
      (Finset.sum (Finset.Icc 2 n) (fun i => (prime_oeis i : ℝ))))
    Filter.atTop
    (nhds L) :=
  answer(sorry)

#print axioms oeis_320146_conjecture_0

