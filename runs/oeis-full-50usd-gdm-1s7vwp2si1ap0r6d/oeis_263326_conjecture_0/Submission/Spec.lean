import FormalConjectures.Util.ProblemImports

open Nat Rat Finset

/--
A263326: Denominator of the rational number $\sum_{d|n} \frac{1}{d+1}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + 1 : ℚ)⁻¹).den

/--
The rational number $\sum_{d|n} \frac{1}{(d+k)^s}$.
-/
noncomputable def S (n k s : ℕ) : ℚ :=
  Finset.sum (Nat.divisors n) fun d : ℕ => (d.cast + k.cast)⁻¹ ^ s.cast

set_option linter.unusedVariables false
set_option maxRecDepth 2000000

theorem S_five_val : S 5 31 1 = 17 / 288 := by
  unfold S
  have hdiv : Nat.divisors 5 = {1, 5} := by rfl
  rw [hdiv]
  have hnot : 1 ∉ ({5} : Finset ℕ) := by decide
  rw [Finset.sum_insert hnot]
  rw [Finset.sum_singleton]
  norm_num

theorem S_1829_val : S 1829 31 1 = 17 / 288 := by
  unfold S
  have hdiv : Nat.divisors 1829 = {1, 31, 59, 1829} := by rfl
  rw [hdiv]
  have hnot1 : 1 ∉ ({31, 59, 1829} : Finset ℕ) := by decide
  rw [Finset.sum_insert hnot1]
  have hnot2 : 31 ∉ ({59, 1829} : Finset ℕ) := by decide
  rw [Finset.sum_insert hnot2]
  have hnot3 : 59 ∉ ({1829} : Finset ℕ) := by decide
  rw [Finset.sum_insert hnot3]
  rw [Finset.sum_singleton]
  norm_num

/--
Conjecture: For any positive integers $k$ and $s$, all the numbers
$\sum_{d|n} \frac{1}{(d+k)^s}$ (for $n = 1,2,3, \dots$)
have pairwise distinct fractional parts, and none of them is an integer.
-/
theorem oeis_263326_conjecture_0.disproof :
  ¬ (∀ (k s : ℕ) (hk : k > 0) (hs : s > 0),
    (∀ n : ℕ, n > 0 → Int.fract (S n k s) ≠ 0) ∧
    (∀ n₁ n₂ : ℕ, n₁ > 0 → n₂ > 0 → n₁ ≠ n₂ →
      Int.fract (S n₁ k s) ≠ Int.fract (S n₂ k s))) := by
  intro h
  have h_inst := h 31 1 (by decide) (by decide)
  have h_distinct := h_inst.2
  have h_not_eq := h_distinct 1829 5 (by decide) (by decide) (by decide)
  have heq : Int.fract (S 1829 31 1) = Int.fract (S 5 31 1) := by
    rw [S_1829_val, S_five_val]
  exact h_not_eq heq


