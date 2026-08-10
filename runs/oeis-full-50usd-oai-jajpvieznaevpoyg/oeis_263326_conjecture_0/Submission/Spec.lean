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


set_option maxRecDepth 100000

/--
Conjecture: For any positive integers $k$ and $s$, all the numbers
$\sum_{d|n} \frac{1}{(d+k)^s}$ (for $n = 1,2,3, \dots$)
have pairwise distinct fractional parts, and none of them is an integer.
-/
theorem oeis_263326_conjecture_0.disproof :
  ¬ (∀ (k s : ℕ), k > 0 → s > 0 →
    (∀ n : ℕ, n > 0 → Int.fract (S n k s) ≠ 0) ∧
    (∀ n₁ n₂ : ℕ, n₁ > 0 → n₂ > 0 → n₁ ≠ n₂ →
      Int.fract (S n₁ k s) ≠ Int.fract (S n₂ k s))) :=
by
  intro h
  have H := (h 31 1 (by norm_num) (by norm_num)).2 5 1829 (by norm_num) (by norm_num) (by norm_num)
  apply H
  have hS : S 5 31 1 = S 1829 31 1 := by
    have h5 : Nat.divisors 5 = ({1, 5} : Finset ℕ) := by decide
    have h1829 : Nat.divisors 1829 = ({1, 31, 59, 1829} : Finset ℕ) := by decide
    norm_num [S, h5, h1829]
  exact congrArg Int.fract hS
