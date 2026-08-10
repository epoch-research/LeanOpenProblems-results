import FormalConjectures.Util.ProblemImports

open Nat Rat Finset

set_option maxRecDepth 8000

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

/--
Conjecture (disproof): The generalization to arbitrary positive integers $k$ and $s$
is false. Taking $k = 31$, $s = 1$, we have
$$S(5,31,1) = \frac{1}{32} + \frac{1}{36} = \frac{17}{288}$$
and, since $1829 = 31 \cdot 59$ has divisors $\{1, 31, 59, 1829\}$,
$$S(1829,31,1) = \frac{1}{32} + \frac{1}{62} + \frac{1}{90} + \frac{1}{1860} = \frac{17}{288}.$$
Thus $5 \neq 1829$ yet the two values (and hence their fractional parts) coincide,
contradicting the pairwise-distinctness part of the conjecture.
-/
theorem oeis_263326_conjecture_0.disproof :
  ¬ (∀ (k s : ℕ), k > 0 → s > 0 →
    (∀ n : ℕ, n > 0 → Int.fract (S n k s) ≠ 0) ∧
    (∀ n₁ n₂ : ℕ, n₁ > 0 → n₂ > 0 → n₁ ≠ n₂ →
      Int.fract (S n₁ k s) ≠ Int.fract (S n₂ k s))) := by
  intro h
  have hb := (h 31 1 (by norm_num) (by norm_num)).2
  apply hb 5 1829 (by norm_num) (by norm_num) (by norm_num)
  have e1 : S 5 31 1 = 17 / 288 := by
    unfold S
    rw [show Nat.divisors 5 = {1, 5} from by decide]
    norm_num
  have e2 : S 1829 31 1 = 17 / 288 := by
    unfold S
    rw [show Nat.divisors 1829 = {1, 31, 59, 1829} from by decide]
    norm_num
  rw [e1, e2]
