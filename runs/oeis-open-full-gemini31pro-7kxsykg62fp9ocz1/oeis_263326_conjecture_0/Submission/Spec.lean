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

/--
Conjecture: For any positive integers $k$ and $s$, all the numbers
$\sum_{d|n} \frac{1}{(d+k)^s}$ (for $n = 1,2,3, \dots$)
have pairwise distinct fractional parts, and none of them is an integer.
-/
theorem oeis_263326_conjecture_0 (k s : ℕ) (hk : k > 0) (hs : s > 0) :
  (∀ n : ℕ, n > 0 → Int.fract (S n k s) ≠ 0) ∧
  (∀ n₁ n₂ : ℕ, n₁ > 0 → n₂ > 0 → n₁ ≠ n₂ →
    Int.fract (S n₁ k s) ≠ Int.fract (S n₂ k s)) :=
by sorry

set_option maxRecDepth 100000

lemma div_1829 : Nat.divisors 1829 = {1, 31, 59, 1829} := by decide
lemma div_5 : Nat.divisors 5 = {1, 5} := by decide

theorem oeis_263326_conjecture_0.disproof : ¬ (type_of% @oeis_263326_conjecture_0) := by
  intro h
  have h_spec := h 31 1 (by norm_num) (by norm_num)
  rcases h_spec with ⟨_, h2⟩
  have h_eq5 : S 5 31 1 = 17 / 288 := by
    unfold S
    rw [div_5]
    simp [sum_insert, sum_singleton]
    norm_num
  have h_eq1829 : S 1829 31 1 = 17 / 288 := by
    unfold S
    rw [div_1829]
    simp [sum_insert, sum_singleton]
    norm_num
  have h_fract : Int.fract (S 5 31 1) = Int.fract (S 1829 31 1) := by
    rw [h_eq5, h_eq1829]
  have h_ne : Int.fract (S 5 31 1) ≠ Int.fract (S 1829 31 1) := 
    h2 5 1829 (by norm_num) (by norm_num) (by norm_num)
  exact h_ne h_fract
