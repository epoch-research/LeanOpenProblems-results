import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

open Nat Finset

/--
A306477: Number of ways to write $n$ as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
with $w,x,y,z$ nonnegative integers, where $\binom{m}{k}$ denotes the binomial coefficient $\frac{m!}{k!(m-k)!}$.
-/
def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  )

theorem A306477_pos_iff (n : ℕ) :
    A306477 n > 0 ↔ ∃ w ∈ Finset.range (n + 1), ∃ x ∈ Finset.range (n + 1), ∃ y ∈ Finset.range (n + 1), ∃ z ∈ Finset.range (n + 1),
      (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n := by
  let R := Finset.range (n + 1)
  have h_nonneg_z (w x y z : ℕ) (_hz : z ∈ R) : 0 ≤ if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0 := by
    split_ifs <;> omega
  have h_nonneg_y (w x y : ℕ) (_hy : y ∈ R) : 0 ≤ ∑ z ∈ R, if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0 := by
    apply Finset.sum_nonneg; intro z hz; exact h_nonneg_z w x y z hz
  have h_nonneg_x (w x : ℕ) (_hx : x ∈ R) : 0 ≤ ∑ y ∈ R, ∑ z ∈ R, if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0 := by
    apply Finset.sum_nonneg; intro y hy; exact h_nonneg_y w x y hy
  have h_nonneg_w (w : ℕ) (_hw : w ∈ R) : 0 ≤ ∑ x ∈ R, ∑ y ∈ R, ∑ z ∈ R, if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0 := by
    apply Finset.sum_nonneg; intro x hx; exact h_nonneg_x w x hx

  change (0 < ∑ w ∈ R, ∑ x ∈ R, ∑ y ∈ R, ∑ z ∈ R, if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0) ↔ _
  rw [Finset.sum_pos_iff_of_nonneg h_nonneg_w]
  simp_rw [Finset.sum_pos_iff_of_nonneg (h_nonneg_x _)]
  simp_rw [Finset.sum_pos_iff_of_nonneg (h_nonneg_y _ _)]
  simp_rw [Finset.sum_pos_iff_of_nonneg (h_nonneg_z _ _ _)]
  simp only [Nat.pos_iff_ne_zero, ne_eq]
  have h_eq (w x y z : ℕ) :
      ((if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0) ≠ 0) ↔
      ((w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n) := by
    split_ifs with h
    · simp [h]
    · simp [h]
  simp_rw [h_eq]
  rfl

/--
The 2-4-6-8 conjecture (oeis_306477_conjecture_5) states that $A306477(n) > 0$ for all $n > 0$.
In other words, any positive integer $n$ can be written as
$\binom{w}{2} + \binom{x}{4} + \binom{y}{6} + \binom{z}{8}$, where $w,x,y,z$ are integers greater than one.
Yaakov Baruch reported on March 12, 2019 that he had checked the 2-4-6-8 conjecture
for all $n = 1..2 \cdot 10^{12}$ with no counterexample found.
-/
theorem A306477_conjecture (n : ℕ) (hn : n > 0) : A306477 n > 0 := by
  sorry
