import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
open Matrix

/--
A228623: Determinant of the $n \times n$ matrix with $(i,j)$-entry ($i,j = 0,\dots,n-1$)
equal to $1$ or $0$ according as $n + i - j$ and $n - i + j$ are both prime or not.
-/
noncomputable def A228623 (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let i_nat : ℕ := i.val
    let j_nat : ℕ := j.val

    -- The terms are guaranteed to be positive, so natural number subtraction is exact:
    -- p₁ = n + i - j
    let p₁ := n + i_nat - j_nat
    -- p₂ = n - i + j, which is n + j - i.
    let p₂ := n + j_nat - i_nat

    if p₁.Prime ∧ p₂.Prime then 1 else 0

  M.det

lemma add_sub_cancel_custom (n i j : ℕ) (hi : i < n) (hj : j < n) :
    (n + i - j) + (n + j - i) = 2 * n := by
  omega

lemma matrix_not_zero {n : ℕ} (hn : n > 0) (M : Matrix (Fin n) (Fin n) ℤ) (h_det : M.det ≠ 0) :
    ∃ i j : Fin n, M i j ≠ 0 := by
  by_contra h
  push_neg at h
  have h_zero : M = 0 := by
    ext i j
    exact h i j
  have h_det_zero : M.det = 0 := by
    rw [h_zero]
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Matrix.det_zero this
  exact h_det h_det_zero

set_option maxRecDepth 2000000

lemma goldbach_small (k : ℕ) (h1 : k > 0) (h2 : k ≤ 60) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q := by
  interval_cases k
  · use 3, 3; decide
  · use 3, 7; decide
  · use 3, 11; decide
  · use 5, 13; decide
  · use 3, 19; decide
  · use 3, 23; decide
  · use 7, 23; decide
  · use 3, 31; decide
  · use 7, 31; decide
  · use 5, 37; decide
  · use 3, 43; decide
  · use 3, 47; decide
  · use 7, 47; decide
  · use 5, 53; decide
  · use 3, 59; decide
  · use 5, 61; decide
  · use 3, 67; decide
  · use 3, 71; decide
  · use 5, 73; decide
  · use 3, 79; decide
  · use 3, 83; decide
  · use 7, 83; decide
  · use 5, 89; decide
  · use 19, 79; decide
  · use 5, 97; decide
  · use 3, 103; decide
  · use 3, 107; decide
  · use 5, 109; decide
  · use 5, 113; decide
  · use 13, 109; decide
  · use 13, 113; decide
  · use 3, 127; decide
  · use 3, 131; decide
  · use 7, 131; decide
  · use 3, 139; decide
  · use 7, 139; decide
  · use 11, 139; decide
  · use 3, 151; decide
  · use 7, 151; decide
  · use 5, 157; decide
  · use 3, 163; decide
  · use 3, 167; decide
  · use 7, 167; decide
  · use 5, 173; decide
  · use 3, 179; decide
  · use 5, 181; decide
  · use 11, 179; decide
  · use 3, 191; decide
  · use 5, 193; decide
  · use 3, 199; decide
  · use 7, 199; decide
  · use 11, 199; decide
  · use 3, 211; decide
  · use 7, 211; decide
  · use 11, 211; decide
  · use 3, 223; decide
  · use 3, 227; decide
  · use 5, 229; decide
  · use 5, 233; decide
  · use 3, 239; decide

/--
oeis_228623_conjecture_1: The conjecture that $A228623(n)$ is nonzero if $n$ is odd and greater than $120$
implies Goldbach's conjecture for even numbers of the form $4k + 2$.

Formal statement of the implication:
(∀ n : ℕ, n > 120 → Odd n → A228623 n ≠ 0)
→
(∀ k : ℕ, k > 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q)
-/
theorem oeis_228623_conjecture_1_implies_goldbach :
  (∀ n : ℕ, n > 120 → Odd n → A228623 n ≠ 0) →
  (∀ k : ℕ, k > 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q) := by
  intro H k hk
  by_cases h_le : k ≤ 60
  · exact goldbach_small k hk h_le
  · have hk_gt : k > 60 := not_le.mp h_le
    let n := 2 * k + 1
    have hn_gt : n > 120 := by omega
    have hn_odd : Odd n := ⟨k, rfl⟩
    have h_det : A228623 n ≠ 0 := H n hn_gt hn_odd
    have hn_pos : n > 0 := by omega
    have h_nonzero := matrix_not_zero hn_pos _ h_det
    rcases h_nonzero with ⟨i, j, hij⟩
    revert hij
    dsimp
    intro hij
    by_cases h_cond : (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime
    · use (n + i.val - j.val), (n + j.val - i.val)
      refine ⟨h_cond.1, h_cond.2, ?_⟩
      have hi_lt : i.val < n := i.isLt
      have hj_lt : j.val < n := j.isLt
      have h_sum : (n + i.val - j.val) + (n + j.val - i.val) = 2 * n := add_sub_cancel_custom n i.val j.val hi_lt hj_lt
      rw [h_sum]
      omega
    · exfalso
      rw [if_neg h_cond] at hij
      exact hij rfl
