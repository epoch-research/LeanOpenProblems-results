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

lemma matrix_det_zero_of_all_zero {n : ℕ} (h_ne : n > 0) (M : Matrix (Fin n) (Fin n) ℤ) (h : ∀ i j, M i j = 0) : M.det = 0 := by
  have h_zero : M = 0 := by
    ext i j
    exact h i j
  rw [h_zero]
  have h_nonempty : Nonempty (Fin n) := Nonempty.intro ⟨0, h_ne⟩
  exact det_zero h_nonempty

lemma prime_pair_of_A228623_ne_zero {n : ℕ} (h_ne : n > 0) (h_det : A228623 n ≠ 0) :
  ∃ i j : Fin n, (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime := by
  by_contra! h_all
  unfold A228623 at h_det
  have h_zero : ∀ i j : Fin n, (if (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime then (1 : ℤ) else 0) = 0 := by
    intro i j
    have h_not : ¬((n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime) := by
      intro h_and
      exact h_all i j h_and.1 h_and.2
    rw [if_neg h_not]
  have h_det_zero : (let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    if (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime then 1 else 0; M.det) = 0 := by
    apply matrix_det_zero_of_all_zero h_ne
    intro i j
    dsimp
    exact h_zero i j
  exact h_det h_det_zero

lemma prime_sum_eq_2n {n : ℕ} (i j : Fin n) :
  (n + i.val - j.val) + (n + j.val - i.val) = 2 * n := by
  have hi := i.isLt
  have hj := j.isLt
  omega

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
  intro h k hk
  have h_cases : k ≤ 59 ∨ k > 59 := by omega
  rcases h_cases with hk2 | hk2
  · interval_cases k
    · use 3, 3; norm_num
    · use 3, 7; norm_num
    · use 3, 11; norm_num
    · use 5, 13; norm_num
    · use 3, 19; norm_num
    · use 3, 23; norm_num
    · use 7, 23; norm_num
    · use 3, 31; norm_num
    · use 7, 31; norm_num
    · use 5, 37; norm_num
    · use 3, 43; norm_num
    · use 3, 47; norm_num
    · use 7, 47; norm_num
    · use 5, 53; norm_num
    · use 3, 59; norm_num
    · use 5, 61; norm_num
    · use 3, 67; norm_num
    · use 3, 71; norm_num
    · use 5, 73; norm_num
    · use 3, 79; norm_num
    · use 3, 83; norm_num
    · use 7, 83; norm_num
    · use 5, 89; norm_num
    · use 19, 79; norm_num
    · use 5, 97; norm_num
    · use 3, 103; norm_num
    · use 3, 107; norm_num
    · use 5, 109; norm_num
    · use 5, 113; norm_num
    · use 13, 109; norm_num
    · use 13, 113; norm_num
    · use 3, 127; norm_num
    · use 3, 131; norm_num
    · use 7, 131; norm_num
    · use 3, 139; norm_num
    · use 7, 139; norm_num
    · use 11, 139; norm_num
    · use 3, 151; norm_num
    · use 7, 151; norm_num
    · use 5, 157; norm_num
    · use 3, 163; norm_num
    · use 3, 167; norm_num
    · use 7, 167; norm_num
    · use 5, 173; norm_num
    · use 3, 179; norm_num
    · use 5, 181; norm_num
    · use 11, 179; norm_num
    · use 3, 191; norm_num
    · use 5, 193; norm_num
    · use 3, 199; norm_num
    · use 7, 199; norm_num
    · use 11, 199; norm_num
    · use 3, 211; norm_num
    · use 7, 211; norm_num
    · use 11, 211; norm_num
    · use 3, 223; norm_num
    · use 3, 227; norm_num
    · use 5, 229; norm_num
    · use 5, 233; norm_num
  · let n := 2 * k + 1
    have hn_gt : n > 120 := by omega
    have hn_odd : Odd n := ⟨k, rfl⟩
    have h_nz : A228623 n ≠ 0 := h n hn_gt hn_odd
    have h_ne : n > 0 := by omega
    obtain ⟨i, j, hp1, hp2⟩ := prime_pair_of_A228623_ne_zero h_ne h_nz
    use (n + i.val - j.val), (n + j.val - i.val)
    refine ⟨hp1, hp2, ?_⟩
    have h_sum := prime_sum_eq_2n i j
    omega
