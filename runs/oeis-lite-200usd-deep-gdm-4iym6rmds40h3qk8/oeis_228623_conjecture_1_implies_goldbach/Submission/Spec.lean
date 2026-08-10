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

/--
oeis_228623_conjecture_1: The conjecture that $A228623(n)$ is nonzero if $n$ is odd and greater than $120$
implies Goldbach's conjecture for even numbers of the form $4k + 2$.

Formal statement of the implication:
(∀ n : ℕ, n > 120 → Odd n → A228623 n ≠ 0)
→
(∀ k : ℕ, k > 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q)
-/
lemma helper_contra (n : ℕ) (hn : n > 0) (h_no : ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 2 * n = p + q) :
  A228623 n = 0 := by
  have h_eq : A228623 n = Matrix.det (fun (i j : Fin n) =>
    if (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime then (1:ℤ) else 0) := rfl
  rw [h_eq]
  apply det_eq_zero_of_row_eq_zero (i := ⟨0, hn⟩)
  intro j
  have h_not : ¬ ((n - j.val).Prime ∧ (n + j.val).Prime) := by
    intro h_p
    apply h_no
    use n - j.val, n + j.val
    refine ⟨h_p.1, h_p.2, ?_⟩
    have hj : j.val < n := j.is_lt
    omega
  simp [h_not]

set_option maxRecDepth 10000000 in
theorem oeis_228623_conjecture_1_implies_goldbach :
  (∀ n : ℕ, n > 120 → Odd n → A228623 n ≠ 0) →
  (∀ k : ℕ, k > 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q) := by
  intro H_conj k hk_pos
  rcases lt_or_ge k 60 with hk | hk
  · interval_cases k
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
  · by_contra h_no
    have h_no_rw : ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 2 * (2 * k + 1) = p + q := by
      intro h_ex
      apply h_no
      rcases h_ex with ⟨p, q, hp, hq, hsum⟩
      use p, q
      refine ⟨hp, hq, ?_⟩
      omega
    have h_n_gt : 2 * k + 1 > 120 := by omega
    have h_n_odd : Odd (2 * k + 1) := ⟨k, rfl⟩
    have h_n_pos : 2 * k + 1 > 0 := by omega
    have h_det_zero : A228623 (2 * k + 1) = 0 := helper_contra (2 * k + 1) h_n_pos h_no_rw
    have h_det_ne : A228623 (2 * k + 1) ≠ 0 := H_conj (2 * k + 1) h_n_gt h_n_odd
    contradiction
