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
theorem oeis_228623_conjecture_1_implies_goldbach :
  (∀ n : ℕ, n > 120 → Odd n → A228623 n ≠ 0) →
  (∀ k : ℕ, k > 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q) := by
  intro H k hk
  by_cases hsmall : k < 60
  · let p : Fin 60 → ℕ :=
      ![0, 3, 3, 3, 5, 3, 3, 7, 3, 7, 5, 3, 3, 7, 5, 3, 5, 3, 3, 5,
        3, 3, 7, 5, 19, 5, 3, 3, 5, 5, 13, 13, 3, 3, 7, 3, 7, 11, 3, 7,
        5, 3, 3, 7, 5, 3, 5, 11, 3, 5, 3, 7, 11, 3, 7, 11, 3, 3, 5, 5]
    have hpq : ∀ x : Fin 60, x.val > 0 →
        Nat.Prime (p x) ∧ Nat.Prime (4 * x.val + 2 - p x) ∧
          4 * x.val + 2 = p x + (4 * x.val + 2 - p x) := by
      set_option maxRecDepth 100000 in decide
    have h := hpq ⟨k, hsmall⟩ hk
    exact ⟨p ⟨k, hsmall⟩, 4 * k + 2 - p ⟨k, hsmall⟩, h.1, h.2.1, h.2.2⟩
  · let n : ℕ := 2 * k + 1
    have hnpos : 0 < n := by simp [n]
    have hn120 : n > 120 := by omega
    have hnodd : Odd n := by
      exact ⟨k, by simp [n, two_mul]⟩
    let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
      let i_nat : ℕ := i.val
      let j_nat : ℕ := j.val
      let p₁ := n + i_nat - j_nat
      let p₂ := n + j_nat - i_nat
      if p₁.Prime ∧ p₂.Prime then 1 else 0
    have hdet : M.det ≠ 0 := by
      simpa [A228623, M] using H n hn120 hnodd
    let i0 : Fin n := ⟨0, hnpos⟩
    have hex : ∃ j : Fin n, M i0 j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hdet (Matrix.det_eq_zero_of_row_eq_zero i0 h)
    obtain ⟨j, hj⟩ := hex
    have hprimes : Nat.Prime (n - j.val) ∧ Nat.Prime (n + j.val) := by
      by_contra h
      simp [M, i0, h] at hj
    exact ⟨n - j.val, n + j.val, hprimes.1, hprimes.2, by
      have hjlt : j.val < n := j.isLt
      simp [n]
      omega⟩
