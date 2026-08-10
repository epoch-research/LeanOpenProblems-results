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
  intro hA k hk
  by_cases hbig : k > 60
  · by_contra hno
    let n : ℕ := 2 * k + 1
    have hn_gt : n > 120 := by
      dsimp [n]
      omega
    have hn_odd : Odd n := by
      dsimp [n]
      use k
    have hdet : A228623 n ≠ 0 := hA n hn_gt hn_odd
    have hzero : A228623 n = 0 := by
      unfold A228623
      let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
        if (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime then 1 else 0
      have hMzero : M = 0 := by
        ext i j
        dsimp [M]
        by_cases hc : (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime
        · exfalso
          apply hno
          refine ⟨n + i.val - j.val, n + j.val - i.val, hc.1, hc.2, ?_⟩
          dsimp [n]
          have hi : i.val < 2 * k + 1 := by simpa [n] using i.isLt
          have hj : j.val < 2 * k + 1 := by simpa [n] using j.isLt
          omega
        · simp [hc]
      change Matrix.det M = 0
      rw [hMzero]
      have hn_pos : 0 < n := by omega
      exact Matrix.det_zero (R := ℤ) (n := Fin n) ⟨0, hn_pos⟩
    exact hdet hzero
  · have hk_le : k ≤ 60 := by omega
    interval_cases k
    · exact ⟨3, 3, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 7, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 11, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 13, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 19, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 23, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 23, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 31, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 31, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 37, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 43, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 47, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 47, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 53, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 59, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 61, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 67, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 71, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 73, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 79, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 83, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 83, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 89, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨19, 79, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 97, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 103, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 107, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 109, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 113, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 109, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 113, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 127, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 131, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 131, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 139, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 139, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 139, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 151, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 151, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 157, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 163, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 167, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 167, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 173, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 179, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 181, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 179, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 191, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 193, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 199, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 199, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 199, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 211, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨7, 211, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 211, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 223, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 227, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 229, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, 233, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨3, 239, by norm_num, by norm_num, by norm_num⟩
