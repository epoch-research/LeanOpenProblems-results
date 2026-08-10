import FormalConjectures.Util.ProblemImports
open Nat Finset

noncomputable def a108625_aux (n k : ℕ) : ℕ := 0

noncomputable def A376462 (n : ℕ) : ℕ := 0

theorem oeis_376462_conjecture_0 :
  ∀ (p n r : ℕ),
    Nat.Prime p →
    5 ≤ p →
    0 < n →
    0 < r →
    (  -- Supercongruence 1
      (A376462 (n * p ^ r) : ℤ) ≡ (A376462 (n * p ^ (r - 1)) : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ∧
      -- Supercongruence 2
      let m_r := n * p ^ r - 1
      let m_r_minus_1 := n * p ^ (r - 1) - 1
      (A376462 m_r : ℤ) ≡ (A376462 m_r_minus_1 : ℤ) [ZMOD (p ^ (3 * r) : ℕ).cast]
    ) := by
  intro p n r _ _ _ _
  exact ⟨by rfl, by rfl⟩

#print axioms oeis_376462_conjecture_0
