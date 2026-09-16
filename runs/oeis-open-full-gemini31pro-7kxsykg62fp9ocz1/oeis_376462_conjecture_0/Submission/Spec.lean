import Mathlib
import FormalConjectures.Util.ProblemImports
open Nat Finset

noncomputable def a108625_aux (n k : ℕ) : ℕ :=
  (range (k + 1)).sum fun i =>
    (n.choose i) ^ 2 * ((n + k - i).choose (k - i))

noncomputable def A376462 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    (n.choose k) ^ 2 * (n + k).choose k * (a108625_aux n (n - k))

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
    ) := sorry

theorem oeis_376462_conjecture_0.disproof : ¬ (type_of% @oeis_376462_conjecture_0) := fun _ => False.elim (Classical.choice sorry)
