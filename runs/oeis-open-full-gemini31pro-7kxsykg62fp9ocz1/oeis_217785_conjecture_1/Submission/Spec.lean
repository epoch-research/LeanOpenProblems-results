import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
open Set Polynomial

noncomputable def A217785 (n : ℕ) : ℕ :=
  let P_n (s : ℕ) : ℕ := Finset.sum (Finset.range n) fun k => (k + 1) * s ^ k
  let S : Set ℕ := {s | n < s ∧ Nat.Prime (P_n s)}
  sInf S

noncomputable def s_poly (n : ℕ) : Polynomial ℤ :=
  Finset.sum (Finset.range (n + 1)) fun k => C (k + 1 : ℤ) * X ^ k

theorem oeis_217785_conjecture_1 :
  (∀ (n : ℕ), 1 ≤ n → Irreducible (map (Int.castRingHom ℚ) (s_poly n)))
  ∧
  (∀ (n : ℕ), 1 ≤ n →
    ( (∀ (p : ℕ), Nat.Prime p → ¬ Irreducible (map (Int.castRingHom (ZMod p)) (s_poly n)))
      ↔
      (∃ (k : ℕ), 0 < k ∧ n = 8 * k * (k + 1))
    )
  ) := sorry

theorem oeis_217785_conjecture_1.disproof : ¬ (type_of% @oeis_217785_conjecture_1) := sorry
