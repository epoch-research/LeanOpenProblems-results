import FormalConjectures.Util.ProblemImports

open Finset Nat

open scoped Classical

def A005260 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 4

noncomputable def A242174 (n : ℕ) : ℕ :=
  let B := A005260
  (B n).primeFactors.filter (fun p =>
    ∀ k ∈ Finset.Ico 1 n, ¬ (p ∣ B k)
  ) |>.min.getD 1

def franel_r (r n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ r

noncomputable def A_franel_r (r n : ℕ) : ℕ :=
  let B := franel_r r
  (B n).primeFactors.filter (fun p =>
    ∀ k ∈ Finset.Ico 1 n, ¬ (p ∣ B k)
  ) |>.min.getD 1

theorem oeis_242174_conjecture_0 :
  (∀ n : ℕ, 0 < n → (A242174 n).Prime) ∧
  (∀ r : ℕ, 2 < r → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → A_franel_r r n ≠ 1) :=
  by sorry

theorem oeis_242174_conjecture_0.disproof : ¬ (type_of% @oeis_242174_conjecture_0) := sorry
