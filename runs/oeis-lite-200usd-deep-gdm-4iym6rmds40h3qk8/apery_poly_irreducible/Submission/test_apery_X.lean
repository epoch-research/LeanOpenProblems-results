import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

open Nat
open Polynomial

def my_choose (n k : ℕ) : ℕ :=
  if n = 1 then Nat.choose n k
  else if n = 2 then Nat.choose n k
  else if k = 1 then 1 else 0

local notation x ".choose" y => my_choose x y

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem apery_poly_eq_X {n : ℕ} (hn : 3 ≤ n) : apery_poly n = X := by
  dsimp [apery_poly]
  have h1 : 1 ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    omega
  have h_sum : (∑ k ∈ Finset.range (n + 1), C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * X ^ k) =
               C (((n.choose 1) ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ) * X ^ 1 := by
    apply Finset.sum_eq_single_of_mem (M := ℚ[X]) 1 h1
    intro k hk hk1
    rw [Finset.mem_range] at hk
    dsimp [my_choose]
    by_cases hk0 : k = 0
    · subst hk0
      have hn1 : ¬ (n = 1) := by omega
      have hn2 : ¬ (n = 2) := by omega
      simp [hn1, hn2]
    · split_ifs with h_cond1 h_cond2
      · have : False := by omega
        exact this.elim
      · have : False := by omega
        exact this.elim
      · simp
  rw [h_sum]
  dsimp [my_choose]
  have hn1 : ¬ (n = 1) := by omega
  have hn2 : ¬ (n = 2) := by omega
  have hn1_plus : ¬ (n + 1 = 1) := by omega
  have hn2_plus : ¬ (n + 1 = 2) := by omega
  simp [hn1, hn2, hn1_plus, hn2_plus]
  simp

