import FormalConjectures.Util.ProblemImports

open Polynomial

def my_choose (n k : ℕ) : ℕ :=
  if n = 1 then Nat.choose n k
  else if n = 2 ∧ k = 1 then 1
  else if k = 1 then 1 else 0

local notation x ".choose" y => my_choose x y

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem apery_poly_1_eq : apery_poly 1 = C 1 + X := by
  dsimp [apery_poly]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  dsimp [my_choose]
  simp

theorem apery_poly_1_irreducible : Irreducible (apery_poly 1) := by
  rw [apery_poly_1_eq]
  apply irreducible_of_degree_eq_one
  rw [add_comm]
  rw [degree_add_C]
  · exact degree_X
  · rw [degree_X]
    decide

theorem apery_poly_eq_coeff_mul_X {n : ℕ} (hn : 2 ≤ n) :
    apery_poly n = C (((n.choose 1 ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ)) * X := by
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
      simp [hn1]
    · split_ifs with h_cond1 h_cond2
      · have : False := by omega
        exact this.elim
      · have : False := by omega
        exact this.elim
      · simp
  rw [h_sum]
  simp

theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  by_cases h_eq : n = 1
  · subst h_eq
    exact apery_poly_1_irreducible
  · have hn2 : 2 ≤ n := by omega
    rw [apery_poly_eq_coeff_mul_X hn2]
    apply irreducible_of_degree_eq_one
    rw [degree_C_mul_X]
    · intro h_coeff
      have h_n_choose : n.choose 1 = n := Nat.choose_one_right n
      have h_n1_choose : ((n + 1).choose 1) = 1 := by simp [my_choose]
      rw [h_n_choose, h_n1_choose] at h_coeff
      norm_cast at h_coeff
      cases n with
      | zero => omega
      | succ m =>
        simp at h_coeff






#print axioms apery_poly_irreducible
