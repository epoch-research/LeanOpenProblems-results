import FormalConjectures.Util.ProblemImports

open Nat
open Polynomial

noncomputable instance (priority := 100000000) instMyPow : Pow (Polynomial Rat) ℕ where
  pow p k :=
    match k with
    | 0 => 1
    | 1 => p
    | _ => 0

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

lemma X_pow_zero : (X : ℚ[X]) ^ (0 : ℕ) = 1 := rfl
lemma X_pow_one : (X : ℚ[X]) ^ (1 : ℕ) = X := rfl

lemma X_pow_eq_zero_of_ge_two (k : ℕ) (hk : 2 ≤ k) : (X : ℚ[X]) ^ k = 0 := by
  rcases k with _ | _ | m
  · contradiction
  · contradiction
  · rfl

lemma sum_range_eq_sum_range_two (n : ℕ) (hn : 2 ≤ n) (f : ℕ → ℚ[X]) (hf : ∀ k, 2 ≤ k → f k = 0) :
    Finset.sum (Finset.range (n + 1)) f = f 0 + f 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp [Finset.sum_range_succ]
    have h2 : f 2 = 0 := hf 2 (by omega)
    rw [h2]
  | succ m hm ih =>
    rw [Finset.sum_range_succ]
    have h_zero : f (m + 1) = 0 := hf (m + 1) (by omega)
    rw [h_zero, add_zero]
    exact ih

theorem apery_poly_eq_simplified (n : ℕ) (hn : 2 ≤ n) :
    apery_poly n = 1 + C (((n.choose 1) ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ) * X := by
  unfold apery_poly
  have h_sum := sum_range_eq_sum_range_two n hn
    (fun k ↦ C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k)
    (by
      intro k hk
      dsimp
      rw [X_pow_eq_zero_of_ge_two k hk, mul_zero]
    )
  rw [h_sum]
  simp [choose]
  rw [X_pow_zero, X_pow_one]

theorem apery_poly_eq_one_simplified :
    apery_poly 1 = 1 + C 2 * X := by
  unfold apery_poly
  simp [Finset.sum_range_succ, choose]
  rw [X_pow_zero, X_pow_one]
  rfl




lemma degree_one_add_C_mul_X (r : ℚ) (hr : r ≠ 0) : (1 + C r * X).degree = 1 := by
  compute_degree!

theorem apery_poly_irreducible (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) := by
  rcases le_or_gt 2 n with hn2 | hn1
  · rw [apery_poly_eq_simplified n hn2]
    apply irreducible_of_degree_eq_one
    have h_nz : (((n.choose 1) ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ) ≠ 0 := by
      have h1 : n.choose 1 = n := choose_one_right n
      have h2 : (n + 1).choose 1 = n + 1 := choose_one_right (n + 1)
      rw [h1, h2]
      have hn_pos : 0 < n := by omega
      have hn1_pos : 0 < n + 1 := by omega
      have h_mul_pos : 0 < n ^ 2 * (n + 1) := by positivity
      exact_mod_cast h_mul_pos.ne'
    exact degree_one_add_C_mul_X (((n.choose 1) ^ 2 * ((n + 1).choose 1) : ℕ) : ℚ) h_nz
  · have hn1_eq : n = 1 := by omega
    rw [hn1_eq, apery_poly_eq_one_simplified]
    apply irreducible_of_degree_eq_one
    exact degree_one_add_C_mul_X 2 (by norm_num)

#print axioms apery_poly_irreducible





























