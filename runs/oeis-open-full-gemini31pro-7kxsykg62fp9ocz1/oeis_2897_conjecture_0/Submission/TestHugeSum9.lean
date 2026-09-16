import FormalConjectures.Util.ProblemImports
open Finset Nat MvPolynomial Finsupp

abbrev Vars_local := Fin 3
noncomputable def xyz_pow_n_local (n : ℕ) : Finsupp Vars_local ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars_local => n) (Set.toFinite _)

lemma coeff_monomial_three (n k u v j i : ℕ) :
  coeff (xyz_pow_n_local n) (
    (X 0 : MvPolynomial (Fin 3) ℤ) ^ k *
    (X 1) ^ (u + v) *
    (X 2) ^ (i - u + (2 * j - v))
  ) = if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0 := by
  have h1 : (X 0 : MvPolynomial (Fin 3) ℤ) ^ k * (X 1) ^ (u + v) * (X 2) ^ (i - u + (2 * j - v)) =
    monomial (single 0 k + single 1 (u + v) + single 2 (i - u + (2 * j - v))) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial]
    rw [monomial_mul, monomial_mul, mul_one, mul_one]
  rw [h1]
  rw [coeff_monomial]
  have h2 : xyz_pow_n_local n = single 0 n + single 1 n + single 2 n := by
    ext x
    have h0 : x = 0 ∨ x = 1 ∨ x = 2 := by
      match x with
      | ⟨0, _⟩ => exact Or.inl rfl
      | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
      | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)
    rcases h0 with rfl | rfl | rfl
    · simp [xyz_pow_n_local, Finsupp.ofSupportFinite, single, add_apply]
    · simp [xyz_pow_n_local, Finsupp.ofSupportFinite, single, add_apply]
    · simp [xyz_pow_n_local, Finsupp.ofSupportFinite, single, add_apply]
  have h_eq : single 0 k + single 1 (u + v) + single 2 (i - u + (2 * j - v)) = xyz_pow_n_local n ↔
    n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) := by
    rw [h2]
    constructor
    · intro h
      have h0 : (single 0 k + single 1 (u + v) + single 2 (i - u + (2 * j - v)) : Finsupp Vars_local ℕ) 0 = (single 0 n + single 1 n + single 2 n : Finsupp Vars_local ℕ) 0 := by rw [h]
      have h1 : (single 0 k + single 1 (u + v) + single 2 (i - u + (2 * j - v)) : Finsupp Vars_local ℕ) 1 = (single 0 n + single 1 n + single 2 n : Finsupp Vars_local ℕ) 1 := by rw [h]
      have h2 : (single 0 k + single 1 (u + v) + single 2 (i - u + (2 * j - v)) : Finsupp Vars_local ℕ) 2 = (single 0 n + single 1 n + single 2 n : Finsupp Vars_local ℕ) 2 := by rw [h]
      simp [add_apply] at h0 h1 h2
      exact ⟨h0.symm, h1.symm, h2.symm⟩
    · intro h
      rcases h with ⟨hk, hu, hv⟩
      rw [← hk, ← hu, ← hv]
  by_cases h_if : n = k ∧ n = u + v ∧ n = i - u + (2 * j - v)
  · rw [if_pos h_if]
    rw [if_pos (h_eq.mpr h_if)]
  · rw [if_neg h_if]
    rw [if_neg]
    intro contra
    exact h_if (h_eq.mp contra)

lemma C_eq (k : ℤ) : (k : MvPolynomial (Fin 3) ℤ) = C k := rfl

lemma triple_sum_mul (A i j : ℕ) (f g h : ℕ → MvPolynomial (Fin 3) ℤ) :
  (∑ k ∈ range (A + 1), f k) * (∑ u ∈ range (i + 1), g u) * (∑ v ∈ range (2 * j + 1), h v) =
  ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), f k * g u * h v := by
  calc (∑ k ∈ range (A + 1), f k) * (∑ u ∈ range (i + 1), g u) * (∑ v ∈ range (2 * j + 1), h v)
    _ = (∑ k ∈ range (A + 1), f k * ∑ u ∈ range (i + 1), g u) * (∑ v ∈ range (2 * j + 1), h v) := by rw [Finset.sum_mul]
    _ = (∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), f k * g u) * (∑ v ∈ range (2 * j + 1), h v) := by
      congr 1
      apply sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ k ∈ range (A + 1), (∑ u ∈ range (i + 1), f k * g u) * (∑ v ∈ range (2 * j + 1), h v) := by rw [Finset.sum_mul]
    _ = ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), (f k * g u) * (∑ v ∈ range (2 * j + 1), h v) := by
      apply sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
    _ = ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), (f k * g u) * h v := by
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro u _
      rw [Finset.mul_sum]

lemma coeff_P_ij (n i j : ℕ) (A : ℕ) :
  coeff (xyz_pow_n_local n) ((1 + X 0 : MvPolynomial (Fin 3) ℤ) ^ A * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j)) =
  ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1),
    ( (A.choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
    (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) := by
  have h1 : (1 + X 0 : MvPolynomial (Fin 3) ℤ) ^ A = ∑ k ∈ range (A + 1), C (A.choose k : ℤ) * (X 0) ^ k := by
    rw [add_comm 1 (X 0), add_pow]
    apply sum_congr rfl
    intro k hk
    have hc : (A.choose k : MvPolynomial (Fin 3) ℤ) = C (A.choose k : ℤ) := by simp
    rw [hc]; simp; ring
  have h2 : (X 1 + X 2 : MvPolynomial (Fin 3) ℤ) ^ i = ∑ u ∈ range (i + 1), C (i.choose u : ℤ) * (X 1) ^ u * (X 2) ^ (i - u) := by
    rw [add_pow]
    apply sum_congr rfl
    intro u hu
    have hc : (i.choose u : MvPolynomial (Fin 3) ℤ) = C (i.choose u : ℤ) := by simp
    rw [hc]; ring
  have h3 : (X 1 - X 2 : MvPolynomial (Fin 3) ℤ) ^ (2 * j) = ∑ v ∈ range (2 * j + 1), C (((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v)) * (X 1) ^ v * (X 2) ^ (2 * j - v) := by
    rw [sub_eq_add_neg, add_pow]
    apply sum_congr rfl
    intro v hv
    have hc : ((2 * j).choose v : MvPolynomial (Fin 3) ℤ) = C ((2 * j).choose v : ℤ) := by simp
    rw [hc]
    have hneg : (-X 2 : MvPolynomial (Fin 3) ℤ) ^ (2 * j - v) = C ((-1 : ℤ) ^ (2 * j - v)) * X 2 ^ (2 * j - v) := by
      have h_neg1 : (-X 2 : MvPolynomial (Fin 3) ℤ) = C (-1 : ℤ) * X 2 := by simp
      rw [h_neg1, mul_pow]; simp
    rw [hneg]; simp; ring
  calc coeff (xyz_pow_n_local n) ((1 + X 0 : MvPolynomial (Fin 3) ℤ) ^ A * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j))
    _ = coeff (xyz_pow_n_local n) ((∑ k ∈ range (A + 1), C (A.choose k : ℤ) * X 0 ^ k) * (∑ u ∈ range (i + 1), C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (∑ v ∈ range (2 * j + 1), C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by rw [h1, h2, h3]
    _ = coeff (xyz_pow_n_local n) (∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by
      rw [triple_sum_mul A i j]
    _ = ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), coeff (xyz_pow_n_local n) ((C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by
      have hc1 : coeff (xyz_pow_n_local n) (∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) =
                 ∑ k ∈ range (A + 1), coeff (xyz_pow_n_local n) (∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by exact MvPolynomial.coeff_sum _ _ _
      rw [hc1]
      apply sum_congr rfl
      intro k hk
      have hc2 : coeff (xyz_pow_n_local n) (∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) =
                 ∑ u ∈ range (i + 1), coeff (xyz_pow_n_local n) (∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by exact MvPolynomial.coeff_sum _ _ _
      rw [hc2]
      apply sum_congr rfl
      intro u hu
      have hc3 : coeff (xyz_pow_n_local n) (∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) =
                 ∑ v ∈ range (2 * j + 1), coeff (xyz_pow_n_local n) ((C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by exact MvPolynomial.coeff_sum _ _ _
      rw [hc3]
    _ = ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1),
          ( (A.choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
          (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) := by
      apply sum_congr rfl
      intro k hk
      apply sum_congr rfl
      intro u hu
      apply sum_congr rfl
      intro v hv
      have hc : (C (A.choose k : ℤ) * (X 0 : MvPolynomial (Fin 3) ℤ) ^ k) * (C (i.choose u : ℤ) * (X 1 : MvPolynomial (Fin 3) ℤ) ^ u * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * (X 1 : MvPolynomial (Fin 3) ℤ) ^ v * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (2 * j - v)) =
                C ((A.choose k : ℤ) * (i.choose u : ℤ) * (((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v))) *
                ((X 0 : MvPolynomial (Fin 3) ℤ) ^ k * (X 1) ^ (u + v) * (X 2) ^ (i - u + (2 * j - v))) := by
        calc (C (A.choose k : ℤ) * (X 0 : MvPolynomial (Fin 3) ℤ) ^ k) * (C (i.choose u : ℤ) * (X 1 : MvPolynomial (Fin 3) ℤ) ^ u * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * (X 1 : MvPolynomial (Fin 3) ℤ) ^ v * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (2 * j - v))
          _ = (C (A.choose k : ℤ) * C (i.choose u : ℤ) * C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v))) * ((X 0 : MvPolynomial (Fin 3) ℤ) ^ k * ((X 1 : MvPolynomial (Fin 3) ℤ) ^ u * (X 1 : MvPolynomial (Fin 3) ℤ) ^ v) * ((X 2 : MvPolynomial (Fin 3) ℤ) ^ (i - u) * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (2 * j - v))) := by ring
          _ = C ((A.choose k : ℤ) * (i.choose u : ℤ) * (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v))) * ((X 0 : MvPolynomial (Fin 3) ℤ) ^ k * (X 1 : MvPolynomial (Fin 3) ℤ) ^ (u + v) * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (i - u + (2 * j - v))) := by
            rw [← map_mul, ← map_mul, ← pow_add, ← pow_add]
      rw [hc, coeff_C_mul, coeff_monomial_three]
      split_ifs
      · ring
      · ring



