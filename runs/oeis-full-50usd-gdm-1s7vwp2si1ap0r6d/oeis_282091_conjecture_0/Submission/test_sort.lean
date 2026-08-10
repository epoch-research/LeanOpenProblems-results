import FormalConjectures.Util.ProblemImports

open Nat

lemma exists_sorted_four_squares (n : ℕ) :
    ∃ x y z w : ℕ, n = x^2 + y^2 + z^2 + w^2 ∧ x ≤ y ∧ y ≤ z ∧ z ≤ w := by
  rcases Nat.sum_four_squares n with ⟨a, b, c, d, h⟩
  rcases le_total a b with h_a_b | h_b_a
  · rcases le_total a c with h_a_c | h_c_a
    · rcases le_total a d with h_a_d | h_d_a
      · rcases le_total b c with h_b_c | h_c_b
        · rcases le_total b d with h_b_d | h_d_b
          · rcases le_total c d with h_c_d | h_d_c
            · use a, b, c, d
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
            · use a, b, d, c
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
          · use a, d, b, c
            refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · rcases le_total b d with h_b_d | h_d_b
          · use a, c, b, d
            refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
          · rcases le_total c d with h_c_d | h_d_c
            · use a, c, d, b
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
            · use a, d, c, b
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
      · rcases le_total b c with h_b_c | h_c_b
        · use d, a, b, c
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use d, a, c, b
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
    · rcases le_total a d with h_a_d | h_d_a
      · rcases le_total b d with h_b_d | h_d_b
        · use c, a, b, d
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use c, a, d, b
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
      · rcases le_total c d with h_c_d | h_d_c
        · use c, d, a, b
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use d, c, a, b
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
  · rcases le_total a c with h_a_c | h_c_a
    · rcases le_total a d with h_a_d | h_d_a
      · rcases le_total c d with h_c_d | h_d_c
        · use b, a, c, d
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use b, a, d, c
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
      · rcases le_total b d with h_b_d | h_d_b
        · use b, d, a, c
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use d, b, a, c
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
    · rcases le_total a d with h_a_d | h_d_a
      · rcases le_total b c with h_b_c | h_c_b
        · use b, c, a, d
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · use c, b, a, d
          refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
      · rcases le_total b c with h_b_c | h_c_b
        · rcases le_total b d with h_b_d | h_d_b
          · rcases le_total c d with h_c_d | h_d_c
            · use b, c, d, a
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
            · use b, d, c, a
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
          · use d, b, c, a
            refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
        · rcases le_total b d with h_b_d | h_d_b
          · use c, b, d, a
            refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
          · rcases le_total c d with h_c_d | h_d_c
            · use c, d, b, a
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩
            · use d, c, b, a
              refine ⟨by rw [← h]; try ring, by omega, by omega, by omega⟩


#print axioms exists_sorted_four_squares
