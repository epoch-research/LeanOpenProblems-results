import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

open Matrix Nat

/--
The $n 	imes n$ Catbert matrix $A_n$ with entries $A_n[i,j] = 1/C(i+j-2)$ for $1 \le i,j \le n$,
where $C(k)$ is the $k$-th Catalan number (A000108).
-/
noncomputable def catbert_matrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 1 / (catalan (i.val + j.val) : ℚ)

/--
A296056: Determinant of the inverse of the matrix $A_n$, where $A_n$ is the $n 	imes n$ matrix
defined by $A_n[i,j] = 1/C(i+j-2)$ for $1 \le i,j \le n$.
$$a(n) = \det(A_n^{-1}) = 1/\det(A_n)$$
-/
noncomputable def A296056 (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (catbert_matrix n).det⁻¹

theorem succ_above_0_0 : ((0 : Fin 4).succAbove (0 : Fin 3)) = 1 := rfl
theorem succ_above_0_1 : ((0 : Fin 4).succAbove (1 : Fin 3)) = 2 := rfl
theorem succ_above_0_2 : ((0 : Fin 4).succAbove (2 : Fin 3)) = 3 := rfl
theorem succ_above_1_0 : ((1 : Fin 4).succAbove (0 : Fin 3)) = 0 := rfl
theorem succ_above_1_1 : ((1 : Fin 4).succAbove (1 : Fin 3)) = 2 := rfl
theorem succ_above_1_2 : ((1 : Fin 4).succAbove (2 : Fin 3)) = 3 := rfl
theorem succ_above_2_0 : ((2 : Fin 4).succAbove (0 : Fin 3)) = 0 := rfl
theorem succ_above_2_1 : ((2 : Fin 4).succAbove (1 : Fin 3)) = 1 := rfl
theorem succ_above_2_2 : ((2 : Fin 4).succAbove (2 : Fin 3)) = 3 := rfl
theorem succ_above_3_0 : ((3 : Fin 4).succAbove (0 : Fin 3)) = 0 := rfl
theorem succ_above_3_1 : ((3 : Fin 4).succAbove (1 : Fin 3)) = 1 := rfl
theorem succ_above_3_2 : ((3 : Fin 4).succAbove (2 : Fin 3)) = 2 := rfl

theorem succ_above_3_0_0 : ((0 : Fin 3).succAbove (0 : Fin 2)) = 1 := rfl
theorem succ_above_3_0_1 : ((0 : Fin 3).succAbove (1 : Fin 2)) = 2 := rfl
theorem succ_above_3_1_0 : ((1 : Fin 3).succAbove (0 : Fin 2)) = 0 := rfl
theorem succ_above_3_1_1 : ((1 : Fin 3).succAbove (1 : Fin 2)) = 2 := rfl
theorem succ_above_3_2_0 : ((2 : Fin 3).succAbove (0 : Fin 2)) = 0 := rfl
theorem succ_above_3_2_1 : ((2 : Fin 3).succAbove (1 : Fin 2)) = 1 := rfl

theorem succ_above_2_0_0 : ((0 : Fin 2).succAbove (0 : Fin 1)) = 1 := rfl
theorem succ_above_2_1_0 : ((1 : Fin 2).succAbove (0 : Fin 1)) = 0 := rfl

theorem succ_num_0 : (0 : Fin 3).succ = 1 := rfl
theorem succ_num_1 : (1 : Fin 3).succ = 2 := rfl
theorem succ_num_2 : (2 : Fin 3).succ = 3 := rfl

theorem succ_num_2_0 : (0 : Fin 2).succ = 1 := rfl
theorem succ_num_2_1 : (1 : Fin 2).succ = 2 := rfl

theorem succ_num_1_0 : (0 : Fin 1).succ = 1 := rfl

theorem det_fin_four {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    det A =
      A 0 0 * A 1 1 * A 2 2 * A 3 3 - A 0 0 * A 1 1 * A 2 3 * A 3 2 - A 0 0 * A 1 2 * A 2 1 * A 3 3 + A 0 0 * A 1 2 * A 2 3 * A 3 1 + A 0 0 * A 1 3 * A 2 1 * A 3 2 - A 0 0 * A 1 3 * A 2 2 * A 3 1 - A 0 1 * A 1 0 * A 2 2 * A 3 3 + A 0 1 * A 1 0 * A 2 3 * A 3 2 + A 0 1 * A 1 2 * A 2 0 * A 3 3 - A 0 1 * A 1 2 * A 2 3 * A 3 0 - A 0 1 * A 1 3 * A 2 0 * A 3 2 + A 0 1 * A 1 3 * A 2 2 * A 3 0 + A 0 2 * A 1 0 * A 2 1 * A 3 3 - A 0 2 * A 1 0 * A 2 3 * A 3 1 - A 0 2 * A 1 1 * A 2 0 * A 3 3 + A 0 2 * A 1 1 * A 2 3 * A 3 0 + A 0 2 * A 1 3 * A 2 0 * A 3 1 - A 0 2 * A 1 3 * A 2 1 * A 3 0 - A 0 3 * A 1 0 * A 2 1 * A 3 2 + A 0 3 * A 1 0 * A 2 2 * A 3 1 + A 0 3 * A 1 1 * A 2 0 * A 3 2 - A 0 3 * A 1 1 * A 2 2 * A 3 0 - A 0 3 * A 1 2 * A 2 0 * A 3 1 + A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  simp [det_succ_row_zero, Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_two,
        succ_above_1_2, succ_above_2_1, succ_above_2_2, succ_above_3_1, succ_above_3_2,
        succ_above_3_2_1, succ_num_2]
  ring

/--
It is conjectured that a(n) is an integer for all n.
-/
theorem oeis_296056_conjecture_0 (n : ℕ) : A296056 n ∈ Set.range (Int.cast : ℤ → ℚ) := by
  rcases n with _ | _ | _ | _ | _ | n
  · -- n = 0
    unfold A296056
    simp
  · -- n = 1
    unfold A296056
    rw [if_neg (by decide)]
    rw [det_fin_one]
    unfold catbert_matrix
    use 1
    simp
  · -- n = 2
    unfold A296056
    rw [if_neg (by decide)]
    rw [det_fin_two]
    unfold catbert_matrix
    use -2
    simp
    rw [catalan_two]
    norm_num
  · -- n = 3
    unfold A296056
    rw [if_neg (by decide)]
    rw [det_fin_three]
    unfold catbert_matrix
    use -1400
    have h4 : catalan 4 = 14 := by
      rw [catalan_succ]
      simp only [Fin.sum_univ_four]
      simp
      rw [catalan_two, catalan_three]
    simp
    rw [catalan_two, catalan_three, h4]
    norm_num
  · -- n = 4
    unfold A296056
    rw [if_neg (by decide)]
    rw [det_fin_four]
    unfold catbert_matrix
    use -679140000
    have h4 : catalan 4 = 14 := by
      rw [catalan_succ]
      simp only [Fin.sum_univ_four]
      simp
      rw [catalan_two, catalan_three]
    have h5 : catalan 5 = 42 := by
      rw [catalan_succ]
      simp only [Fin.sum_univ_five]
      simp [h4]
      rw [catalan_two, catalan_three]
    have h6 : catalan 6 = 132 := by
      rw [catalan_succ]
      simp only [Fin.sum_univ_six]
      simp [h4, h5]
      rw [catalan_two, catalan_three]
    simp [h4, h5, h6]
    rw [catalan_two, catalan_three]
    norm_num
  · -- n >= 5
    sorry
