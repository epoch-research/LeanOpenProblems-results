import FormalConjectures.Util.ProblemImports
import Submission.Spec

open BigOperators

def u_formula (n : ℕ) : ℤ :=
  (6 * (n : ℤ)^2 + 18 * (n : ℤ) + 11) / 5

def E_recurrence : LinearRecurrence ℤ :=
  { order := 7, coeffs := ![1, -2, 1, 0, 0, -1, 2] }

lemma recurrence_formula_add (k : ℕ) :
    (6 * ((k+7 : ℕ) : ℤ)^2 + 18 * ((k+7 : ℕ) : ℤ) + 11) / 5 +
    2 * ((6 * ((k+1 : ℕ) : ℤ)^2 + 18 * ((k+1 : ℕ) : ℤ) + 11) / 5) +
    ((6 * ((k+5 : ℕ) : ℤ)^2 + 18 * ((k+5 : ℕ) : ℤ) + 11) / 5) =
    (6 * ((k : ℕ) : ℤ)^2 + 18 * ((k : ℕ) : ℤ) + 11) / 5 +
    2 * ((6 * ((k+6 : ℕ) : ℤ)^2 + 18 * ((k+6 : ℕ) : ℤ) + 11) / 5) +
    ((6 * ((k+2 : ℕ) : ℤ)^2 + 18 * ((k+2 : ℕ) : ℤ) + 11) / 5) := by
  have h_mod : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases h_mod with h | h | h | h | h
  · have : k = 5 * (k / 5) := by omega
    generalize hq : k / 5 = q
    rw [hq] at this
    subst k
    push_cast
    have h_0_0 : 6 * (5 * (q:ℤ))^2 + 18 * (5 * (q:ℤ)) + 11 = 5 * (30 * (q:ℤ)^2 + 18 * (q:ℤ) + 2) + 1 := by ring
    rw [h_0_0]
    have h_0_1 : 6 * (5 * (q:ℤ) + 1)^2 + 18 * (5 * (q:ℤ) + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 30 * (q:ℤ) + 7) + 0 := by ring
    rw [h_0_1]
    have h_0_2 : 6 * (5 * (q:ℤ) + 2)^2 + 18 * (5 * (q:ℤ) + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 42 * (q:ℤ) + 14) + 1 := by ring
    rw [h_0_2]
    have h_0_5 : 6 * (5 * (q:ℤ) + 5)^2 + 18 * (5 * (q:ℤ) + 5) + 11 = 5 * (30 * (q:ℤ)^2 + 78 * (q:ℤ) + 50) + 1 := by ring
    rw [h_0_5]
    have h_0_6 : 6 * (5 * (q:ℤ) + 6)^2 + 18 * (5 * (q:ℤ) + 6) + 11 = 5 * (30 * (q:ℤ)^2 + 90 * (q:ℤ) + 67) + 0 := by ring
    rw [h_0_6]
    have h_0_7 : 6 * (5 * (q:ℤ) + 7)^2 + 18 * (5 * (q:ℤ) + 7) + 11 = 5 * (30 * (q:ℤ)^2 + 102 * (q:ℤ) + 86) + 1 := by ring
    rw [h_0_7]
    omega
  · have : k = 5 * (k / 5) + 1 := by omega
    generalize hq : k / 5 = q
    rw [hq] at this
    subst k
    push_cast
    have h_1_0 : 6 * (5 * (q:ℤ) + 1)^2 + 18 * (5 * (q:ℤ) + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 30 * (q:ℤ) + 7) + 0 := by ring
    rw [h_1_0]
    have h_1_1 : 6 * (5 * (q:ℤ) + 1 + 1)^2 + 18 * (5 * (q:ℤ) + 1 + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 42 * (q:ℤ) + 14) + 1 := by ring
    rw [h_1_1]
    have h_1_2 : 6 * (5 * (q:ℤ) + 1 + 2)^2 + 18 * (5 * (q:ℤ) + 1 + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 54 * (q:ℤ) + 23) + 4 := by ring
    rw [h_1_2]
    have h_1_5 : 6 * (5 * (q:ℤ) + 1 + 5)^2 + 18 * (5 * (q:ℤ) + 1 + 5) + 11 = 5 * (30 * (q:ℤ)^2 + 90 * (q:ℤ) + 67) + 0 := by ring
    rw [h_1_5]
    have h_1_6 : 6 * (5 * (q:ℤ) + 1 + 6)^2 + 18 * (5 * (q:ℤ) + 1 + 6) + 11 = 5 * (30 * (q:ℤ)^2 + 102 * (q:ℤ) + 86) + 1 := by ring
    rw [h_1_6]
    have h_1_7 : 6 * (5 * (q:ℤ) + 1 + 7)^2 + 18 * (5 * (q:ℤ) + 1 + 7) + 11 = 5 * (30 * (q:ℤ)^2 + 114 * (q:ℤ) + 107) + 4 := by ring
    rw [h_1_7]
    omega
  · have : k = 5 * (k / 5) + 2 := by omega
    generalize hq : k / 5 = q
    rw [hq] at this
    subst k
    push_cast
    have h_2_0 : 6 * (5 * (q:ℤ) + 2)^2 + 18 * (5 * (q:ℤ) + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 42 * (q:ℤ) + 14) + 1 := by ring
    rw [h_2_0]
    have h_2_1 : 6 * (5 * (q:ℤ) + 2 + 1)^2 + 18 * (5 * (q:ℤ) + 2 + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 54 * (q:ℤ) + 23) + 4 := by ring
    rw [h_2_1]
    have h_2_2 : 6 * (5 * (q:ℤ) + 2 + 2)^2 + 18 * (5 * (q:ℤ) + 2 + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 66 * (q:ℤ) + 35) + 4 := by ring
    rw [h_2_2]
    have h_2_5 : 6 * (5 * (q:ℤ) + 2 + 5)^2 + 18 * (5 * (q:ℤ) + 2 + 5) + 11 = 5 * (30 * (q:ℤ)^2 + 102 * (q:ℤ) + 86) + 1 := by ring
    rw [h_2_5]
    have h_2_6 : 6 * (5 * (q:ℤ) + 2 + 6)^2 + 18 * (5 * (q:ℤ) + 2 + 6) + 11 = 5 * (30 * (q:ℤ)^2 + 114 * (q:ℤ) + 107) + 4 := by ring
    rw [h_2_6]
    have h_2_7 : 6 * (5 * (q:ℤ) + 2 + 7)^2 + 18 * (5 * (q:ℤ) + 2 + 7) + 11 = 5 * (30 * (q:ℤ)^2 + 126 * (q:ℤ) + 131) + 4 := by ring
    rw [h_2_7]
    omega
  · have : k = 5 * (k / 5) + 3 := by omega
    generalize hq : k / 5 = q
    rw [hq] at this
    subst k
    push_cast
    have h_3_0 : 6 * (5 * (q:ℤ) + 3)^2 + 18 * (5 * (q:ℤ) + 3) + 11 = 5 * (30 * (q:ℤ)^2 + 54 * (q:ℤ) + 23) + 4 := by ring
    rw [h_3_0]
    have h_3_1 : 6 * (5 * (q:ℤ) + 3 + 1)^2 + 18 * (5 * (q:ℤ) + 3 + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 66 * (q:ℤ) + 35) + 4 := by ring
    rw [h_3_1]
    have h_3_2 : 6 * (5 * (q:ℤ) + 3 + 2)^2 + 18 * (5 * (q:ℤ) + 3 + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 78 * (q:ℤ) + 50) + 1 := by ring
    rw [h_3_2]
    have h_3_5 : 6 * (5 * (q:ℤ) + 3 + 5)^2 + 18 * (5 * (q:ℤ) + 3 + 5) + 11 = 5 * (30 * (q:ℤ)^2 + 114 * (q:ℤ) + 107) + 4 := by ring
    rw [h_3_5]
    have h_3_6 : 6 * (5 * (q:ℤ) + 3 + 6)^2 + 18 * (5 * (q:ℤ) + 3 + 6) + 11 = 5 * (30 * (q:ℤ)^2 + 126 * (q:ℤ) + 131) + 4 := by ring
    rw [h_3_6]
    have h_3_7 : 6 * (5 * (q:ℤ) + 3 + 7)^2 + 18 * (5 * (q:ℤ) + 3 + 7) + 11 = 5 * (30 * (q:ℤ)^2 + 138 * (q:ℤ) + 158) + 1 := by ring
    rw [h_3_7]
    omega
  · have : k = 5 * (k / 5) + 4 := by omega
    generalize hq : k / 5 = q
    rw [hq] at this
    subst k
    push_cast
    have h_4_0 : 6 * (5 * (q:ℤ) + 4)^2 + 18 * (5 * (q:ℤ) + 4) + 11 = 5 * (30 * (q:ℤ)^2 + 66 * (q:ℤ) + 35) + 4 := by ring
    rw [h_4_0]
    have h_4_1 : 6 * (5 * (q:ℤ) + 4 + 1)^2 + 18 * (5 * (q:ℤ) + 4 + 1) + 11 = 5 * (30 * (q:ℤ)^2 + 78 * (q:ℤ) + 50) + 1 := by ring
    rw [h_4_1]
    have h_4_2 : 6 * (5 * (q:ℤ) + 4 + 2)^2 + 18 * (5 * (q:ℤ) + 4 + 2) + 11 = 5 * (30 * (q:ℤ)^2 + 90 * (q:ℤ) + 67) + 0 := by ring
    rw [h_4_2]
    have h_4_5 : 6 * (5 * (q:ℤ) + 4 + 5)^2 + 18 * (5 * (q:ℤ) + 4 + 5) + 11 = 5 * (30 * (q:ℤ)^2 + 126 * (q:ℤ) + 131) + 4 := by ring
    rw [h_4_5]
    have h_4_6 : 6 * (5 * (q:ℤ) + 4 + 6)^2 + 18 * (5 * (q:ℤ) + 4 + 6) + 11 = 5 * (30 * (q:ℤ)^2 + 138 * (q:ℤ) + 158) + 1 := by ring
    rw [h_4_6]
    have h_4_7 : 6 * (5 * (q:ℤ) + 4 + 7)^2 + 18 * (5 * (q:ℤ) + 4 + 7) + 11 = 5 * (30 * (q:ℤ)^2 + 150 * (q:ℤ) + 187) + 0 := by ring
    rw [h_4_7]
    omega

lemma u_is_solution : E_recurrence.IsSolution u_formula := by
  intro n
  unfold u_formula E_recurrence LinearRecurrence.IsSolution
  dsimp only
  -- now it is a sum over Fin 7!
  -- Let us unfold the sum using Fin.sum_univ_succ
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.empty_val', Fin.sum_univ_zero, add_zero]
  -- Now it is a simple sum of 7 terms, let us linarith!
  linarith [recurrence_formula_add n]

lemma u_formula_init (n : Fin 7) : u_formula n = (![2, 7, 14, 23, 35, 50, 67] : Fin 7 → ℤ) n := by
  fin_cases n <;> rfl

lemma A227582_base_eq_u_formula (k : ℕ) : A227582_base k = u_formula k := by
  have h : A227582_base k = E_recurrence.mkSol ![2, 7, 14, 23, 35, 50, 67] k := rfl
  rw [h]
  have h_eq : u_formula = E_recurrence.mkSol ![2, 7, 14, 23, 35, 50, 67] := by
    apply LinearRecurrence.eq_mk_of_is_sol_of_eq_init'
    · exact u_is_solution
    · exact u_formula_init
  rw [←h_eq]
