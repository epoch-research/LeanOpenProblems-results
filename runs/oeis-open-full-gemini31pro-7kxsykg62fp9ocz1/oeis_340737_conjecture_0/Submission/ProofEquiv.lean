import Submission.Spec
import Submission.ProofFull

lemma A340737_eq_A_int (n : ℕ) : (A340737 n : ℤ) = A_int n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | n'
  · rw [A340737, A_int]; rfl
  · rw [A340737, A_int]; rfl
  · rw [A340737, A_int]; rfl
  · rw [A340737, A_int]
    dsimp
    have ih1 : (A340737 (n' + 2) : ℤ) = A_int (n' + 2) := ih (n' + 2) (by omega)
    have ih2 : (A340737 (n' + 1) : ℤ) = A_int (n' + 1) := ih (n' + 1) (by omega)
    have ih3 : (A340737 n' : ℤ) = A_int n' := ih n' (by omega)
    split_ifs with h_even
    · push_cast
      rw [ih1, ih2, ih3]
      have eq3 : ((n' + 1 : ℤ) / 2) = ((n' + 3 - 2 : ℤ) / 2) := by congr 1; omega
      rw [eq3]
      apply Int.toNat_of_nonneg
      have H := A_int_pos (n'+3)
      rw [A_int] at H
      dsimp at H
      rw [if_pos h_even] at H
      have h1 : n' + 3 - 2 = n' + 1 := by omega
      have h2 : n' + 3 - 3 = n' := by omega
      rw [h1, h2] at H
      exact H
    · push_cast
      rw [ih1, ih2]

lemma A340738_eq_B_int (n : ℕ) : (A340738 n : ℤ) = B_int n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | n'
  · rw [A340738, B_int]; rfl
  · rw [A340738, B_int]; rfl
  · rw [A340738, B_int]; rfl
  · rw [A340738, B_int]
    dsimp
    have ih1 : (A340738 (n' + 2) : ℤ) = B_int (n' + 2) := ih (n' + 2) (by omega)
    have ih2 : (A340738 (n' + 1) : ℤ) = B_int (n' + 1) := ih (n' + 1) (by omega)
    have ih3 : (A340738 n' : ℤ) = B_int n' := ih n' (by omega)
    split_ifs with h_even
    · push_cast
      rw [ih1, ih2, ih3]
      have eq3 : ((n' + 1 : ℤ) / 2) = ((n' + 3 - 2 : ℤ) / 2) := by congr 1; omega
      rw [eq3]
      apply Int.toNat_of_nonneg
      have H := B_int_pos (n'+3) (by omega)
      rw [B_int] at H
      dsimp at H
      rw [if_pos h_even] at H
      have h1 : n' + 3 - 2 = n' + 1 := by omega
      have h2 : n' + 3 - 3 = n' := by omega
      rw [h1, h2] at H
      linarith
    · push_cast
      rw [ih1, ih2]
