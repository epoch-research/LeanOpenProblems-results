import FormalConjectures.Util.ProblemImports
import Mathlib
import Submission.ProofFull

open Polynomial Filter Topology
open scoped Polynomial

noncomputable def A340737 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | n' + 3 =>
    let n := n' + 3
    let a_nm1 := A340737 (n - 1)
    let a_nm2 := A340737 (n - 2)
    let a_nm3 := A340737 (n - 3)
    if n % 2 = 0 then
      let c1 : ℕ := (n + 2) / 2
      let c2 : ℕ := (n - 2) / 2
      Int.toNat (Int.ofNat c1 * Int.ofNat a_nm1 - Int.ofNat a_nm2 - Int.ofNat c2 * Int.ofNat a_nm3)
    else
      2 * a_nm1 + n * a_nm2
termination_by n

noncomputable def A340738 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n' + 3 =>
    let n := n' + 3
    let b_nm1 := A340738 (n - 1)
    let b_nm2 := A340738 (n - 2)
    let b_nm3 := A340738 (n - 3)
    if n % 2 = 0 then
      let c1 : ℕ := (n + 2) / 2
      let c2 : ℕ := (n - 2) / 2
      Int.toNat (Int.ofNat c1 * Int.ofNat b_nm1 - Int.ofNat b_nm2 - Int.ofNat c2 * Int.ofNat b_nm3)
    else
      2 * b_nm1 + n * b_nm2
termination_by n

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

theorem oeis_340737_conjecture_0 :
  Filter.Tendsto (fun n : ℕ => (A340737 n : ℝ) / (A340738 n : ℝ)) Filter.atTop (nhds (Real.exp 1)) := by
  have H := final_limit
  have heq : (fun n : ℕ => (A340737 n : ℝ) / (A340738 n : ℝ)) = (fun n => (A_int n : ℝ) / (B_int n : ℝ)) := by
    ext n
    have hA : (A340737 n : ℝ) = (A_int n : ℝ) := by exact_mod_cast A340737_eq_A_int n
    have hB : (A340738 n : ℝ) = (B_int n : ℝ) := by exact_mod_cast A340738_eq_B_int n
    rw [hA, hB]
  rw [heq]
  exact H

theorem oeis_340737_conjecture_0.disproof : ¬ (type_of% @oeis_340737_conjecture_0) := sorry
