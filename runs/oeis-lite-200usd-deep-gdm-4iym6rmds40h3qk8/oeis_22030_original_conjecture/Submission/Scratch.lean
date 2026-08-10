import FormalConjectures.Util.ProblemImports
open Nat

def a_seq (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | 2 => 63
  | n + 3 => 4 * a_seq (n + 2) - a_seq n


noncomputable def A022030_original (n : ℕ) : ℕ :=
  if h0 : n = 0 then 4
  else if h1 : n = 1 then 16
  else
    let b_n_1 := A022030_original (n - 1)
    let b_n_2 := A022030_original (n - 2)
    let num := b_n_1 ^ 2
    let den := b_n_2
    (num + den - 1) / den - 1
termination_by n

def D_seq (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 4
  | 2 => 1
  | 3 => 16
  | n + 4 => 4 * D_seq (n + 2) + D_seq (n + 1)

lemma a_seq_pos (n : ℕ) : a_seq (n + 1) ≥ 3 * a_seq n ∧ a_seq n > 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | n
    · decide
    · decide
    · decide
    · have ih1 := ih (n + 2) (by omega)
      have ih2 := ih (n + 1) (by omega)
      have ih1_1 : a_seq (n + 3) ≥ 3 * a_seq (n + 2) := ih1.left
      have ih2_1 : a_seq (n + 2) ≥ 3 * a_seq (n + 1) := ih2.left
      have ih2_2 : a_seq (n + 1) > 0 := ih2.right
      have h_def4 : a_seq (n + 4) = 4 * a_seq (n + 3) - a_seq (n + 1) := rfl
      revert ih1_1 ih2_1 ih2_2 h_def4
      generalize a_seq (n + 4) = s4
      generalize a_seq (n + 3) = s3
      generalize a_seq (n + 2) = s2
      generalize a_seq (n + 1) = s1
      intro h_def4 ih2_2 ih2_1 ih1_1
      constructor
      · omega
      · omega


lemma a_seq_D_seq_relation (n : ℕ) : a_seq (n + 1) * a_seq (n + 1) = a_seq n * a_seq (n + 2) + D_seq (n + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · decide
    · decide
    · decide
    · have ha3 : a_seq (k + 3) = 4 * a_seq (k + 2) - a_seq k := rfl
      have ha4 : a_seq (k + 4) = 4 * a_seq (k + 3) - a_seq (k + 1) := rfl
      have ha5 : a_seq (k + 5) = 4 * a_seq (k + 4) - a_seq (k + 2) := rfl
      have ⟨pos_k_lt, pos_k_gt⟩ := a_seq_pos k
      have ⟨pos_k1_lt, pos_k1_gt⟩ := a_seq_pos (k + 1)
      have ⟨pos_k2_lt, pos_k2_gt⟩ := a_seq_pos (k + 2)
      have ⟨pos_k3_lt, pos_k3_gt⟩ := a_seq_pos (k + 3)
      change a_seq (k + 2) ≥ 3 * a_seq (k + 1) at pos_k1_lt
      change a_seq (k + 3) ≥ 3 * a_seq (k + 2) at pos_k2_lt
      change a_seq (k + 4) ≥ 3 * a_seq (k + 3) at pos_k3_lt
      have h_ineq0 : a_seq (k + 2) ≥ a_seq k := by omega
      have h_ineq1 : a_seq (k + 3) ≥ a_seq (k + 1) := by omega
      have h_ineq2 : a_seq (k + 4) ≥ a_seq (k + 2) := by omega
      have ha3_add : a_seq (k + 3) + a_seq k = 4 * a_seq (k + 2) := by omega
      have ha4_add : a_seq (k + 4) + a_seq (k + 1) = 4 * a_seq (k + 3) := by omega
      have ha5_add : a_seq (k + 5) + a_seq (k + 2) = 4 * a_seq (k + 4) := by omega
      have ih1 := ih (k + 1) (by omega)
      have ih2 := ih k (by omega)
      change a_seq (k + 2) * a_seq (k + 2) = a_seq (k + 1) * a_seq (k + 3) + D_seq (k + 2) at ih1
      change a_seq (k + 1) * a_seq (k + 1) = a_seq k * a_seq (k + 2) + D_seq (k + 1) at ih2
      have h_D4 : D_seq (k + 4) = 4 * D_seq (k + 2) + D_seq (k + 1) := rfl
      zify at ha3_add ha4_add ha5_add ih1 ih2 h_D4
      zify
      linear_combination (a_seq (k + 2) : ℤ) * ha3_add + ((a_seq (k + 4) : ℤ) - (a_seq (k + 1) : ℤ)) * ha4_add - (a_seq (k + 3) : ℤ) * ha5_add - h_D4 + 4 * ih1 + ih2


lemma D_seq_le_a_seq (k : ℕ) : D_seq (k + 1) ≤ a_seq k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | m
    · decide
    · decide
    · decide
    · -- k = m + 3
      change D_seq (m + 4) ≤ a_seq (m + 3)
      have ih1 := ih (m + 1) (by omega)
      have ih2 := ih m (by omega)
      change D_seq (m + 2) ≤ a_seq (m + 1) at ih1
      change D_seq (m + 1) ≤ a_seq m at ih2
      have h_D4 : D_seq (m + 4) = 4 * D_seq (m + 2) + D_seq (m + 1) := rfl
      have ha3 : a_seq (m + 3) = 4 * a_seq (m + 2) - a_seq m := rfl
      have ⟨pos_m_lt, pos_m_gt⟩ := a_seq_pos m
      have ⟨pos_m1_lt, pos_m1_gt⟩ := a_seq_pos (m + 1)
      have ⟨pos_m2_lt, pos_m2_gt⟩ := a_seq_pos (m + 2)
      change a_seq (m + 2) ≥ 3 * a_seq (m + 1) at pos_m1_lt
      change a_seq (m + 3) ≥ 3 * a_seq (m + 2) at pos_m2_lt
      have ha3_add : a_seq (m + 3) + a_seq m = 4 * a_seq (m + 2) := by omega
      omega

lemma D_seq_pos (k : ℕ) : D_seq (k + 1) ≥ 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | m
    · decide
    · decide
    · decide
    · change D_seq (m + 4) ≥ 1
      have ih1 := ih (m + 1) (by omega)
      change D_seq (m + 2) ≥ 1 at ih1
      have h_D4 : D_seq (m + 4) = 4 * D_seq (m + 2) + D_seq (m + 1) := rfl
      omega


lemma nat_div_helper (A B C : ℕ) (hA : A > 0) (hC : C < A) : (A * B + C) / A = B := by
  have h1 : A * B + C = C + B * A := by ring
  rw [h1]
  rw [Nat.add_mul_div_right C B hA]
  have h2 : C / A = 0 := Nat.div_eq_of_lt hC
  rw [h2, Nat.zero_add]

lemma a_seq_recurrence_step (k : ℕ) : a_seq (k + 2) = (a_seq (k + 1) ^ 2 + a_seq k - 1) / a_seq k - 1 := by
  have h_pos := (a_seq_pos k).right
  have h_D_pos := D_seq_pos k
  have h_D_le := D_seq_le_a_seq k
  have h_rel := a_seq_D_seq_relation k
  have h_sq : a_seq (k + 1) ^ 2 = a_seq (k + 1) * a_seq (k + 1) := by ring
  rw [h_sq, h_rel]
  have h_dist : a_seq k * (a_seq (k + 2) + 1) = a_seq k * a_seq (k + 2) + a_seq k := by ring
  have h_num : a_seq k * a_seq (k + 2) + D_seq (k + 1) + a_seq k - 1 = a_seq k * (a_seq (k + 2) + 1) + (D_seq (k + 1) - 1) := by
    rw [h_dist]
    omega
  rw [h_num]
  rw [nat_div_helper (a_seq k) (a_seq (k + 2) + 1) (D_seq (k + 1) - 1) h_pos (by omega)]
  omega

theorem A022030_original_eq_a_seq (n : ℕ) : A022030_original n = a_seq n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold A022030_original
    rcases n with _ | _ | k
    · rfl
    · rfl
    · -- n = k + 2
      have ih1 := ih (k + 1) (by omega)
      have ih2 := ih k (by omega)
      simp
      rw [ih1, ih2]
      exact (a_seq_recurrence_step k).symm


theorem oeis_22030_original_conjecture (n : ℕ) :
  A022030_original n = (
    if n = 0 then 4
    else if n = 1 then 16
    else if n = 2 then 63
    else
      4 * (A022030_original (n - 1)) - (A022030_original (n - 3))
  ) := by
  rw [A022030_original_eq_a_seq n]
  rcases n with _ | _ | _ | k
  · rfl
  · rfl
  · rfl
  · -- n = k + 3
    have ih1 : A022030_original (k + 2) = a_seq (k + 2) := A022030_original_eq_a_seq (k + 2)
    have ih2 : A022030_original k = a_seq k := A022030_original_eq_a_seq k
    have h_sub1 : k + 1 + 1 + 1 - 1 = k + 2 := by omega
    have h_sub2 : k + 1 + 1 + 1 - 3 = k := by omega
    rw [h_sub1, h_sub2]
    rw [ih1, ih2]
    rfl


#print axioms oeis_22030_original_conjecture




