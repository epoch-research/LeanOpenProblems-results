import FormalConjectures.Util.ProblemImports
open Nat

noncomputable section

def F : ℕ → ℕ → ℕ → ℕ
| n, 0, 0 => n
| _, 0, _+1 => 0
| n, _+1, 0 => n
| n, t+1, i+1 => (F n t i + F n t (i+1))/2

lemma F_zero (n t) : F n t 0 = n := by cases t <;> rfl
lemma F_init_succ (n i) : F n 0 (i+1)=0 := rfl
lemma F_step_succ (n t i) : F n (t+1) (i+1) = (F n t i + F n t (i+1))/2 := rfl

lemma half_le_self_of_le {x n : ℕ} (hx : x ≤ n) : (n + x)/2 ≤ n := by
  apply Nat.div_le_of_le_mul (k:=2)
  omega

lemma F_mono_index (n t i) : F n t (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero => cases i <;> simp [F]
  | succ t ih =>
      cases i with
      | zero =>
          rw [F_zero, F_step_succ, F_zero]
          exact half_le_self_of_le (by simpa [F_zero] using ih 0)
      | succ i =>
          rw [F_step_succ, F_step_succ]
          apply Nat.div_le_div_right
          exact Nat.add_le_add (ih i) (ih (i+1))

lemma lower_shift (n t i) : F (n+1) (t+1) (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero =>
      cases i with
      | zero =>
          rw [F_step_succ, F_zero]
          simp [F]
          apply Nat.div_le_of_le_mul (k:=2)
          omega
      | succ i => simp [F]
  | succ t ih =>
      cases i with
      | zero =>
          rw [F_step_succ, F_zero]
          exact half_le_self_of_le (by simpa [F_zero] using ih 0)
      | succ i =>
          rw [F_step_succ, F_step_succ]
          apply Nat.div_le_div_right
          exact Nat.add_le_add (ih i) (ih (i+1))

lemma ceil_half_le_of_double_le {a b : ℕ} (h : a ≤ 2*b) : (a+1)/2 ≤ b := by
  apply Nat.div_le_of_le_mul (k:=2)
  omega

lemma half_sum_ceil_le (x y : ℕ) : ((x + y)/2 + 1)/2 ≤ (((x+1)/2) + ((y+1)/2))/2 := by
  apply Nat.div_le_of_le_mul (k:=2)
  have hx : x ≤ 2 * ((x+1)/2) := by
    rw [Nat.le_div_iff_mul_le] <;> omega
  have hy : y ≤ 2 * ((y+1)/2) := by
    rw [Nat.le_div_iff_mul_le] <;> omega
  have hxy : (x+y)/2 + 1 ≤ ((x+1)/2 + (y+1)/2) * 2 := by
    apply Nat.div_le_of_le_mul (k:=2)
    omega
  omega

lemma upper_quant (n t i) : max (F n t (i+1)) ((F n t i + 1)/2) ≤ F (n+1) (t+2) (i+1) := by
  induction t generalizing i with
  | zero =>
      cases i with
      | zero =>
          simp [F]
          constructor
          · omega
          · apply Nat.div_le_of_le_mul (k:=2); omega
      | succ i => simp [F]
  | succ t ih =>
      cases i with
      | zero =>
          -- target max(F n (t+1) 1, (n+1)/2) <= F(n+1)(t+3)1
          rw [F_step_succ, F_step_succ, F_zero, F_zero]
          constructor
          · -- F n (t+1)1 <= average of n+1 and something >= F n(t+1)1
            have hlow := lower_shift n (t+1) 0
            have hq := ih 0
            -- hq gives (F n t 0+1)/2 <= F(n+1)(t+2)1 and F n t1 <= ...
            apply Nat.div_le_of_le_mul (k:=2)
            omega
          · apply Nat.div_le_of_le_mul (k:=2)
            omega
      | succ i =>
          rw [F_step_succ, F_step_succ]
          have hi := ih i
          have hi1 := ih (i+1)
          constructor
          · -- successor tail component
            have h1 : F n t (i+1+1) ≤ F (n+1) (t+2) (i+1+1) := le_trans (le_max_left _ _) hi1
            have h0 : F n t (i+1) ≤ F (n+1) (t+2) (i+1) := by
              -- from ceil half? actually max left at ih i is F n t(i+1)
              exact le_trans (le_max_left _ _) hi
            rw [F_step_succ]
            apply Nat.div_le_div_right
            exact Nat.add_le_add h0 h1
          · -- ceil half of current average
            have h0 : (F n t i + 1)/2 ≤ F (n+1) (t+2) (i+1) := le_trans (le_max_right _ _) hi
            have h1 : (F n t (i+1) + 1)/2 ≤ F (n+1) (t+2) (i+1+1) := le_trans (le_max_right _ _) hi1
            have har := half_sum_ceil_le (F n t i) (F n t (i+1))
            refine le_trans har ?_
            rw [F_step_succ]
            apply Nat.div_le_div_right
            exact Nat.add_le_add h0 h1

lemma upper_pos_shift (n t i) : 0 < F n t i → 0 < F (n+1) (t+2) (i+1) := by
  intro h
  have hq := upper_quant n t i
  have : 0 < (F n t i + 1)/2 := by
    rw [Nat.div_pos_iff_lt]
    omega
  exact lt_of_lt_of_le this (le_trans (le_max_right _ _) hq)

end
