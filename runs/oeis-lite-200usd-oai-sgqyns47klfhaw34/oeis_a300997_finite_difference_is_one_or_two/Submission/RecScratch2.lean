import FormalConjectures.Util.ProblemImports
open List Nat Function Set

noncomputable section

def F : ℕ → ℕ → ℕ → ℕ
| n, 0, 0 => n
| _, 0, _+1 => 0
| n, _+1, 0 => n
| n, t+1, i+1 => F n t (i+1) + (F n t i - F n t (i+1))/2

lemma half_rewrite {x y : ℕ} (h : y ≤ x) : y + (x - y)/2 = (x + y)/2 := by
  have : x = (x - y) + y := by omega
  rw [this]
  omega

lemma F_zero (n t) : F n t 0 = n := by cases t <;> rfl

lemma F_step_succ (n t i) : F n (t+1) (i+1) = (F n t i + F n t (i+1))/2 := by
  rw [F]
  rw [half_rewrite]
  · rw [Nat.add_comm]
  · -- monotone index
    induction t generalizing i with
    | zero => cases i <;> simp [F]
    | succ t ih =>
        cases i with
        | zero => simp [F, F_zero]
        | succ i =>
            rw [F_step_succ, F_step_succ]
            apply Nat.div_le_div_right
            exact add_le_add (ih i) (ih (i+1))
termination_by t

lemma F_mono_index (n t i) : F n t (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero => cases i <;> simp [F]
  | succ t ih =>
      cases i with
      | zero =>
          rw [F_zero, F_step_succ]
          have h := ih 0
          omega
      | succ i =>
          rw [F_step_succ, F_step_succ]
          apply Nat.div_le_div_right
          exact add_le_add (ih i) (ih (i+1))

lemma lower_shift (n t i) : F (n+1) (t+1) (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero =>
      cases i with
      | zero =>
          rw [F_step_succ, F_zero]
          simp [F]
      | succ i => simp [F, F_step_succ]
  | succ t ih =>
      cases i with
      | zero =>
          rw [F_step_succ, F_zero]
          have h : F (n+1) (t+1) 1 ≤ n := ih 0
          omega
      | succ i =>
          rw [F_step_succ, F_step_succ]
          apply Nat.div_le_div_right
          exact add_le_add (ih i) (ih (i+1))

end
