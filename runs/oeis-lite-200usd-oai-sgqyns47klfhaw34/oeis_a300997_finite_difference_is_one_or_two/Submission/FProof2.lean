import FormalConjectures.Util.ProblemImports
open Nat

def F : ℕ → ℕ → ℕ → ℕ
| n, 0, 0 => n
| _, 0, _+1 => 0
| n, _+1, 0 => n
| n, t+1, i+1 => (F n t i + F n t (i+1))/2

lemma F_zero (n t) : F n t 0 = n := by cases t <;> rfl
lemma F_step_succ (n t i) : F n (t+1) (i+1) = (F n t i + F n t (i+1))/2 := rfl

lemma half_le_self_of_le {x n : ℕ} (hx : x ≤ n) : (n + x)/2 ≤ n := by
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]
  omega
lemma half_succ_le_self_of_le {x n : ℕ} (hx : x ≤ n) : (n+1+x)/2 ≤ n := by
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]
  omega

lemma F_mono_index (n t i) : F n t (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero => cases i <;> simp [F]
  | succ t ih =>
      cases i with
      | zero => rw [F_zero, F_step_succ, F_zero]; exact half_le_self_of_le (by simpa [F_zero] using ih 0)
      | succ i => rw [F_step_succ, F_step_succ]; exact Nat.div_le_div_right (Nat.add_le_add (ih i) (ih (i+1)))

lemma avgceil_two (n t i) : (F n t i + F n t (i+1) + 1)/2 ≤ F (n+1) (t+2) (i+1) := by
  induction t generalizing i with
  | zero =>
      cases i with
      | zero =>
          simp [F]
          rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]; omega
      | succ i => simp [F]
  | succ t ih =>
      cases i with
      | zero =>
          rw [F_step_succ, F_step_succ, F_zero, F_zero]
          have h := ih 0
          have hm := F_mono_index n t 0
          -- h : (n + F n t 1 + 1)/2 ≤ F(n+1)(t+2)1
          rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]
          omega
      | succ i =>
          rw [F_step_succ, F_step_succ, F_step_succ]
          have h0 := ih i
          have h1 := ih (i+1)
          have hm0 := F_mono_index n t i
          have hm1 := F_mono_index n t (i+1)
          rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]
          omega
