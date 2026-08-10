import FormalConjectures.Util.ProblemImports
open Nat

set_option linter.unusedVariables false

def F : ℕ → ℕ → ℕ → ℕ
| n, 0, 0 => n
| _, 0, _+1 => 0
| n, _+1, 0 => n
| n, t+1, i+1 => (F n t i + F n t (i+1))/2

lemma F_zero (n t) : F n t 0 = n := by cases t <;> rfl
lemma F_step_succ (n t i) : F n (t+1) (i+1) = (F n t i + F n t (i+1))/2 := rfl

lemma half_le_self_of_le {x n : ℕ} (hx : x ≤ n) : (n + x)/2 ≤ n := by
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]; omega
lemma half_succ_le_self_of_le {x n : ℕ} (hx : x ≤ n) : (n + 1 + x)/2 ≤ n := by
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]; omega
lemma div2_lt_of_add_two_le {s y : ℕ} (h : s + 2 ≤ y) : s/2 < y/2 := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]; omega
lemma div2_lt_of_boundary {x y : ℕ} (hpos : 0 < x) (h : x + 1 + x/2 ≤ y) : x/2 < y/2 := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]; omega

lemma F_mono_index (n t i) : F n t (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero => cases i <;> simp [F]
  | succ t ih =>
      cases i with
      | zero => rw [F_zero, F_step_succ, F_zero]; exact half_le_self_of_le (by simpa [F_zero] using ih 0)
      | succ i => rw [F_step_succ, F_step_succ]; exact Nat.div_le_div_right (Nat.add_le_add (ih i) (ih (i+1)))

lemma F_mono_n (n t i) : F n t i ≤ F (n+1) t i := by
  induction t generalizing i with
  | zero => cases i <;> simp [F]
  | succ t ih =>
      cases i with
      | zero => simp [F_zero]
      | succ i => rw [F_step_succ, F_step_succ]; exact Nat.div_le_div_right (Nat.add_le_add (ih i) (ih (i+1)))

lemma half_shift_le (n t i) : F n t i / 2 ≤ F (n+1) (t+1) (i+1) := by
  rw [F_step_succ]
  exact le_trans (Nat.div_le_div_right (F_mono_n n t i)) (Nat.div_le_div_right (by omega : F (n+1) t i ≤ F (n+1) t i + F (n+1) t (i+1)))

lemma lower_shift (n t i) : F (n+1) (t+1) (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero =>
      cases i with
      | zero => rw [F_step_succ, F_zero]; simp [F]; rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]; omega
      | succ i => simp [F]
  | succ t ih =>
      cases i with
      | zero => rw [F_step_succ, F_zero]; exact half_succ_le_self_of_le (by simpa [F_zero] using ih 0)
      | succ i => rw [F_step_succ, F_step_succ]; exact Nat.div_le_div_right (Nat.add_le_add (ih i) (ih (i+1)))

lemma strict_shift (n t i) : F n t i = 0 ∨ F n t i < F (n+1) (t+1) i := by
  induction t generalizing i with
  | zero =>
      cases i with
      | zero => right; simp [F]
      | succ i => left; simp [F]
  | succ t ih =>
      cases i with
      | zero => right; rw [F_zero, F_zero]; omega
      | succ i =>
          rw [F_step_succ, F_step_succ]
          by_cases hnext : F n t (i+1) = 0
          · by_cases hcur0 : F n t i = 0
            · left; simp [hcur0, hnext]
            · right
              have hcurpos : 0 < F n t i := Nat.pos_of_ne_zero hcur0
              have hyi : F n t i < F (n+1) (t+1) i := by
                rcases ih i with hz | hp
                · exact (hcur0 hz).elim
                · exact hp
              have hbd := half_shift_le n t i
              rw [hnext, add_zero]
              have hsum : F n t i + 1 + F n t i / 2 ≤ F (n+1) (t+1) i + F (n+1) (t+1) (i+1) := by omega
              exact div2_lt_of_boundary hcurpos hsum
          · right
            have hyi : F n t i < F (n+1) (t+1) i := by
              rcases ih i with hz | hp
              · have hm := F_mono_index n t i; omega
              · exact hp
            have hyip : F n t (i+1) < F (n+1) (t+1) (i+1) := by
              rcases ih (i+1) with hz | hp
              · omega
              · exact hp
            have hsum : F n t i + F n t (i+1) + 2 ≤ F (n+1) (t+1) i + F (n+1) (t+1) (i+1) := by omega
            exact div2_lt_of_add_two_le hsum

lemma upper_pos_shift (n t i) (h : 0 < F n t i) : 0 < F (n+1) (t+2) (i+1) := by
  have hs := strict_shift n t i
  have hy : F n t i < F (n+1) (t+1) i := by
    rcases hs with hz | hp
    · omega
    · exact hp
  rw [F_step_succ]
  have : 2 ≤ F (n+1) (t+1) i + F (n+1) (t+1) (i+1) := by omega
  rw [Nat.lt_div_iff_mul_lt (by norm_num : 0 < 2)]
  omega
