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
lemma div2_le_self (n : ℕ) : n / 2 ≤ n := by
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]; omega
lemma half_le_half_add_right (a b : ℕ) : a/2 ≤ (a+b)/2 := by
  apply Nat.div_le_div_right; omega
lemma half_le_self_of_le {x n : ℕ} (hx : x ≤ n) : (n + x)/2 ≤ n := by
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]; omega
lemma half_succ_le_self_of_le {x n : ℕ} (hx : x ≤ n) : (n + 1 + x)/2 ≤ n := by
  rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]
  omega


lemma div2_lt_of_add_two_le {s y : ℕ} (h : s + 2 ≤ y) : s/2 < y/2 := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
  omega
lemma div2_lt_of_boundary {x y : ℕ} (hpos : 0 < x) (h : x + 1 + x/2 ≤ y) : x/2 < y/2 := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
  omega

lemma F_mono_index (n t i) : F n t (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero => cases i <;> simp [F]
  | succ t ih =>
      cases i with
      | zero => rw [F_zero, F_step_succ, F_zero]; exact half_le_self_of_le (by simpa [F_zero] using ih 0)
      | succ i => rw [F_step_succ, F_step_succ]; exact Nat.div_le_div_right (Nat.add_le_add (ih i) (ih (i+1)))

lemma rel (n t : ℕ) :
    (∀ i, F (n+1) (t+1) (i+1) ≤ F n t i) ∧
    (∀ i, F n t i = 0 ∨ F n t i < F (n+1) (t+1) i) ∧
    (∀ i, F n t (i+2) = 0 → F n t i / 2 ≤ F (n+1) (t+1) (i+1)) := by
  induction t with
  | zero =>
      constructor
      · intro i
        cases i with
        | zero =>
            rw [F_step_succ, F_zero]
            simp [F]
            rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]
            omega
        | succ i => simp [F]
      constructor
      · intro i
        cases i with
        | zero => right; simp [F]
        | succ i => left; simp [F]
      · intro i h
        cases i with
        | zero =>
            rw [F_step_succ, F_zero]
            simp [F]
            rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]
            omega
        | succ i => simp [F]
  | succ t ih =>
      rcases ih with ⟨hR2, hR3, hR4⟩
      constructor
      · intro i
        cases i with
        | zero =>
            rw [F_step_succ, F_zero]
            have h := hR2 0
            -- F(n+1,t+1,1) <= n
            exact half_succ_le_self_of_le (by simpa [F_zero] using h)
        | succ i =>
            rw [F_step_succ, F_step_succ]
            exact Nat.div_le_div_right (Nat.add_le_add (hR2 i) (hR2 (i+1)))
      constructor
      · intro i
        cases i with
        | zero =>
            right
            rw [F_zero, F_zero]
            omega
        | succ i =>
            rw [F_step_succ, F_step_succ]
            by_cases hnext : F n t (i+1) = 0
            · by_cases hcur0 : F n t i = 0
              · left
                simp [hcur0, hnext]
              · right
                have hcurpos : 0 < F n t i := Nat.pos_of_ne_zero hcur0
                have hnext2 : F n t (i+2) = 0 := by
                  have hm := F_mono_index n t (i+1)
                  omega
                have hbd := hR4 i hnext2
                -- x' = x/2, y' >= (y_i + y_{i+1})/2 with y_i > x_i and y_{i+1} >= x_i/2
                have hyi : F n t i < F (n+1) (t+1) i := by
                  rcases hR3 i with hz | hp
                  · exact (hcur0 hz).elim
                  · exact hp
                rw [hnext, add_zero]
                have hsum : F n t i + 1 + F n t i / 2 ≤ F (n+1) (t+1) i + F (n+1) (t+1) (i+1) := by omega
                exact div2_lt_of_boundary hcurpos hsum
            · right
              have hposnext : 0 < F n t (i+1) := Nat.pos_of_ne_zero hnext
              have hyi : F n t i < F (n+1) (t+1) i := by
                rcases hR3 i with hz | hp
                · have := F_mono_index n t i
                  omega
                · exact hp
              have hyip : F n t (i+1) < F (n+1) (t+1) (i+1) := by
                rcases hR3 (i+1) with hz | hp
                · omega
                · exact hp
              have hsum : F n t i + F n t (i+1) + 2 ≤ F (n+1) (t+1) i + F (n+1) (t+1) (i+1) := by omega
              exact div2_lt_of_add_two_le hsum
      · intro i hzero
        cases i with
        | zero =>
            rw [F_zero]
            rw [F_step_succ, F_zero] at hzero
            have hnle : n ≤ 1 := by omega
            have hndiv : n / 2 = 0 := by omega
            rw [hndiv]
            exact Nat.zero_le _
        | succ i =>
            rw [F_step_succ] at hzero
            have hx1 : F n t (i+1) = 0 := by
              have hm := F_mono_index n t (i+1)
              omega
            have hbd := hR4 i hx1
            rw [F_step_succ, hx1, add_zero]
            exact le_trans (Nat.div_le_div_right hbd) (half_le_half_add_right (F (n+1) (t+1) (i+1)) (F (n+1) (t+1) (i+1+1)))
