import Mathlib
import Submission.ExactDef
import Submission.Vals
import Submission.Steps.Step_A_2000
import Submission.Steps.Step_A_4000
import Submission.Steps.Step_A_6000
import Submission.Steps.Step_A_8000
import Submission.Steps.Step_A_10000
import Submission.Steps.Step_A_12000
import Submission.Steps.Step_A_14000
import Submission.Steps.Step_A_16000
import Submission.Steps.Step_A_18000
import Submission.Steps.Step_A_20000
import Submission.Steps.Step_A_22000
import Submission.Steps.Step_A_24000
import Submission.Steps.Step_A_26000
import Submission.Steps.Step_A_28000
import Submission.Steps.Step_A_30000
import Submission.Steps.Step_A_32000
import Submission.Steps.Step_A_34000
import Submission.Steps.Step_A_36000
import Submission.Steps.Step_A_38000
import Submission.Steps.Step_A_40000
import Submission.Steps.Step_A_42000
import Submission.Steps.Step_A_44000
import Submission.Steps.Step_A_46000
import Submission.Steps.Step_A_48000
import Submission.Steps.Step_A_50000
import Submission.Steps.Step_A_52000
import Submission.Steps.Step_A_54000
import Submission.Steps.Step_A_56000
import Submission.Steps.Step_A_58000
import Submission.Steps.Step_A_60000
import Submission.Steps.Step_A_62000
import Submission.Steps.Step_A_64000
import Submission.Steps.Step_A_66000
import Submission.Steps.Step_A_68000
import Submission.Steps.Step_A_70000
import Submission.Steps.Step_A_72000
import Submission.Steps.Step_A_74000
import Submission.Steps.Step_A_76000
import Submission.Steps.Step_A_78000
import Submission.Steps.Step_A_80000
import Submission.Steps.Step_A_82000
import Submission.Steps.Step_A_84000
import Submission.Steps.Step_A_86000
import Submission.Steps.Step_A_88000
import Submission.Steps.Step_A_90000
import Submission.Steps.Step_A_92000
import Submission.Steps.Step_A_94000
import Submission.Steps.Step_A_96000
import Submission.Steps.Step_A_98000
import Submission.Steps.Step_A_100000
import Submission.Steps.Step_A_102000
import Submission.Steps.Step_A_104000
import Submission.Steps.Step_A_106000
import Submission.Steps.Step_A_108000
import Submission.Steps.Step_A_110000
import Submission.Steps.Step_A_112000
import Submission.Steps.Step_A_114000
import Submission.Steps.Step_A_116000
import Submission.Steps.Step_A_117648
import Submission.Steps.Step_B_2000
import Submission.Steps.Step_B_4000
import Submission.Steps.Step_B_6000
import Submission.Steps.Step_B_8000
import Submission.Steps.Step_B_10000
import Submission.Steps.Step_B_12000
import Submission.Steps.Step_B_14000
import Submission.Steps.Step_B_16000
import Submission.Steps.Step_B_16806

open Nat Finset
def a_term (n k : Nat) := (n.choose k) * (n.choose k) * ((n + k - 1).choose k) * ((n + k - 1).choose k)

def a_sum (n k : Nat) : Nat :=
  match k with
  | 0 => 1
  | k'+1 => a_sum n k' + a_term n (k' + 1)

def a_state (n k : Nat) : Nat × Nat × Nat :=
  (n.choose k, (n + k - 1).choose k, a_sum n k)

theorem choose_mul_eq (n k : Nat) (h : k < n) : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := by
  have h1 := choose_mul (n := n) (k := k + 1) (s := k) (by omega)
  have h2 : k + 1 - k = 1 := by omega
  rw [h2] at h1
  have hc1 : (k + 1).choose k = k + 1 := by simp
  have hc2 : (n - k).choose 1 = n - k := by simp
  rw [hc1, hc2] at h1
  exact h1

theorem c_new_eq (n k : Nat) (h : k < n) :
  (n.choose k * (n - k)) / (k + 1) = n.choose (k + 1) := by
  have h1 := choose_mul_eq n k h
  rw [← h1]
  apply Nat.mul_div_cancel
  omega

theorem choose_add_mul_eq (n k : Nat) (hn : n > 0) :
  (n + k).choose (k + 1) * (k + 1) = (n + k - 1).choose k * (n + k) := by
  have h := Nat.add_one_mul_choose_eq (n + k - 1) k
  have h1 : n + k - 1 + 1 = n + k := by omega
  rw [h1] at h
  rw [← h]
  ring

theorem c3_new_eq (n k : Nat) (hn : n > 0) :
  ((n + k - 1).choose k * (n + k)) / (k + 1) = (n + k).choose (k + 1) := by
  have h := choose_add_mul_eq n k hn
  rw [← h]
  apply Nat.mul_div_cancel
  omega

theorem step_exact_correct (n k : Nat) (hn : n > 0) (hk : k < n) :
  step_exact n k (a_state n k) = a_state n (k + 1) := by
  unfold step_exact a_state
  dsimp
  have h1 := c_new_eq n k hk
  have h2 := c3_new_eq n k hn
  have h3 : n + k = n + (k + 1) - 1 := by omega
  rw [h1, h2, h3]
  have h4 : a_sum n (k + 1) = a_sum n k + a_term n (k + 1) := rfl
  rw [h4]
  unfold a_term
  ring_nf
  rfl

theorem apply_exact_correct (n steps start : Nat) (hn : n > 0) (h : start + steps ≤ n) :
  apply_exact n steps start (a_state n start) = a_state n (start + steps) := by
  induction steps generalizing start with
  | zero =>
    simp [apply_exact]
  | succ step ih =>
    have h1 : start < n := by omega
    have h2 := step_exact_correct n start hn h1
    unfold apply_exact
    rw [h2]
    have h3 : start + 1 + step = start + (step + 1) := by omega
    rw [← h3]
    apply ih
    omega

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k => (n.choose k) ^ 2 * ((n + k - 1).choose k) ^ 2

theorem a_sum_eq_a (n k : Nat) (hn : n > 0) : Finset.sum (Finset.range (k + 1)) (fun j => (n.choose j)^2 * ((n + j - 1).choose j)^2) = a_sum n k := by
  induction k with
  | zero =>
    unfold a_sum
    simp
  | succ k' ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    have h1 : a_sum n (k' + 1) = a_sum n k' + a_term n (k' + 1) := rfl
    rw [h1]
    unfold a_term
    have h2 : n + (k' + 1) - 1 = n + k' := by omega
    rw [h2]
    simp only [sq]
    congr 1
    ring_nf
    rfl

theorem a_eq_apply_exact (n : Nat) (hn : n > 0) : a n = (apply_exact n (n - 1) 0 (1, 1, 1)).2.2 := by
  have h1 := apply_exact_correct n (n - 1) 0 hn (by omega)
  have h2 : 0 + (n - 1) = n - 1 := by omega
  rw [h2] at h1
  have h3 : a_state n 0 = (1, 1, 1) := by
    unfold a_state a_sum
    simp
  rw [h3] at h1
  have h4 : (apply_exact n (n - 1) 0 (1, 1, 1)).2.2 = a_sum n (n - 1) := by
    rw [h1]
    rfl
  rw [h4]
  have h5 := a_sum_eq_a n (n - 1) hn
  have h6 : n - 1 + 1 = n := by omega
  rw [h6] at h5
  unfold a
  rw [← h5]

theorem eq_A_0 : apply_exact 117649 0 0 val_A_0 = val_A_0 := rfl

theorem eq_A_2000 : apply_exact 117649 2000 0 val_A_0 = val_A_2000 := by
  rw [apply_exact_add 117649 0 2000 0 val_A_0]
  rw [eq_A_0]
  rw [step_A_2000]

theorem eq_A_4000 : apply_exact 117649 4000 0 val_A_0 = val_A_4000 := by
  rw [apply_exact_add 117649 2000 2000 0 val_A_0]
  rw [eq_A_2000]
  rw [step_A_4000]

theorem eq_A_6000 : apply_exact 117649 6000 0 val_A_0 = val_A_6000 := by
  rw [apply_exact_add 117649 4000 2000 0 val_A_0]
  rw [eq_A_4000]
  rw [step_A_6000]

theorem eq_A_8000 : apply_exact 117649 8000 0 val_A_0 = val_A_8000 := by
  rw [apply_exact_add 117649 6000 2000 0 val_A_0]
  rw [eq_A_6000]
  rw [step_A_8000]

theorem eq_A_10000 : apply_exact 117649 10000 0 val_A_0 = val_A_10000 := by
  rw [apply_exact_add 117649 8000 2000 0 val_A_0]
  rw [eq_A_8000]
  rw [step_A_10000]

theorem eq_A_12000 : apply_exact 117649 12000 0 val_A_0 = val_A_12000 := by
  rw [apply_exact_add 117649 10000 2000 0 val_A_0]
  rw [eq_A_10000]
  rw [step_A_12000]

theorem eq_A_14000 : apply_exact 117649 14000 0 val_A_0 = val_A_14000 := by
  rw [apply_exact_add 117649 12000 2000 0 val_A_0]
  rw [eq_A_12000]
  rw [step_A_14000]

theorem eq_A_16000 : apply_exact 117649 16000 0 val_A_0 = val_A_16000 := by
  rw [apply_exact_add 117649 14000 2000 0 val_A_0]
  rw [eq_A_14000]
  rw [step_A_16000]

theorem eq_A_18000 : apply_exact 117649 18000 0 val_A_0 = val_A_18000 := by
  rw [apply_exact_add 117649 16000 2000 0 val_A_0]
  rw [eq_A_16000]
  rw [step_A_18000]

theorem eq_A_20000 : apply_exact 117649 20000 0 val_A_0 = val_A_20000 := by
  rw [apply_exact_add 117649 18000 2000 0 val_A_0]
  rw [eq_A_18000]
  rw [step_A_20000]

theorem eq_A_22000 : apply_exact 117649 22000 0 val_A_0 = val_A_22000 := by
  rw [apply_exact_add 117649 20000 2000 0 val_A_0]
  rw [eq_A_20000]
  rw [step_A_22000]

theorem eq_A_24000 : apply_exact 117649 24000 0 val_A_0 = val_A_24000 := by
  rw [apply_exact_add 117649 22000 2000 0 val_A_0]
  rw [eq_A_22000]
  rw [step_A_24000]

theorem eq_A_26000 : apply_exact 117649 26000 0 val_A_0 = val_A_26000 := by
  rw [apply_exact_add 117649 24000 2000 0 val_A_0]
  rw [eq_A_24000]
  rw [step_A_26000]

theorem eq_A_28000 : apply_exact 117649 28000 0 val_A_0 = val_A_28000 := by
  rw [apply_exact_add 117649 26000 2000 0 val_A_0]
  rw [eq_A_26000]
  rw [step_A_28000]

theorem eq_A_30000 : apply_exact 117649 30000 0 val_A_0 = val_A_30000 := by
  rw [apply_exact_add 117649 28000 2000 0 val_A_0]
  rw [eq_A_28000]
  rw [step_A_30000]

theorem eq_A_32000 : apply_exact 117649 32000 0 val_A_0 = val_A_32000 := by
  rw [apply_exact_add 117649 30000 2000 0 val_A_0]
  rw [eq_A_30000]
  rw [step_A_32000]

theorem eq_A_34000 : apply_exact 117649 34000 0 val_A_0 = val_A_34000 := by
  rw [apply_exact_add 117649 32000 2000 0 val_A_0]
  rw [eq_A_32000]
  rw [step_A_34000]

theorem eq_A_36000 : apply_exact 117649 36000 0 val_A_0 = val_A_36000 := by
  rw [apply_exact_add 117649 34000 2000 0 val_A_0]
  rw [eq_A_34000]
  rw [step_A_36000]

theorem eq_A_38000 : apply_exact 117649 38000 0 val_A_0 = val_A_38000 := by
  rw [apply_exact_add 117649 36000 2000 0 val_A_0]
  rw [eq_A_36000]
  rw [step_A_38000]

theorem eq_A_40000 : apply_exact 117649 40000 0 val_A_0 = val_A_40000 := by
  rw [apply_exact_add 117649 38000 2000 0 val_A_0]
  rw [eq_A_38000]
  rw [step_A_40000]

theorem eq_A_42000 : apply_exact 117649 42000 0 val_A_0 = val_A_42000 := by
  rw [apply_exact_add 117649 40000 2000 0 val_A_0]
  rw [eq_A_40000]
  rw [step_A_42000]

theorem eq_A_44000 : apply_exact 117649 44000 0 val_A_0 = val_A_44000 := by
  rw [apply_exact_add 117649 42000 2000 0 val_A_0]
  rw [eq_A_42000]
  rw [step_A_44000]

theorem eq_A_46000 : apply_exact 117649 46000 0 val_A_0 = val_A_46000 := by
  rw [apply_exact_add 117649 44000 2000 0 val_A_0]
  rw [eq_A_44000]
  rw [step_A_46000]

theorem eq_A_48000 : apply_exact 117649 48000 0 val_A_0 = val_A_48000 := by
  rw [apply_exact_add 117649 46000 2000 0 val_A_0]
  rw [eq_A_46000]
  rw [step_A_48000]

theorem eq_A_50000 : apply_exact 117649 50000 0 val_A_0 = val_A_50000 := by
  rw [apply_exact_add 117649 48000 2000 0 val_A_0]
  rw [eq_A_48000]
  rw [step_A_50000]

theorem eq_A_52000 : apply_exact 117649 52000 0 val_A_0 = val_A_52000 := by
  rw [apply_exact_add 117649 50000 2000 0 val_A_0]
  rw [eq_A_50000]
  rw [step_A_52000]

theorem eq_A_54000 : apply_exact 117649 54000 0 val_A_0 = val_A_54000 := by
  rw [apply_exact_add 117649 52000 2000 0 val_A_0]
  rw [eq_A_52000]
  rw [step_A_54000]

theorem eq_A_56000 : apply_exact 117649 56000 0 val_A_0 = val_A_56000 := by
  rw [apply_exact_add 117649 54000 2000 0 val_A_0]
  rw [eq_A_54000]
  rw [step_A_56000]

theorem eq_A_58000 : apply_exact 117649 58000 0 val_A_0 = val_A_58000 := by
  rw [apply_exact_add 117649 56000 2000 0 val_A_0]
  rw [eq_A_56000]
  rw [step_A_58000]

theorem eq_A_60000 : apply_exact 117649 60000 0 val_A_0 = val_A_60000 := by
  rw [apply_exact_add 117649 58000 2000 0 val_A_0]
  rw [eq_A_58000]
  rw [step_A_60000]

theorem eq_A_62000 : apply_exact 117649 62000 0 val_A_0 = val_A_62000 := by
  rw [apply_exact_add 117649 60000 2000 0 val_A_0]
  rw [eq_A_60000]
  rw [step_A_62000]

theorem eq_A_64000 : apply_exact 117649 64000 0 val_A_0 = val_A_64000 := by
  rw [apply_exact_add 117649 62000 2000 0 val_A_0]
  rw [eq_A_62000]
  rw [step_A_64000]

theorem eq_A_66000 : apply_exact 117649 66000 0 val_A_0 = val_A_66000 := by
  rw [apply_exact_add 117649 64000 2000 0 val_A_0]
  rw [eq_A_64000]
  rw [step_A_66000]

theorem eq_A_68000 : apply_exact 117649 68000 0 val_A_0 = val_A_68000 := by
  rw [apply_exact_add 117649 66000 2000 0 val_A_0]
  rw [eq_A_66000]
  rw [step_A_68000]

theorem eq_A_70000 : apply_exact 117649 70000 0 val_A_0 = val_A_70000 := by
  rw [apply_exact_add 117649 68000 2000 0 val_A_0]
  rw [eq_A_68000]
  rw [step_A_70000]

theorem eq_A_72000 : apply_exact 117649 72000 0 val_A_0 = val_A_72000 := by
  rw [apply_exact_add 117649 70000 2000 0 val_A_0]
  rw [eq_A_70000]
  rw [step_A_72000]

theorem eq_A_74000 : apply_exact 117649 74000 0 val_A_0 = val_A_74000 := by
  rw [apply_exact_add 117649 72000 2000 0 val_A_0]
  rw [eq_A_72000]
  rw [step_A_74000]

theorem eq_A_76000 : apply_exact 117649 76000 0 val_A_0 = val_A_76000 := by
  rw [apply_exact_add 117649 74000 2000 0 val_A_0]
  rw [eq_A_74000]
  rw [step_A_76000]

theorem eq_A_78000 : apply_exact 117649 78000 0 val_A_0 = val_A_78000 := by
  rw [apply_exact_add 117649 76000 2000 0 val_A_0]
  rw [eq_A_76000]
  rw [step_A_78000]

theorem eq_A_80000 : apply_exact 117649 80000 0 val_A_0 = val_A_80000 := by
  rw [apply_exact_add 117649 78000 2000 0 val_A_0]
  rw [eq_A_78000]
  rw [step_A_80000]

theorem eq_A_82000 : apply_exact 117649 82000 0 val_A_0 = val_A_82000 := by
  rw [apply_exact_add 117649 80000 2000 0 val_A_0]
  rw [eq_A_80000]
  rw [step_A_82000]

theorem eq_A_84000 : apply_exact 117649 84000 0 val_A_0 = val_A_84000 := by
  rw [apply_exact_add 117649 82000 2000 0 val_A_0]
  rw [eq_A_82000]
  rw [step_A_84000]

theorem eq_A_86000 : apply_exact 117649 86000 0 val_A_0 = val_A_86000 := by
  rw [apply_exact_add 117649 84000 2000 0 val_A_0]
  rw [eq_A_84000]
  rw [step_A_86000]

theorem eq_A_88000 : apply_exact 117649 88000 0 val_A_0 = val_A_88000 := by
  rw [apply_exact_add 117649 86000 2000 0 val_A_0]
  rw [eq_A_86000]
  rw [step_A_88000]

theorem eq_A_90000 : apply_exact 117649 90000 0 val_A_0 = val_A_90000 := by
  rw [apply_exact_add 117649 88000 2000 0 val_A_0]
  rw [eq_A_88000]
  rw [step_A_90000]

theorem eq_A_92000 : apply_exact 117649 92000 0 val_A_0 = val_A_92000 := by
  rw [apply_exact_add 117649 90000 2000 0 val_A_0]
  rw [eq_A_90000]
  rw [step_A_92000]

theorem eq_A_94000 : apply_exact 117649 94000 0 val_A_0 = val_A_94000 := by
  rw [apply_exact_add 117649 92000 2000 0 val_A_0]
  rw [eq_A_92000]
  rw [step_A_94000]

theorem eq_A_96000 : apply_exact 117649 96000 0 val_A_0 = val_A_96000 := by
  rw [apply_exact_add 117649 94000 2000 0 val_A_0]
  rw [eq_A_94000]
  rw [step_A_96000]

theorem eq_A_98000 : apply_exact 117649 98000 0 val_A_0 = val_A_98000 := by
  rw [apply_exact_add 117649 96000 2000 0 val_A_0]
  rw [eq_A_96000]
  rw [step_A_98000]

theorem eq_A_100000 : apply_exact 117649 100000 0 val_A_0 = val_A_100000 := by
  rw [apply_exact_add 117649 98000 2000 0 val_A_0]
  rw [eq_A_98000]
  rw [step_A_100000]

theorem eq_A_102000 : apply_exact 117649 102000 0 val_A_0 = val_A_102000 := by
  rw [apply_exact_add 117649 100000 2000 0 val_A_0]
  rw [eq_A_100000]
  rw [step_A_102000]

theorem eq_A_104000 : apply_exact 117649 104000 0 val_A_0 = val_A_104000 := by
  rw [apply_exact_add 117649 102000 2000 0 val_A_0]
  rw [eq_A_102000]
  rw [step_A_104000]

theorem eq_A_106000 : apply_exact 117649 106000 0 val_A_0 = val_A_106000 := by
  rw [apply_exact_add 117649 104000 2000 0 val_A_0]
  rw [eq_A_104000]
  rw [step_A_106000]

theorem eq_A_108000 : apply_exact 117649 108000 0 val_A_0 = val_A_108000 := by
  rw [apply_exact_add 117649 106000 2000 0 val_A_0]
  rw [eq_A_106000]
  rw [step_A_108000]

theorem eq_A_110000 : apply_exact 117649 110000 0 val_A_0 = val_A_110000 := by
  rw [apply_exact_add 117649 108000 2000 0 val_A_0]
  rw [eq_A_108000]
  rw [step_A_110000]

theorem eq_A_112000 : apply_exact 117649 112000 0 val_A_0 = val_A_112000 := by
  rw [apply_exact_add 117649 110000 2000 0 val_A_0]
  rw [eq_A_110000]
  rw [step_A_112000]

theorem eq_A_114000 : apply_exact 117649 114000 0 val_A_0 = val_A_114000 := by
  rw [apply_exact_add 117649 112000 2000 0 val_A_0]
  rw [eq_A_112000]
  rw [step_A_114000]

theorem eq_A_116000 : apply_exact 117649 116000 0 val_A_0 = val_A_116000 := by
  rw [apply_exact_add 117649 114000 2000 0 val_A_0]
  rw [eq_A_114000]
  rw [step_A_116000]

theorem eq_A_117648 : apply_exact 117649 117648 0 val_A_0 = val_A_117648 := by
  rw [apply_exact_add 117649 116000 1648 0 val_A_0]
  rw [eq_A_116000]
  rw [step_A_117648]

theorem eq_B_0 : apply_exact 16807 0 0 val_B_0 = val_B_0 := rfl

theorem eq_B_2000 : apply_exact 16807 2000 0 val_B_0 = val_B_2000 := by
  rw [apply_exact_add 16807 0 2000 0 val_B_0]
  rw [eq_B_0]
  rw [step_B_2000]

theorem eq_B_4000 : apply_exact 16807 4000 0 val_B_0 = val_B_4000 := by
  rw [apply_exact_add 16807 2000 2000 0 val_B_0]
  rw [eq_B_2000]
  rw [step_B_4000]

theorem eq_B_6000 : apply_exact 16807 6000 0 val_B_0 = val_B_6000 := by
  rw [apply_exact_add 16807 4000 2000 0 val_B_0]
  rw [eq_B_4000]
  rw [step_B_6000]

theorem eq_B_8000 : apply_exact 16807 8000 0 val_B_0 = val_B_8000 := by
  rw [apply_exact_add 16807 6000 2000 0 val_B_0]
  rw [eq_B_6000]
  rw [step_B_8000]

theorem eq_B_10000 : apply_exact 16807 10000 0 val_B_0 = val_B_10000 := by
  rw [apply_exact_add 16807 8000 2000 0 val_B_0]
  rw [eq_B_8000]
  rw [step_B_10000]

theorem eq_B_12000 : apply_exact 16807 12000 0 val_B_0 = val_B_12000 := by
  rw [apply_exact_add 16807 10000 2000 0 val_B_0]
  rw [eq_B_10000]
  rw [step_B_12000]

theorem eq_B_14000 : apply_exact 16807 14000 0 val_B_0 = val_B_14000 := by
  rw [apply_exact_add 16807 12000 2000 0 val_B_0]
  rw [eq_B_12000]
  rw [step_B_14000]

theorem eq_B_16000 : apply_exact 16807 16000 0 val_B_0 = val_B_16000 := by
  rw [apply_exact_add 16807 14000 2000 0 val_B_0]
  rw [eq_B_14000]
  rw [step_B_16000]

theorem eq_B_16806 : apply_exact 16807 16806 0 val_B_0 = val_B_16806 := by
  rw [apply_exact_add 16807 16000 806 0 val_B_0]
  rw [eq_B_16000]
  rw [step_B_16806]

theorem sumA : a 117649 = val_A_117648.2.2 := by
  have h := a_eq_apply_exact 117649 (by omega)
  rw [h]
  rw [eq_A_117648]

theorem sumB : a 16807 = val_B_16806.2.2 := by
  have h := a_eq_apply_exact 16807 (by omega)
  rw [h]
  rw [eq_B_16806]

