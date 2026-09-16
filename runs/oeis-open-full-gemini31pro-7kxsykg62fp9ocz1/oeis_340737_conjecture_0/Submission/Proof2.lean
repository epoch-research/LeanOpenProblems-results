import Mathlib
open Nat
open Polynomial Filter Topology
open scoped Polynomial

-- Sequences and bounds
noncomputable def A_int (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | n' + 3 =>
    let n := n' + 3
    if n % 2 = 0 then
      let c1 : ℤ := (n + 2) / 2
      let c2 : ℤ := (n - 2) / 2
      c1 * A_int (n - 1) - A_int (n - 2) - c2 * A_int (n - 3)
    else
      2 * A_int (n - 1) + n * A_int (n - 2)
termination_by n

noncomputable def B_int (n : ℕ) : ℤ :=
  match n with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n' + 3 =>
    let n := n' + 3
    if n % 2 = 0 then
      let c1 : ℤ := (n + 2) / 2
      let c2 : ℤ := (n - 2) / 2
      c1 * B_int (n - 1) - B_int (n - 2) - c2 * B_int (n - 3)
    else
      2 * B_int (n - 1) + n * B_int (n - 2)
termination_by n

lemma A_int_odd (k : ℕ) : A_int (2*k + 3) = 2 * A_int (2*k + 2) + (2*k + 3) * A_int (2*k + 1) := by
  change A_int (2*k + 0 + 3) = _
  rw [A_int]
  dsimp
  have h_mod : (2*k + 3) % 2 = 1 := by omega
  rw [if_neg]
  · congr 1; omega
  · omega

lemma A_int_even (k : ℕ) : A_int (2*k + 4) = (k + 3) * A_int (2*k + 3) - A_int (2*k + 2) - (k + 1) * A_int (2*k + 1) := by
  change A_int (2*k + 1 + 3) = _
  rw [A_int]
  dsimp
  have h_mod : (2*k + 4) % 2 = 0 := by omega
  rw [if_pos h_mod]
  have H : (2 * (k : ℤ) + 1 + 3 + 2) / 2 = k + 3 := by omega
  have H2 : (2 * (k : ℤ) + 1 + 3 - 2) / 2 = k + 1 := by omega
  rw [H, H2]
  congr 2 <;> omega

lemma A_int_jump (k : ℕ) : A_int (2*k + 5) = (4*(k:ℤ) + 10) * A_int (2*k + 3) + A_int (2*k + 1) := by
  have h1 : A_int (2*k + 5) = 2 * A_int (2*k + 4) + (2*(k:ℤ) + 5) * A_int (2*k + 3) := by
    have h := A_int_odd (k+1)
    have e1 : 2 * (k + 1) + 3 = 2 * k + 5 := by omega
    have e2 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
    have e3 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    rw [e1, e2, e3] at h
    push_cast at h
    exact h
  have h2 := A_int_even k
  have h3 := A_int_odd k
  linarith

lemma B_int_odd (k : ℕ) : B_int (2*k + 3) = 2 * B_int (2*k + 2) + (2*k + 3) * B_int (2*k + 1) := by
  change B_int (2*k + 0 + 3) = _
  rw [B_int]
  dsimp
  have h_mod : (2*k + 3) % 2 = 1 := by omega
  rw [if_neg]
  · congr 1; omega
  · omega

lemma B_int_even (k : ℕ) : B_int (2*k + 4) = (k + 3) * B_int (2*k + 3) - B_int (2*k + 2) - (k + 1) * B_int (2*k + 1) := by
  change B_int (2*k + 1 + 3) = _
  rw [B_int]
  dsimp
  have h_mod : (2*k + 4) % 2 = 0 := by omega
  rw [if_pos h_mod]
  have H : (2 * (k : ℤ) + 1 + 3 + 2) / 2 = k + 3 := by omega
  have H2 : (2 * (k : ℤ) + 1 + 3 - 2) / 2 = k + 1 := by omega
  rw [H, H2]
  congr 2 <;> omega

lemma B_int_jump (k : ℕ) : B_int (2*k + 5) = (4*(k:ℤ) + 10) * B_int (2*k + 3) + B_int (2*k + 1) := by
  have h1 : B_int (2*k + 5) = 2 * B_int (2*k + 4) + (2*(k:ℤ) + 5) * B_int (2*k + 3) := by
    have h := B_int_odd (k+1)
    have e1 : 2 * (k + 1) + 3 = 2 * k + 5 := by omega
    have e2 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
    have e3 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    rw [e1, e2, e3] at h
    push_cast at h
    exact h
  have h2 := B_int_even k
  have h3 := B_int_odd k
  linarith

noncomputable def a_seq (k : ℕ) : ℝ := (-1 : ℝ)^(k+1) * ((k+1).factorial : ℝ) * (A_int (2*k + 1) : ℝ)
noncomputable def b_seq (k : ℕ) : ℝ := (-1 : ℝ)^(k+1) * ((k+1).factorial : ℝ) * (B_int (2*k + 1) : ℝ)

lemma a_seq_rec (k : ℕ) : a_seq (k + 2) = - (4*(k+3:ℝ)-2)*(k+3) * a_seq (k+1) + (k+3)*(k+2) * a_seq k := by
  -- Let's change the indices. The target index in a_seq is k.
  -- Wait! Previously I used k+3 in a_seq_rec!
  -- Let's write the lemma for k+2 in terms of k+1 and k.
  -- a_seq (k+2) = (-1)^(k+3) (k+3)! A_int(2k+5)
  unfold a_seq
  have h := A_int_jump k
  have hR : (A_int (2 * k + 5) : ℝ) = (4 * (k:ℝ) + 10) * (A_int (2 * k + 3) : ℝ) + (A_int (2 * k + 1) : ℝ) := by exact_mod_cast h
  have e1 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
  have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [e1, e2]
  rw [hR]
  have fact_3 : ((k+3).factorial : ℝ) = (k+3)*(k+2)*((k+1).factorial : ℝ) := by
    have : (k+3).factorial = (k+3)*(k+2)*(k+1).factorial := by
      change (k+1+2).factorial = _
      rw [Nat.factorial_succ, Nat.factorial_succ]
      ring
    exact_mod_cast this
  have fact_2 : ((k+2).factorial : ℝ) = (k+2)*((k+1).factorial : ℝ) := by
    have : (k+2).factorial = (k+2)*(k+1).factorial := rfl
    exact_mod_cast this
  have e3 : k + 2 + 1 = k + 3 := by omega
  have e4 : k + 1 + 1 = k + 2 := by omega
  rw [e3, e4]
  rw [fact_3, fact_2]
  have sign_3 : (-1 : ℝ)^(k+3) = -1 * (-1)^(k+2) := by ring
  have sign_2 : (-1 : ℝ)^(k+2) = -1 * (-1)^(k+1) := by ring
  rw [sign_3, sign_2]
  ring

lemma b_seq_rec (k : ℕ) : b_seq (k + 2) = - (4*(k+3:ℝ)-2)*(k+3) * b_seq (k+1) + (k+3)*(k+2) * b_seq k := by
  unfold b_seq
  have h := B_int_jump k
  have hR : (B_int (2 * k + 5) : ℝ) = (4 * (k:ℝ) + 10) * (B_int (2 * k + 3) : ℝ) + (B_int (2 * k + 1) : ℝ) := by exact_mod_cast h
  have e1 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
  have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [e1, e2]
  rw [hR]
  have fact_3 : ((k+3).factorial : ℝ) = (k+3)*(k+2)*((k+1).factorial : ℝ) := by
    have : (k+3).factorial = (k+3)*(k+2)*(k+1).factorial := by
      change (k+1+2).factorial = _
      rw [Nat.factorial_succ, Nat.factorial_succ]
      ring
    exact_mod_cast this
  have fact_2 : ((k+2).factorial : ℝ) = (k+2)*((k+1).factorial : ℝ) := by
    have : (k+2).factorial = (k+2)*(k+1).factorial := rfl
    exact_mod_cast this
  have e3 : k + 2 + 1 = k + 3 := by omega
  have e4 : k + 1 + 1 = k + 2 := by omega
  rw [e3, e4]
  rw [fact_3, fact_2]
  have sign_3 : (-1 : ℝ)^(k+3) = -1 * (-1)^(k+2) := by ring
  have sign_2 : (-1 : ℝ)^(k+2) = -1 * (-1)^(k+1) := by ring
  rw [sign_3, sign_2]
  ring
