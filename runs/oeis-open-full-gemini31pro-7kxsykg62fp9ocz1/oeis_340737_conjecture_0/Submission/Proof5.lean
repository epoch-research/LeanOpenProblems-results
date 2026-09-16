import Mathlib
open Nat
open Polynomial Filter Topology
open scoped Polynomial

noncomputable def P (k : ℕ) : ℝ[X] := X^k * (1 - X)^k
noncomputable def E_poly (k : ℕ) : ℝ[X] := - X^(k-1) * (1 - X)^(k-1) * (X^2 - (2*k+1 : ℝ[X]) * X + (k : ℝ[X]))
lemma E_eval_zero (k : ℕ) : eval 0 (E_poly (k+2)) = 0 := by unfold E_poly; dsimp; simp
lemma E_eval_one (k : ℕ) : eval 1 (E_poly (k+2)) = 0 := by unfold E_poly; dsimp; simp

noncomputable def Q : ℕ → ℝ[X]
| 0 => 1
| 1 => - X^2 + 3 * X - 3
| (k+2) => (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * Q (k+1) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * Q k + E_poly (k+2)

lemma Q_ind (k : ℕ) (h1 : derivative (Q (k+1)) + Q (k+1) = P (k+1)) (h0 : derivative (Q k) + Q k = P k) :
  derivative (Q (k+2)) + Q (k+2) = P (k+2) := by
  unfold Q
  dsimp
  have H : derivative ((- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * Q (k + 1) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * Q k + E_poly (k + 2)) =
    (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * derivative (Q (k + 1)) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * derivative (Q k) + derivative (E_poly (k + 2)) := by
    simp [derivative_mul, derivative_add, derivative_sub, derivative_natCast]
  rw [H]
  have H2 : (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * derivative (Q (k + 1)) +
    ((k+2:ℝ[X])*(k+1:ℝ[X])) * derivative (Q k) + derivative (E_poly (k + 2)) +
    ((- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * Q (k + 1) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * Q k + E_poly (k + 2)) =
    (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * (derivative (Q (k + 1)) + Q (k + 1)) +
      ((k+2:ℝ[X])*(k+1:ℝ[X])) * (derivative (Q k) + Q k) +
      derivative (E_poly (k + 2)) + E_poly (k + 2) := by ring
  rw [H2, h1, h0]
  unfold P E_poly
  dsimp
  simp [derivative_mul, derivative_pow, derivative_sub, derivative_add, derivative_natCast]
  have h_X2 : (X : ℝ[X])^(k+2) = X^k * X^2 := by ring
  have h_X1 : (X : ℝ[X])^(k+1) = X^k * X := by ring
  have h_Y2 : (1 - X : ℝ[X])^(k+2) = (1-X)^k * (1-X)^2 := by ring
  have h_Y1 : (1 - X : ℝ[X])^(k+1) = (1-X)^k * (1-X) := by ring
  rw [h_X2, h_X1, h_Y2, h_Y1]
  rw [map_ofNat (C : ℝ →+* ℝ[X]) 2]
  ring

lemma Q_eq_P (k : ℕ) : derivative (Q k) + Q k = P k := by
  induction' k using Nat.strong_induction_on with k ih
  rcases k with _ | _ | k
  · dsimp [Q, P]; simp
  · change derivative (- X^2 + 3 * X - 3 : ℝ[X]) + (- X^2 + 3 * X - 3) = X^1 * (1 - X)^1
    simp; ring
  · apply Q_ind k
    · apply ih (k+1) (by omega)
    · apply ih k (by omega)

lemma mvt_poly (k : ℕ) :
  ∃ c ∈ Set.Ioo (0 : ℝ) 1,
    ((Q k).eval 1) * Real.exp 1 - ((Q k).eval 0) = ((P k).eval c) * Real.exp c := by
  have h_deriv : ∀ x, HasDerivAt (fun y => ((Q k).eval y) * Real.exp y) (((P k).eval x) * Real.exp x) x := by
    intro x
    have h1 := ((Q k).hasDerivAt x)
    have h2 := (Real.hasDerivAt_exp x)
    have h3 := HasDerivAt.mul h1 h2
    have h4 : (derivative (Q k)).eval x * Real.exp x + (Q k).eval x * Real.exp x = (P k).eval x * Real.exp x := by
      have h5 : (derivative (Q k)).eval x + (Q k).eval x = (P k).eval x := by
        have h_eq := Q_eq_P k
        rw [← eval_add, h_eq]
      calc (derivative (Q k)).eval x * Real.exp x + (Q k).eval x * Real.exp x
        _ = ((derivative (Q k)).eval x + (Q k).eval x) * Real.exp x := by ring
        _ = (P k).eval x * Real.exp x := by rw [h5]
    exact h4 ▸ h3
  have h_mvt := exists_hasDerivAt_eq_slope (fun y => ((Q k).eval y) * Real.exp y) (fun x => ((P k).eval x) * Real.exp x) (by norm_num : (0:ℝ) < 1)
    (fun x _ => (h_deriv x).continuousAt.continuousWithinAt)
    (fun x _ => h_deriv x)
  rcases h_mvt with ⟨c, hc1, hc2⟩
  use c
  constructor
  · exact hc1
  · have hc3 : (1 : ℝ) - 0 = 1 := by ring
    rw [hc3, div_one] at hc2
    dsimp at hc2
    have hQ0 : Real.exp 0 = 1 := Real.exp_zero
    rw [hQ0, mul_one] at hc2
    exact hc2.symm

lemma P_bound (k : ℕ) (c : ℝ) (hc1 : 0 < c) (hc2 : c < 1) :
  (P k).eval c * Real.exp c ≤ Real.exp 1 / 4^k := by
  unfold P
  simp
  have h1 : c * (1 - c) ≤ 1 / 4 := by
    have h2 : c * (1 - c) = 1/4 - (c - 1/2)^2 := by ring
    rw [h2]
    linarith [sq_nonneg (c - 1/2)]
  have h2 : 0 ≤ c * (1 - c) := by
    have : 0 ≤ c := by linarith
    have : 0 ≤ 1 - c := by linarith
    positivity
  have h3 : (c * (1 - c))^k ≤ (1 / 4)^k := by gcongr
  have h4 : Real.exp c ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    linarith
  have h5 : c^k * (1 - c)^k = (c * (1 - c))^k := by rw [mul_pow]
  rw [h5]
  have h6 : (c * (1 - c))^k * Real.exp c ≤ (1 / 4)^k * Real.exp 1 := by
    have : 0 ≤ (c * (1 - c))^k := by positivity
    have : 0 ≤ Real.exp c := by positivity
    nlinarith
  have h7 : (1 / 4 : ℝ)^k * Real.exp 1 = Real.exp 1 / 4^k := by
    calc (1 / 4 : ℝ)^k * Real.exp 1
      _ = (1^k / 4^k : ℝ) * Real.exp 1 := by rw [div_pow]
      _ = (1 / 4^k) * Real.exp 1 := by rw [one_pow]
      _ = Real.exp 1 / 4^k := by ring
  rw [← h7]
  exact h6

lemma P_pos (k : ℕ) (c : ℝ) (hc1 : 0 < c) (hc2 : c < 1) :
  0 ≤ (P k).eval c * Real.exp c := by
  unfold P
  simp
  have : 0 ≤ c := by linarith
  have : 0 ≤ 1 - c := by linarith
  positivity

lemma Q_eval_zero_rec (k : ℕ) : eval 0 (Q (k+2)) = - (4*(k+2:ℝ)-2)*(k+2) * eval 0 (Q (k+1)) + (k+2)*(k+1) * eval 0 (Q k) := by
  have H : Q (k+2) = (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * Q (k+1) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * Q k + E_poly (k+2) := by rfl
  rw [H, eval_add, eval_add, eval_mul, eval_mul]
  have hE := E_eval_zero k
  rw [hE, add_zero]
  simp

lemma Q_eval_one_rec (k : ℕ) : eval 1 (Q (k+2)) = - (4*(k+2:ℝ)-2)*(k+2) * eval 1 (Q (k+1)) + (k+2)*(k+1) * eval 1 (Q k) := by
  have H : Q (k+2) = (- (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])) * Q (k+1) + ((k+2:ℝ[X])*(k+1:ℝ[X])) * Q k + E_poly (k+2) := by rfl
  rw [H, eval_add, eval_add, eval_mul, eval_mul]
  have hE := E_eval_one k
  rw [hE, add_zero]
  simp

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
  · exact h_mod

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

lemma A_int_even_rel (k : ℕ) : 2 * A_int (2*k + 4) = (2*(k:ℤ) + 5) * A_int (2*k + 3) + A_int (2*k + 1) := by
  have h_even := A_int_even k
  have h_odd0 := A_int_odd k
  linarith

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
  · exact h_mod

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

lemma B_int_even_rel (k : ℕ) : 2 * B_int (2*k + 4) = (2*(k:ℤ) + 5) * B_int (2*k + 3) + B_int (2*k + 1) := by
  have h_even := B_int_even k
  have h_odd0 := B_int_odd k
  linarith

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

lemma B_int_odd_pos : ∀ k, 1 ≤ B_int (2*k + 1)
| 0 => by
  change 1 ≤ B_int 1
  have : B_int 1 = 1 := by rw [B_int]
  rw [this]
| 1 => by
  change 1 ≤ B_int 3
  have h := B_int_odd 0
  change B_int 3 = 2 * B_int 2 + 3 * B_int 1 at h
  have b1 : B_int 1 = 1 := by rw [B_int]
  have b2 : B_int 2 = 2 := by rw [B_int]
  linarith
| (k+2) => by
  have h := B_int_jump k
  have h1 := B_int_odd_pos (k+1)
  have h2 := B_int_odd_pos k
  have h_pos : 0 ≤ 4 * (k : ℤ) + 10 := by omega
  have e1 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
  have e2 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [e1]
  rw [e2] at h1
  nlinarith

lemma B_int_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ B_int n := by
  by_cases h : n % 2 = 1
  · have : ∃ k, n = 2*k + 1 := ⟨n/2, by omega⟩
    rcases this with ⟨k, rfl⟩
    apply B_int_odd_pos
  · have : ∃ k, n = 2*k + 2 := ⟨n/2 - 1, by omega⟩
    rcases this with ⟨k, rfl⟩
    rcases k with _ | k
    · have : B_int 2 = 2 := by rw [B_int]
      rw [this]
      norm_num
    · have h_rel := B_int_even_rel k
      have h1 := B_int_odd_pos (k+1)
      have h2 := B_int_odd_pos k
      have hk : 0 ≤ 2 * (k : ℤ) + 5 := by omega
      have e1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [e1] at h1
      have h3 : 2 * B_int (2 * k + 4) ≥ 2 := by
        calc 2 * B_int (2 * k + 4) = (2 * (k : ℤ) + 5) * B_int (2 * k + 3) + B_int (2 * k + 1) := h_rel
          _ ≥ (2 * (k : ℤ) + 5) * 1 + 1 := by nlinarith
          _ ≥ 2 := by omega
      have e2 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
      rw [e2]
      omega

noncomputable def a_seq (k : ℕ) : ℝ := (-1 : ℝ)^(k+1) * ((k+1).factorial : ℝ) * (A_int (2*k + 1) : ℝ)
noncomputable def b_seq (k : ℕ) : ℝ := (-1 : ℝ)^(k+1) * ((k+1).factorial : ℝ) * (B_int (2*k + 1) : ℝ)

lemma a_seq_rec (k : ℕ) : a_seq (k + 2) = - (4*(k+3:ℝ)-2)*(k+3) * a_seq (k+1) + (k+3)*(k+2) * a_seq k := by
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

lemma two_step_ind (P : ℕ → Prop) (h0 : P 0) (h1 : P 1) (h2 : ∀ k, P k → P (k+1) → P (k+2)) : ∀ n, P n := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | k
  · exact h0
  · exact h1
  · apply h2
    · apply ih k; omega
    · apply ih (k+1); omega

lemma a_seq_eq_Q (k : ℕ) : a_seq k = eval 0 (Q (k+1)) := by
  apply two_step_ind (fun m => a_seq m = eval 0 (Q (m+1))) _ _ _ k
  · unfold a_seq
    have : A_int 1 = 3 := by rw [A_int]
    rw [this]
    change (-1 : ℝ)^(0+1) * ((0+1).factorial : ℝ) * 3 = eval 0 (- X^2 + 3 * X - 3 : ℝ[X])
    simp; ring
  · unfold a_seq
    have : A_int 3 = 19 := by rw [A_int]; rfl
    rw [this]
    change (-1 : ℝ)^(1+1) * ((1+1).factorial : ℝ) * 19 = eval 0 (-(4 * (2:ℝ[X]) - 2) * (2:ℝ[X]) * (- X^2 + 3 * X - 3 : ℝ[X]) + (2:ℝ[X])*(1:ℝ[X]) * 1 + E_poly 2)
    have : eval 0 (E_poly 2) = 0 := E_eval_zero 0
    simp [this]
    ring
  · intro m hm0 hm1
    have hR := a_seq_rec m
    have hQ := Q_eval_zero_rec (m+1)
    have e1 : m + 1 + 2 = m + 3 := by omega
    have e2 : m + 1 + 1 = m + 2 := by omega
    rw [e1, e2] at hQ
    rw [hR]
    rw [hm0, hm1]
    rw [hQ]
    push_cast
    ring

lemma b_seq_eq_Q (k : ℕ) : b_seq k = eval 1 (Q (k+1)) := by
  apply two_step_ind (fun m => b_seq m = eval 1 (Q (m+1))) _ _ _ k
  · unfold b_seq
    have : B_int 1 = 1 := by rw [B_int]
    rw [this]
    change (-1 : ℝ)^(0+1) * ((0+1).factorial : ℝ) * 1 = eval 1 (- X^2 + 3 * X - 3 : ℝ[X])
    simp; ring
  · unfold b_seq
    have : B_int 3 = 7 := by rw [B_int]; rfl
    rw [this]
    change (-1 : ℝ)^(1+1) * ((1+1).factorial : ℝ) * 7 = eval 1 (-(4 * (2:ℝ[X]) - 2) * (2:ℝ[X]) * (- X^2 + 3 * X - 3 : ℝ[X]) + (2:ℝ[X])*(1:ℝ[X]) * 1 + E_poly 2)
    have : eval 1 (E_poly 2) = 0 := E_eval_one 0
    simp [this]
    ring
  · intro m hm0 hm1
    have hR := b_seq_rec m
    have hQ := Q_eval_one_rec (m+1)
    have e1 : m + 1 + 2 = m + 3 := by omega
    have e2 : m + 1 + 1 = m + 2 := by omega
    rw [e1, e2] at hQ
    rw [hR]
    rw [hm0, hm1]
    rw [hQ]
    push_cast
    ring
