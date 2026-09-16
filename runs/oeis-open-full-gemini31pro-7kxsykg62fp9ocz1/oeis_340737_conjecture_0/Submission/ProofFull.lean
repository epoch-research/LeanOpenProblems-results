import Mathlib
open Nat
open Polynomial Filter Topology
open scoped Polynomial

-- 1. Polynomials
noncomputable def P (k : ℕ) : ℝ[X] := X^k * (1 - X)^k

noncomputable def E_poly (k : ℕ) : ℝ[X] :=
  - X^(k-1) * (1 - X)^(k-1) * (X^2 - (2*k+1 : ℝ[X]) * X + (k : ℝ[X]))

lemma E_eval_zero (k : ℕ) : eval 0 (E_poly (k+2)) = 0 := by unfold E_poly; dsimp; simp
lemma E_eval_one (k : ℕ) : eval 1 (E_poly (k+2)) = 0 := by unfold E_poly; dsimp; simp

noncomputable def Q : ℕ → ℝ[X]
| 0 => 1
| 1 => - X^2 + 3 * X - 3
| (k+2) =>
  let c1 : ℝ[X] := - (4*(k+2:ℝ[X])-2)*(k+2:ℝ[X])
  let c2 : ℝ[X] := (k+2:ℝ[X])*(k+1:ℝ[X])
  c1 * Q (k+1) + c2 * Q k + E_poly (k+2)

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

-- 2. Integer sequences
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

lemma A_int_1 : A_int 1 = 3 := by rw [A_int]
lemma A_int_3 : A_int 3 = 19 := by
  change A_int (0+3) = 19
  rw [A_int]
  rw [if_neg (by omega)]
  change 2 * A_int 2 + 3 * A_int 1 = 19
  have a1 : A_int 1 = 3 := by rw [A_int]
  have a2 : A_int 2 = 5 := by rw [A_int]
  omega

lemma B_int_1 : B_int 1 = 1 := by rw [B_int]
lemma B_int_3 : B_int 3 = 7 := by
  change B_int (0+3) = 7
  rw [B_int]
  rw [if_neg (by omega)]
  change 2 * B_int 2 + 3 * B_int 1 = 7
  have b1 : B_int 1 = 1 := by rw [B_int]
  have b2 : B_int 2 = 2 := by rw [B_int]
  omega

lemma A_int_odd (k : ℕ) : A_int (2*k + 3) = 2 * A_int (2*k + 2) + (2*k + 3) * A_int (2*k + 1) := by
  change A_int (2*k + 0 + 3) = _
  rw [A_int]
  dsimp
  rw [if_neg (by omega)]
  have : 2 * k + 3 - 2 = 2 * k + 1 := by omega
  rw [this]

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
  rw [if_neg (by omega)]
  have : 2 * k + 3 - 2 = 2 * k + 1 := by omega
  rw [this]

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
    rw [A_int_1]
    have : (0+1).factorial = 1 := rfl
    rw [this]
    have : eval 0 (Q 1) = -3 := by rw [Q]; simp
    rw [this]
    ring
  · unfold a_seq
    rw [A_int_3]
    have : (1+1).factorial = 2 := rfl
    rw [this]
    have : Q 2 = Q (0+2) := rfl
    rw [this, Q]
    have hz : eval 0 (E_poly 2) = 0 := E_eval_zero 0
    simp [hz]
    have hq1 : eval 0 (Q 1) = -3 := by rw [Q]; simp
    have hq0 : eval 0 (Q 0) = 1 := by rw [Q]; simp
    rw [hq1, hq0]
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
    rw [B_int_1]
    have : (0+1).factorial = 1 := rfl
    rw [this]
    have : eval 1 (Q 1) = -1 := by rw [Q]; simp
    rw [this]
    ring
  · unfold b_seq
    rw [B_int_3]
    have : (1+1).factorial = 2 := rfl
    rw [this]
    have : Q 2 = Q (0+2) := rfl
    rw [this, Q]
    have hz : eval 1 (E_poly 2) = 0 := E_eval_one 0
    simp [hz]
    have hq1 : eval 1 (Q 1) = -1 := by rw [Q]; simp
    have hq0 : eval 1 (Q 0) = 1 := by rw [Q]; simp
    rw [hq1, hq0]
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

-- 3. Bounds and E_int limits
noncomputable def E_int (A_int B_int : ℕ → ℝ) (n : ℕ) : ℝ := B_int n * Real.exp 1 - A_int n

lemma E_int_odd_bound (k : ℕ) :
  |E_int (fun n => A_int n) (fun n => B_int n) (2*k+1)| ≤ Real.exp 1 / (((k+1).factorial : ℝ) * 4^(k+1)) := by
  have ha := a_seq_eq_Q k
  have hb := b_seq_eq_Q k
  have hmvt := mvt_poly (k+1)
  rcases hmvt with ⟨c, hc_Ioo, hc_eq⟩
  unfold E_int
  have e1 : b_seq k * Real.exp 1 - a_seq k = (-1 : ℝ)^(k+1) * ((k+1).factorial : ℝ) * ((B_int (2*k+1) : ℝ) * Real.exp 1 - (A_int (2*k+1) : ℝ)) := by
    unfold a_seq b_seq
    ring
  have h1 : 0 ≤ b_seq k * Real.exp 1 - a_seq k := by
    rw [hb, ha, hc_eq]
    apply P_pos (k+1) c hc_Ioo.1 hc_Ioo.2
  have h2 : b_seq k * Real.exp 1 - a_seq k ≤ Real.exp 1 / 4^(k+1) := by
    rw [hb, ha, hc_eq]
    exact P_bound (k+1) c hc_Ioo.1 hc_Ioo.2
  have h3 : |(-1 : ℝ)^(k+1) * ((k+1).factorial : ℝ) * ((B_int (2*k+1):ℝ) * Real.exp 1 - (A_int (2*k+1):ℝ))| ≤ Real.exp 1 / 4^(k+1) := by
    rw [← e1]
    rw [abs_of_nonneg h1]
    exact h2
  rw [abs_mul, abs_mul] at h3
  have h4 : |(-1 : ℝ)^(k+1)| = 1 := by simp
  have h5 : |((k+1).factorial : ℝ)| = ((k+1).factorial : ℝ) := by
    apply abs_of_nonneg
    positivity
  rw [h4, h5, one_mul] at h3
  have h_pos : (0 : ℝ) < (k+1).factorial := by exact_mod_cast Nat.factorial_pos _
  have h6 : |(B_int (2 * k + 1):ℝ) * Real.exp 1 - (A_int (2 * k + 1):ℝ)| ≤ (Real.exp 1 / 4^(k+1)) / ((k+1).factorial : ℝ) := by
    rw [le_div_iff₀ h_pos]
    rw [mul_comm]
    exact h3
  have h7 : (Real.exp 1 / 4^(k+1)) / ((k+1).factorial : ℝ) = Real.exp 1 / (((k+1).factorial : ℝ) * 4^(k+1)) := by ring
  rw [h7] at h6
  exact h6

lemma bound_even (k : ℕ) (hk : 1 ≤ k) :
  ((2*k+3 : ℝ)/2) / ((k+1).factorial * 4^(k+1)) + (1/2) / (k.factorial * 4^k) ≤ 4 / (k : ℝ) := by
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : ((k^2 : ℕ) : ℝ) ≤ (k+1).factorial := by
    have h1 : k^2 ≤ (k+1).factorial := by
      have : (k+1).factorial = (k+1) * k.factorial := rfl
      rw [this]
      have h2 : k ≤ k.factorial := Nat.self_le_factorial k
      calc k^2 = k * k := by ring
        _ ≤ (k+1) * k := by gcongr; omega
        _ ≤ (k+1) * k.factorial := by gcongr
    exact_mod_cast h1
  have hk2 : (k^2 : ℝ) = ((k^2 : ℕ) : ℝ) := by exact_mod_cast rfl

  have h3 : (k^2 : ℝ) ≤ (k+1).factorial * 4^(k+1) := by
    calc (k^2 : ℝ) = ((k^2 : ℕ) : ℝ) * 1 := by rw [← hk2, mul_one]
      _ ≤ (k+1).factorial * 1 := by gcongr
      _ ≤ (k+1).factorial * 4^(k+1) := by
        gcongr
        have : (1 : ℝ) = 1^(k+1) := by ring
        rw [this]
        gcongr
        norm_num

  have h4 : (2*k+3 : ℝ) / 2 / ((k+1).factorial * 4^(k+1)) ≤ (2*k+3) / 2 / (k^2 : ℝ) := by
    apply div_le_div_of_nonneg_left
    · positivity
    · positivity
    · exact h3

  have h7 : (k : ℝ) ≤ k.factorial * 4^k := by
    have hk1 : (k:ℝ) = (k:ℝ) * 1 := by ring
    rw [hk1]
    have hkfact : (k : ℝ) ≤ k.factorial := by exact_mod_cast Nat.self_le_factorial k
    calc (k : ℝ) * 1 ≤ k.factorial * 1 := by gcongr
      _ ≤ k.factorial * 4^k := by
        gcongr
        have : (1 : ℝ) = 1^k := by ring
        rw [this]
        gcongr
        norm_num

  have h8 : (1/2 : ℝ) / (k.factorial * 4^k) ≤ (1/2) / (k : ℝ) := by
    apply div_le_div_of_nonneg_left
    · norm_num
    · positivity
    · exact h7

  have h9 : (2*k+3 : ℝ) / 2 / (k^2 : ℝ) + (1/2) / (k : ℝ) ≤ 4 / (k : ℝ) := by
    rw [div_div, div_div]
    have e1 : (2*(k:ℝ)+3)/(2*(k:ℝ)^2) + 1/(2*(k:ℝ)) - 4/(k:ℝ) = (3 - 5*(k:ℝ))/(2*(k:ℝ)^2) := by
      have h_2k2 : 2 * (k:ℝ)^2 ≠ 0 := by positivity
      have h_2k : 2 * (k:ℝ) ≠ 0 := by positivity
      have h_k : (k:ℝ) ≠ 0 := by positivity
      rw [eq_div_iff h_2k2]
      calc ((2*(k:ℝ)+3)/(2*(k:ℝ)^2) + 1/(2*(k:ℝ)) - 4/(k:ℝ)) * (2*(k:ℝ)^2)
        _ = (2*(k:ℝ)+3)/(2*(k:ℝ)^2) * (2*(k:ℝ)^2) + (1/(2*(k:ℝ)) * (2*(k:ℝ))) * (k:ℝ) - (4/(k:ℝ) * (k:ℝ)) * (2*(k:ℝ)) := by ring
        _ = (2*(k:ℝ)+3) + 1 * (k:ℝ) - 4 * (2*(k:ℝ)) := by
          rw [div_mul_cancel₀ _ h_2k2, div_mul_cancel₀ _ h_2k, div_mul_cancel₀ _ h_k]
        _ = 3 - 5*(k:ℝ) := by ring
    have num_le : 3 - 5*(k:ℝ) ≤ 0 := by linarith
    have den_pos : 0 ≤ (2*k^2 : ℝ) := by positivity
    have e2 : (3 - 5*(k:ℝ))/(2*k^2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg num_le den_pos
    linarith
  linarith

lemma bound_even_shifted (k : ℕ) :
  ((2*k+5 : ℝ)/2) / (((k+2).factorial : ℝ) * 4^(k+2)) + (1/2) / (((k+1).factorial : ℝ) * 4^(k+1)) ≤ 4 / (k+1 : ℝ) := by
  have hk : 1 ≤ k+1 := by omega
  have h := bound_even (k+1) hk
  exact_mod_cast h

lemma E_int_even_bound (k : ℕ) :
  |E_int (fun n => A_int n) (fun n => B_int n) (2*k+4)| ≤ 4 * Real.exp 1 / (k+1 : ℝ) := by
  have hb3 := E_int_odd_bound (k+1)
  have hb1 := E_int_odd_bound k
  have e1_2k3 : 2*(k+1)+1 = 2*k+3 := by omega
  have e1_2k1 : 2*k+1 = 2*k+1 := by omega
  rw [e1_2k3] at hb3
  rw [e1_2k1] at hb1
  unfold E_int at hb3 hb1 ⊢
  have heA := A_int_even_rel k
  have heB := B_int_even_rel k
  have e1 : (B_int (2 * k + 4) : ℝ) * Real.exp 1 - (A_int (2 * k + 4) : ℝ) =
    ((2*(k:ℝ)+5)/2) * ((B_int (2*k+3):ℝ) * Real.exp 1 - (A_int (2*k+3):ℝ)) + (1/2) * ((B_int (2*k+1):ℝ) * Real.exp 1 - (A_int (2*k+1):ℝ)) := by
    calc (B_int (2 * k + 4):ℝ) * Real.exp 1 - (A_int (2 * k + 4):ℝ)
      _ = (2 * (B_int (2 * k + 4):ℝ)) * Real.exp 1 / 2 - (2 * (A_int (2 * k + 4):ℝ)) / 2 := by ring
      _ = ((2 * (k:ℝ) + 5) * (B_int (2 * k + 3):ℝ) + (B_int (2 * k + 1):ℝ)) * Real.exp 1 / 2 - ((2 * (k:ℝ) + 5) * (A_int (2 * k + 3):ℝ) + (A_int (2 * k + 1):ℝ)) / 2 := by
        have heB_r : 2 * (B_int (2*k+4):ℝ) = (2*(k:ℝ)+5) * (B_int (2*k+3):ℝ) + (B_int (2*k+1):ℝ) := by exact_mod_cast heB
        have heA_r : 2 * (A_int (2*k+4):ℝ) = (2*(k:ℝ)+5) * (A_int (2*k+3):ℝ) + (A_int (2*k+1):ℝ) := by exact_mod_cast heA
        rw [heB_r, heA_r]
      _ = ((2*(k:ℝ)+5)/2) * ((B_int (2*k+3):ℝ) * Real.exp 1 - (A_int (2*k+3):ℝ)) + (1/2) * ((B_int (2*k+1):ℝ) * Real.exp 1 - (A_int (2*k+1):ℝ)) := by ring
  rw [e1]
  have h_tri := abs_add_le (((2*(k:ℝ)+5)/2) * ((B_int (2*k+3):ℝ) * Real.exp 1 - (A_int (2*k+3):ℝ))) ((1/2) * ((B_int (2*k+1):ℝ) * Real.exp 1 - (A_int (2*k+1):ℝ)))
  have h_mul1 : |((2*(k:ℝ)+5)/2) * ((B_int (2*k+3):ℝ) * Real.exp 1 - (A_int (2*k+3):ℝ))| = ((2*(k:ℝ)+5)/2) * |(B_int (2*k+3):ℝ) * Real.exp 1 - (A_int (2*k+3):ℝ)| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
  have h_mul2 : |(1/2 : ℝ) * ((B_int (2*k+1):ℝ) * Real.exp 1 - (A_int (2*k+1):ℝ))| = (1/2 : ℝ) * |(B_int (2*k+1):ℝ) * Real.exp 1 - (A_int (2*k+1):ℝ)| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
  rw [h_mul1, h_mul2] at h_tri
  have h_b3 : ((2*(k:ℝ)+5)/2) * |(B_int (2*k+3):ℝ) * Real.exp 1 - (A_int (2*k+3):ℝ)| ≤ ((2*(k:ℝ)+5)/2) * (Real.exp 1 / (((k+2).factorial : ℝ) * 4^(k+2))) := by
    gcongr
  have h_b1 : (1/2 : ℝ) * |(B_int (2*k+1):ℝ) * Real.exp 1 - (A_int (2*k+1):ℝ)| ≤ (1/2 : ℝ) * (Real.exp 1 / (((k+1).factorial : ℝ) * 4^(k+1))) := by
    gcongr
  have h_sum : |((2 * ↑k + 5) / 2 * (↑(B_int (2 * k + 3)) * Real.exp 1 - ↑(A_int (2 * k + 3))) + 1 / 2 * (↑(B_int (2 * k + 1)) * Real.exp 1 - ↑(A_int (2 * k + 1))))| ≤
    ((2*(k:ℝ)+5)/2) / (((k+2).factorial : ℝ) * 4^(k+2)) * Real.exp 1 + (1/2) / (((k+1).factorial : ℝ) * 4^(k+1)) * Real.exp 1 := by
    calc |((2 * ↑k + 5) / 2 * (↑(B_int (2 * k + 3)) * Real.exp 1 - ↑(A_int (2 * k + 3))) + 1 / 2 * (↑(B_int (2 * k + 1)) * Real.exp 1 - ↑(A_int (2 * k + 1))))|
      _ ≤ ((2*(k:ℝ)+5)/2) * |(B_int (2*k+3):ℝ) * Real.exp 1 - (A_int (2*k+3):ℝ)| + (1/2 : ℝ) * |(B_int (2*k+1):ℝ) * Real.exp 1 - (A_int (2*k+1):ℝ)| := h_tri
      _ ≤ ((2*(k:ℝ)+5)/2) * (Real.exp 1 / (((k+2).factorial : ℝ) * 4^(k+2))) + (1/2 : ℝ) * (Real.exp 1 / (((k+1).factorial : ℝ) * 4^(k+1))) := by linarith
      _ = ((2*(k:ℝ)+5)/2) / (((k+2).factorial : ℝ) * 4^(k+2)) * Real.exp 1 + (1/2) / (((k+1).factorial : ℝ) * 4^(k+1)) * Real.exp 1 := by ring
  have h1 := bound_even_shifted k
  have h3 : (((2*k+5 : ℝ)/2) / (((k+2).factorial : ℝ) * 4^(k+2)) + (1/2) / (((k+1).factorial : ℝ) * 4^(k+1))) * Real.exp 1 ≤ (4 / (k+1 : ℝ)) * Real.exp 1 := by
    nlinarith [h1, Real.exp_pos 1 |>.le]
  have h4 : |(B_int (2 * k + 4):ℝ) * Real.exp 1 - (A_int (2 * k + 4):ℝ)| = |((2 * ↑k + 5) / 2 * (↑(B_int (2 * k + 3)) * Real.exp 1 - ↑(A_int (2 * k + 3))) + 1 / 2 * (↑(B_int (2 * k + 1)) * Real.exp 1 - ↑(A_int (2 * k + 1))))| := by rw [e1]
  have h5 : ((2*(k:ℝ)+5)/2) / (((k+2).factorial : ℝ) * 4^(k+2)) * Real.exp 1 + (1/2) / (((k+1).factorial : ℝ) * 4^(k+1)) * Real.exp 1 = (((2*k+5 : ℝ)/2) / (((k+2).factorial : ℝ) * 4^(k+2)) + (1/2) / (((k+1).factorial : ℝ) * 4^(k+1))) * Real.exp 1 := by ring
  have h6 : (((2*k+5 : ℝ)/2) / (((k+2).factorial : ℝ) * 4^(k+2)) + (1/2) / (((k+1).factorial : ℝ) * 4^(k+1))) * Real.exp 1 ≤ (4 / (k+1 : ℝ)) * Real.exp 1 := h3
  have h7 : (4 / (k+1 : ℝ)) * Real.exp 1 = 4 * Real.exp 1 / (k+1 : ℝ) := by ring
  linarith

lemma tendsto_E_odd_atTop : Tendsto (fun n => E_int (fun n => A_int n) (fun n => B_int n) (2*n+1)) atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _))
  · filter_upwards [eventually_ge_atTop 1]
    intro n hn
    have h1 : |E_int (fun n => A_int n) (fun n => B_int n) (2*n+1)| ≤ Real.exp 1 / (((n+1).factorial : ℝ) * 4^(n+1)) := E_int_odd_bound n
    have h2 : Real.exp 1 / (((n+1).factorial : ℝ) * 4^(n+1)) ≤ Real.exp 1 / (n : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      calc (n : ℝ) ≤ (n+1:ℝ) := by linarith
        _ ≤ ((n+1).factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial (n+1)
        _ = ((n+1).factorial : ℝ) * 1 := by ring
        _ ≤ ((n+1).factorial : ℝ) * 4^(n+1) := by
          gcongr
          have : (1 : ℝ) = 1^(n+1) := by ring
          rw [this]
          gcongr
          norm_num
    exact le_trans h1 h2
  · exact tendsto_const_div_atTop_nhds_zero_nat (Real.exp 1)

lemma tendsto_E_even_atTop : Tendsto (fun n => E_int (fun n => A_int n) (fun n => B_int n) (2*n)) atTop (nhds 0) := by
  have H : Tendsto (fun n => E_int (fun n => A_int n) (fun n => B_int n) (2*n+4)) atTop (nhds 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _))
    · filter_upwards [eventually_ge_atTop 1]
      intro n hn
      have h1 : |E_int (fun n => A_int n) (fun n => B_int n) (2*n+4)| ≤ 4 * Real.exp 1 / (n+1 : ℝ) := E_int_even_bound n
      have h2 : 4 * Real.exp 1 / (n+1 : ℝ) ≤ 4 * Real.exp 1 / (n : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        linarith
      exact le_trans h1 h2
    · exact tendsto_const_div_atTop_nhds_zero_nat (4 * Real.exp 1)
  -- 2*n+4 = 2*(n+2). Use Filter.tendsto_add_atTop_iff_nat.
  have e1 : (fun n => E_int (fun n => A_int n) (fun n => B_int n) (2*n+4)) = (fun n => E_int (fun n => A_int n) (fun n => B_int n) (2*(n+2))) := by
    ext n
    have H_eq : 2 * n + 4 = 2 * (n + 2) := by omega
    rw [H_eq]
  rw [e1] at H
  have h_shift := Filter.tendsto_add_atTop_iff_nat (f := fun n => E_int (fun n => A_int n) (fun n => B_int n) (2*n)) (l := nhds 0) 2
  exact h_shift.mp H

lemma tendsto_of_even_odd (f : ℕ → ℝ) (L : ℝ)
  (heven : Tendsto (fun k => f (2*k)) atTop (nhds L))
  (hodd : Tendsto (fun k => f (2*k+1)) atTop (nhds L)) :
  Tendsto f atTop (nhds L) := by
  rw [Metric.tendsto_atTop] at heven hodd ⊢
  intro ε hε
  rcases heven ε hε with ⟨N1, h1⟩
  rcases hodd ε hε with ⟨N2, h2⟩
  use max (2*N1) (2*N2+1)
  intro n hn
  by_cases h : n % 2 = 0
  · have : ∃ k, n = 2*k := ⟨n/2, by omega⟩
    rcases this with ⟨k, rfl⟩
    apply h1
    omega
  · have : ∃ k, n = 2*k+1 := ⟨n/2, by omega⟩
    rcases this with ⟨k, rfl⟩
    apply h2
    omega

lemma tendsto_div_of_tendsto_zero (X Y : ℕ → ℝ) (hX : Tendsto X atTop (nhds 0)) (hY : ∀ n ≥ 1, 1 ≤ Y n) :
  Tendsto (fun n => X n / Y n) atTop (nhds 0) := by
  have h_bound : ∀ n ≥ 1, |X n / Y n| ≤ |X n| := by
    intro n hn
    rw [abs_div]
    have h1 : |Y n| = Y n := abs_of_pos (by linarith [hY n hn])
    rw [h1]
    have h2 : Y n ≥ 1 := hY n hn
    have h3 : |X n| / Y n ≤ |X n| / 1 := by
      apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) h2
    rw [div_one] at h3
    exact h3
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _))
  · filter_upwards [eventually_ge_atTop 1]
    intro n hn
    exact h_bound n hn
  · exact (tendsto_zero_iff_abs_tendsto_zero X).mp hX

lemma tendsto_A_div_B (A B : ℕ → ℝ) (e : ℝ) (h : Tendsto (fun n => e - A n / B n) atTop (nhds 0)) :
  Tendsto (fun n => A n / B n) atTop (nhds e) := by
  have h2 : Tendsto (fun n => e - (e - A n / B n)) atTop (nhds (e - 0)) := Tendsto.const_sub e h
  rw [sub_zero] at h2
  have h3 : (fun n => e - (e - A n / B n)) = (fun n => A n / B n) := by ext n; ring
  rw [h3] at h2
  exact h2

lemma E_div_B (A B : ℕ → ℝ) (e : ℝ) (n : ℕ) (hBn : B n ≠ 0) :
  e - A n / B n = (B n * e - A n) / B n := by
  calc e - A n / B n
    _ = e * B n / B n - A n / B n := by rw [mul_div_cancel_right₀ _ hBn]
    _ = (e * B n - A n) / B n := by rw [sub_div]
    _ = (B n * e - A n) / B n := by ring

-- Combine!
theorem final_limit : Tendsto (fun n => (A_int n : ℝ) / (B_int n : ℝ)) atTop (nhds (Real.exp 1)) := by
  have ht_E := tendsto_of_even_odd (E_int (fun n => A_int n) (fun n => B_int n)) 0 tendsto_E_even_atTop tendsto_E_odd_atTop
  have hY : ∀ n ≥ 1, 1 ≤ (B_int n : ℝ) := by
    intro n hn
    have := B_int_pos n hn
    exact_mod_cast this
  have ht_div := tendsto_div_of_tendsto_zero (E_int (fun n => A_int n) (fun n => B_int n)) (fun n => B_int n) ht_E hY
  have heq : EventuallyEq atTop (fun n => E_int (fun n => A_int n) (fun n => B_int n) n / (B_int n : ℝ)) (fun n => Real.exp 1 - (A_int n : ℝ) / (B_int n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1]
    intro n hn
    have hb : (B_int n : ℝ) ≠ 0 := by
      have := hY n hn
      linarith
    have := E_div_B (fun x => A_int x) (fun x => B_int x) (Real.exp 1) n hb
    unfold E_int
    exact this.symm
  have ht_div2 := Filter.Tendsto.congr' heq ht_div
  exact tendsto_A_div_B _ _ _ ht_div2


lemma A_int_pos_odd (k : ℕ) : 0 ≤ A_int (2*k + 1) ∧ 0 ≤ A_int (2*k + 3) := by
  induction' k with k ih
  · constructor
    · have : 2*0+1 = 1 := rfl; rw [this, A_int]; norm_num
    · have : 2*0+3 = 3 := rfl; rw [this, A_int_3]; norm_num
  · rcases ih with ⟨h1, h2⟩
    constructor
    · have : 2*(k+1)+1 = 2*k+3 := by ring
      rw [this]
      exact h2
    · have : 2*(k+1)+3 = 2*k+5 := by ring
      rw [this]
      have hj := A_int_jump k
      rw [hj]
      have hp : 0 ≤ (4*(k:ℤ)+10) * A_int (2*k+3) := by positivity
      linarith

lemma A_int_pos (n : ℕ) : 0 ≤ A_int n := by
  by_cases h : n % 2 = 1
  · obtain ⟨k, hk⟩ : ∃ k, n = 2*k + 1 := ⟨n / 2, by omega⟩
    rw [hk]
    exact (A_int_pos_odd k).1
  · obtain ⟨k, hk⟩ : ∃ k, n = 2*k := ⟨n / 2, by omega⟩
    rw [hk]
    rcases k with _ | k'
    · have : 2*0 = 0 := rfl; rw [this, A_int]
    · rcases k' with _ | k''
      · have : 2*1 = 2 := rfl; rw [this, A_int]; norm_num
      · have H := A_int_even_rel k''
        have hodd1 := (A_int_pos_odd k'').1
        have hodd3 := (A_int_pos_odd k'').2
        have hp : 0 ≤ (2*(k'':ℤ)+5) * A_int (2*k''+3) := by positivity
        have h_sum : 0 ≤ 2 * A_int (2*k''+4) := by linarith
        have heq : 2*(k''+2) = 2*k''+4 := by ring
        rw [heq]
        linarith
