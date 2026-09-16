import Mathlib

lemma my_sq_le_sq (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a^2 ≤ b^2) : a ≤ b := by nlinarith
lemma my_sq_lt_sq (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a^2 < b^2) : a < b := by nlinarith

lemma jump_P_even (k P Q x : ℤ) 
  (hk : 0 < k) (hP : 0 < P) (hx : 0 < x) (hQ_pos : 0 < Q)
  (hQ : Q^2 = 2*P^2 + 1)
  (hx1 : x^2 ≤ 2*k^2)
  (hx2 : 2*k^2 ≤ x^2 + 2*x)
  (hx3 : 2*k^2 - x^2 ≥ 1)
  (h_kP : k ≤ P) :
  (x + Q)^2 ≤ 2*(k + P)^2 ∧ 2*(k + P)^2 < (x + Q + 1)^2 := by
  constructor
  · have h_sq1 : (x * Q)^2 ≤ (2 * k * P)^2 := by
      calc (x * Q)^2 = x^2 * Q^2 := by ring
        _ = x^2 * (2*P^2 + 1) := by rw [hQ]
        _ = 2 * P^2 * x^2 + x^2 := by ring
        _ ≤ 2 * P^2 * (2*k^2 - 1) + x^2 := by nlinarith
        _ = 4 * k^2 * P^2 - 2 * P^2 + x^2 := by ring
        _ ≤ 4 * k^2 * P^2 := by nlinarith
        _ = (2 * k * P)^2 := by ring
    have H_low : x * Q ≤ 2 * k * P := my_sq_le_sq (x*Q) (2*k*P) (by nlinarith) (by nlinarith) h_sq1
    nlinarith
  · have h_sq2 : (2*k*P)^2 ≤ ((x+1)*Q)^2 := by
      calc (2*k*P)^2 = 4*k^2*P^2 := by ring
        _ ≤ (2*x^2 + 4*x)*P^2 := by nlinarith
        _ ≤ (2*x^2 + 4*x)*P^2 + x^2 + 2*x + 2*P^2 + 1 := by nlinarith
        _ = (x^2 + 2*x + 1)*(2*P^2 + 1) := by ring
        _ = (x+1)^2 * Q^2 := by rw [←hQ]; ring
        _ = ((x+1)*Q)^2 := by ring
    have H_up : 2*k*P ≤ (x+1)*Q := my_sq_le_sq (2*k*P) ((x+1)*Q) (by nlinarith) (by nlinarith) h_sq2
    nlinarith

lemma jump_P_odd (k P Q x : ℤ) 
  (hk : 0 < k) (hP : 0 < P) (hx : 0 < x) (hQ_pos : 0 < Q)
  (hQ : Q^2 = 2*P^2 - 1)
  (hx1 : x^2 ≤ 2*k^2)
  (hx2 : 2*k^2 ≤ x^2 + 2*x)
  (hx3 : 2*k^2 - x^2 ≥ 1)
  (h_kP : k ≤ P) :
  (x + Q)^2 ≤ 2*(k + P)^2 ∧ 2*(k + P)^2 < (x + Q + 1)^2 := by
  constructor
  · have h_sq1 : (x * Q)^2 ≤ (2 * k * P)^2 := by
      calc (x * Q)^2 = x^2 * Q^2 := by ring
        _ = x^2 * (2*P^2 - 1) := by rw [hQ]
        _ = 2 * P^2 * x^2 - x^2 := by ring
        _ ≤ 2 * P^2 * (2*k^2) - x^2 := by nlinarith
        _ = 4 * k^2 * P^2 - x^2 := by ring
        _ ≤ 4 * k^2 * P^2 := by nlinarith
        _ = (2 * k * P)^2 := by ring
    have H_low : x * Q ≤ 2 * k * P := my_sq_le_sq (x*Q) (2*k*P) (by nlinarith) (by nlinarith) h_sq1
    nlinarith
  · have H_cases : k ≤ P - 1 ∨ k = P := by omega
    rcases H_cases with hkP | hkP
    · have H_diff2 : (2 * k * P)^2 < ((x + 1) * Q)^2 := by
        have H_step : 0 < ((x + 1) * Q)^2 - (2 * k * P)^2 := by
          calc ((x + 1) * Q)^2 - (2 * k * P)^2 = (x + 1)^2 * Q^2 - 4 * k^2 * P^2 := by ring
            _ ≥ (2*k^2 + 1) * Q^2 - 4 * k^2 * P^2 := by nlinarith
            _ = 2*k^2*Q^2 + Q^2 - 4*k^2*P^2 := by ring
            _ = 2*k^2*(2*P^2 - 1) + Q^2 - 4*k^2*P^2 := by rw [hQ]
            _ = Q^2 - 2*k^2 := by ring
            _ = 2*P^2 - 1 - 2*k^2 := by rw [hQ]
            _ ≥ 2*P^2 - 1 - 2*(P - 1)^2 := by nlinarith
            _ = 4*P - 3 := by ring
            _ > 0 := by linarith
        linarith
      have H_XU : 2*k*P < (x+1)*Q := my_sq_lt_sq (2*k*P) ((x+1)*Q) (by nlinarith) (by nlinarith) H_diff2
      calc 2*(k + P)^2 = 2*k^2 + 4*k*P + 2*P^2 := by ring
        _ ≤ ((x + 1)^2 - 1) + 4*k*P + (Q^2 + 1) := by linarith
        _ ≤ ((x + 1)^2 - 1) + (2*(x + 1)*Q - 2) + (Q^2 + 1) := by linarith
        _ = (x + Q + 1)^2 - 2 := by ring
        _ < (x + Q + 1)^2 := by linarith
    · have h1 : x^2 ≤ Q^2 + 1 := by
        calc x^2 ≤ 2*k^2 := by linarith
          _ = 2*P^2 := by rw [hkP]
          _ = Q^2 + 1 := by linarith
      have h2 : Q^2 + 1 < (x + 1)^2 := by
        calc Q^2 + 1 = 2*P^2 := by linarith
          _ = 2*k^2 := by rw [hkP]
          _ ≤ x^2 + 2*x := by linarith
          _ < x^2 + 2*x + 1 := by linarith
          _ = (x + 1)^2 := by ring
      have h3 : x = Q := by nlinarith
      calc 2*(k + P)^2 = 8*P^2 := by rw [hkP]; ring
        _ = 4*(2*P^2) := by ring
        _ = 4*(Q^2 + 1) := by linarith
        _ = 4*Q^2 + 4 := by ring
        _ < 4*Q^2 + 4*Q + 1 := by linarith
        _ = (Q + Q + 1)^2 := by ring
        _ = (x + Q + 1)^2 := by rw [h3]

lemma jump_2P_even (k P Q x : ℤ) 
  (hk : 0 < k) (hP : 0 < P) (hx : 0 < x) (hQ_pos : 0 < Q)
  (hQ : Q^2 = 2*P^2 + 1)
  (hx1 : x^2 ≤ 2*k^2)
  (hx2 : 2*k^2 ≤ x^2 + 2*x)
  (hx3 : 2*k^2 - x^2 ≥ 1)
  (hkP : 2*k^2 ≤ P^2 - 1) :
  (x + 2*Q)^2 ≤ 2*(k + 2*P)^2 ∧ 2*(k + 2*P)^2 < (x + 2*Q + 1)^2 := by
  constructor
  · have h_sq1 : (x * Q)^2 < (2 * k * P)^2 := by
      have H_step : 0 < (2 * k * P)^2 - (x * Q)^2 := by
        calc (2 * k * P)^2 - (x * Q)^2 = 4 * k^2 * P^2 - x^2 * Q^2 := by ring
          _ = 4 * k^2 * P^2 - x^2 * (2*P^2 + 1) := by rw [hQ]
          _ = 2 * P^2 * (2*k^2 - x^2) - x^2 := by ring
          _ ≥ 2 * P^2 * 1 - x^2 := by nlinarith
          _ = 2 * P^2 - x^2 := by ring
          _ ≥ 2 * P^2 - (2*k^2) := by nlinarith
          _ ≥ 2 * P^2 - (P^2 - 1) := by nlinarith
          _ = P^2 + 1 := by ring
          _ > 0 := by nlinarith
      linarith
    have H_low : x * Q < 2 * k * P := my_sq_lt_sq (x*Q) (2*k*P) (by nlinarith) (by nlinarith) h_sq1
    calc (x + 2*Q)^2 = x^2 + 4*x*Q + 4*Q^2 := by ring
      _ ≤ 2*k^2 - 1 + 4*x*Q + 4*Q^2 := by linarith
      _ ≤ 2*k^2 - 1 + (8*k*P - 4) + 4*Q^2 := by linarith
      _ = 2*k^2 + 8*k*P - 5 + 4*Q^2 := by ring
      _ = 2*k^2 + 8*k*P - 5 + 4*(2*P^2 + 1) := by rw [hQ]
      _ = 2*k^2 + 8*k*P + 8*P^2 - 1 := by ring
      _ ≤ 2*(k + 2*P)^2 := by linarith
  · have H_X : 2*k^2 + 1 ≤ (x + 1)^2 := by
      calc 2*k^2 + 1 ≤ x^2 + 2*x + 1 := by linarith
        _ = (x + 1)^2 := by ring
    have h_sq2 : (2 * k * P)^2 < ((x + 1) * Q)^2 := by
      have H_step : 0 < ((x + 1) * Q)^2 - (2 * k * P)^2 := by
        calc ((x + 1) * Q)^2 - (2 * k * P)^2 = (x + 1)^2 * Q^2 - 4 * k^2 * P^2 := by ring
          _ = (x + 1)^2 * (2*P^2 + 1) - 4 * k^2 * P^2 := by rw [hQ]
          _ = 2 * P^2 * ((x + 1)^2 - 2*k^2) + (x + 1)^2 := by ring
          _ ≥ 2 * P^2 * 1 + (x + 1)^2 := by nlinarith
          _ > 0 := by nlinarith
      linarith
    have H_up : 2 * k * P < (x + 1) * Q := my_sq_lt_sq (2*k*P) ((x+1)*Q) (by nlinarith) (by nlinarith) h_sq2
    calc 2*(k + 2*P)^2 = 2*k^2 + 8*k*P + 8*P^2 := by ring
      _ ≤ ((x + 1)^2 - 1) + 8*k*P + 8*P^2 := by linarith
      _ ≤ ((x + 1)^2 - 1) + (4*(x + 1)*Q - 4) + 8*P^2 := by linarith
      _ = (x + 1)^2 + 4*(x + 1)*Q - 5 + 4*(2*P^2) := by ring
      _ = (x + 1)^2 + 4*(x + 1)*Q - 5 + 4*(Q^2 - 1) := by linarith
      _ = x^2 + 4*x*Q + 4*Q^2 + 2*x + 4*Q - 8 := by ring
      _ < x^2 + 4*x*Q + 4*Q^2 + 2*x + 4*Q + 1 := by linarith
      _ = (x + 2*Q + 1)^2 := by ring
