import FormalConjectures.Util.ProblemImports

open Complex Filter Asymptotics Topology

noncomputable def a (n : ℕ) : ℤ :=
  let product_term (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod product_term).im)

open Nat

def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (x, y) := P n
    (x - (n + 1) * y, (n + 1) * x + y)

theorem a_eq_P_im (n : ℕ) : a n = (P n).2 := sorry

def InductionHyp (n : ℕ) : Prop :=
  let k := n / 4
  match n % 4 with
  | 0 => 2^k ∣ (P n).1 ∧ 2^k ∣ (P n).2
  | 1 => 2^k ∣ (P n).1 ∧ 2^k ∣ (P n).2 ∧ 2^(k+1) ∣ ((P n).1 - (P n).2)
  | 2 => 2^k ∣ (P n).1 ∧ 2^k ∣ (P n).2 ∧ 2^(k+1) ∣ ((P n).1 - (P n).2)
  | _ => 2^(k+1) ∣ (P n).1 ∧ 2^(k+1) ∣ (P n).2

theorem induction_hyp_step (n : ℕ) : InductionHyp n := sorry

theorem valuation_a_eq_k (n : ℕ) (h_ih : InductionHyp n) (h_mod : n % 4 = 1 ∨ n % 4 = 2) :
    padicValInt 2 (P n).2 = n / 4 := sorry

lemma valuation_a_le (n : ℕ) : (padicValInt 2 (a n) : ℚ) ≤ (n : ℚ) / 4 + 2 * (Nat.sqrt n : ℚ) + 3 := by
  have h_mod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h_mod with h0 | h1 | h2 | h3
  · sorry
  · rw [a_eq_P_im]
    have h_val := valuation_a_eq_k n (induction_hyp_step n) (Or.inl h1)
    rw [h_val]
    have h_div : (n / 4 : ℕ) * 4 ≤ n := Nat.div_mul_le_self n 4
    have h_div_q : ((n / 4 : ℕ) : ℚ) * 4 ≤ (n : ℚ) := by exact_mod_cast h_div
    have : ((n / 4 : ℕ) : ℚ) ≤ (n : ℚ) / 4 := by linarith
    have h_sqrt : (Nat.sqrt n : ℚ) ≥ 0 := by positivity
    linarith
  · rw [a_eq_P_im]
    have h_val := valuation_a_eq_k n (induction_hyp_step n) (Or.inr h2)
    rw [h_val]
    have h_div : (n / 4 : ℕ) * 4 ≤ n := Nat.div_mul_le_self n 4
    have h_div_q : ((n / 4 : ℕ) : ℚ) * 4 ≤ (n : ℚ) := by exact_mod_cast h_div
    have : ((n / 4 : ℕ) : ℚ) ≤ (n : ℚ) / 4 := by linarith
    have h_sqrt : (Nat.sqrt n : ℚ) ≥ 0 := by positivity
    linarith
  · sorry
