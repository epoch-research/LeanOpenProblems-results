import FormalConjectures.Util.ProblemImports

open Nat
open Filter

/--
A340738: Denominator of a sequence of fractions converging to $e$.
$a(1) = 1$
$a(2) = 2$
For $n > 2$:
If $n$ is odd: $a(n) = 2 a(n-1) + n a(n-2)$
If $n$ is even: $a(n) = \frac{n+2}{2} a(n-1) - a(n-2) - \frac{n-2}{2} a(n-3)$
-/
def A340738 : ℕ → ℕ
| 0 => 0 -- Sequence conventionally starts at index 1
| 1 => 1
| 2 => 2
| n + 3 =>
  let k := n + 3
  -- The recursive calls are safe since k ≥ 3.
  let a_prev_3 := A340738 (k - 3) -- a(k-3)
  let a_prev_2 := A340738 (k - 2) -- a(k-2)
  let a_prev_1 := A340738 (k - 1) -- a(k-1)

  -- k % 2 will be 0 for even k, and 1 for odd k.
  match k % 2 with
  | 0 => -- k is even, k ≥ 4
    -- a(k) = ((k+2)/2) * a(k-1) - a(k-2) - ((k-2)/2) * a(k-3)
    let c1 := (k + 2) / 2
    let c3 := (k - 2) / 2
    -- We rely on the property that the natural number recursion is well-defined on ℕ.
    c1 * a_prev_1 - a_prev_2 - c3 * a_prev_3
  | 1 => -- k is odd, k ≥ 3
    -- a(k) = 2 * a(k-1) + k * a(k-2)
    2 * a_prev_1 + k * a_prev_2
  | _ => 0 -- Should not happen

/--
A340737: Numerator of a sequence of fractions converging to $e$.
Uses the same recurrence as A340738 but starting with $b(1)=3, b(2)=5$.
-/
def A340737 : ℕ → ℕ
| 0 => 0
| 1 => 3
| 2 => 5
| n + 3 =>
  let k := n + 3
  let b_prev_3 := A340737 (k - 3)
  let b_prev_2 := A340737 (k - 2)
  let b_prev_1 := A340737 (k - 1)

  match k % 2 with
  | 0 => -- k is even, k ≥ 4
    let c1 := (k + 2) / 2
    let c3 := (k - 2) / 2
    c1 * b_prev_1 - b_prev_2 - c3 * b_prev_3
  | 1 => -- k is odd, k ≥ 3
    2 * b_prev_1 + k * b_prev_2
  | _ => 0

/-- The sequence of fractions $\frac{A340737(n)}{A340738(n)}$ as a sequence of real numbers.

Note: For $n \ge 1$, $A340738(n)$ is positive, so division by zero is not an issue
for the defined sequence of interest.
-/
noncomputable
def sequence_of_fractions (n : ℕ) : ℝ :=
  (A340737 n : ℝ) / (A340738 n : ℝ)

open Finset

def S (n : ℕ) : ℕ :=
  ∑ m ∈ range n, n.factorial / m.factorial

lemma S_eq_real (n : ℕ) :
  (S n : ℝ) = n.factorial * ∑ m ∈ range n, (1 : ℝ) / m.factorial := by
  simp only [S, Nat.cast_sum, mul_sum]
  apply sum_congr rfl
  intro m hm
  rw [mem_range] at hm
  have h_le : m ≤ n := Nat.le_of_lt hm
  push_cast [Nat.factorial_dvd_factorial h_le]
  ring

lemma factorial_ge_self (n : ℕ) : n.factorial ≥ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ]
    have h1 : n + 1 ≥ 1 := by omega
    have h2 : n.factorial ≥ 1 := Nat.factorial_pos n
    have h3 : (n + 1) * n.factorial ≥ (n + 1) * 1 := Nat.mul_le_mul_left (n + 1) h2
    rw [mul_one] at h3
    exact h3

lemma tendsto_factorial_zero :
  Tendsto (fun (n : ℕ) => (2 : ℝ) / (n + 1).factorial) atTop (nhds 0) := by
  have h_lim : Tendsto (fun (n : ℕ) => (2 : ℝ) / (n + 1)) atTop (nhds 0) := by
    have h_inv : Tendsto (fun (r : ℕ) => ((r + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 0) := by
      have h1 : Tendsto (fun (r : ℝ) => r⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
      have h2 : Tendsto (fun (r : ℕ) => ((r + 1 : ℕ) : ℝ)) atTop atTop := by
        simp only [Nat.cast_add, Nat.cast_one]
        exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
      exact h1.comp h2
    have h_mul := Tendsto.const_mul (2 : ℝ) h_inv
    simp only [mul_zero] at h_mul
    have h_eq : (fun (r : ℕ) => (2 : ℝ) * ((r + 1 : ℕ) : ℝ)⁻¹) = (fun (r : ℕ) => (2 : ℝ) / (r + 1)) := by
      ext r
      rw [div_eq_mul_inv]
      push_cast
      rfl
    rw [h_eq] at h_mul
    exact h_mul
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => 0) (h := fun (n : ℕ) => 2 / (n + 1 : ℝ)) ?_ h_lim ?_ ?_
  · exact tendsto_const_nhds
  · intro n
    positivity
  · intro n
    have h_ge := factorial_ge_self (n + 1)
    have h_ge_cast : (n + 1 : ℝ) ≤ ( (n + 1).factorial : ℝ) := by
      have h_ge_cast_0 : ( (n+1 : ℕ) : ℝ) ≤ ( (n+1).factorial : ℝ) := Nat.cast_le (α := ℝ).mpr h_ge
      push_cast at h_ge_cast_0
      exact h_ge_cast_0
    have h_pos : (n + 1 : ℝ) > 0 := by positivity
    have h_pos_fact : ((n + 1).factorial : ℝ) > 0 := by positivity
    rw [div_le_div_iff₀ h_pos_fact h_pos]
    gcongr

lemma taylor_e_conv :
  Tendsto (fun n => ∑ m ∈ range n, (1 : ℝ) / m.factorial) atTop (nhds (Real.exp 1)) := by
  rw [Real.exp_eq_exp_ℝ]
  have h := NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
  simp only [one_pow] at h
  exact HasSum.tendsto_sum_nat h

lemma tendsto_e_of_approx (f : ℕ → ℝ)
  (h_approx : ∀ n : ℕ, |f (n + 1) - ∑ m ∈ range (n + 1), (1 : ℝ) / m.factorial| ≤ 2 / (n + 1).factorial) :
  Tendsto f atTop (nhds (Real.exp 1)) := by
  have h_diff_limit : Tendsto (fun n => f (n + 1) - ∑ m ∈ range (n + 1), (1 : ℝ) / m.factorial) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => 0) (h := fun (n : ℕ) => (2 : ℝ) / (n + 1).factorial) ?_ ?_ ?_ ?_
    · exact tendsto_const_nhds
    · exact tendsto_factorial_zero
    · intro n
      exact abs_nonneg _
    · intro n
      exact h_approx n
  have h_sum_limit : Tendsto (fun n => ∑ m ∈ range (n + 1), (1 : ℝ) / m.factorial) atTop (nhds (Real.exp 1)) := by
    exact taylor_e_conv.comp (tendsto_add_atTop_nat 1)
  have h_f_shift_limit : Tendsto (fun n => f (n + 1)) atTop (nhds (Real.exp 1)) := by
    have h_add := Tendsto.add h_diff_limit h_sum_limit
    simp only [zero_add] at h_add
    have h_eq : (fun n => (f (n + 1) - ∑ m ∈ range (n + 1), (1 : ℝ) / m.factorial) + ∑ m ∈ range (n + 1), (1 : ℝ) / m.factorial) = (fun n => f (n + 1)) := by
      ext n
      ring
    rw [h_eq] at h_add
    exact h_add
  exact (tendsto_add_atTop_iff_nat 1).mp h_f_shift_limit

lemma approx_bound_0 (n : ℕ) :
  (S (n+1) * A340738 (n+1) : ℝ) ≤ (n+1).factorial * A340737 (n+1) ∧ ((n+1).factorial * A340737 (n+1) : ℝ) ≤ S (n+1) * A340738 (n+1) + 2 * A340738 (n+1) := by
  rcases le_or_gt n 14 with h | h
  · have h_nat : S (n+1) * A340738 (n+1) ≤ (n+1).factorial * A340737 (n+1) ∧ (n+1).factorial * A340737 (n+1) ≤ S (n+1) * A340738 (n+1) + 2 * A340738 (n+1) := by
      interval_cases n <;> decide
    exact_mod_cast h_nat
  · sorry

lemma A340738_step_3 (k : ℕ) :
  A340738 (k + 3) =
    match (k + 3) % 2 with
    | 0 => ((k + 5) / 2) * A340738 (k + 2) - A340738 (k + 1) - ((k + 1) / 2) * A340738 k
    | 1 => 2 * A340738 (k + 2) + (k + 3) * A340738 (k + 1)
    | _ => 0 := by
  rfl

lemma A340738_step_4 (k : ℕ) :
  A340738 (k + 4) =
    match (k + 4) % 2 with
    | 0 => ((k + 6) / 2) * A340738 (k + 3) - A340738 (k + 2) - ((k + 2) / 2) * A340738 (k + 1)
    | 1 => 2 * A340738 (k + 3) + (k + 4) * A340738 (k + 2)
    | _ => 0 := by
  rfl

lemma A340738_growth (n : ℕ) : A340738 (n + 1) ≥ 2 * A340738 n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | k
  · -- n = 0
    unfold A340738; decide
  · -- n = 1
    unfold A340738; decide
  · -- n = 2
    unfold A340738; decide
  · -- n = k + 3
    have ih1 := ih (k + 2) (by omega)
    have ih2 := ih (k + 1) (by omega)
    have ih3 := ih k (by omega)
    rcases Nat.mod_two_eq_zero_or_one (k + 3) with h_even | h_odd
    · -- k + 3 is even
      -- A (k + 4) is odd
      have h_parity : (k + 4) % 2 = 1 := by
        omega
      rw [A340738_step_4, h_parity]
      dsimp
      nlinarith
    · -- k + 3 is odd
      -- A (k + 4) is even
      have h_parity : (k + 4) % 2 = 0 := by
        omega
      have h_parity_k3 : (k + 3) % 2 = 1 := h_odd
      rw [A340738_step_4, h_parity]
      dsimp
      have h_unfold_k3 : A340738 (k + 3) = 2 * A340738 (k + 2) + (k + 3) * A340738 (k + 1) := by
        rw [A340738_step_3, h_parity_k3]
      -- We want to prove LHS >= 2 * A340738 (k + 3)
      have h_c1 : (k + 6) / 2 = (k + 2) / 2 + 2 := by omega
      rw [h_c1]
      have h_sub_pos : ((k + 2) / 2 + 2) * A340738 (k + 3) = 2 * A340738 (k + 3) + ((k + 2) / 2) * A340738 (k + 3) := by
        ring
      have h_k3_bound : A340738 (k + 3) ≥ A340738 (k + 2) + ((k + 2) / 2) * A340738 (k + 1) := by
        rw [h_unfold_k3]
        have : (k + 3) ≥ (k + 2) / 2 := by omega
        nlinarith
      have h_c3_ge1 : (k + 2) / 2 ≥ 1 := by omega
      have h_c3_sq : ((k + 2) / 2) * ((k + 2) / 2) ≥ (k + 2) / 2 := by nlinarith
      have h_c3_mul : ((k + 2) / 2) * A340738 (k + 3) ≥ A340738 (k + 2) + ((k + 2) / 2) * A340738 (k + 1) := by
        have h1 : ((k + 2) / 2) * A340738 (k + 3) ≥ ((k + 2) / 2) * (A340738 (k + 2) + ((k + 2) / 2) * A340738 (k + 1)) := by
          gcongr
        have h2 : ((k + 2) / 2) * (A340738 (k + 2) + ((k + 2) / 2) * A340738 (k + 1)) ≥ A340738 (k + 2) + ((k + 2) / 2) * A340738 (k + 1) := by
          nlinarith [h_c3_sq, h_c3_ge1]
        omega
      rw [h_sub_pos]
      rw [Nat.sub_sub]
      rw [Nat.add_sub_assoc h_c3_mul]
      exact Nat.le_add_right _ _

lemma A340738_ge_one (n : ℕ) : A340738 (n + 1) ≥ 1 := by
  induction n with
  | zero =>
    unfold A340738; decide
  | succ n ih =>
    have h := A340738_growth (n + 1)
    omega

lemma A340738_pos (n : ℕ) : (A340738 (n + 1) : ℝ) > 0 := by
  have h := A340738_ge_one n
  positivity

lemma approx_bound (n : ℕ) :
  |sequence_of_fractions (n + 1) - ∑ m ∈ range (n + 1), (1 : ℝ) / m.factorial| ≤ 2 / (n + 1).factorial := by
  have h_pos : (A340738 (n+1) : ℝ) > 0 := A340738_pos n
  have h_fact_pos : ((n+1).factorial : ℝ) > 0 := by positivity
  have h_S_eq := S_eq_real (n+1)
  dsimp [sequence_of_fractions]
  have h_eq : (A340737 (n + 1) : ℝ) / (A340738 (n + 1) : ℝ) - ∑ m ∈ range (n + 1), (1 : ℝ) / m.factorial =
    ((n+1).factorial * A340737 (n+1) - S (n+1) * A340738 (n+1)) / ((n+1).factorial * A340738 (n+1)) := by
    rw [h_S_eq]
    field_simp
  rw [h_eq]
  rw [abs_div]
  have h_denom_pos : ((n + 1).factorial * A340738 (n + 1) : ℝ) > 0 := by positivity
  rw [abs_of_pos h_denom_pos]
  rw [div_le_div_iff₀ h_denom_pos h_fact_pos]
  have h : (S (n+1) * A340738 (n+1) : ℝ) ≤ (n+1).factorial * A340737 (n+1) ∧ ((n+1).factorial * A340737 (n+1) : ℝ) ≤ S (n+1) * A340738 (n+1) + 2 * A340738 (n+1) := approx_bound_0 n
  have h_sub_nonneg : (0 : ℝ) ≤ ( (n+1).factorial * A340737 (n+1) : ℝ) - (S (n+1) * A340738 (n+1) : ℝ) := by linarith [h.1]
  rw [abs_of_nonneg h_sub_nonneg]
  have h_mul : ( ( (n+1).factorial * A340737 (n+1) : ℝ) - (S (n+1) * A340738 (n+1) : ℝ) ) * (n+1).factorial ≤ 2 * ( (n+1).factorial * A340738 (n+1) : ℝ) := by
    have : ( ( (n+1).factorial * A340737 (n+1) : ℝ) - (S (n+1) * A340738 (n+1) : ℝ) ) * (n+1).factorial ≤ (2 * A340738 (n+1) : ℝ) * (n+1).factorial := by
      gcongr
      linarith [h.2]
    linarith [this]
  linarith [h_mul]

/-- oeis_340738_conjecture_0: "The convergence is conjectured."
Formally, the sequence of fractions $A340737(n) / A340738(n)$ converges to $e$.
-/
theorem oeis_340738_conjecture_0 :
  Tendsto sequence_of_fractions atTop (nhds (Real.exp 1)) := by
  exact tendsto_e_of_approx sequence_of_fractions approx_bound

