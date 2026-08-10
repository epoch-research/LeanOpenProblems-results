import Mathlib

open PowerSeries

namespace ExpFrame

open Finset

/-- Recursive coefficient function for the formal exponential solving `F(0)=1, F' = F·D`.
`a 0 = 1` and `a (m+1) = (∑ i<m+1, a i · [x^{m-i}]D)/(m+1)`. -/
noncomputable def expOfAux (D : PowerSeries ℚ) : ℕ → ℚ
  | 0 => 1
  | (m + 1) =>
      (∑ i ∈ (Finset.range (m + 1)).attach,
          expOfAux D i.1 * coeff (m - i.1) D) / (m + 1)
  termination_by n => n
  decreasing_by exact Finset.mem_range.mp i.2

theorem expOfAux_zero (D : PowerSeries ℚ) : expOfAux D 0 = 1 := by
  rw [expOfAux]

theorem expOfAux_succ (D : PowerSeries ℚ) (m : ℕ) :
    expOfAux D (m + 1) =
      (∑ i ∈ Finset.range (m + 1), expOfAux D i * coeff (m - i) D) / (m + 1) := by
  rw [expOfAux]
  congr 1
  rw [← Finset.sum_attach (Finset.range (m + 1)) (fun i => expOfAux D i * coeff (m - i) D)]

/-- The formal exponential `expOf D` characterized by `F(0)=1, F' = F·D`. -/
noncomputable def expOf (D : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (expOfAux D)

theorem coeff_expOf (D : PowerSeries ℚ) (n : ℕ) :
    coeff n (expOf D) = expOfAux D n := by
  rw [expOf, coeff_mk]

/-- Deliverable 2: constant coefficient is 1. -/
theorem expOf_coeff_zero (D : PowerSeries ℚ) : coeff 0 (expOf D) = 1 := by
  rw [coeff_expOf, expOfAux_zero]

/-- Deliverable 3: the core ODE `F' = F·D`. -/
theorem expOf_deriv (D : PowerSeries ℚ) :
    d⁄dX ℚ (expOf D) = expOf D * D := by
  ext n
  rw [coeff_derivative, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun ij => coeff ij.1 (expOf D) * coeff ij.2 D) n]
  simp only [coeff_expOf]
  rw [expOfAux_succ]
  have hne : ((n : ℚ) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  rw [div_mul_cancel₀ _ hne]

/-- Deliverable 4: uniqueness of the solution to the ODE. -/
theorem expOf_unique (D G : PowerSeries ℚ) (h0 : coeff 0 G = 1)
    (hG : d⁄dX ℚ G = G * D) : G = expOf D := by
  have key : ∀ n, coeff n G = coeff n (expOf D) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => rw [h0, expOf_coeff_zero]
      | succ m =>
        have hne : ((m : ℚ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
        -- coefficient recursion coming from `hG`
        have hco : coeff m (d⁄dX ℚ G) = coeff m (G * D) := by rw [hG]
        rw [coeff_derivative, coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
            (fun ij => coeff ij.1 G * coeff ij.2 D) m] at hco
        -- coefficient recursion for the constructed solution (via `expOf_deriv`)
        have hcE : coeff m (d⁄dX ℚ (expOf D)) = coeff m (expOf D * D) := by
          rw [expOf_deriv]
        rw [coeff_derivative, coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
            (fun ij => coeff ij.1 (expOf D) * coeff ij.2 D) m] at hcE
        -- the two sums agree by the induction hypothesis
        have hsum : (∑ k ∈ range (m + 1), coeff k G * coeff (m - k) D)
            = ∑ k ∈ range (m + 1), coeff k (expOf D) * coeff (m - k) D := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          rw [ih k (by omega)]
        rw [hsum] at hco
        have : coeff (m + 1) G * ((m : ℚ) + 1)
            = coeff (m + 1) (expOf D) * ((m : ℚ) + 1) := by
          rw [hco, hcE]
        exact mul_right_cancel₀ hne this
  exact PowerSeries.ext key

/-- Deliverable 6 (base case): `expOf 0 = 1`. -/
theorem expOf_zero : expOf (0 : PowerSeries ℚ) = 1 := by
  symm
  apply expOf_unique
  · simp
  · simp

/-- Deliverable 5: the exponential law `expOf D · expOf E = expOf (D + E)`. -/
theorem expOf_mul (D E : PowerSeries ℚ) : expOf D * expOf E = expOf (D + E) := by
  apply expOf_unique
  · rw [coeff_zero_eq_constantCoeff_apply, map_mul,
      ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      expOf_coeff_zero, expOf_coeff_zero, mul_one]
  · rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    rw [expOf_deriv, expOf_deriv]
    ring

/-- Deliverable 6: `(expOf D)^n = expOf (n • D)`. -/
theorem expOf_pow (D : PowerSeries ℚ) (n : ℕ) : (expOf D) ^ n = expOf (n • D) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, expOf_zero]
  | succ k ih => rw [pow_succ, ih, expOf_mul, succ_nsmul]

