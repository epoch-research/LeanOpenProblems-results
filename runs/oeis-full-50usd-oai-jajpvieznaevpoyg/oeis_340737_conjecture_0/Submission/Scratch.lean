import FormalConjectures.Util.ProblemImports

open Nat
open scoped Interval

noncomputable section

open MeasureTheory intervalIntegral Filter

example (r : ℕ) : deriv (fun x : ℝ => (x * (1 - x)) ^ r) =
    fun x => (r : ℝ) * (x * (1 - x)) ^ (r - 1) * (1 - 2 * x) := by
  funext x
  by_cases hr : r = 0
  · subst r
    simp
  · have hder : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * x) x := by
      convert ((hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))) using 1
      · simp
        ring
    have hp := hder.pow r
    rw [deriv]
    exact hp.deriv

end

lemma deriv_tpow (r : ℕ) : deriv (fun x : ℝ => (x * (1 - x)) ^ r) =
    fun x => (r : ℝ) * (x * (1 - x)) ^ (r - 1) * (1 - 2 * x) := by
  funext x
  by_cases hr : r = 0
  · subst r
    simp
  · have hder : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * x) x := by
      convert ((hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))) using 1
      · simp
        ring
    have hp := hder.pow r
    rw [deriv]
    exact hp.deriv

lemma deriv2_tpow_chain (r : ℕ) (hr : 2 ≤ r) : deriv (deriv (fun x : ℝ => (x * (1 - x)) ^ r)) =
    fun x => (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2) * (1 - 2 * x) ^ 2
        - 2 * (r : ℝ) * (x * (1 - x)) ^ (r - 1) := by
  funext x
  rw [deriv_tpow]
  have hder : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * x) x := by
    convert ((hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))) using 1
    · simp
      ring
  have hlin : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) x := by
    simpa [two_mul] using (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_const x (2:ℝ)).mul (hasDerivAt_id x))
  have hpow := hder.pow (r - 1)
  have hprod := (hpow.mul hlin).const_mul (r : ℝ)
  rw [deriv]
  convert hprod.deriv using 1
  · ring
  · have h1 : r - 1 - 1 = r - 2 := by omega
    have h2 : (r - 1 : ℝ) = (r : ℝ) - 1 := by norm_num
    rw [h1]
    ring


example (r : ℕ) (hr : 2 ≤ r) (x : ℝ) :
    deriv (fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1) * (1 - 2 * y)) x =
      (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2) * (1 - 2 * x) ^ 2
        - 2 * (r : ℝ) * (x * (1 - x)) ^ (r - 1) := by
  simp only [deriv_mul, differentiableAt_const, differentiableAt_id, DifferentiableAt.mul,
    DifferentiableAt.sub, deriv_const, deriv_id'', zero_sub, one_mul]
  sorry

