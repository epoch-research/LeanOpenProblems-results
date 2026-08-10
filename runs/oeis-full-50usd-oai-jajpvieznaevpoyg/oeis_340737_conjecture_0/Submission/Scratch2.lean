import FormalConjectures.Util.ProblemImports
open scoped Interval
open MeasureTheory intervalIntegral Filter

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

lemma deriv_second_aux (r : ℕ) (hr : 2 ≤ r) (x : ℝ) :
    deriv (fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1) * (1 - 2 * y)) x =
      (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2) * (1 - 2 * x) ^ 2
        - 2 * (r : ℝ) * (x * (1 - x)) ^ (r - 1) := by
  have hpow : deriv (fun y : ℝ => (y * (1 - y)) ^ (r - 1)) x =
      ((r - 1 : ℕ) : ℝ) * (x * (1 - x)) ^ ((r - 1) - 1) * (1 - 2 * x) := by
    simpa using congrFun (deriv_tpow (r - 1)) x
  have hconst : deriv (fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1)) x =
      (r : ℝ) * deriv (fun y : ℝ => (y * (1 - y)) ^ (r - 1)) x := by
    rw [deriv_const_mul]
    fun_prop
  have hlin : deriv (fun y : ℝ => 1 - 2 * y) x = -2 := by
    have h : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) x := by
      convert (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_const x (2:ℝ)).mul (hasDerivAt_id x)) using 1
      · norm_num
    exact h.deriv
  change deriv (((fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1)) *
      (fun y : ℝ => 1 - 2 * y))) x = _
  rw [deriv_mul (c := fun y : ℝ => (r : ℝ) * (y * (1 - y)) ^ (r - 1))
      (d := fun y : ℝ => 1 - 2 * y)]
  · rw [hconst, hpow, hlin]
    have h1 : r - 1 - 1 = r - 2 := by omega
    have hcast : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r)]
      norm_num
    rw [h1, hcast]
    ring
  · fun_prop
  · fun_prop


lemma deriv2_tpow_chain (r : ℕ) (hr : 2 ≤ r) : deriv (deriv (fun x : ℝ => (x * (1 - x)) ^ r)) =
    fun x => (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2) * (1 - 2 * x) ^ 2
        - 2 * (r : ℝ) * (x * (1 - x)) ^ (r - 1) := by
  funext x
  rw [deriv_tpow]
  exact deriv_second_aux r hr x

lemma deriv2_tpow_expanded (r : ℕ) (hr : 2 ≤ r) : deriv (deriv (fun x : ℝ => (x * (1 - x)) ^ r)) =
    fun x => (r : ℝ) * (r - 1 : ℝ) * (x * (1 - x)) ^ (r - 2)
        - (2 * (r : ℝ) * (2 * (r : ℝ) - 1)) * (x * (1 - x)) ^ (r - 1) := by
  rw [deriv2_tpow_chain r hr]
  funext x
  have hpow : (x * (1 - x)) ^ (r - 1) = (x * (1 - x)) ^ (r - 2) * (x * (1 - x)) := by
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
  rw [hpow]
  ring
