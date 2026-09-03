import FormalConjecturesUtil

/-! Elementary conditional quadratic bounds. The needed Jacobsthal
recurrence is not proved here. -/

namespace Erdos970Aux

/-- An auxiliary implication only: no recurrence for Jacobsthal's function
is assumed to have been proved. -/
theorem sqrt_step {x y A : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hA : 0 ≤ A) (h : x - y ≤ A * Real.sqrt x) :
    Real.sqrt x ≤ Real.sqrt y + A := by
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hnx := Real.sqrt_nonneg x
  have hny := Real.sqrt_nonneg y
  by_contra hn
  have ht : Real.sqrt y + A < Real.sqrt x := lt_of_not_ge hn
  have hd : 0 < Real.sqrt x - Real.sqrt y - A := by linarith
  have hp := mul_nonneg hnx (le_of_lt hd)
  have hq := mul_nonneg hny (show 0 ≤ Real.sqrt x - Real.sqrt y by linarith)
  have hpx : 0 < Real.sqrt x := by linarith
  have hp' := mul_pos hpx hd
  nlinarith

/-- Any nonnegative real sequence satisfying this recurrence has quadratic
size. This does not establish the recurrence for Jacobsthal's function. -/
theorem quadratic_of_sqrt_recurrence (f : ℕ → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hf : ∀ n, 0 ≤ f n) (hzero : f 0 ≤ 1)
    (hstep : ∀ n, f (n + 1) - f n ≤ A * Real.sqrt (f (n + 1))) :
    ∀ n, f n ≤ (1 + A * n) ^ 2 := by
  have hs : ∀ n : ℕ, Real.sqrt (f n) ≤ 1 + A * n := by
    intro n
    induction n with
    | zero =>
      have hsq := Real.sq_sqrt (hf 0)
      have hn := Real.sqrt_nonneg (f 0)
      norm_num
      nlinarith
    | succ n ih =>
      have ht := sqrt_step (hf (n + 1)) (hf n) hA (hstep n)
      push_cast
      nlinarith
  intro n
  have ht := hs n
  have hsq := Real.sq_sqrt (hf n)
  have hn := Real.sqrt_nonneg (f n)
  have hb : 0 ≤ 1 + A * (n : ℝ) := by positivity
  nlinarith [sq_nonneg (1 + A * (n : ℝ) - Real.sqrt (f n))]

/-- Conditional big-O form with an explicit positive constant. -/
theorem exists_quadratic_bound_of_sqrt_recurrence (f : ℕ → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hf : ∀ n, 0 ≤ f n) (hzero : f 0 ≤ 1)
    (hstep : ∀ n, f (n + 1) - f n ≤ A * Real.sqrt (f (n + 1))) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n → f n ≤ C * n ^ 2 := by
  refine ⟨(1 + A) ^ 2, by positivity, ?_⟩
  intro n hn
  have hnn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    f n ≤ (1 + A * n) ^ 2 :=
      quadratic_of_sqrt_recurrence f A hA hf hzero hstep n
    _ ≤ ((1 + A) * n) ^ 2 := by
      gcongr
      nlinarith
    _ = (1 + A) ^ 2 * (n : ℝ) ^ 2 := by ring

end Erdos970Aux

#print axioms Erdos970Aux.exists_quadratic_bound_of_sqrt_recurrence
#print axioms Erdos970Aux.sqrt_step
#print axioms Erdos970Aux.quadratic_of_sqrt_recurrence
