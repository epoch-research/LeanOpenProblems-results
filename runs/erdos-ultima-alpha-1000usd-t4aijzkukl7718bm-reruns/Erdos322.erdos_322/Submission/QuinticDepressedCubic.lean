import FormalConjecturesUtil

/-!
A coefficient obstruction to constant sums of fifth powers of depressed cubics.
It also applies when the quadratic coefficient vector is proportional to the
leading coefficient vector, since a common translation depresses all the cubics.
This is a construction obstruction, not a bound for representationCount.
-/
namespace Erdos322Research.QuinticDepressedCubic

noncomputable section
open Polynomial Finset
set_option Elab.async false
set_option maxHeartbeats 0

private def cubic (a c d : ℝ) : ℝ[X] := C a * X^3 + C c * X + C d

private lemma selected_coefficients (a c d : ℝ) :
    (cubic a c d ^ 5).coeff 15 = a^5 ∧
    (cubic a c d ^ 5).coeff 13 = 5*a^4*c ∧
    (cubic a c d ^ 5).coeff 12 = 5*a^4*d := by
  dsimp [cubic]
  ring_nf
  simp only [← map_pow, coeff_add, coeff_C_mul, coeff_mul_C,
    coeff_X_pow, coeff_X, coeff_C, coeff_mul_ofNat]
  norm_num

/-- Three high coefficients force the leading-weighted coordinate sum to
vanish identically. There is no restriction on the signs of the coefficients. -/
theorem leading_projection_zero {ι : Type*} [Fintype ι]
    (a c d : ι → ℝ) (N : ℝ)
    (h : (∑ i, (C (a i)*X^3+C (c i)*X+C (d i))^5) = C N) (t : ℝ) :
    (∑ i, a i^4*(a i*t^3+c i*t+d i)) = 0 := by
  have h15 := congrArg (fun p : ℝ[X] => p.coeff 15) h
  have h13 := congrArg (fun p : ℝ[X] => p.coeff 13) h
  have h12 := congrArg (fun p : ℝ[X] => p.coeff 12) h
  change (∑ i, cubic (a i) (c i) (d i)^5).coeff 15 = (C N).coeff 15 at h15
  change (∑ i, cubic (a i) (c i) (d i)^5).coeff 13 = (C N).coeff 13 at h13
  change (∑ i, cubic (a i) (c i) (d i)^5).coeff 12 = (C N).coeff 12 at h12
  simp only [finset_sum_coeff, (selected_coefficients _ _ _).1, coeff_C,
    OfNat.ofNat_ne_zero, if_false] at h15
  simp only [finset_sum_coeff, (selected_coefficients _ _ _).2.1, coeff_C,
    OfNat.ofNat_ne_zero, if_false] at h13
  simp only [finset_sum_coeff, (selected_coefficients _ _ _).2.2, coeff_C,
    OfNat.ofNat_ne_zero, if_false] at h12
  have hs13 : (∑ i, 5*a i^4*c i) = 5*(∑ i, a i^4*c i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hs12 : (∑ i, 5*a i^4*d i) = 5*(∑ i, a i^4*d i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs13] at h13
  rw [hs12] at h12
  have hc : (∑ i, a i^4*c i) = 0 := by linarith
  have hd : (∑ i, a i^4*d i) = 0 := by linarith
  calc
    (∑ i, a i^4*(a i*t^3+c i*t+d i)) =
        (∑ i, a i^5)*t^3+(∑ i, a i^4*c i)*t+(∑ i, a i^4*d i) := by
      simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [h15, hc, hd]; ring

/-- The leading-weighted projection also follows from a pointwise identity. -/
theorem leading_projection_zero_of_identity {ι : Type*} [Fintype ι]
    (a c d : ι → ℝ) (N : ℝ)
    (h : ∀ t : ℝ, (∑ i, (a i*t^3+c i*t+d i)^5) = N) (t : ℝ) :
    (∑ i, a i^4*(a i*t^3+c i*t+d i)) = 0 := by
  apply leading_projection_zero a c d N ?_ t
  apply Polynomial.funext
  intro u
  simpa only [eval_finset_sum, eval_pow, eval_add, eval_mul, eval_C, eval_X]
    using h u

/-- At a nonnegative point every coordinate with a nonzero leading
coefficient must vanish. Lower-degree coordinates are not asserted to vanish. -/
theorem nonnegative_point_supported_on_lower_degrees {ι : Type*} [Fintype ι]
    (a c d : ι → ℝ) (N t : ℝ)
    (h : ∀ u : ℝ, (∑ i, (a i*u^3+c i*u+d i)^5) = N)
    (hp : ∀ i, 0 ≤ a i*t^3+c i*t+d i) :
    ∀ i, a i ≠ 0 → a i*t^3+c i*t+d i = 0 := by
  have hz := leading_projection_zero_of_identity a c d N h t
  have hn (i : ι) (_ : i ∈ (univ : Finset ι)) :
      0 ≤ a i^4*(a i*t^3+c i*t+d i) := mul_nonneg (by positivity) (hp i)
  intro i hi
  have he := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz i (mem_univ i)
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 4 hi)

/-- A nonconstant depressed-cubic identity cannot pass through the positive
orthant. The number of coordinates is unrestricted. -/
theorem no_positive_depressed_cubic {ι : Type*} [Fintype ι]
    (a c d : ι → ℝ) (N t : ℝ) (ha : ∃ i, a i ≠ 0)
    (hp : ∀ i, 0 < a i*t^3+c i*t+d i) :
    ¬ (∀ u : ℝ, (∑ i, (a i*u^3+c i*u+d i)^5) = N) := by
  intro h
  obtain ⟨i, hi⟩ := ha
  have hz := nonnegative_point_supported_on_lower_degrees a c d N t h
    (fun j => (hp j).le) i hi
  exact (ne_of_gt (hp i)) hz

private lemma translation_formula (a c d r u : ℝ) :
    a*(u-r/3)^3 + (r*a)*(u-r/3)^2 + c*(u-r/3) + d =
      a*u^3 + (c-a*r^2/3)*u + (d-r*c/3+2*a*r^3/27) := by
  ring

/-- A common proportional quadratic coefficient vector can be removed by
translation. In a constant identity, at every nonnegative point the coordinates
with nonzero cubic coefficients vanish. -/
theorem proportional_quadratic_nonnegative_point {ι : Type*} [Fintype ι]
    (a c d : ι → ℝ) (r N t : ℝ)
    (h : ∀ u : ℝ, (∑ i, (a i*u^3+(r*a i)*u^2+c i*u+d i)^5) = N)
    (hp : ∀ i, 0 ≤ a i*t^3+(r*a i)*t^2+c i*t+d i) :
    ∀ i, a i ≠ 0 → a i*t^3+(r*a i)*t^2+c i*t+d i = 0 := by
  let c' (i : ι) := c i-a i*r^2/3
  let d' (i : ι) := d i-r*c i/3+2*a i*r^3/27
  have h' : ∀ u : ℝ, (∑ i, (a i*u^3+c' i*u+d' i)^5) = N := by
    intro u
    have hh := h (u-r/3)
    simp only [translation_formula] at hh
    exact hh
  have ht (i : ι) : a i*(t+r/3)^3+c' i*(t+r/3)+d' i =
      a i*t^3+(r*a i)*t^2+c i*t+d i := by
    dsimp [c', d']
    ring
  have hh := nonnegative_point_supported_on_lower_degrees a c' d' N (t+r/3) h'
    (fun i => by rw [ht]; exact hp i)
  intro i hi
  simpa only [ht] using hh i hi

/-- Every positive constant-sum cubic family with a nonzero cubic coefficient
must have a quadratic coefficient vector not proportional to its leading vector.
This does not rule out families with nonproportional quadratic coefficients. -/
theorem no_positive_proportional_quadratic {ι : Type*} [Fintype ι]
    (a c d : ι → ℝ) (r N t : ℝ) (ha : ∃ i, a i ≠ 0)
    (hp : ∀ i, 0 < a i*t^3+(r*a i)*t^2+c i*t+d i) :
    ¬ (∀ u : ℝ, (∑ i, (a i*u^3+(r*a i)*u^2+c i*u+d i)^5) = N) := by
  intro h
  obtain ⟨i, hi⟩ := ha
  have hz := proportional_quadratic_nonnegative_point a c d r N t h
    (fun j => (hp j).le) i hi
  exact (ne_of_gt (hp i)) hz

private lemma linear_second_coefficient (c d : ℝ) :
    ((C c*X+C d)^5).coeff 2 = 10*c^2*d^3 := by
  ring_nf
  simp only [← map_pow, coeff_add, coeff_C_mul, coeff_mul_C,
    coeff_X_pow, coeff_X, coeff_C, coeff_mul_ofNat]
  norm_num

private lemma positive_linear_constant {ι : Type*} [Fintype ι]
    (c d : ι → ℝ) (N t : ℝ)
    (h : ∀ u : ℝ, (∑ i, (c i*u+d i)^5) = N)
    (hp : ∀ i, 0 < c i*t+d i) : ∀ i, c i = 0 := by
  have hh : (∑ i, (C (c i)*X+C (c i*t+d i))^5 : ℝ[X]) = C N := by
    apply Polynomial.funext
    intro u
    have he := h (u+t)
    simp only [eval_finset_sum, eval_pow, eval_add, eval_mul, eval_C, eval_X]
    convert he using 2
    ring
  have he := congrArg (fun p : ℝ[X] => p.coeff 2) hh
  simp only [finset_sum_coeff, linear_second_coefficient, coeff_C,
    OfNat.ofNat_ne_zero, if_false] at he
  have hn (i : ι) (_ : i ∈ (univ : Finset ι)) :
      0 ≤ 10*c i^2*(c i*t+d i)^3 := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (pow_nonneg (hp i).le _)
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hn).mp he i (mem_univ i)
  have hp3 : (c i*t+d i)^3 ≠ 0 := ne_of_gt (pow_pos (hp i) 3)
  have hsq : c i^2 = 0 := by
    have hz := (mul_eq_zero.mp hi).resolve_right hp3
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  exact eq_zero_of_pow_eq_zero hsq

/-- Complete positive-point rigidity for this chart, including the case where
all cubic coefficients were zero from the outset. All the coordinates are
constant; no nonzero-leading-coefficient hypothesis is needed. -/
theorem positive_proportional_quadratic_is_constant {ι : Type*} [Fintype ι]
    (a c d : ι → ℝ) (r N t : ℝ)
    (h : ∀ u : ℝ, (∑ i, (a i*u^3+(r*a i)*u^2+c i*u+d i)^5) = N)
    (hp : ∀ i, 0 < a i*t^3+(r*a i)*t^2+c i*t+d i) :
    (∀ i, a i = 0) ∧ (∀ i, c i = 0) := by
  have ha : ∀ i, a i = 0 := by
    intro i
    by_contra hi
    exact no_positive_proportional_quadratic a c d r N t ⟨i, hi⟩ hp h
  have hlin : ∀ u : ℝ, (∑ i, (c i*u+d i)^5) = N := by
    simpa only [ha, mul_zero, zero_mul, zero_add] using h
  have hpos : ∀ i, 0 < c i*t+d i := by
    simpa only [ha, mul_zero, zero_mul, zero_add] using hp
  exact ⟨ha, positive_linear_constant c d N t hlin hpos⟩

end
end Erdos322Research.QuinticDepressedCubic
