import Submission.FullCountDiscrepancy

/-! An unconditional endpoint estimate at an exponentially small parameter.
The parameter is uniform over all prime sets of a fixed cardinality budget
and every interval length. Its exponential dependence does NOT give the
critical-rate endpoint estimate or settle the quadratic conjecture. -/
namespace Erdos970.GapAverages
open Finset Real

/-- A general finite Gibbs comparison, retaining the full count-range loss. -/
theorem endpointLaplace_ge_of_count_range (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (t A B : ℝ) (ht : 0 ≤ t)
    (hlo : ∀ r : Phase P, A ≤ intervalCount P m r)
    (hhi : ∀ r : Phase P, intervalCount P m r ≤ B) :
    exp (-t*(B-A))*density P*countLaplace P t m ≤ endpointLaplace P t m := by
  have hF : countLaplace P t m ≤ exp (-t*A) := by
    have hh : phaseMean P (fun r => exp (-t*intervalCount P m r)) ≤
        phaseMean P (fun _ => exp (-t*A)) := by
      apply phaseMean_mono
      intro r
      exact exp_le_exp.mpr
        (by nlinarith only [mul_nonneg ht (sub_nonneg.mpr (hlo r))])
    change countLaplace P t m ≤ phaseMean P (fun _ => exp (-t*A)) at hh
    rwa [phaseMean_const P hP] at hh
  have hG : exp (-t*B)*density P ≤ endpointLaplace P t m := by
    have hh : phaseMean P (fun r => exp (-t*B)*point P m r) ≤
        endpointLaplace P t m := by
      apply phaseMean_mono
      intro r
      have hp : 0 ≤ point P m r := by
        rcases point_eq_zero_or_one P m r with h | h
        · rw [h]
        · rw [h]; norm_num
      have he : exp (-t*B) ≤ exp (-t*intervalCount P m r) :=
        exp_le_exp.mpr (by nlinarith only [mul_nonneg ht (sub_nonneg.mpr (hhi r))])
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right he hp
    rwa [phaseMean_mul, phaseMean_point P hP] at hh
  calc
    exp (-t*(B-A))*density P*countLaplace P t m ≤
        exp (-t*(B-A))*density P*exp (-t*A) :=
      mul_le_mul_of_nonneg_left hF (mul_nonneg (exp_pos _).le (density_pos P hP).le)
    _ = exp (-t*B)*density P := by
      rw [mul_right_comm, ← exp_add]
      congr 1
      congr 1
      ring
    _ ≤ endpointLaplace P t m := hG

/-- Full inclusion-exclusion makes the comparison independent of m and of
the sizes of the primes, at the cost of an exponential cardinality loss. -/
theorem endpointLaplace_ge_full_cost (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    exp (-t*(2 : ℝ)^(P.card+1))*density P*countLaplace P t m ≤
      endpointLaplace P t m := by
  have hh := endpointLaplace_ge_of_count_range P hP m t
    ((m : ℝ)*density P-(2 : ℝ)^P.card)
    ((m : ℝ)*density P+(2 : ℝ)^P.card) ht
    (fun r => by have := (abs_le.mp (intervalCount_full_discrepancy P hP m r)).1; linarith)
    (fun r => by have := (abs_le.mp (intervalCount_full_discrepancy P hP m r)).2; linarith)
  have he : ((m : ℝ)*density P+(2 : ℝ)^P.card) -
      ((m : ℝ)*density P-(2 : ℝ)^P.card) = (2 : ℝ)^(P.card+1) := by
    rw [pow_succ]
    ring
  rwa [he] at hh

noncomputable def budgetEndpointParameter (k : ℕ) : ℝ := log 2/(2 : ℝ)^(k+1)

lemma budgetEndpointParameter_pos (k : ℕ) : 0 < budgetEndpointParameter k :=
  div_pos (log_pos (by norm_num)) (by positivity)

/-- A genuine positive-parameter bound, uniform over all |P|<=k and all m.
The parameter still shrinks exponentially in k. -/
theorem budget_softEndpoint (k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hk : P.card ≤ k) (m : ℕ) :
    (1/2 : ℝ)*density P*countLaplace P (budgetEndpointParameter k) m ≤
      endpointLaplace P (budgetEndpointParameter k) m := by
  have ht := budgetEndpointParameter_pos k
  have hp : budgetEndpointParameter k*(2 : ℝ)^(P.card+1) ≤ log 2 := by
    calc
      _ ≤ budgetEndpointParameter k*(2 : ℝ)^(k+1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hk 1)) ht.le
      _ = log 2 := by unfold budgetEndpointParameter; field_simp
  have he : (1/2 : ℝ) ≤ exp (-budgetEndpointParameter k*(2 : ℝ)^(P.card+1)) := by
    calc
      (1/2 : ℝ) = exp (-log 2) := by rw [exp_neg, exp_log (by norm_num)]; norm_num
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right he
    (mul_nonneg (density_pos P hP).le (countLaplace_nonneg P (budgetEndpointParameter k) m))
  have hh := endpointLaplace_ge_full_cost P hP m (budgetEndpointParameter k) ht.le
  calc
    (1/2 : ℝ)*density P*countLaplace P (budgetEndpointParameter k) m ≤
        exp (-budgetEndpointParameter k*(2 : ℝ)^(P.card+1))*density P*
          countLaplace P (budgetEndpointParameter k) m := by
      simpa only [mul_assoc] using hm
    _ ≤ _ := hh

/-- The corresponding unconditional void bound. Its rate is exponential in
-k and is far too weak for the previously verified critical criterion. -/
theorem budget_exponential_void (k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hk : P.card ≤ k) (m : ℕ) :
    coveredFraction P m ≤ exp
      (-((density P/2)*(1-exp (-budgetEndpointParameter k))*(m : ℝ))) := by
  apply (coveredFraction_le_countLaplace P (budgetEndpointParameter k) m).trans
  apply countLaplace_le_of_endpoint_rate P hP _ _ (budgetEndpointParameter_pos k).le
  intro n
  simpa only [div_eq_mul_inv, one_mul, mul_comm (density P)] using
    budget_softEndpoint k P hP hk n

#print axioms endpointLaplace_ge_of_count_range
#print axioms endpointLaplace_ge_full_cost
#print axioms budget_softEndpoint
#print axioms budget_exponential_void
end Erdos970.GapAverages
