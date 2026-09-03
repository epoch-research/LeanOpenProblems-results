import Submission.QuadraticPrimePrefixBounds

/-! Reciprocal prime mass in fixed power windows. No Sidon assertion. -/
namespace Erdos1206.PrimePowerWindowMass
open Finset Filter FinitePrimeMass PrimeLogMomentNearOne
open scoped Classical Topology

lemma eventually_log_moment :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ y : ℝ in atTop,
      (∑ p ∈ primePrefix y, Real.log (p:ℝ)/(p:ℝ)) ≤ D*Real.log y := by
  obtain ⟨B,hB,hbound⟩ := eventually_primeMoment_bound
  refine ⟨Real.exp 1*B,by positivity,?_⟩
  filter_upwards [QuadraticPrimePrefixBounds.smoothing_tendsto.eventually hbound,
    eventually_gt_atTop (1:ℝ)] with y hy hy1
  have hlog : 0 < Real.log y := Real.log_pos hy1
  have hs : 1 < 1+1/Real.log y := by linarith [one_div_pos.mpr hlog]
  have hscale : ((1+1/Real.log y)-1)*Real.log y ≤ 1 := by
    field_simp
    ring_nf
    rfl
  have hp := prefix_log_moment hs hy1 hscale
  have hy' := mul_le_mul_of_nonneg_left hy hlog.le
  have he : Real.log y * (((1+1/Real.log y)-1)*primeMoment (1+1/Real.log y)) =
      primeMoment (1+1/Real.log y) := by
    field_simp
    ring
  rw [he] at hy'
  exact hp.trans (by nlinarith [Real.exp_pos (1:ℝ)])

/-- The bound applies to any finite set of primes in the indicated window. -/
lemma window_mass {D : ℝ} (_hD : 0 ≤ D) {U k : ℕ} (hU : 1 < U)
    (hb : (∑ p ∈ primePrefix ((U:ℝ)^k),Real.log (p:ℝ)/(p:ℝ)) ≤
      D*Real.log ((U:ℝ)^k)) (P : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime ∧ U < p ∧ p ≤ U^k) :
    (∑ p ∈ P,(1:ℝ)/p) ≤ D*k := by
  have hUR : (1:ℝ) < U := by exact_mod_cast hU
  have hlog : 0 < Real.log (U:ℝ) := Real.log_pos hUR
  let Q : Finset Nat.Primes := P.subtype Nat.Prime
  have hQ : Q ⊆ primePrefix ((U:ℝ)^k) := by
    intro p hp
    have hpP : (p:ℕ) ∈ P := (Finset.mem_subtype.mp hp)
    apply (mem_primePrefix (by positivity) p).mpr
    exact_mod_cast (hP p hpP).2.2
  have hsum : (∑ p ∈ P,Real.log (p:ℝ)/(p:ℝ)) =
      ∑ p ∈ Q,Real.log (p:ℝ)/(p:ℝ) := by
    symm
    exact Finset.sum_subtype_of_mem (fun p : ℕ => Real.log (p:ℝ)/(p:ℝ)) (fun p hp => (hP p hp).1)
  have hlo : Real.log (U:ℝ)*(∑ p ∈ P,(1:ℝ)/p) ≤
      ∑ p ∈ P,Real.log (p:ℝ)/(p:ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
    exact Real.log_le_log (zero_lt_one.trans hUR)
      (by exact_mod_cast (hP p hp).2.1.le)
  have hhi : (∑ p ∈ P,Real.log (p:ℝ)/(p:ℝ)) ≤ D*Real.log ((U:ℝ)^k) := by
    rw [hsum]
    apply (sum_le_sum_of_subset_of_nonneg hQ ?_).trans hb
    intro p _ _
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast p.prop.one_le)) (by positivity)
  rw [Real.log_pow] at hhi
  nlinarith

/-- One constant works for all fixed positive integer power exponents, once
 the lower endpoint is sufficiently large. -/
theorem eventually_window_mass :
    ∃ D : ℝ, 0 < D ∧ ∃ H : ℕ, ∀ U : ℕ,H ≤ U → ∀ k : ℕ,0 < k →
      ∀ P : Finset ℕ,(∀ p ∈ P,p.Prime ∧ U < p ∧ p ≤ U^k) →
        (∑ p ∈ P,(1:ℝ)/p) ≤ D*k := by
  obtain ⟨D,hD,hbound⟩ := eventually_log_moment
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hbound
  obtain ⟨H,hH⟩ := exists_nat_gt (max Y 2)
  refine ⟨D,hD,H,fun U hU k hk P hP => ?_⟩
  have hUR : max Y 2 < (U:ℝ) := hH.trans_le (by exact_mod_cast hU)
  have hU2 : 1 < U := by have := (le_max_right Y 2).trans_lt hUR; exact_mod_cast (by linarith : (1:ℝ) < U)
  apply window_mass hD.le hU2 _ P hP
  apply hY
  have hp : U ≤ U^k := Nat.le_self_pow (by omega) U
  exact (le_max_left Y 2).trans (hUR.le.trans (by exact_mod_cast hp))

#print axioms eventually_log_moment
#print axioms window_mass
#print axioms eventually_window_mass
end Erdos1206.PrimePowerWindowMass
