import Submission.LatticePhaseCoordinates

/-! A lattice-valued recurrence obstruction in an arbitrary finite-dimensional
real normed space. Failure of recurrence yields a nonzero integral dual
functional, with its norm separated from the arithmetic denominator. -/
namespace Erdos3LatticeRecurrenceObstruction
open Finset Module Erdos3LatticePhaseCoordinates Erdos3AnisotropicPolynomialObstruction
  Erdos3AnisotropicAvoidanceParameters Erdos3SharpHigherPhaseWeylInverse
  Erdos3CircleIntegerApproximation
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The operator norm bound only involves the short structural frequency.
The separate denominator q can be much larger without changing that norm. -/
theorem lattice_recurrence_obstruction (b : Basis I ℝ E) (α : E)
    (k : ℕ) (t : I → ℕ) (N : ℕ) {η : ℝ}
    (hprecision : (∑ i, (1/2 : ℝ)^(t i)*‖b i‖) ≤ 4*η)
    (hN : 2^(sharpWeylConstant k*(frequencyMeanExponent t+1)) ≤ N)
    (havoid : ∀ n : ℕ, 0 < n → n ≤ N → ∀ y : E,
      y ∈ Submodule.span ℤ (Set.range b) → η < ‖((n^(k+1) : ℕ) : ℝ) • α-y‖) :
    ∃ F : E →L[ℝ] ℝ, F ≠ 0 ∧
      (∀ y : E, y ∈ Submodule.span ℤ (Set.range b) → ∃ c : ℤ, F y = (c : ℝ)) ∧
      ‖F‖ ≤ (kernelPower t : ℝ)*(∑ i, (2 : ℝ)^(t i+2)*‖coordinate b i‖) ∧
      ∃ q : ℕ, ∃ c : ℤ, 0 < q ∧
      q ≤ 2^(sharpWeylConstant k*(frequencyMeanExponent t+1)+(k+1).factorial) ∧
      |(q : ℝ)*F α-(c : ℝ)| ≤
        (2 : ℝ)^(sharpWeylConstant k*(frequencyMeanExponent t+1))/(N : ℝ)^(k+1) := by
  have hav : ∀ n : ℕ, 0 < n → n ≤ N → ∃ i, (1/2 : ℝ)^(t i) ≤
      ‖ephase (((n^(k+1) : ℕ) : ℝ)*(b.repr α i))-1‖ := by
    intro n hn hnN
    by_contra hh
    push_neg at hh
    have hphase : ∀ i, ‖ephase (b.repr (((n^(k+1) : ℕ) : ℝ) • α) i)-1‖ ≤ (1/2 : ℝ)^(t i) := by
      intro i
      simpa only [map_smul,Finsupp.smul_apply,smul_eq_mul] using (hh i).le
    obtain ⟨y,hy,hclose⟩ := exists_lattice_near_of_chords b (((n^(k+1) : ℕ) : ℝ) • α)
      (fun i ↦ (1/2 : ℝ)^(t i)) hphase
    have hle : ‖((n^(k+1) : ℕ) : ℝ) • α-y‖ ≤ η := by linarith only [hclose,hprecision]
    exact (not_lt_of_ge hle) (havoid n hn hnN y hy)
  obtain ⟨h,hne,hbound,q,c,hq,hqb,hsmall⟩ := anisotropic_real_obstruction
    k t N (fun i ↦ b.repr α i) hN hav
  refine ⟨dualFrequency b h,dualFrequency_ne_zero b h hne,
    fun y hy ↦ dualFrequency_integral b h y hy,?_,q,c,hq,hqb,?_⟩
  · calc
      _ ≤ ∑ i, ((kernelPower t : ℝ)*(2 : ℝ)^(t i+2))*‖coordinate b i‖ :=
        dualFrequency_norm b h _ (fun i ↦ by exact_mod_cast (hbound i).le)
      _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro i _; ring
  · simpa only [dualFrequency_apply] using hsmall

/-- A convenient dimension-only conditioning hypothesis for the dual norm.
It is explicit: no well-conditioned lattice basis is silently assumed. -/
lemma dual_norm_budget (b : Basis I ℝ E) (t : I → ℕ) {A D : ℝ}
    (hA : 0 ≤ A)
    (hscale : ∀ i, (2 : ℝ)^(t i) ≤ A*‖b i‖)
    (hcondition : ∀ i, ‖b i‖*‖coordinate b i‖ ≤ D) :
    (kernelPower t : ℝ)*(∑ i, (2 : ℝ)^(t i+2)*‖coordinate b i‖) ≤
      4*(kernelPower t : ℝ)*(Fintype.card I : ℝ)*A*D := by
  have hh (i : I) : (2 : ℝ)^(t i+2)*‖coordinate b i‖ ≤ 4*A*D := by
    rw [pow_add]
    norm_num only [pow_two]
    have h1 := mul_le_mul_of_nonneg_right (hscale i) (norm_nonneg (coordinate b i))
    have h2 := mul_le_mul_of_nonneg_left (hcondition i) hA
    nlinarith only [h1,h2]
  calc
    _ ≤ (kernelPower t : ℝ)*(∑ _i : I, 4*A*D) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ ↦ hh i)) (Nat.cast_nonneg _)
    _ = _ := by rw [sum_const,card_univ,nsmul_eq_mul]; ring

#print axioms lattice_recurrence_obstruction
#print axioms dual_norm_budget
end Erdos3LatticeRecurrenceObstruction
