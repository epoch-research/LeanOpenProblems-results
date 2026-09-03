import Submission.ConditionedLatticeBasis
import Submission.LatticeRecurrenceObstruction

/-! Dyadic coordinate precisions whose total cost is controlled by the logarithm
of the product of basis lengths, rather than by their maximum independently. -/
namespace Erdos3LatticePrecisionBudget
open Finset Module Erdos3AnisotropicAvoidanceParameters Erdos3ConditionedLatticeBasis
  Erdos3LatticePhaseCoordinates
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

variable {I : Type*} [Fintype I]

def basisPrecisionBudget (m s W : ℕ) : ℕ := m*(s+m+2)+W+1

lemma dyadic_upper_scale {x : ℝ} (hx : 1 ≤ x) :
    ∃ r : ℕ, x ≤ (2:ℝ)^r ∧ (2:ℝ)^r ≤ 2*x := by
  obtain ⟨r,hr,hxlt⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ) < 2)
  refine ⟨r+1,hxlt.le,?_⟩
  rw [pow_succ]
  linarith

/-- A product bound controls the sum of all dyadic precisions. -/
theorem exists_dyadic_precisions (a : I → ℝ) (W s : ℕ)
    (ha : ∀ i, 1 ≤ a i) (hprod : (∏ i, a i) ≤ (2:ℝ)^W) :
    ∃ t : I → ℕ,
      precisionMass t ≤ basisPrecisionBudget (Fintype.card I) s W ∧
      (∀ i, (2:ℝ)^(t i) ≤ (2:ℝ)^(s+Fintype.card I+1)*a i) ∧
      (∑ i, (1/2:ℝ)^(t i)*a i) ≤ (1/2:ℝ)^s := by
  choose r hr hr' using fun i ↦ dyadic_upper_scale (ha i)
  let m := Fintype.card I
  have hsumr : (∑ i, r i) ≤ m+W := by
    have hp : (2:ℝ)^(∑ i, r i) ≤ (2:ℝ)^(m+W) := by
      calc
        _ = ∏ i, (2:ℝ)^(r i) := (prod_pow_eq_pow_sum _ _ _).symm
        _ ≤ ∏ i, 2*a i := prod_le_prod (fun i _ ↦ by positivity) (fun i _ ↦ hr' i)
        _ = (2:ℝ)^m*(∏ i, a i) := by rw [prod_mul_distrib,prod_const,card_univ]
        _ ≤ (2:ℝ)^m*(2:ℝ)^W := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = _ := (pow_add _ _ _).symm
    exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp hp
  let t : I → ℕ := fun i ↦ s+m+r i
  have ht : (∑ i, t i) = m*(s+m)+(∑ i, r i) := by
    simp only [t,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,m]
    ring
  have hmass : precisionMass t ≤ basisPrecisionBudget m s W := by
    unfold precisionMass basisPrecisionBudget
    rw [ht]
    dsimp only [m] at *
    nlinarith only [hsumr]
  have hscale (i : I) : (2:ℝ)^(t i) ≤ (2:ℝ)^(s+m+1)*a i := by
    calc
      _ = (2:ℝ)^(s+m)*(2:ℝ)^(r i) := pow_add _ _ _
      _ ≤ (2:ℝ)^(s+m)*(2*a i) := mul_le_mul_of_nonneg_left (hr' i) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hsmall (i : I) : (1/2:ℝ)^(t i)*a i ≤ (1/2:ℝ)^(s+m) := by
    have hi : (1/2:ℝ)^(r i)*a i ≤ 1 := by
      calc
        _ ≤ (1/2:ℝ)^(r i)*(2:ℝ)^(r i) :=
          mul_le_mul_of_nonneg_left (hr i) (by positivity)
        _ = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = (1/2:ℝ)^(s+m)*((1/2:ℝ)^(r i)*a i) := by dsimp only [t]; rw [pow_add]; ring
      _ ≤ (1/2:ℝ)^(s+m)*1 := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := mul_one _
  refine ⟨t,hmass,hscale,?_⟩
  have hm : (m:ℝ) ≤ (2:ℝ)^m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  calc
    _ ≤ ∑ _i : I, (1/2:ℝ)^(s+m) := sum_le_sum (fun i _ ↦ hsmall i)
    _ = (m:ℝ)*(1/2:ℝ)^(s+m) := by rw [sum_const,card_univ,nsmul_eq_mul]
    _ ≤ (2:ℝ)^m*(1/2:ℝ)^(s+m) := mul_le_mul_of_nonneg_right hm (by positivity)
    _ = (1/2:ℝ)^s := by rw [pow_add,div_pow,div_pow,one_pow,one_pow]; field_simp

lemma meanExponent_le_mass (t : I → ℕ) :
    frequencyMeanExponent t+1 ≤ (2*Fintype.card I+9)*precisionMass t := by
  have hm : Fintype.card I ≤ precisionMass t := by unfold precisionMass; omega
  have hs : (∑ i,t i) ≤ precisionMass t := by unfold precisionMass; omega
  have hp := precisionMass_pos t
  have hs' : (∑ i,t i)+Fintype.card I+1 = precisionMass t := by unfold precisionMass; omega
  unfold frequencyMeanExponent
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Simultaneous geometric and analytic parameters for a lattice with minimum
nonzero length at least one and covolume at most 2^V. -/
theorem lattice_precision_parameters (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (s V : ℕ)
    (hmin : ∀ x : E, x ∈ L → x ≠ 0 → 1 ≤ ‖x‖)
    (hvol : ZLattice.covolume L ≤ (2:ℝ)^V) :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, ∃ t : Fin (finrank ℝ E) → ℕ,
      Submodule.span ℤ (Set.range b) = L ∧
      (∀ i, 1 ≤ ‖b i‖) ∧
      (∏ i, ‖b i‖) ≤ (2:ℝ)^((finrank ℝ E)^2+V) ∧
      (∀ i, ‖b i‖*‖coordinate b i‖ ≤ (2:ℝ)^((finrank ℝ E)^2)) ∧
      precisionMass t ≤ basisPrecisionBudget (finrank ℝ E) s ((finrank ℝ E)^2+V) ∧
      (∀ i, (2:ℝ)^(t i) ≤ (2:ℝ)^(s+finrank ℝ E+1)*‖b i‖) ∧
      (∑ i, (1/2:ℝ)^(t i)*‖b i‖) ≤ (1/2:ℝ)^s := by
  obtain ⟨b,hspan,hprod,hcondition⟩ := exists_conditioned_lattice_basis L
  have hbmin (i) : 1 ≤ ‖b i‖ := hmin (b i)
    (by rw [← hspan]; exact Submodule.subset_span (Set.mem_range_self i)) (b.ne_zero i)
  have hp : (∏ i, ‖b i‖) ≤ (2:ℝ)^((finrank ℝ E)^2+V) := by
    calc
      _ ≤ (2:ℝ)^((finrank ℝ E)^2)*ZLattice.covolume L := hprod
      _ ≤ (2:ℝ)^((finrank ℝ E)^2)*(2:ℝ)^V := mul_le_mul_of_nonneg_left hvol (by positivity)
      _ = _ := (pow_add _ _ _).symm
  obtain ⟨t,ht,htscale,htsmall⟩ := exists_dyadic_precisions (fun i ↦ ‖b i‖) ((finrank ℝ E)^2+V) s hbmin hp
  refine ⟨b,t,hspan,hbmin,hp,hcondition,?_,?_,htsmall⟩
  · simpa only [Fintype.card_fin] using ht
  · simpa only [Fintype.card_fin] using htscale

#print axioms lattice_precision_parameters
end Erdos3LatticePrecisionBudget
