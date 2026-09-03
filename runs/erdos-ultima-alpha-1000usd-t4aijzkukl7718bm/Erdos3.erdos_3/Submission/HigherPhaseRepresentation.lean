import Submission.SimultaneousPolynomialRecurrence

/-! Exact monomial coordinates for circle-valued polynomial sequences. Root
choices are purely algebraic; no inference about closeness of roots is made. -/
namespace Erdos3HigherPhaseRepresentation
open Finset Metric Erdos3HigherPhaseDifferences Erdos3LocalQuadraticProgressions
  Erdos3FiniteBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2000000

lemma circle_nsmul_surjective {m : ℕ} (hm : 0 < m) (z : Additive Circle) :
    ∃ w : Additive Circle, m • w = z := by
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq (phase z) hm
  have hn : ‖v‖ = 1 := by
    have hh := congrArg norm hv
    rw [norm_pow,phase_norm] at hh
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg v) (Nat.ne_of_gt hm)).mp hh
  let w : Additive Circle := Additive.ofMul (⟨v,mem_sphere_zero_iff_norm.mpr hn⟩ : Circle)
  refine ⟨w,?_⟩
  apply Circle.coe_injective
  change phase (m • w) = phase z
  rw [phase_nsmul]
  exact hv

lemma diffIter_constant_of_next_zero {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (k : ℕ) (hf : diffIter (k+1) f = 0) :
    diffIter k f = fun _ ↦ diffIter k f 0 := by
  have hstep (n : ℕ) : diffIter k f (n+1)-diffIter k f n = 0 := by
    have hh := congr_fun hf n
    simpa only [diffIter,Function.iterate_succ_apply',fwdDiff,Pi.zero_apply] using hh
  funext n
  have hh := constant_step_shift (diffIter k f) 0 hstep 0 n
  simpa only [Nat.zero_add,nsmul_zero,add_zero] using hh

/-- Every degree-at-most-k polynomial sequence in the circle has exact
monomial coordinates. The k! divisibility is justified by actual circle roots. -/
theorem polynomial_phase_representation (k : ℕ) (f : ℕ → Additive Circle)
    (hf : diffIter (k+1) f = 0) :
    ∃ c : Fin (k+1) → Additive Circle, ∀ n : ℕ, f n = ∑ j, (n^j.val) • c j := by
  induction k generalizing f with
  | zero =>
    have hh := diffIter_constant_of_next_zero f 0 hf
    refine ⟨fun _ ↦ f 0,?_⟩
    intro n
    simpa using congr_fun hh n
  | succ k ih =>
    let z := diffIter (k+1) f 0
    have htop : diffIter (k+1) f = fun _ ↦ z := diffIter_constant_of_next_zero f (k+1) hf
    obtain ⟨w,hw⟩ := circle_nsmul_surjective (Nat.factorial_pos (k+1)) z
    let g : ℕ → Additive Circle := fun n ↦ f n-(n^(k+1)) • w
    have hg : diffIter (k+1) g = 0 := by
      change diffIter (k+1) (f-(fun n ↦ (n^(k+1)) • w)) = 0
      rw [diffIter_sub,diffIter_monomial,htop,hw]
      exact sub_self _
    obtain ⟨c,hc⟩ := ih g hg
    refine ⟨Fin.lastCases w c,?_⟩
    intro n
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last,Fin.val_castSucc,Fin.val_last]
    have hh := hc n
    change f n-(n^(k+1)) • w = _ at hh
    exact (sub_eq_iff_eq_add).mp hh

lemma phase_sum {I : Type*} (S : Finset I) (f : I → Additive Circle) :
    phase (∑ i ∈ S, f i) = ∏ i ∈ S, phase (f i) := by
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert i S hi ih => rw [sum_insert hi,prod_insert hi,phase_add,ih]

lemma phase_sum_oscillation {I : Type*} (S : Finset I) (f : I → Additive Circle) :
    ‖phase (∑ i ∈ S, f i)-1‖ ≤ ∑ i ∈ S, ‖phase (f i)-1‖ := by
  induction S using Finset.induction_on with
  | empty => simp [phase]
  | @insert i S hi ih =>
    rw [sum_insert hi,sum_insert hi,phase_add]
    exact (norm_mul_sub_one_le (phase_norm (f i))).trans (add_le_add le_rfl ih)

lemma phase_sub_norm (x y : Additive Circle) :
    ‖phase x-phase y‖ = ‖phase (x-y)-1‖ := by
  have he : phase x-phase y = (phase (x-y)-1)*phase y := by
    rw [sub_mul,one_mul,← phase_add,sub_add_cancel]
  rw [he,norm_mul,phase_norm,mul_one]

/-- Complex-valued form of the monomial representation. -/
theorem polynomial_phase_product (k : ℕ) (f : ℕ → Additive Circle)
    (hf : diffIter (k+1) f = 0) :
    ∃ c : Fin (k+1) → ℂ, (∀ j, ‖c j‖ = 1) ∧
      ∀ n : ℕ, phase (f n) = ∏ j, (c j)^(n^j.val) := by
  obtain ⟨c,hc⟩ := polynomial_phase_representation k f hf
  refine ⟨fun j ↦ phase (c j),fun j ↦ phase_norm _,?_⟩
  intro n
  rw [hc,phase_sum]
  simp only [phase_nsmul]

#print axioms polynomial_phase_representation
#print axioms polynomial_phase_product
end Erdos3HigherPhaseRepresentation
