import Submission.PartitionObstruction

/-! A fixed-marginal strengthening of the finite partition test. Any strictly
positive marginal on the seven states admits a non-symmetric coupling with the
same low-mass inclusion moments as its independent coupling. This is a finite
model only, not a claim about the actual prime-factor marginal law or arithmetic
correlations. In particular it is not a disproof of Erdős 371. -/
namespace Erdos371.FixedMarginalPartitionPerturbation
open Finset
open PartitionObstructionWithSmallParts (parts largest weight)
attribute [local instance] Classical.propDecidable

noncomputable def kernel (i j : Fin 7) : ℝ := (weight i j : ℝ)-weight j i

lemma kernel_swap (i j : Fin 7) : kernel j i = -kernel i j := by
  unfold kernel
  ring

lemma kernel_row_zero (i : Fin 7) : (∑ j, kernel i j) = 0 := by
  unfold kernel
  rw [sum_sub_distrib]
  have he : (∑ j, (weight i j : ℝ)) = ∑ j, (weight j i : ℝ) := by
    exact_mod_cast PartitionObstructionWithSmallParts.equal_marginals i
  rw [he,sub_self]

lemma kernel_column_zero (j : Fin 7) : (∑ i, kernel i j) = 0 := by
  have he (i : Fin 7) : kernel i j = -kernel j i := kernel_swap j i
  simp_rw [he,sum_neg_distrib,kernel_row_zero,neg_zero]

lemma kernel_abs_le (i j : Fin 7) : |kernel i j| ≤ 2 := by
  have h : ∀ i j : Fin 7, |(weight i j : ℤ)-weight j i| ≤ 2 := by decide +kernel
  unfold kernel
  exact_mod_cast h i j

noncomputable def conditionalMass (W : Fin 7 → Fin 7 → ℝ) (P : Fin 7 → Fin 7 → Prop) : ℝ :=
  ∑ i, ∑ j, if P i j then W i j else 0

lemma conditionalMass_linear (W V : Fin 7 → Fin 7 → ℝ) (ε : ℝ)
    (P : Fin 7 → Fin 7 → Prop) :
    conditionalMass (fun i j => W i j+ε*V i j) P =
      conditionalMass W P+ε*conditionalMass V P := by
  have he (i j : Fin 7) :
      (if P i j then W i j+ε*V i j else 0) =
        (if P i j then W i j else 0)+ε*(if P i j then V i j else 0) := by
    split_ifs <;> ring
  simp only [conditionalMass,he,sum_add_distrib,← mul_sum]

lemma conditionalMass_swap (W : Fin 7 → Fin 7 → ℝ) (P : Fin 7 → Fin 7 → Prop) :
    conditionalMass (fun i j => W j i) P = conditionalMass W (fun i j => P j i) := by
  unfold conditionalMass
  rw [sum_comm]

noncomputable def inclusionMoment (W : Fin 7 → Fin 7 → ℝ) (s t : Finset ℕ) : ℝ :=
  conditionalMass W (fun i j => s ⊆ parts i ∧ t ⊆ parts j)

lemma weight_inclusionMoment (s t : Finset ℕ) :
    inclusionMoment (fun i j => (weight i j : ℝ)) s t =
      PartitionObstructionWithSmallParts.moment s t := by
  unfold inclusionMoment conditionalMass PartitionObstructionWithSmallParts.moment
  push_cast
  rfl

/-- The antisymmetric perturbation is invisible to every inclusion moment
within the one-partition mass budget. -/
lemma kernel_inclusionMoment_zero (s t : Finset ℕ)
    (h : (∑ a ∈ s, a)+(∑ b ∈ t, b) ≤ 945) : inclusionMoment kernel s t = 0 := by
  have he : kernel = fun i j => (weight i j : ℝ)+(-1 : ℝ)*(weight j i : ℝ) := by
    funext i j
    unfold kernel
    ring
  unfold inclusionMoment
  rw [he,conditionalMass_linear]
  rw [conditionalMass_swap (fun i j => (weight i j : ℝ))
    (fun i j => s ⊆ parts i ∧ t ⊆ parts j)]
  have he' : conditionalMass (fun i j => (weight i j : ℝ))
      (fun i j => s ⊆ parts j ∧ t ⊆ parts i) =
      inclusionMoment (fun i j => (weight i j : ℝ)) t s := by
    simp only [inclusionMoment,and_comm]
  rw [he']
  change inclusionMoment (fun i j => (weight i j : ℝ)) s t +
    (-1 : ℝ)*inclusionMoment (fun i j => (weight i j : ℝ)) t s = 0
  rw [weight_inclusionMoment,weight_inclusionMoment,
    PartitionObstructionWithSmallParts.small_moment_symmetry s t h]
  ring

lemma kernel_rising_mass : conditionalMass kernel (fun i j => largest i < largest j) = -2 := by
  have h : (∑ i : Fin 7, ∑ j : Fin 7,
      if largest i < largest j then (weight i j : ℤ)-weight j i else 0) = -2 := by
    decide +kernel
  unfold conditionalMass kernel
  exact_mod_cast h

lemma kernel_falling_mass : conditionalMass kernel (fun i j => largest j < largest i) = 2 := by
  have h : (∑ i : Fin 7, ∑ j : Fin 7,
      if largest j < largest i then (weight i j : ℤ)-weight j i else 0) = 2 := by
    decide +kernel
  unfold conditionalMass kernel
  exact_mod_cast h

/-- Fix the entire marginal in advance. Low-mass moments even equal those of
the independent coupling, yet the largest-part comparison can be biased. -/
theorem exists_biased_coupling_with_fixed_marginal
    (μ : Fin 7 → ℝ) (hμ : ∀ i, 0 < μ i) (hμsum : ∑ i, μ i = 1) :
    ∃ W : Fin 7 → Fin 7 → ℝ,
      (∀ i j, 0 < W i j) ∧
      (∀ i, ∑ j, W i j = μ i) ∧
      (∀ j, ∑ i, W i j = μ j) ∧
      (∀ s t : Finset ℕ, (∑ a ∈ s, a)+(∑ b ∈ t, b) ≤ 945 →
        inclusionMoment W s t = inclusionMoment (fun i j => μ i*μ j) s t) ∧
      conditionalMass W (fun i j => largest i < largest j) <
        conditionalMass W (fun i j => largest j < largest i) := by
  let δ : ℝ := univ.inf' univ_nonempty μ
  have hδ : 0 < δ := (lt_inf'_iff univ_nonempty).mpr (fun i _ => hμ i)
  have hδi (i : Fin 7) : δ ≤ μ i := inf'_le μ (mem_univ i)
  let ε : ℝ := δ^2/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  let W := fun i j : Fin 7 => μ i*μ j+ε*kernel i j
  refine ⟨W,?_,?_,?_,?_,?_⟩
  · intro i j
    have hk : -2 ≤ kernel i j := (abs_le.mp (kernel_abs_le i j)).1
    have hm := mul_le_mul_of_nonneg_left hk hε.le
    have hp : δ^2 ≤ μ i*μ j := by
      simpa only [pow_two] using mul_le_mul (hδi i) (hδi j) hδ.le (hμ i).le
    have hs : 0 < δ^2 := sq_pos_of_pos hδ
    dsimp only [W,ε] at *
    nlinarith
  · intro i
    simp only [W,sum_add_distrib,← mul_sum,kernel_row_zero,hμsum,mul_zero,add_zero,mul_one]
  · intro j
    simp only [W,sum_add_distrib,← sum_mul,← mul_sum,kernel_column_zero,hμsum,mul_zero,add_zero,one_mul]
  · intro s t hst
    change conditionalMass (fun i j => μ i*μ j+ε*kernel i j)
      (fun i j => s ⊆ parts i ∧ t ⊆ parts j) = _
    rw [conditionalMass_linear]
    change inclusionMoment (fun i j => μ i*μ j) s t+ε*inclusionMoment kernel s t = _
    rw [kernel_inclusionMoment_zero s t hst,mul_zero,add_zero]
  · change conditionalMass (fun i j => μ i*μ j+ε*kernel i j) _ <
      conditionalMass (fun i j => μ i*μ j+ε*kernel i j) _
    rw [conditionalMass_linear,conditionalMass_linear,kernel_rising_mass,kernel_falling_mass]
    have he : conditionalMass (fun i j => μ i*μ j) (fun i j => largest i < largest j) =
        conditionalMass (fun i j => μ i*μ j) (fun i j => largest j < largest i) := by
      rw [← conditionalMass_swap]
      simp only [mul_comm]
    rw [he]
    linarith

#print axioms kernel_inclusionMoment_zero
#print axioms exists_biased_coupling_with_fixed_marginal
end Erdos371.FixedMarginalPartitionPerturbation
