import FormalConjecturesUtil
import Submission.RestrictedMoments

/-! The existing finite mass-partition model has symmetric pair intensities,
not merely the stated subcritical moments. Thus even the full family of
antisymmetric one-part-pair weighted identities does not force its largest-
part comparison to be balanced. This is not an arithmetic counterexample. -/

namespace Erdos371PrimePairWeightModelObstruction

open Finset Erdos371RestrictedMoments

abbrev Size := Fin 6

def occurrence (i : State) (a : Size) : ℤ := (parts i).count a.val

def intensity (a b : Size) : ℤ :=
  ∑ i : State, ∑ j : State, weight i j * occurrence i a * occurrence j b

lemma intensity_symmetric : ∀ a b : Size, intensity a b = intensity b a := by
  decide +kernel

noncomputable def pairScore (c : Size → Size → ℝ) (i j : State) : ℝ :=
  ∑ a : Size, ∑ b : Size, c a b * (occurrence i a : ℝ) * (occurrence j b : ℝ)

lemma weighted_sum_reindex (c : Size → Size → ℝ) :
    (∑ i : State, ∑ j : State, (weight i j : ℝ)*pairScore c i j) =
      ∑ a : Size, ∑ b : Size, c a b * (intensity a b : ℝ) := by
  simp only [pairScore, intensity, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Every antisymmetric pair weight cancels in this model. -/
theorem all_pair_weights_cancel (c : Size → Size → ℝ)
    (hc : ∀ a b, c b a = -c a b) :
    (∑ i : State, ∑ j : State, (weight i j : ℝ)*pairScore c i j) = 0 := by
  rw [weighted_sum_reindex]
  have he : (∑ a : Size, ∑ b : Size, c a b * (intensity a b : ℝ)) =
      -(∑ a : Size, ∑ b : Size, c a b * (intensity a b : ℝ)) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hc a b, intensity_symmetric b a]
    ring
  linarith

noncomputable def superCoefficient (f : Size → ℝ) (a b : Size) : ℝ :=
  if 5 < a.val+b.val then (a.val : ℝ)*b.val*(f b-f a) else 0

lemma superCoefficient_swap (f : Size → ℝ) (a b : Size) :
    superCoefficient f b a = -superCoefficient f a b := by
  unfold superCoefficient
  rw [Nat.add_comm b.val a.val]
  split_ifs <;> ring

/-- In particular, the newly proved supercritical logarithmic-weight identity
is also satisfied here for every choice of the prime-function analogue. -/
theorem all_supercritical_weights_cancel (f : Size → ℝ) :
    (∑ i : State, ∑ j : State, (weight i j : ℝ)*pairScore (superCoefficient f) i j) = 0 :=
  all_pair_weights_cancel _ (superCoefficient_swap f)

/-- Cancellation of this entire family of weights is compatible with a
nonzero largest-part bias in a mass-one model (after scaling parts by 1/5). -/
theorem weighted_identities_do_not_extract_comparison :
    (∀ f : Size → ℝ, (∑ i : State, ∑ j : State,
      (weight i j : ℝ)*pairScore (superCoefficient f) i j) = 0) ∧
    (∑ i : State, ∑ j : State, weight i j *
      (if largest i > largest j then 1 else if largest i < largest j then -1 else 0)) = 2 :=
  ⟨all_supercritical_weights_cancel, largest_comparison_biased⟩

end Erdos371PrimePairWeightModelObstruction

#print axioms Erdos371PrimePairWeightModelObstruction.weighted_identities_do_not_extract_comparison
