import Submission.ForestProduct

/-! Uniform probability on a nonempty finite subset, expressed on the ambient
finite type for compatibility with product-coordinate arguments. -/
namespace Erdos7ForestRestricted
open scoped BigOperators
open Erdos7ForestUnion
set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {X : Type*} [Fintype X] [DecidableEq X]

lemma sum_bit (B : Finset X) : (∑ x : X,bit (x ∈ B)) = (B.card:ℚ) := by
  classical
  letI : DecidablePred (fun x : X => x ∈ B) := fun _ => Classical.propDecidable _
  unfold bit
  rw [Finset.sum_boole]
  congr 1
  apply congrArg Finset.card
  ext x
  simp

noncomputable def restricted (U : Finset X) (x : X) : ℚ := bit (x ∈ U)/(U.card:ℚ)
lemma restricted_nonneg (U : Finset X) (x : X) : 0 ≤ restricted U x :=
  div_nonneg (bit_bounds _).1 (Nat.cast_nonneg _)

lemma restricted_mass (U B : Finset X) :
    mass (restricted U) (fun x => x ∈ B) = ((U ∩ B).card:ℚ)/U.card := by
  classical
  unfold mass restricted
  have he (x : X) : bit (x ∈ U)/(U.card:ℚ)*bit (x ∈ B) =
      bit (x ∈ U ∩ B)/(U.card:ℚ) := by
    rw [Finset.mem_inter,bit_and]
    ring
  simp_rw [he]
  rw [← Finset.sum_div,sum_bit]

lemma restricted_sum (U : Finset X) (hU : U.Nonempty) : (∑ x,restricted U x) = 1 := by
  have hn : (U.card:ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hU.card_pos
  unfold restricted
  rw [← Finset.sum_div,sum_bit,div_self hn]

lemma restricted_full (U : Finset X) (hU : U.Nonempty) : mass (restricted U) (fun _ => True) = 1 := by
  simpa [mass,bit] using restricted_sum U hU

lemma restricted_singleton_eq (U : Finset X) (x : X) (hx : x ∈ U) :
    mass (restricted U) (fun y => y ∈ ({x}:Finset X)) = 1/(U.card:ℚ) := by
  rw [restricted_mass,Finset.inter_singleton_of_mem hx,Finset.card_singleton,Nat.cast_one]

lemma restricted_singleton_le (U : Finset X) (x : X) :
    mass (restricted U) (fun y => y ∈ ({x}:Finset X)) ≤ 1/(U.card:ℚ) := by
  rw [restricted_mass]
  have hh : ((U ∩ ({x}:Finset X)).card:ℚ) ≤ 1 := by
    exact_mod_cast (show (U ∩ ({x}:Finset X)).card ≤ 1 from
      (Finset.card_le_card Finset.inter_subset_right).trans_eq (Finset.card_singleton x))
  exact div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)

#print axioms restricted_mass
#print axioms restricted_sum
end Erdos7ForestRestricted
