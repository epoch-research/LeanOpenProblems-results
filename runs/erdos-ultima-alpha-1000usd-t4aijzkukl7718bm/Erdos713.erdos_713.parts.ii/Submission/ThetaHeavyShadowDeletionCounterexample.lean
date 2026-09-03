import FormalConjecturesUtil
import Submission.ThetaHeavyThreeHalvesCounterexample

/-! The heavy-pair shadow of a theta-free relation cannot always be made
C4-free by deleting O(number of rows) ordered pairs. Auxiliary only. -/
open Finset
open scoped Classical
namespace Erdos713ThetaHeavyShadowDeletionCounterexample
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaAffineStars
open Erdos713ThetaC4Deletion Erdos713ThetaHeavySparsifier
open Erdos713ThetaHeavyThreeHalvesCounterexample
variable {A B : Type*}
set_option maxHeartbeats 2000000

def shadow (R : A → B → Prop) (x y : B) : Prop :=
  x ≠ y ∧ 3 ≤ codegree R x y

lemma heavy_le_shadow_add [Fintype A] [Fintype B] (R : A → B → Prop) :
    heavyCount R ≤ edges (shadow R)+Nat.card B := by
  let H : B → B → Prop := fun x y => 3 ≤ codegree R x y
  have hsub : ∀ x y, shadow R x y → H x y := fun _ _ h => h.2
  have he := edge_split hsub
  have hdiag : loss H (shadow R) ≤ Nat.card B := by
    let T := {p : B × B // H p.1 p.2 ∧ ¬ shadow R p.1 p.2}
    have hEq (p : T) : p.val.1 = p.val.2 := by
      by_contra h
      exact p.property.2 ⟨h,p.property.1⟩
    have hinj : Function.Injective (fun p : T => p.val.1) := by
      intro p q h
      apply Subtype.ext
      exact Prod.ext h ((hEq p).symm.trans (h.trans (hEq q)))
    exact Nat.card_le_card_of_injective _ hinj
  change edges (shadow R)+loss H (shadow R) = heavyCount R at he
  omega

lemma columns_le_rows_of_cube (k m : ℕ) (h : k^3 ≤ m^2) : k ≤ m := by
  by_cases hk : k = 0
  · simp only [hk,Nat.zero_le]
  have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hpow : k^2 ≤ k^3 := by
    simpa only [pow_succ] using Nat.le_mul_of_pos_right (k^2) hkpos
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (hpow.trans h)

lemma heavy_bound_of_deletion [Fintype A] [Fintype B] (R : A → B → Prop)
    (Q : B → B → Prop) (C : ℕ)
    (hsize : (Nat.card B)^3 ≤ (Nat.card A)^2)
    (hsub : ∀ x y, Q x y → shadow R x y) (hQ : FourFree Q)
    (hloss : loss (shadow R) Q ≤ C*Nat.card A) :
    heavyCount R ≤ (C+3)*Nat.card A := by
  have hk := columns_le_rows_of_cube _ _ hsize
  have hsq := sqrt_term_le_of_cube_le _ _ hsize
  have hfour := four_free_real_bound hQ
  have hkR : (Nat.card B : ℝ) ≤ Nat.card A := by exact_mod_cast hk
  have heR : (edges Q : ℝ) ≤ 2*(Nat.card A : ℝ) := by
    nlinarith only [hfour,hsq,hkR]
  have he : edges Q ≤ 2*Nat.card A := by exact_mod_cast heR
  have hs := edge_split hsub
  have hh := heavy_le_shadow_add R
  nlinarith only [he,hs,hh,hloss,hk]

/-- No linear deletion budget works, even for the stronger rectangular
notion `FourFree` on the retained ordered-pair relation. -/
theorem exists_no_shadow_deletion (C : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ (Nat.card B)^3 ≤ (Nat.card A)^2 ∧
      ¬ ∃ Q : B → B → Prop,
        (∀ x y, Q x y → shadow R x y) ∧ FourFree Q ∧ loss (shadow R) Q ≤ C*Nat.card A := by
  obtain ⟨A,B,iA,iB,R,hfree,_hm,hsize,hbig⟩ := exists_row_counterexample (C+3)
  refine ⟨A,B,iA,iB,R,hfree,hsize,?_⟩
  rintro ⟨Q,hsub,hQ,hloss⟩
  exact (not_le_of_gt hbig) (heavy_bound_of_deletion R Q C hsize hsub hQ hloss)

theorem no_universal_shadow_deletion :
    ¬ ∃ C : ℕ, ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → ∃ Q : B → B → Prop,
        (∀ x y, Q x y → shadow R x y) ∧ FourFree Q ∧ loss (shadow R) Q ≤ C*Nat.card A := by
  rintro ⟨C,hC⟩
  obtain ⟨A,B,iA,iB,R,hf,_hsize,hno⟩ := exists_no_shadow_deletion C
  exact hno (hC A B R hf)

#print axioms heavy_le_shadow_add
#print axioms heavy_bound_of_deletion
#print axioms exists_no_shadow_deletion
#print axioms no_universal_shadow_deletion
end Erdos713ThetaHeavyShadowDeletionCounterexample
