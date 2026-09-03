import FormalConjecturesUtil
import Submission.ThetaHeavyMatching
import Submission.ThetaRigidBookMass
import Submission.ThetaZeroTriangle

/-! A conditional matching theorem for rigid theta-free relations.
Zero triangles are still an explicit excluded configuration; this does not
prove their exclusion in extremal hosts or settle Erdős 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaRigidHeavyMatching
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyMatching Erdos713ThetaAnchorPacking Erdos713ThetaPrivatePetals
open Erdos713ThetaDisjointSupports Erdos713ThetaRigidBookMass Erdos713ThetaZeroTriangle
variable {A B : Type*} [Fintype A] [Fintype B]
set_option maxHeartbeats 2000000

/-- Rigidity lowers the private-petal degree threshold from four to three. -/
theorem private_family {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (S : Finset A) {p : B × B} (hp : p.1 ≠ p.2)
    (hmin : ∀ a ∈ commonRows R S p, 3 ≤ (row R a).card) :
    ∃ x : ↥(commonRows R S p) → B,
      (∀ a, x a ∈ privatePetal R S p a.val) ∧ Function.Injective x ∧
      ∀ a b, a ≠ b → codegree R (x a) (x b) = 0 := by
  have hex (a : ↥(commonRows R S p)) : (privatePetal R S p a.val).Nonempty := by
    rw [← card_pos,private_card hr S hp a.property]
    have hd := hmin a.val a.property
    omega
  choose x hx using hex
  have hz (a b : ↥(commonRows R S p)) (hab : a ≠ b) :
      codegree R (x a) (x b) = 0 :=
    private_cross_zero hf S hp a.property b.property
      (fun he => hab (Subtype.ext he)) (hx a) (hx b)
  refine ⟨x,hx,?_,hz⟩
  intro a b he
  by_contra hab
  have ha := (mem_privatePetal R S p a.val (x a)).mp (hx a)
  exact not_common_of_codegree_zero (hz a b hab) a.val ⟨ha.1,he ▸ ha.1⟩

/-- Every heavy pair has a row consisting of exactly its two columns,
provided zero-codegree triangles are excluded and row intersections are rigid. -/
theorem exact_pair_row {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (hz : NoZeroTriangle R) {x y : B} (hxy : x ≠ y)
    (hh : 3 ≤ codegree R x y) : ∃ a : A, row R a = {x,y} := by
  by_contra h
  let T := commonRows R univ (x,y)
  have hmin (a : A) (ha : a ∈ T) : 3 ≤ (row R a).card := by
    have ha' : R a x ∧ R a y := (mem_filter.mp ha).2
    have hs : ({x,y} : Finset B) ⊆ row R a := by
      simp only [insert_subset_iff,singleton_subset_iff,mem_row]
      exact ha'
    by_contra hc
    have he : row R a = {x,y} := (eq_of_subset_of_card_le hs (by simp [hxy]; omega)).symm
    exact h ⟨a,he⟩
  obtain ⟨p,_hp,hpi,hzero⟩ := private_family hf hr univ hxy hmin
  have hT : 3 ≤ Fintype.card T := by
    simpa only [T,commonRows,mem_filter,mem_univ,true_and,Fintype.card_coe,
      codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  obtain ⟨f : Fin 3 ↪ T⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 3) ≤ Fintype.card T by simpa using hT)
  have hi : Function.Injective (fun i : Fin 3 => p (f i)) := hpi.comp f.injective
  have h01 : p (f 0) ≠ p (f 1) := fun he => (by decide : (0 : Fin 3) ≠ 1) (hi he)
  have h02 : p (f 0) ≠ p (f 2) := fun he => (by decide : (0 : Fin 3) ≠ 2) (hi he)
  have h12 : p (f 1) ≠ p (f 2) := fun he => (by decide : (1 : Fin 3) ≠ 2) (hi he)
  exact hz _ _ _ h01 h02 h12
    (hzero _ _ (f.injective.ne (by decide : (0 : Fin 3) ≠ 1)))
    (hzero _ _ (f.injective.ne (by decide : (0 : Fin 3) ≠ 2)))
    (hzero _ _ (f.injective.ne (by decide : (1 : Fin 3) ≠ 2)))

abbrev HeavyPair (R : A → B → Prop) := {p : Pair B // 3 ≤ (supports R p).card}

theorem exists_matching {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (hz : NoZeroTriangle R) :
    ∃ f : HeavyPair R → A, Function.Injective f ∧
      ∀ p, row R (f p) = p.val.val := by
  have hex (p : HeavyPair R) : ∃ a : A, row R a = p.val.val := by
    obtain ⟨x,y,hxy,he⟩ := card_eq_two.mp (pair_card p.val)
    have heq : supports R p.val = univ.filter (fun a => R a x ∧ R a y) := by
      ext a
      simp [mem_supports,he,insert_subset_iff,singleton_subset_iff,mem_row]
    have hh : 3 ≤ codegree R x y := by
      have hp := p.property
      rw [heq] at hp
      simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hp
    obtain ⟨a,ha⟩ := exact_pair_row hf hr hz hxy hh
    exact ⟨a,ha.trans he.symm⟩
  choose f hf' using hex
  refine ⟨f,?_,hf'⟩
  intro p q he
  apply Subtype.ext
  apply Subtype.ext
  exact (hf' p).symm.trans ((congrArg (fun a => row R a) he).trans (hf' q))

theorem heavy_pair_card_le {R : A → B → Prop} (hf : ¬ HasTheta R)
    (hr : ∀ a b, a ≠ b → (row R a ∩ row R b).card ≤ 2)
    (hz : NoZeroTriangle R) : Nat.card (HeavyPair R) ≤ Nat.card A := by
  obtain ⟨f,hi,_⟩ := exists_matching hf hr hz
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hi

#print axioms private_family
#print axioms exact_pair_row
#print axioms exists_matching
#print axioms heavy_pair_card_le
end Erdos713ThetaRigidHeavyMatching
