import FormalConjecturesUtil
import Submission.ThetaDisjointSupports
import Submission.ThetaAffineStars

/-! A conditional robustness result for theta-free relations: absence of
zero-codegree triangles forces heavy pairs to have low-degree witnesses.
No such absence condition is asserted for arbitrary graph extremal hosts. -/
open Finset
namespace Erdos713ThetaZeroTriangle
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaAnchorPacking Erdos713ThetaDisjointSupports
open Erdos713ThetaAffineStars Erdos713ThetaCross
variable {A B : Type*}
set_option maxHeartbeats 2000000

def NoZeroTriangle (R : A → B → Prop) : Prop :=
  ∀ x y z : B, x ≠ y → x ≠ z → y ≠ z →
    codegree R x y = 0 → codegree R x z = 0 → codegree R y z ≠ 0

lemma high_book_le_two [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hz : NoZeroTriangle R) {p : B × B}
    (hp : p.1 ≠ p.2) (hh : 3 ≤ codegree R p.1 p.2) :
    (commonRows R (highRows R) p).card ≤ 2 := by
  classical
  obtain ⟨x,_,hinj,hzero⟩ := exists_private_zero_family hf (highRows R) hp hh
    (fun a ha => (mem_filter.mp (mem_filter.mp ha).1).2)
  by_contra h
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := two_lt_card_iff.mp (by omega :
    2 < (commonRows R (highRows R) p).card)
  let a' : ↥(commonRows R (highRows R) p) := ⟨a,ha⟩
  let b' : ↥(commonRows R (highRows R) p) := ⟨b,hb⟩
  let c' : ↥(commonRows R (highRows R) p) := ⟨c,hc⟩
  have hab' : a' ≠ b' := fun he => hab (congrArg Subtype.val he)
  have hac' : a' ≠ c' := fun he => hac (congrArg Subtype.val he)
  have hbc' : b' ≠ c' := fun he => hbc (congrArg Subtype.val he)
  exact hz (x a') (x b') (x c')
    (fun he => hab' (hinj he)) (fun he => hac' (hinj he)) (fun he => hbc' (hinj he))
    (hzero _ _ hab') (hzero _ _ hac') (hzero _ _ hbc')

lemma heavy_has_small_row [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hz : NoZeroTriangle R) {x y : B}
    (hxy : x ≠ y) (hh : 3 ≤ codegree R x y) :
    ∃ a : A, R a x ∧ R a y ∧ (row R a).card ≤ 3 := by
  classical
  by_contra h
  have hlarge : ∀ a, R a x → R a y → 4 ≤ (row R a).card := by
    intro a hx hy
    by_contra ha
    exact h ⟨a,hx,hy,by omega⟩
  have he : commonRows R (highRows R) (x,y) =
      (univ : Finset A).filter (fun a => R a x ∧ R a y) := by
    ext a
    simp only [commonRows,highRows,mem_filter,mem_univ,true_and]
    exact ⟨fun ha => ha.2,fun ha => ⟨hlarge a ha.1 ha.2,ha⟩⟩
  have hl := high_book_le_two hf hz (p := (x,y)) hxy hh
  rw [he] at hl
  have hh' : 3 ≤ ((univ : Finset A).filter (fun a => R a x ∧ R a y)).card := by
    simpa only [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  omega

open scoped Classical in
noncomputable def heavyOffDiag [Fintype A] [Fintype B] (R : A → B → Prop) : Finset (B × B) :=
  univ.filter (fun p => p.1 ≠ p.2 ∧ 3 ≤ codegree R p.1 p.2)

lemma small_row_pairs_le_six [Fintype B] (R : A → B → Prop) (a : A)
    (ha : (row R a).card ≤ 3) : (row R a).offDiag.card ≤ 6 := by
  classical
  rw [offDiag_card]
  interval_cases h : (row R a).card <;> norm_num

/-- Only rows of degree at most three are charged, each by at most six
ordered distinct pairs. -/
theorem heavy_off_diag_le_six_rows [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hz : NoZeroTriangle R) :
    (heavyOffDiag R).card ≤ 6*Fintype.card A := by
  classical
  let S := (univ : Finset A).filter (fun a => (row R a).card ≤ 3)
  have hsub : heavyOffDiag R ⊆ S.biUnion (fun a => (row R a).offDiag) := by
    intro p hp
    obtain ⟨a,ha1,ha2,ha⟩ := heavy_has_small_row hf hz (mem_filter.mp hp).2.1
      (mem_filter.mp hp).2.2
    exact mem_biUnion.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,ha⟩,
      mem_offDiag.mpr ⟨(mem_row R _ _).mpr ha1,(mem_row R _ _).mpr ha2,
        (mem_filter.mp hp).2.1⟩⟩
  calc
    _ ≤ (S.biUnion (fun a => (row R a).offDiag)).card := card_le_card hsub
    _ ≤ ∑ a ∈ S, (row R a).offDiag.card := card_biUnion_le
    _ ≤ ∑ _a ∈ S, 6 := sum_le_sum (fun a ha =>
      small_row_pairs_le_six R a (mem_filter.mp ha).2)
    _ = S.card*6 := by simp
    _ ≤ Fintype.card A*6 := Nat.mul_le_mul_right 6 (card_le_univ S)
    _ = _ := by omega

/-- A quadratic density gap under the additional zero-triangle exclusion.
The light count includes ordered diagonal pairs. -/
theorem density_gap [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (hz : NoZeroTriangle R) :
    (Fintype.card B)^2 ≤ 12*Fintype.card A+2*lightCount R := by
  classical
  let T : Finset (B × B) := univ.filter (fun p => codegree R p.1 p.2 ≤ 2)
  have hT : T.card = lightCount R := by
    simp only [T,lightCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hsub : (univ : Finset B).offDiag ⊆ heavyOffDiag R ∪ T := by
    intro p hp
    by_cases hh : 3 ≤ codegree R p.1 p.2
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,(mem_offDiag.mp hp).2.2,hh⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,by omega⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hu := heavy_off_diag_le_six_rows hf hz
  rw [offDiag_card,card_univ,hT] at hc
  by_cases hk : 2 ≤ Fintype.card B
  · have h1 : Fintype.card B ≤ Fintype.card B*Fintype.card B := by
      nlinarith only [hk]
    have h2 := Nat.sub_add_cancel h1
    nlinarith only [hc,hu,hk,h2]
  · by_cases hm : 0 < Fintype.card A
    · have hsmall : Fintype.card B ≤ 1 := by omega
      nlinarith only [hsmall,hm]
    · have hempty : Fintype.card A = 0 := by omega
      letI : IsEmpty A := Fintype.card_eq_zero_iff.mp hempty
      have hz' (x y : B) : codegree R x y = 0 := by
        simp only [codegree,Nat.card_of_isEmpty]
      have ht : T = univ := by ext p; simp only [T,mem_filter,mem_univ,hz']; simp
      have he : lightCount R = (Fintype.card B)^2 := by
        rw [← hT,ht,card_univ,Fintype.card_prod,pow_two]
      rw [he]
      omega

#print axioms high_book_le_two
#print axioms heavy_has_small_row
#print axioms heavy_off_diag_le_six_rows
#print axioms density_gap
end Erdos713ThetaZeroTriangle
