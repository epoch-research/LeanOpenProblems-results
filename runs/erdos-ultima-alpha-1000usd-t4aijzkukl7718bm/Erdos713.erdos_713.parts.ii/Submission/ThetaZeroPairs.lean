import FormalConjecturesUtil
import Submission.ThetaAllWitnessPacking

/-! Private book charges are missing pairs, not merely light pairs. -/
open Finset
namespace Erdos713ThetaZeroPairs
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaAnchorPacking
open Erdos713ThetaPrivatePetals Erdos713ThetaAllWitnessPacking
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma cross_codegree_zero [Fintype A] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {a b : A} (hab : a ≠ b) {z w x y : B}
    (hzw : z ≠ w) (haz : R a z) (haw : R a w) (hbz : R b z) (hbw : R b w)
    (hax : R a x) (hbx : ¬ R b x) (hby : R b y) (hay : ¬ R a y) :
    codegree R x y = 0 := by
  classical
  have hempty : IsEmpty {c // R c x ∧ R c y} := ⟨by
    rintro ⟨c,hcx,hcy⟩
    have hca : c ≠ a := by rintro rfl; exact hay hcy
    have hcb : c ≠ b := by rintro rfl; exact hbx hcx
    have hxz : x ≠ z := by rintro rfl; exact hbx hbz
    have hxw : x ≠ w := by rintro rfl; exact hbx hbw
    have hyz : y ≠ z := by rintro rfl; exact hay haz
    have hyw : y ≠ w := by rintro rfl; exact hay haw
    have hxy : x ≠ y := by rintro rfl; exact hay hax
    exact hf (theta_of_rows hab hca hcb hzw hxz hxw hyz hyw hxy
      haz haw hbz hbw hax hby hcx hcy)⟩
  letI := hempty
  exact Nat.card_of_isEmpty

open scoped Classical in
noncomputable def zeroSet [Fintype A] [Fintype B] (R : A → B → Prop) : Finset (B × B) :=
  univ.filter (fun p => codegree R p.1 p.2 = 0)

open scoped Classical in
noncomputable def zeroAt [Fintype A] [Fintype B] (R : A → B → Prop) (a : A) : Finset (B × B) :=
  (zeroSet R).filter (fun p => R a p.1)

open scoped Classical in
theorem root_all_zero_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) (r : ℕ)
    (hmin : ∀ b ∈ S, r ≤ (row R b).card) (a : A) (ha : a ∈ S) :
    (witnesses R S a).card*((row R a).card-3)*(r-3) ≤ 6*(zeroAt R a).card := by
  classical
  let P := ↥(witnesses R S a)
  let X (w : P) : Finset (B × B) :=
    (row R a \ row R w.val.2) ×ˢ privatePetal R S w.val.1 w.val.2
  have hdata (w : P) :
      R a w.val.1.1 ∧ R a w.val.1.2 ∧ R w.val.2 w.val.1.1 ∧ R w.val.2 w.val.1.2 ∧
      w.val.1.1 ≠ w.val.1.2 ∧ w.val.2 ≠ a ∧ w.val.2 ∈ S ∧
      3 ≤ codegree R w.val.1.1 w.val.1.2 := by
    have h := (mem_witnesses R S a w.val).mp w.property
    have hp := mem_offDiag.mp (mem_filter.mp h.1).1
    have hb := mem_filter.mp h.2.1
    exact ⟨(mem_row R _ _).mp hp.1,(mem_row R _ _).mp hp.2.1,hb.2.1,hb.2.2,
      hp.2.2,h.2.2,hb.1,anchor_heavy h.1⟩
  have hXsub (w : P) : X w ⊆ zeroAt R a := by
    intro q hq
    obtain ⟨hx,hy⟩ := mem_product.mp hq
    have hy' := (mem_privatePetal R S w.val.1 w.val.2 q.2).mp hy
    obtain ⟨ha1,ha2,hb1,hb2,hp,hba,hbS,hh⟩ := hdata w
    have hax := (mem_row R _ _).mp (mem_sdiff.mp hx).1
    have hbx : ¬ R w.val.2 q.1 := by simpa [mem_row] using (mem_sdiff.mp hx).2
    have hay : ¬ R a q.2 := hy'.2.2.2 a (mem_filter.mpr ⟨ha,ha1,ha2⟩) hba.symm
    have hl := cross_codegree_zero (x := q.1) (y := q.2) hf hba.symm hp
      ha1 ha2 hb1 hb2 hax hbx hy'.1 hay
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hl⟩,hax⟩
  have hXcard (w : P) : ((row R a).card-3)*(r-3) ≤ (X w).card := by
    obtain ⟨ha1,ha2,hb1,hb2,hp,hba,hbS,hh⟩ := hdata w
    have hI := intersection_le_three hf hba.symm hp hh ⟨ha1,ha2⟩ ⟨hb1,hb2⟩
    have h1 : (row R a).card-3 ≤ (row R a \ row R w.val.2).card := by
      rw [card_sdiff,inter_comm]
      exact Nat.sub_le_sub_left hI _
    have h2 : r-3 ≤ (privatePetal R S w.val.1 w.val.2).card :=
      (Nat.sub_le_sub_right (hmin _ hbS) 3).trans
        (privatePetal_card_lower hf S hp hh ⟨hb1,hb2⟩)
    simpa only [X,card_product] using Nat.mul_le_mul h1 h2
  let Inc : P → (B × B) → Prop := fun w q => q ∈ X w
  have habove (w : P) : (zeroAt R a).bipartiteAbove Inc w = X w := by
    ext q
    simp only [bipartiteAbove,mem_filter,Inc]
    exact and_iff_right_of_imp (fun h => hXsub w h)
  have hbelow (q : B × B) : ((univ : Finset P).bipartiteBelow Inc q).card ≤ 6 := by
    by_cases hay : R a q.2
    · have he : (univ : Finset P).bipartiteBelow Inc q = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro w hw
        have hy := (mem_privatePetal R S w.val.1 w.val.2 q.2).mp
          (mem_product.mp (mem_filter.mp hw).2).2
        obtain ⟨ha1,ha2,_,_,_,hba,_,_⟩ := hdata w
        exact hy.2.2.2 a (mem_filter.mpr ⟨ha,ha1,ha2⟩) hba.symm hay
      simp [he]
    · apply (card_le_card (show (univ : Finset P).bipartiteBelow Inc q ⊆
          univ.filter (fun w => q.2 ∈ privatePetal R S w.val.1 w.val.2) from ?_)).trans
        (private_multiplicity hf S a q.2 hay)
      intro w hw
      exact mem_filter.mpr ⟨mem_univ _,(mem_product.mp (mem_filter.mp hw).2).2⟩
  calc
    _ = ∑ _w : P, ((row R a).card-3)*(r-3) := by simp [P,Nat.mul_assoc]
    _ ≤ ∑ w : P, (X w).card := sum_le_sum (fun w _ => hXcard w)
    _ = ∑ w : P, ((zeroAt R a).bipartiteAbove Inc w).card := by simp only [habove]
    _ = ∑ q ∈ zeroAt R a, ((univ : Finset P).bipartiteBelow Inc q).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ ≤ ∑ _q ∈ zeroAt R a, 6 := sum_le_sum (fun q _ => hbelow q)
    _ = _ := by simp [Nat.mul_comm]

open scoped Classical in
/-- Summing the root packing bound costs only ONE column degree per
ordered zero pair, not its product with the other column degree. -/
theorem total_all_zero_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) (r D : ℕ)
    (hmin : ∀ b ∈ S, r ≤ (row R b).card)
    (hD : ∀ x, Nat.card {a // R a x} ≤ D) :
    (∑ a ∈ S, (witnesses R S a).card*((row R a).card-3)*(r-3)) ≤
      6*D*(zeroSet R).card := by
  classical
  have hs : (∑ a ∈ S, (zeroAt R a).card) ≤ D*(zeroSet R).card := by
    let Inc : A → (B × B) → Prop := fun a p => R a p.1
    have ha (a : A) : (zeroSet R).bipartiteAbove Inc a = zeroAt R a := rfl
    have hb (p : B × B) : (S.bipartiteBelow Inc p).card ≤ D := by
      have hsub : S.bipartiteBelow Inc p ⊆ (univ : Finset A).filter (fun a => R a p.1) := by
        intro a ha
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ha).2⟩
      apply (card_le_card hsub).trans
      simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using hD p.1
    calc
      _ = ∑ a ∈ S, ((zeroSet R).bipartiteAbove Inc a).card := by simp only [ha]
      _ = ∑ p ∈ zeroSet R, (S.bipartiteBelow Inc p).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
      _ ≤ ∑ _p ∈ zeroSet R, D := sum_le_sum (fun p _ => hb p)
      _ = _ := by simp [Nat.mul_comm]
  calc
    _ ≤ ∑ a ∈ S, 6*(zeroAt R a).card := sum_le_sum (fun a ha => root_all_zero_bound hf S r hmin a ha)
    _ = 6*(∑ a ∈ S, (zeroAt R a).card) := by rw [mul_sum]
    _ ≤ 6*(D*(zeroSet R).card) := Nat.mul_le_mul_left 6 hs
    _ = _ := by ring

#print axioms total_all_zero_bound
#print axioms cross_codegree_zero
#print axioms root_all_zero_bound
end Erdos713ThetaZeroPairs
