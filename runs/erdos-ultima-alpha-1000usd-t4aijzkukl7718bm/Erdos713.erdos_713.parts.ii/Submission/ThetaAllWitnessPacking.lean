import FormalConjecturesUtil
import Submission.ThetaPrivatePetals

/-! Packing all retained witnesses, rather than one per heavy anchor. -/
open Finset
namespace Erdos713ThetaAllWitnessPacking
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaAnchorPacking
open Erdos713ThetaCrossAccounting Erdos713ThetaPrivatePetals
variable {A B : Type*}
set_option maxHeartbeats 2000000

open scoped Classical in
noncomputable def witnesses [Fintype B] (R : A → B → Prop)
    (S : Finset A) (a : A) : Finset ((B × B) × A) :=
  (anchors R S a).biUnion (fun p => {p} ×ˢ (commonRows R S p).erase a)

open scoped Classical in
lemma mem_witnesses [Fintype B] (R : A → B → Prop)
    (S : Finset A) (a : A) (w : (B × B) × A) :
    w ∈ witnesses R S a ↔
      w.1 ∈ anchors R S a ∧ w.2 ∈ commonRows R S w.1 ∧ w.2 ≠ a := by
  classical
  simp only [witnesses,mem_biUnion,mem_product,mem_singleton,mem_erase]
  constructor
  · rintro ⟨p,hp,he,hne,hb⟩
    subst p
    exact ⟨hp,hb,hne⟩
  · rintro ⟨hp,hb,hne⟩
    exact ⟨w.1,hp,rfl,hne,hb⟩

open scoped Classical in
lemma witnesses_card [Fintype B] (R : A → B → Prop)
    (S : Finset A) (a : A) (ha : a ∈ S) :
    (witnesses R S a).card = ∑ p ∈ anchors R S a, ((commonRows R S p).card-1) := by
  classical
  rw [witnesses,card_biUnion]
  · apply sum_congr rfl
    intro p hp
    have hp' := mem_offDiag.mp (mem_filter.mp hp).1
    have ham : a ∈ commonRows R S p := mem_filter.mpr ⟨ha,
      (mem_row R _ _).mp hp'.1,(mem_row R _ _).mp hp'.2.1⟩
    simp only [card_product,card_singleton,one_mul,card_erase_of_mem ham]
  · intro p hp q hq hpq
    apply disjoint_left.mpr
    rintro w hw hw'
    have he : w.1 = p := by simpa using (mem_product.mp hw).1
    have he' : w.1 = q := by simpa using (mem_product.mp hw').1
    exact hpq (he.symm.trans he')

open scoped Classical in
/-- Across all witnesses and all anchors, a private outside column has
multiplicity at most six at a fixed root. -/
theorem private_multiplicity [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) (a : A) (y : B) (hay : ¬ R a y) :
    ((univ : Finset ↥(witnesses R S a)).filter (fun w =>
      y ∈ privatePetal R S w.val.1 w.val.2)).card ≤ 6 := by
  classical
  let T := (univ : Finset ↥(witnesses R S a)).filter (fun w =>
    y ∈ privatePetal R S w.val.1 w.val.2)
  by_cases hT : T.Nonempty
  · obtain ⟨w₀,hw₀⟩ := hT
    have h₀ := (mem_witnesses R S a w₀.val).mp w₀.property
    have hp₀ := mem_offDiag.mp (mem_filter.mp h₀.1).1
    have hb₀ := (mem_filter.mp h₀.2.1).2
    have hy₀ := (mem_privatePetal R S w₀.val.1 w₀.val.2 y).mp (mem_filter.mp hw₀).2
    let I := row R a ∩ row R w₀.val.2
    have hI : I.card ≤ 3 := intersection_le_three hf h₀.2.2.symm hp₀.2.2
      (anchor_heavy h₀.1) ⟨(mem_row R _ _).mp hp₀.1,(mem_row R _ _).mp hp₀.2.1⟩ hb₀
    have heq (w : ↥(witnesses R S a)) (hw : w ∈ T) : w.val.2 = w₀.val.2 := by
      have h := (mem_witnesses R S a w.val).mp w.property
      have hp := mem_offDiag.mp (mem_filter.mp h.1).1
      have hb := (mem_filter.mp h.2.1).2
      have hy := (mem_privatePetal R S w.val.1 w.val.2 y).mp (mem_filter.mp hw).2
      by_contra hne
      have hx1 := other_witness_endpoint hf h₀.2.2.symm h.2.2 hne hp₀.2.2
        ((mem_row R _ _).mp hp₀.1) ((mem_row R _ _).mp hp₀.2.1)
        hb₀.1 hb₀.2 ((mem_row R _ _).mp hp.1) hb.1 hy₀.1 hy.1 hay
      have hx2 := other_witness_endpoint hf h₀.2.2.symm h.2.2 hne hp₀.2.2
        ((mem_row R _ _).mp hp₀.1) ((mem_row R _ _).mp hp₀.2.1)
        hb₀.1 hb₀.2 ((mem_row R _ _).mp hp.2.1) hb.2 hy₀.1 hy.1 hay
      have hc : w₀.val.2 ∈ commonRows R S w.val.1 := by
        refine mem_filter.mpr ⟨(mem_filter.mp h₀.2.1).1,?_,?_⟩
        · rcases hx1 with he | he <;> simpa only [he] using (by first | exact hb₀.1 | exact hb₀.2)
        · rcases hx2 with he | he <;> simpa only [he] using (by first | exact hb₀.1 | exact hb₀.2)
      exact hy.2.2.2 _ hc (Ne.symm hne) hy₀.1
    have hsub : ∀ w ∈ T, w.val.1 ∈ I.offDiag := by
      intro w hw
      have h := (mem_witnesses R S a w.val).mp w.property
      have hp := mem_offDiag.mp (mem_filter.mp h.1).1
      have hb := (mem_filter.mp h.2.1).2
      rw [heq w hw] at hb
      exact mem_offDiag.mpr ⟨mem_inter.mpr ⟨hp.1,(mem_row R _ _).mpr hb.1⟩,
        mem_inter.mpr ⟨hp.2.1,(mem_row R _ _).mpr hb.2⟩,hp.2.2⟩
    have hc : T.card ≤ I.offDiag.card := card_le_card_of_injOn (fun w => w.val.1) hsub (by
      intro w hw v hv h
      apply Subtype.ext
      exact Prod.ext h ((heq w hw).trans (heq v hv).symm))
    have hi : I.offDiag.card ≤ 6 := by
      rw [offDiag_card]
      interval_cases h : I.card <;> simp
    exact hc.trans hi
  · have he : T = ∅ := not_nonempty_iff_eq_empty.mp hT
    change T.card ≤ 6
    simp [he]

open scoped Classical in
theorem root_all_bound [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) (S : Finset A) (r : ℕ)
    (hmin : ∀ b ∈ S, r ≤ (row R b).card) (a : A) (ha : a ∈ S) :
    (witnesses R S a).card*((row R a).card-3)*(r-3) ≤ 6*(lightAt R a).card := by
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
  have hXsub (w : P) : X w ⊆ lightAt R a := by
    intro q hq
    obtain ⟨hx,hy⟩ := mem_product.mp hq
    have hy' := (mem_privatePetal R S w.val.1 w.val.2 q.2).mp hy
    obtain ⟨ha1,ha2,hb1,hb2,hp,hba,hbS,hh⟩ := hdata w
    have hax := (mem_row R _ _).mp (mem_sdiff.mp hx).1
    have hbx : ¬ R w.val.2 q.1 := by simpa [mem_row] using (mem_sdiff.mp hx).2
    have hay : ¬ R a q.2 := hy'.2.2.2 a (mem_filter.mpr ⟨ha,ha1,ha2⟩) hba.symm
    have hl := cross_light_of_two_common (x := q.1) (y := q.2) hf hba.symm hp
      (fun h => hbx (h ▸ hb1)) (fun h => hbx (h ▸ hb2)) hy'.2.1 hy'.2.2.1
      (fun h => hay (h ▸ hax)) ha1 ha2 hb1 hb2 hax hy'.1
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
  have habove (w : P) : (lightAt R a).bipartiteAbove Inc w = X w := by
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
    _ = ∑ w : P, ((lightAt R a).bipartiteAbove Inc w).card := by simp only [habove]
    _ = ∑ q ∈ lightAt R a, ((univ : Finset P).bipartiteBelow Inc q).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ ≤ ∑ _q ∈ lightAt R a, 6 := sum_le_sum (fun q _ => hbelow q)
    _ = _ := by simp [Nat.mul_comm]

#print axioms witnesses_card
#print axioms private_multiplicity
#print axioms root_all_bound
end Erdos713ThetaAllWitnessPacking
