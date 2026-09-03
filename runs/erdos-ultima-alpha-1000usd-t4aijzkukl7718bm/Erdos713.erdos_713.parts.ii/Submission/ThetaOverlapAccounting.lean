import FormalConjecturesUtil
import Submission.ThetaHeavyShadow
import Submission.ThetaCrossCompletion

/-! Exact accounting for large row overlaps in a theta-free relation.
This does not assert the pending capped weighted theta estimate. -/
open Finset
namespace Erdos713ThetaOverlap
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow Erdos713ThetaCross
variable {A B : Type*}
set_option maxHeartbeats 2000000

lemma third_common_of_codegree [Fintype A] {R : A → B → Prop}
    {x y : B} (hc : 3 ≤ codegree R x y) (a b : A) :
    ∃ c : A, c ≠ a ∧ c ≠ b ∧ R c x ∧ R c y := by
  classical
  let S := (univ : Finset A).filter (fun c => R c x ∧ R c y)
  have hS : 3 ≤ S.card := by
    simpa only [S,codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hc
  obtain ⟨c,hcS,hcab⟩ := exists_mem_notMem_of_card_lt_card
    (show ({a,b} : Finset A).card < S.card from card_le_two.trans_lt (by omega))
  simp only [mem_insert,mem_singleton,not_or] at hcab
  exact ⟨c,hcab.1,hcab.2,(mem_filter.mp hcS).2⟩

open scoped Classical in
/-- If two rows share at least four columns, every distinct cross pair
of their neighborhoods is light: two unused common columns complete theta. -/
lemma large_overlap_cross_light [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) {a b : A} (hab : a ≠ b)
    (hlarge : 4 ≤ (row R a ∩ row R b).card)
    {x y : B} (hxy : x ≠ y)
    (hax : R a x) (hby : R b y) :
    codegree R x y ≤ 2 := by
  classical
  by_contra h
  obtain ⟨c,hca,hcb,hcx,hcy⟩ := third_common_of_codegree (R := R) (x := x) (y := y) (by omega) a b
  obtain ⟨z,hz,hzxy⟩ := exists_mem_notMem_of_card_lt_card
    (show ({x,y} : Finset B).card < (row R a ∩ row R b).card from
      card_le_two.trans_lt (by omega))
  have h3 : ({x,y,z} : Finset B).card ≤ 3 := by
    simpa using List.toFinset_card_le ([x,y,z] : List B)
  obtain ⟨w,hw,hwxyz⟩ := exists_mem_notMem_of_card_lt_card (h3.trans_lt (by omega :
    3 < (row R a ∩ row R b).card))
  simp only [mem_insert,mem_singleton,not_or] at hzxy hwxyz
  have haz : R a z := (mem_row R a z).mp (mem_inter.mp hz).1
  have hbz : R b z := (mem_row R b z).mp (mem_inter.mp hz).2
  have haw : R a w := (mem_row R a w).mp (mem_inter.mp hw).1
  have hbw : R b w := (mem_row R b w).mp (mem_inter.mp hw).2
  let f : Fin 3 → A := ![a,b,c]
  let g : Fin 4 → B := ![z,w,x,y]
  have hfi : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hgi : Function.Injective g := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [g]
  exact hf ⟨f,g,hfi,hgi,haz,hbz,haw,hbw,hax,hcx,hby,hcy⟩

open scoped Classical in
noncomputable def largeRowPairs [Fintype A] [Fintype B] (R : A → B → Prop) : Finset (A × A) :=
  univ.filter (fun p => p.1 ≠ p.2 ∧ 4 ≤ (row R p.1 ∩ row R p.2).card)

open scoped Classical in
noncomputable def lightSet [Fintype B] (R : A → B → Prop) : Finset (B × B) :=
  univ.filter (fun p => codegree R p.1 p.2 ≤ 2)

lemma lightSet_card [Fintype B] (R : A → B → Prop) : (lightSet R).card = lightCount R := by
  classical
  simp only [lightSet,lightCount,Nat.card_eq_fintype_card,Fintype.card_subtype]

open scoped Classical in
/-- Ordered row pairs contribute twice. A light column pair has at most
two common rows, hence can receive at most two ordered charges. -/
theorem sum_large_overlaps [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) :
    (∑ p ∈ largeRowPairs R, (row R p.1 ∩ row R p.2).offDiag.card) ≤ 2*lightCount R := by
  classical
  let Inc : (A × A) → (B × B) → Prop := fun p q =>
    R p.1 q.1 ∧ R p.1 q.2 ∧ R p.2 q.1 ∧ R p.2 q.2 ∧ q.1 ≠ q.2
  have habove (p : A × A) (hp : p ∈ largeRowPairs R) :
      (lightSet R).bipartiteAbove Inc p = (row R p.1 ∩ row R p.2).offDiag := by
    have hp' : p.1 ≠ p.2 ∧ 4 ≤ (row R p.1 ∩ row R p.2).card := (mem_filter.mp hp).2
    ext q
    simp only [bipartiteAbove,mem_filter,lightSet,mem_univ,true_and,Inc,mem_offDiag,
      mem_inter,mem_row]
    constructor
    · rintro ⟨_,h1,h2,h3,h4,hne⟩
      exact ⟨⟨h1,h3⟩,⟨h2,h4⟩,hne⟩
    · rintro ⟨⟨h1,h3⟩,⟨h2,h4⟩,hne⟩
      exact ⟨large_overlap_cross_light hf hp'.1 hp'.2 hne h1 h4,h1,h2,h3,h4,hne⟩
  have hbelow (q : B × B) (hq : q ∈ lightSet R) :
      ((largeRowPairs R).bipartiteBelow Inc q).card ≤ 2 := by
    let S := (univ : Finset A).filter (fun a => R a q.1 ∧ R a q.2)
    have hcard : S.card ≤ 2 := by
      have hh : codegree R q.1 q.2 ≤ 2 := (mem_filter.mp hq).2
      simpa only [S,codegree,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
    have hsub : (largeRowPairs R).bipartiteBelow Inc q ⊆ S.offDiag := by
      intro p hp
      obtain ⟨hp,hInc⟩ := mem_filter.mp hp
      have hne : p.1 ≠ p.2 := (mem_filter.mp hp).2.1
      exact mem_offDiag.mpr ⟨by simp [S,hInc.1,hInc.2.1],
        by simp [S,hInc.2.2.1,hInc.2.2.2.1],hne⟩
    apply (card_le_card hsub).trans
    rw [offDiag_card]
    interval_cases h : S.card <;> simp
  calc
    _ = ∑ p ∈ largeRowPairs R, ((lightSet R).bipartiteAbove Inc p).card := by
      apply sum_congr rfl
      intro p hp
      rw [habove p hp]
    _ = ∑ q ∈ lightSet R, ((largeRowPairs R).bipartiteBelow Inc q).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Inc
    _ ≤ ∑ _q ∈ lightSet R, 2 := sum_le_sum (fun q hq => hbelow q hq)
    _ = 2*lightCount R := by simp [lightSet_card,Nat.mul_comm]

open scoped Classical in
theorem sum_large_overlap_products [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) :
    (∑ p ∈ largeRowPairs R,
      (row R p.1 ∩ row R p.2).card*((row R p.1 ∩ row R p.2).card-1)) ≤ 2*lightCount R := by
  have h := sum_large_overlaps hf
  simpa only [offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_one] using h

/-- In particular, even the number of ordered large-overlap row pairs is
controlled by the global light-pair count. Small overlaps are not included. -/
theorem large_row_pairs_card [Fintype A] [Fintype B] {R : A → B → Prop}
    (hf : ¬ HasTheta R) : 6*(largeRowPairs R).card ≤ lightCount R := by
  classical
  have hlo : 12*(largeRowPairs R).card ≤
      ∑ p ∈ largeRowPairs R,
        (row R p.1 ∩ row R p.2).card*((row R p.1 ∩ row R p.2).card-1) := by
    calc
      _ = ∑ _p ∈ largeRowPairs R, 12 := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro p hp
        have h : 4 ≤ (row R p.1 ∩ row R p.2).card := (mem_filter.mp hp).2.2
        have h1 : 3 ≤ (row R p.1 ∩ row R p.2).card-1 := by omega
        exact show 4*3 ≤ _ from Nat.mul_le_mul h h1
  have hh := hlo.trans (sum_large_overlap_products hf)
  omega

#print axioms large_overlap_cross_light
#print axioms sum_large_overlaps
#print axioms sum_large_overlap_products
#print axioms large_row_pairs_card
end Erdos713ThetaOverlap
