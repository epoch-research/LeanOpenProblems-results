import FormalConjecturesUtil
import Submission.ThetaRowTruncation

/-! A light-pair budget for arbitrary incidence deletions. -/
open Finset
open scoped Classical
namespace Erdos713IncidencePruningBudget
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaCross Erdos713ThetaOverlap Erdos713ThetaRowTruncation
variable {A B : Type*}
set_option maxHeartbeats 1000000

noncomputable def pairLoss [Fintype B] (R Q : A → B → Prop) (a : A) : Finset (B × B) :=
  (row R a ×ˢ row R a) \ (row Q a ×ˢ row Q a)

/-- Every newly light pair lost at least one supporting row. -/
theorem light_le_of_pair_loss [Fintype A] [Fintype B] (R Q : A → B → Prop) :
    lightCount Q ≤ lightCount R + ∑ a : A, (pairLoss R Q a).card := by
  have hsub : lightSet Q ⊆ lightSet R ∪ univ.biUnion (pairLoss R Q) := by
    intro p hp
    by_cases hl : codegree R p.1 p.2 ≤ 2
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hl⟩)
    · apply mem_union_right
      by_contra hn
      have h (a : A) (ha : R a p.1 ∧ R a p.2) : Q a p.1 ∧ Q a p.2 := by
        by_contra hq
        apply hn
        refine mem_biUnion.mpr ⟨a,mem_univ _,?_⟩
        simpa only [pairLoss,mem_sdiff,mem_product,mem_row] using And.intro ha hq
      let f : {a // R a p.1 ∧ R a p.2} → {a // Q a p.1 ∧ Q a p.2} :=
        fun a => ⟨a.val,h a.val a.property⟩
      have hc : codegree R p.1 p.2 ≤ codegree Q p.1 p.2 :=
        Nat.card_le_card_of_injective f (fun a b he => Subtype.ext
          (congrArg (fun u : {a // Q a p.1 ∧ Q a p.2} => u.val) he))
      exact hl (hc.trans (mem_filter.mp hp).2)
  rw [← lightSet_card,← lightSet_card R]
  calc
    _ ≤ (lightSet R ∪ univ.biUnion (pairLoss R Q)).card := card_le_card hsub
    _ ≤ (lightSet R).card + (univ.biUnion (pairLoss R Q)).card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left card_biUnion_le _

lemma pairLoss_card [Fintype B] {R Q : A → B → Prop}
    (hsub : ∀ a b, Q a b → R a b) (a : A) :
    (pairLoss R Q a).card = (row R a).card^2-(row Q a).card^2 := by
  have hs : row Q a ⊆ row R a := fun b hb => (mem_row R a b).mpr
    (hsub a b ((mem_row Q a b).mp hb))
  rw [pairLoss,card_sdiff_of_subset (product_subset_product hs hs),card_product,card_product]
  simp only [pow_two]

lemma no_theta_of_subrelation {R Q : A → B → Prop}
    (hf : ¬ HasTheta R) (hsub : ∀ a b, Q a b → R a b) : ¬ HasTheta Q := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  exact hf ⟨a,b,ha,hb,hsub _ _ h00,hsub _ _ h10,hsub _ _ h01,hsub _ _ h11,
    hsub _ _ h02,hsub _ _ h22,hsub _ _ h13,hsub _ _ h23⟩

#print axioms light_le_of_pair_loss
#print axioms pairLoss_card
#print axioms no_theta_of_subrelation
end Erdos713IncidencePruningBudget
