import Submission.AdaptivePacketChoiceExplore

/-! Insertion loads for one replacement point per prescribed rank cell. -/
namespace Erdos66AdaptiveSingletonAlgebra
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66AdaptivePacketAlgebra Erdos66AdaptivePacketChoice
open scoped Classical
set_option maxHeartbeats 2200000
variable {α : Type*} [Fintype α]

noncomputable def partnerChoices (A : Finset ℕ) (f : α → ℕ) (z : ℕ) : Finset α :=
  Finset.univ.filter (fun a ↦ f a ≤ z ∧ z-f a∈A)

noncomputable def insertionHits (A F : Finset ℕ) (f : α → ℕ) (z : ℕ) : Finset α :=
  partnerChoices A f z ∪ partnerChoices F f z ∪ Finset.univ.filter (fun a ↦ 2*f a=z)

noncomputable def insertionChoices (A : Finset ℕ) (f : α → ℕ) (n : ℕ) : Finset α :=
  Finset.univ \ ((Finset.univ.filter (fun a ↦ f a∈A)) ∪ partnerChoices A f n)

noncomputable def insertionEnergy (A F : Finset ℕ) (z : ℕ) : ℝ :=
  2*pairs F A z+sumRep (F : Set ℕ) z

lemma singleton_pairs (u z : ℕ) (A : Finset ℕ) :
    pairs {u} A z=if u ≤ z ∧ z-u∈A then 1 else 0 := by
  rw [pairs_eq_filter,Finset.filter_singleton]
  split_ifs <;> simp_all

lemma insertionEnergy_step (A F : Finset ℕ) (f : α → ℕ) (a : α) (hu : f a∉F) (z : ℕ) :
    insertionEnergy A (insert (f a) F) z-insertionEnergy A F z ≤
      5*(if a∈insertionHits A F f z then (1 : ℝ) else 0) := by
  have hd : Disjoint ({f a} : Finset ℕ) F := by simpa using hu
  have he : ({f a} : Finset ℕ)∪F=insert (f a) F := by simp
  have hload : insertionEnergy A (insert (f a) F) z-insertionEnergy A F z =
      2*(if f a ≤ z ∧ z-f a∈A then (1 : ℝ) else 0)+
      2*(if f a ≤ z ∧ z-f a∈F then (1 : ℝ) else 0)+
      (if 2*f a=z then (1 : ℝ) else 0) := by
    rw [insertionEnergy,insertionEnergy,←he,pairs_union_left _ _ _ _ hd,
      sumRep_union_self _ _ _ hd,singleton_pairs,singleton_pairs]
    simp only [Finset.coe_singleton,singleton_rep]
    push_cast
    ring
  rw [hload]
  by_cases ha : a∈insertionHits A F f z
  · rw [if_pos ha]
    split_ifs <;> norm_num
  · have hn : ¬(f a ≤ z ∧ z-f a∈A) ∧ ¬(f a ≤ z ∧ z-f a∈F) ∧ 2*f a≠z := by
      simpa only [insertionHits,partnerChoices,Finset.mem_union,Finset.mem_filter,
        Finset.mem_univ,true_and,not_or,and_assoc] using ha
    simp [ha,hn.1,hn.2.1,hn.2.2]

lemma insertionHits_card (A F : Finset ℕ) (f : α → ℕ) (hf : Function.Injective f)
    (z : ℕ) (K : ℝ) (hK : ((partnerChoices A f z).card : ℝ) ≤ K) :
    ((insertionHits A F f z).card : ℝ) ≤ K+F.card+1 := by
  have hF : ((partnerChoices F f z).card : ℝ) ≤ F.card := by
    exact_mod_cast injective_partner_card F f hf z
  have hd : ((Finset.univ.filter (fun a ↦ 2*f a=z)).card : ℝ) ≤ 1 := by
    exact_mod_cast injective_double_card f hf z
  have hu : ((insertionHits A F f z).card : ℝ) ≤
      (partnerChoices A f z).card+(partnerChoices F f z).card+
        (Finset.univ.filter (fun a ↦ 2*f a=z)).card := by
    have h1 := Finset.card_union_le (partnerChoices A f z ∪ partnerChoices F f z)
      (Finset.univ.filter (fun a ↦ 2*f a=z))
    have h2 := Finset.card_union_le (partnerChoices A f z) (partnerChoices F f z)
    exact_mod_cast h1.trans (Nat.add_le_add_right h2 _)
  linarith

lemma insertionChoices_card (A : Finset ℕ) (f : α → ℕ) (n : ℕ) (B₀ B₁ q : ℝ)
    (h₀ : ((Finset.univ.filter (fun a ↦ f a∈A)).card : ℝ) ≤ B₀)
    (h₁ : ((partnerChoices A f n).card : ℝ) ≤ B₁)
    (hbudget : q+B₀+B₁ ≤ Fintype.card α) :
    q ≤ (insertionChoices A f n).card := by
  have hu : (((Finset.univ.filter (fun a ↦ f a∈A)) ∪ partnerChoices A f n).card : ℝ) ≤
      (Finset.univ.filter (fun a ↦ f a∈A)).card+(partnerChoices A f n).card := by
    exact_mod_cast Finset.card_union_le _ _
  have he := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ ((Finset.univ.filter (fun a ↦ f a∈A)) ∪ partnerChoices A f n))
  have he' : ((insertionChoices A f n).card : ℝ)+
      (((Finset.univ.filter (fun a ↦ f a∈A)) ∪ partnerChoices A f n).card : ℝ)=Fintype.card α := by
    exact_mod_cast he
  linarith

lemma insertionChoices_properties (A : Finset ℕ) (f : α → ℕ) (n : ℕ) (a : α)
    (ha : a∈insertionChoices A f n) : f a∉A ∧ pairs {f a} A n=0 := by
  have hh := Finset.notMem_union.mp (Finset.mem_sdiff.mp ha).2
  have h0 : f a∉A := fun he ↦ hh.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  have h1 : ¬(f a ≤ n ∧ n-f a∈A) := fun he ↦ hh.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  exact ⟨h0,by rw [singleton_pairs,if_neg h1]⟩

end Erdos66AdaptiveSingletonAlgebra
