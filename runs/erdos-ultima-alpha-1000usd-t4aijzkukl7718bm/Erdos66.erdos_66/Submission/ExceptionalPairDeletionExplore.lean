import Submission.NatPairAlgebraExplore

/-! Removing every point incident to a forbidden sum kills those sums. The
collateral loss at other targets is controlled by triple intersections,
not by the total number of removed points. -/
namespace Erdos66ExceptionalPairDeletion
open AdditiveCombinatorics Erdos66NatPairAlgebra
open scoped Classical
set_option maxHeartbeats 1700000

noncomputable def removed (D T : Finset ℕ) : Finset ℕ :=
  D.filter (fun a ↦ ∃ b∈D, a+b∈T)

noncomputable def kept (D T : Finset ℕ) : Finset ℕ := D\removed D T

noncomputable def tripleFiber (D : Finset ℕ) (b q : ℕ) : Finset ℕ :=
  D.filter (fun a ↦ a ≤ b ∧ a ≤ q ∧ b-a∈D ∧ q-a∈D)

noncomputable def codegree (D : Finset ℕ) (b q : ℕ) : ℕ := (tripleFiber D b q).card

lemma removed_subset (D T : Finset ℕ) : removed D T ⊆ D := Finset.filter_subset _ _

lemma kept_subset (D T : Finset ℕ) : kept D T ⊆ D := Finset.sdiff_subset

lemma kept_union_removed (D T : Finset ℕ) : kept D T ∪ removed D T=D :=
  Finset.sdiff_union_of_subset (removed_subset D T)

lemma kept_disjoint_removed (D T : Finset ℕ) : Disjoint (kept D T) (removed D T) :=
  Finset.sdiff_disjoint

/-- All representations at an exceptional center disappear, including its
diagonal representation. -/
theorem kept_rep_zero (D T : Finset ℕ) (q : ℕ) (hq : q∈T) :
    sumRep (kept D T : Set ℕ) q=0 := by
  rw [←pairs_self,pairs,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro p hp he
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
  have haD := kept_subset D T ha
  have hbD := kept_subset D T hb
  have haR : p.1∈removed D T := Finset.mem_filter.mpr ⟨haD,p.2,hbD,he ▸ hq⟩
  exact (Finset.mem_sdiff.mp ha).2 haR

lemma removed_mixed_le_codegrees (D T : Finset ℕ) (q : ℕ) :
    pairs (removed D T) D q ≤ ∑ b∈T, codegree D b q := by
  rw [pairs_eq_filter]
  have hs : ((removed D T).filter (fun a ↦ a ≤ q ∧ q-a∈D)) ⊆
      T.biUnion (fun b ↦ tripleFiber D b q) := by
    intro a ha
    obtain ⟨ha,hqa,hqD⟩ := Finset.mem_filter.mp ha
    obtain ⟨haD,b,hbD,hab⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_biUnion.mpr
    refine ⟨a+b,hab,?_⟩
    exact Finset.mem_filter.mpr ⟨haD,by omega,hqa,by simpa using hbD,hqD⟩
  exact (Finset.card_le_card hs).trans (Finset.card_biUnion_le)

/-- Deleting both endpoints of every forbidden pair costs at most two
triple intersections per exceptional target at any other target. -/
theorem representation_loss_le_codegrees (D T : Finset ℕ) (q : ℕ) :
    sumRep (D : Set ℕ) q-sumRep (kept D T : Set ℕ) q ≤
      2*∑ b∈T, codegree D b q := by
  have hd := kept_disjoint_removed D T
  have hu := sumRep_union_self (kept D T) (removed D T) q hd
  rw [kept_union_removed] at hu
  have hm := pairs_union_right (removed D T) (kept D T) (removed D T) q hd
  rw [kept_union_removed,pairs_comm (removed D T) (kept D T),pairs_self] at hm
  have hb := removed_mixed_le_codegrees D T q
  omega

/-- A uniform off-diagonal codegree bound makes the collateral depend on
|T|, not on the much larger number of points incident to T. -/
theorem representation_loss_le (D T : Finset ℕ) (R q : ℕ) (hq : q∉T)
    (hR : ∀ b∈T, b≠q → codegree D b q ≤ R) :
    sumRep (D : Set ℕ) q-sumRep (kept D T : Set ℕ) q ≤ 2*T.card*R := by
  have hs : (∑ b∈T, codegree D b q) ≤ T.card*R := by
    calc
      _ ≤ ∑ _b∈T, R := Finset.sum_le_sum (fun b hb ↦ hR b hb (fun he ↦ hq (he ▸ hb)))
      _ = _ := by simp
  have hh := representation_loss_le_codegrees D T q
  nlinarith

lemma codegree_symm (D : Finset ℕ) (b q : ℕ) : codegree D b q=codegree D q b := by
  unfold codegree tripleFiber
  congr 1
  ext a
  simp only [Finset.mem_filter]
  tauto

lemma codegree_zero_above_support (D : Finset ℕ) (L b q : ℕ)
    (hD : D ⊆ Finset.range (L+1)) (hq : 2*L < q) : codegree D b q=0 := by
  rw [codegree,Finset.card_eq_zero,tripleFiber,Finset.filter_eq_empty_iff]
  intro a ha he
  have h₁ := Finset.mem_range.mp (hD ha)
  have h₂ := Finset.mem_range.mp (hD he.2.2.2)
  omega

lemma codegrees_extend (D : Finset ℕ) (L R : ℕ) (hD : D ⊆ Finset.range (L+1))
    (hR : ∀ b ≤ 2*L, ∀ q ≤ 2*L, b≠q → codegree D b q ≤ R) :
    ∀ b q, b≠q → codegree D b q ≤ R := by
  intro b q hbq
  by_cases hq : q ≤ 2*L
  · by_cases hb : b ≤ 2*L
    · exact hR b hb q hq hbq
    · rw [codegree_symm,codegree_zero_above_support D L q b hD (by omega)]
      omega
  · rw [codegree_zero_above_support D L b q hD (by omega)]
    omega

end Erdos66ExceptionalPairDeletion
