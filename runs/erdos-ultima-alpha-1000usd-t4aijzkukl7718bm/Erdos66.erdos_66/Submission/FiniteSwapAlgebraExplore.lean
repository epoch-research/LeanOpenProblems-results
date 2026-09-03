import Submission.OrderedPartialReplacementExplore
import Submission.NatPairAlgebraExplore
import Submission.NaturalSidonExtractionExplore
import Submission.SidonSelectionExplore

/-! Finite natural-number swaps: exact target accounting and collateral bounds. -/
namespace Erdos66FiniteSwapAlgebra
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66NaturalSidonExtraction
  Erdos66OrderedPartialReplacement Erdos66UniformSelection Erdos66Explore
open scoped Classical
set_option maxHeartbeats 2000000

lemma pairs_mono_right {A B C : Finset ℕ} (h : B ⊆ C) (n : ℕ) :
    pairs A B n ≤ pairs A C n := by
  rw [pairs_eq_filter,pairs_eq_filter]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨ha,han,hb⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨ha,han,h hb⟩

lemma pairs_mono_left {A B C : Finset ℕ} (h : A ⊆ B) (n : ℕ) :
    pairs A C n ≤ pairs B C n := by
  rw [pairs_comm A,pairs_comm B]
  exact pairs_mono_right h n

lemma pairs_eq_zero_of_no_partner (A B : Finset ℕ) (n : ℕ)
    (h : ∀ a ∈ A, a ≤ n → n-a ∉ B) : pairs A B n=0 := by
  rw [pairs_eq_filter,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro a ha hb
  exact h a ha hb.1 hb.2

lemma pairs_eq_card_of_partner (A B : Finset ℕ) (n : ℕ)
    (h : ∀ a ∈ A, a ≤ n ∧ n-a ∈ B) : pairs A B n=A.card := by
  rw [pairs_eq_filter,Finset.filter_eq_self.mpr h]

lemma pairs_above_half (A B : Finset ℕ) (n : ℕ)
    (hA : ∀ a ∈ A, n<2*a) (hB : ∀ b ∈ B, n<2*b) : pairs A B n=0 := by
  apply pairs_eq_zero_of_no_partner
  intro a ha han hb
  have h1 := hA a ha
  have h2 := hB (n-a) hb
  omega

noncomputable def swapped (A D F : Finset ℕ) : Finset ℕ := (A \ D) ∪ F

lemma swapped_coe (A D F : Finset ℕ) :
    (swapped A D F : Set ℕ)=swap (A : Set ℕ) D F := by
  ext a
  simp [swapped,swap]

lemma swapped_card (A D F : Finset ℕ) (hD : D ⊆ A) (hF : Disjoint A F)
    (hc : D.card=F.card) : (swapped A D F).card=A.card := by
  rw [swapped,Finset.card_union_of_disjoint (hF.mono_left Finset.sdiff_subset)]
  have hh := Finset.card_sdiff_add_card_eq_card hD
  omega

lemma sumRep_swapped_upper (A D F : Finset ℕ) (hF : Disjoint A F) (n : ℕ) :
    sumRep (swapped A D F : Set ℕ) n ≤
      sumRep (A : Set ℕ) n+2*pairs F A n+sumRep (F : Set ℕ) n := by
  have hrep := sumRep_mono (show ((A \ D : Finset ℕ) : Set ℕ) ⊆ (A : Set ℕ) from
    fun a ha ↦ (Finset.mem_sdiff.mp ha).1) n
  have hm := pairs_mono_right (show A \ D ⊆ A from Finset.sdiff_subset) (A := F) n
  rw [swapped,sumRep_union_self _ _ _ (hF.mono_left Finset.sdiff_subset),pairs_comm (A \ D) F]
  omega

lemma sumRep_swapped_lower (A D F : Finset ℕ) (hD : D ⊆ A) (n : ℕ) :
    sumRep (A : Set ℕ) n ≤ sumRep (swapped A D F : Set ℕ) n+2*pairs D A n := by
  have hs := sumRep_union_self (A \ D) D n Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset hD] at hs
  have hd := pairs_union_right D (A \ D) D n Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset hD,pairs_comm D (A \ D),pairs_self] at hd
  have hm := sumRep_mono (show ((A \ D : Finset ℕ) : Set ℕ) ⊆ (swapped A D F : Set ℕ) from
    fun a ha ↦ Finset.mem_union_left _ ha) n
  omega

lemma swapped_target_exact (A D F : Finset ℕ) (hD : D ⊆ A) (hF : Disjoint A F) (n : ℕ)
    (hDA : pairs D A n=0) (hFA : pairs F A n=F.card)
    (hFD : pairs F D n=0) (hFF : sumRep (F : Set ℕ) n=0) :
    sumRep (swapped A D F : Set ℕ) n=sumRep (A : Set ℕ) n+2*F.card := by
  have hdd := pairs_mono_right hD (A := D) n
  rw [hDA,pairs_self] at hdd
  have hdc := pairs_mono_right (show A \ D ⊆ A from Finset.sdiff_subset) (A := D) n
  rw [hDA,pairs_comm D (A \ D)] at hdc
  have hs := sumRep_union_self (A \ D) D n Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset hD] at hs
  have hf := pairs_union_right F (A \ D) D n Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset hD,hFA,hFD,pairs_comm F (A \ D)] at hf
  rw [swapped,sumRep_union_self _ _ _ (hF.mono_left Finset.sdiff_subset),hFF]
  omega

lemma image_pairs_hits {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (x : α → ℕ) (hx : Function.Injective x) (ω : ι → α) (hω : Function.Injective ω)
    (A : Finset ℕ) (n : ℕ) :
    (pairs (Finset.univ.image (fun i ↦ x (ω i))) A n : ℝ)=
      hits (Finset.univ.filter (fun i ↦ x i ≤ n ∧ n-x i ∈ A)) ω := by
  have hinj : Function.Injective (fun i ↦ x (ω i)) := hx.comp hω
  rw [pairs_eq_filter,Finset.filter_image,Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    hits,Finset.mem_filter,Finset.mem_univ,true_and]

end Erdos66FiniteSwapAlgebra
