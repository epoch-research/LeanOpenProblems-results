import Submission.FiniteRepairExplore

/-! Exact count-preserving finite swaps and their signed collateral budget. -/
namespace Erdos66IntegerFiniteSwapAlgebra
open Erdos66OriginRepair Erdos66FiniteRepair Erdos66SymmetricSidon
open scoped Classical
set_option maxHeartbeats 1400000

noncomputable def swap (A D F : Finset ℤ) : Finset ℤ := (A \ D) ∪ F

lemma pairCount_mono_right (S A B : Finset ℤ) (h : A ⊆ B) (z : ℤ) :
    pairCount S A z ≤ pairCount S B z := by
  apply Finset.card_le_card
  intro a ha
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,h (Finset.mem_filter.mp ha).2⟩

lemma swap_card (A D F : Finset ℤ) (hD : D ⊆ A) (hF : Disjoint A F)
    (hcard : D.card=F.card) : (swap A D F).card=A.card := by
  rw [swap,Finset.card_union_of_disjoint (Finset.disjoint_of_subset_left Finset.sdiff_subset hF)]
  have hh := Finset.card_sdiff_add_card_eq_card hD
  omega

lemma upper_self_zero (F : Finset ℤ) (n : ℤ) (hF : ∀ a ∈ F, n<2*a) :
    pairCount F F n=0 := by
  rw [pairCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  intro a ha hb
  have hh := hF a ha
  have hh' := hF (n-a) hb
  omega

lemma deleted_center_zero (A D : Finset ℤ) (n : ℤ)
    (hD : ∀ a ∈ D, n-a ∉ A) : pairCount D A n=0 := by
  rw [pairCount,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  exact hD

lemma swap_center (A D F : Finset ℤ) (n : ℤ)
    (hD : D ⊆ A) (hF : Disjoint A F)
    (hdelete : ∀ a ∈ D, n-a ∉ A)
    (hinsert : ∀ a ∈ F, n-a ∈ A \ D)
    (hupper : ∀ a ∈ F, n<2*a) :
    pairCount (swap A D F) (swap A D F) n=pairCount A A n+2*F.card := by
  have hDA := deleted_center_zero A D n hdelete
  have hDC : pairCount D (A \ D) n=0 :=
    Nat.eq_zero_of_le_zero ((pairCount_mono_right D _ _ Finset.sdiff_subset n).trans_eq hDA)
  have hDD : pairCount D D n=0 :=
    Nat.eq_zero_of_le_zero ((pairCount_mono_right D _ _ hD n).trans_eq hDA)
  have hsplit := pairCount_union_self (A \ D) D n Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset hD,hDC,hDD] at hsplit
  have hFC : pairCount F (A \ D) n=F.card := by
    rw [pairCount,Finset.filter_eq_self.mpr hinsert]
  rw [swap,pairCount_union_self _ _ _
    (Finset.disjoint_of_subset_left Finset.sdiff_subset hF),hFC,upper_self_zero F n hupper]
  omega

/-- A deletion and insertion bound that retains all quadratic contributions.
Only the inserted self-count is charged separately. -/
theorem swap_error_bound (A D F : Finset ℤ) (hD : D ⊆ A) (hF : Disjoint A F) (z : ℤ) :
    |(pairCount (swap A D F) (swap A D F) z : ℝ)-pairCount A A z| ≤
      2*(pairCount D A z : ℝ)+2*(pairCount F A z : ℝ)+pairCount F F z := by
  have hsplit := pairCount_union_self (A \ D) D z Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset hD] at hsplit
  have hDA := pairCount_union_right D (A \ D) D z Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset hD] at hDA
  have hFC := pairCount_mono_right F (A \ D) A Finset.sdiff_subset z
  have hnew := pairCount_union_self (A \ D) F z
    (Finset.disjoint_of_subset_left Finset.sdiff_subset hF)
  change pairCount (swap A D F) (swap A D F) z=_ at hnew
  have hs : (pairCount A A z : ℝ)=(pairCount (A \ D) (A \ D) z : ℝ)+
      2*pairCount D (A \ D) z+pairCount D D z := by exact_mod_cast hsplit
  have hd : (pairCount D A z : ℝ)=(pairCount D (A \ D) z : ℝ)+pairCount D D z := by
    exact_mod_cast hDA
  have hn : (pairCount (swap A D F) (swap A D F) z : ℝ)=
      (pairCount (A \ D) (A \ D) z : ℝ)+2*pairCount F (A \ D) z+pairCount F F z := by
    exact_mod_cast hnew
  have hf : (pairCount F (A \ D) z : ℝ) ≤ pairCount F A z := by exact_mod_cast hFC
  rw [abs_le]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (pairCount D D z),
    Nat.cast_nonneg (α := ℝ) (pairCount D (A \ D) z),
    Nat.cast_nonneg (α := ℝ) (pairCount F (A \ D) z),
    Nat.cast_nonneg (α := ℝ) (pairCount F F z)]

end Erdos66IntegerFiniteSwapAlgebra
