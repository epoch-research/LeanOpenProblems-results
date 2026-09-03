import Submission.InterceptOppositePruningExplore

/-! Elementary L1 costs of deleting weighted fibers and pointwise costs of
restoring finitely many points to an actual set. -/
namespace Erdos66FinitePruningError
open Erdos66CrossGraph Erdos66FiniteField Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def weightedFiber {α β : Type*} [DecidableEq β]
    (S : Finset α) (k : α → β) (w : α → ℤ) (b : β) : ℤ :=
  ∑ x∈S, if k x=b then w x else 0

lemma weightedFiber_l1 {α β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset α) (k : α → β) (w : α → ℤ) (hw : ∀x∈S, |w x|≤1) :
    (∑ b : β, |weightedFiber S k w b|) ≤ (S.card : ℤ) := by
  calc
    _ ≤ ∑ b : β, ∑ x∈S, |if k x=b then w x else 0| :=
      Finset.sum_le_sum (fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ x∈S, |w x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [apply_ite abs,abs_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    _ ≤ ∑ _x∈S, (1:ℤ) := Finset.sum_le_sum hw
    _ = _ := by simp

lemma weightedFiber_pruning {α β : Type*} [Fintype β] [DecidableEq β]
    (S T : Finset α) (hTS : T⊆S) (k : α → β) (w : α → ℤ)
    (hw : ∀x∈S, |w x|≤1) :
    (∑ b : β, |weightedFiber T k w b|) ≤
      (∑ b : β, |weightedFiber S k w b|)+(S.card-T.card : ℕ) := by
  have hpoint (b : β) : |weightedFiber T k w b| ≤
      |weightedFiber S k w b|+|weightedFiber (S\T) k w b| := by
    have he : weightedFiber (S\T) k w b+weightedFiber T k w b=weightedFiber S k w b :=
      Finset.sum_sdiff hTS
    have ht := abs_sub_le (weightedFiber T k w b) (weightedFiber S k w b) 0
    have hd : |weightedFiber T k w b-weightedFiber S k w b|=|weightedFiber (S\T) k w b| := by
      rw [abs_sub_comm]
      congr 1
      linarith only [he]
    rw [sub_zero,sub_zero,hd] at ht
    linarith only [ht]
  have hh := Finset.sum_le_sum (fun b (_ : b∈Finset.univ) ↦ hpoint b)
  rw [Finset.sum_add_distrib] at hh
  have hD := weightedFiber_l1 (S\T) k w (fun x hx ↦ hw x (Finset.mem_sdiff.mp hx).1)
  rw [Finset.card_sdiff_of_subset hTS] at hD
  linarith

lemma crossCharFiber_pruning {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (U V : Finset F) (hVU : V⊆U) :
    (∑s : F, |crossCharFiber V V s|) ≤
      (∑s : F, |crossCharFiber U U s|)+(U.card^2-V.card^2 : ℕ) := by
  have hsub : V×ˢV ⊆ U×ˢU := by
    intro x hx
    obtain ⟨hx1,hx2⟩ := Finset.mem_product.mp hx
    exact Finset.mem_product.mpr ⟨hVU hx1,hVU hx2⟩
  have hh := weightedFiber_pruning (U×ˢU) (V×ˢV) hsub
    (fun e ↦ e.1+e.2) (fun e ↦ quadraticChar F e.1*quadraticChar F e.2) (by
      intro e he
      rw [abs_mul]
      nlinarith [quadraticChar_abs_le_one e.1,quadraticChar_abs_le_one e.2,
        abs_nonneg (quadraticChar F e.1),abs_nonneg (quadraticChar F e.2)])
  simpa only [weightedFiber,Finset.sum_product,crossCharFiber,Finset.card_product,pow_two] using hh

lemma square_card_loss {α : Type*} (U V : Finset α) (hVU : V⊆U) (r : ℕ)
    (hloss : U.card ≤ V.card+r) : U.card^2-V.card^2 ≤ 2*U.card*r := by
  have hc := Finset.card_le_card hVU
  have hp : V.card^2 ≤ U.card^2 := Nat.pow_le_pow_left hc 2
  have he : U.card^2-V.card^2+V.card^2=U.card^2 := Nat.sub_add_cancel hp
  have hm : U.card*(U.card-V.card) ≤ U.card*r := Nat.mul_le_mul_left _ (by omega)
  have he' : U.card-V.card+V.card=U.card := Nat.sub_add_cancel hc
  nlinarith

lemma pairCount_union_small {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A E : Finset G) (z : G) :
    pairCount A A z ≤ pairCount (A∪E) (A∪E) z ∧
      pairCount (A∪E) (A∪E) z ≤ pairCount A A z+2*E.card := by
  constructor
  · apply Finset.card_le_card
    intro x hx
    obtain ⟨hx,hzx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hx,Finset.mem_union_left _ hzx⟩
  · have hs : (A∪E).filter (fun x ↦ z-x∈A∪E) ⊆
        (A.filter (fun x ↦ z-x∈A))∪E∪E.image (fun x ↦ z-x) := by
      intro x hx
      obtain ⟨hx,hzx⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hzx with hzx | hzx
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,hzx⟩))
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z-x,hzx,sub_sub_cancel z x⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
    have hc' := Finset.card_union_le (A.filter (fun x ↦ z-x∈A)) E
    have hi := @Finset.card_image_le _ _ E (fun x ↦ z-x) _
    unfold pairCount
    omega

lemma pairCount_union_abs_error {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A E : Finset G) (z : G) :
    |(pairCount (A∪E) (A∪E) z : ℝ)-pairCount A A z| ≤ 2*E.card := by
  obtain ⟨hlo,hhi⟩ := pairCount_union_small A E z
  have hl : (pairCount A A z : ℝ) ≤ pairCount (A∪E) (A∪E) z := by exact_mod_cast hlo
  have hh : (pairCount (A∪E) (A∪E) z : ℝ) ≤ pairCount A A z+2*E.card := by exact_mod_cast hhi
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  linarith

end Erdos66FinitePruningError
