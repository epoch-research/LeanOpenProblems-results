import Submission.GreedyBatchSharedWitnesses
import Submission.GreedyBatchSharedLoss

/-! Actual shared-link update for the conservative mixed batch. Every new
link is charged to the correct one- or two-mark original-edge witness. -/
namespace Erdos773.GreedyBatchSharedStep
open Finset GreedyBatchState RegularizationSharedLinks GreedyBatchSharedWitnesses
set_option maxHeartbeats 3000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma data_of_residuals {H : Finset (Finset α)} {R A e f : Finset α} {x y : α}
    (hxy : x≠y) (hA : A.card=2) (hxA : x∉A) (hyA : y∉A)
    (hxR : x∉R) (hyR : y∉R) (he : e∈H) (hf : f∈H)
    (heq : e \ R=insert x A) (hfq : f \ R=insert y A) :
    Data H x y e.card f.card e A f ∧ witness x y (⟨e,A,f⟩:Index α)⊆R := by
  have hxe : x∈e := (mem_sdiff.mp (heq.symm ▸ mem_insert_self x A)).1
  have hyf : y∈f := (mem_sdiff.mp (hfq.symm ▸ mem_insert_self y A)).1
  have hye : y∉e := by
    intro hy
    have hh : y∈insert x A := heq ▸ mem_sdiff.mpr ⟨hy,hyR⟩
    exact (mem_insert.mp hh).elim hxy.symm hyA
  have hxf : x∉f := by
    intro hx
    have hh : x∈insert y A := hfq ▸ mem_sdiff.mpr ⟨hx,hxR⟩
    exact (mem_insert.mp hh).elim hxy hxA
  have hAe : A⊆e := fun a ha => (mem_sdiff.mp (heq.symm ▸ mem_insert_of_mem ha)).1
  have hAf : A⊆f := fun a ha => (mem_sdiff.mp (hfq.symm ▸ mem_insert_of_mem ha)).1
  refine ⟨⟨he,hf,rfl,rfl,hxe,hyf,hye,hxf,hA,hAe,hAf,hxA,hyA⟩,?_⟩
  intro a ha
  by_contra haR
  rcases mem_union.mp ha with ha | ha
  · exact (mem_sdiff.mp ha).2 (heq ▸ mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,haR⟩)
  · exact (mem_sdiff.mp ha).2 (hfq ▸ mem_sdiff.mpr ⟨(mem_sdiff.mp ha).1,haR⟩)

lemma next_link_sources (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x y : α) (hxy : x≠y)
    (A : Finset α) (hA : A∈links (next H R) x y) :
    ∃ e f, (3≤e.card ∧ e.card≤4) ∧ (3≤f.card ∧ f.card≤4) ∧
      Data H x y e.card f.card e A f ∧
      witness x y (⟨e,A,f⟩:Index α)⊆R ∧ A⊆carrier H R := by
  obtain ⟨hAc,hxA,hyA,hx,hy⟩ := mem_links.mp hA
  have hxQ := next_subset hx (mem_insert_self _ _)
  have hyQ := next_subset hy (mem_insert_self _ _)
  have hAQ : A⊆carrier H R := (subset_insert _ _).trans (next_subset hx)
  obtain ⟨e,he,heq⟩ := mem_image.mp hx
  obtain ⟨f,hf,hfq⟩ := mem_image.mp hy
  have heH := (mem_filter.mp he).1
  have hfH := (mem_filter.mp hf).1
  have he3 : 3≤e.card := by
    have hh := card_le_card (sdiff_subset : e \ R⊆e)
    rw [heq,card_insert_of_notMem hxA,hAc] at hh
    exact hh
  have hf3 : 3≤f.card := by
    have hh := card_le_card (sdiff_subset : f \ R⊆f)
    rw [hfq,card_insert_of_notMem hyA,hAc] at hh
    exact hh
  obtain ⟨hd,hw⟩ := data_of_residuals hxy hAc hxA hyA
    (mem_carrier.mp hxQ).1 (mem_carrier.mp hyQ).1 heH hfH heq hfq
  exact ⟨e,f,⟨he3,hH e heH⟩,⟨hf3,hH f hfH⟩,hd,hw,hAQ⟩

def created (H : Finset (Finset α)) (x y : α) (r s : ℕ) (R : Finset α) : Finset (Finset α) :=
  ((family H x y r s).filter (fun i => witness x y i⊆R)).image (fun i => i.2.1)

lemma created_card (H : Finset (Finset α)) (x y : α) (r s : ℕ) (R : Finset α) :
    (created H x y r s R).card≤cost H x y r s R := card_image_le

lemma old_of_three {H : Finset (Finset α)} {x y : α} {e A f : Finset α}
    (h : Data H x y 3 3 e A f) : A∈links H x y := by
  have he : insert x A=e := eq_of_subset_of_card_le (insert_subset h.x_mem h.A_e)
    (by rw [card_insert_of_notMem h.x_A,h.A_card,h.e_card])
  have hf : insert y A=f := eq_of_subset_of_card_le (insert_subset h.y_mem h.A_f)
    (by rw [card_insert_of_notMem h.y_A,h.A_card,h.f_card])
  exact mem_links.mpr ⟨h.A_card,h.x_A,h.y_A,he.symm ▸ h.e_mem,hf.symm ▸ h.f_mem⟩

lemma next_link_cover (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x y : α) (hxy : x≠y) :
    links (next H R) x y⊆
      (((links H x y).filter (fun A => A⊆carrier H R)∪created H x y 3 4 R)∪created H x y 4 3 R)∪
        created H x y 4 4 R := by
  intro A hA
  obtain ⟨e,f,he,hf,hd,hw,hAQ⟩ := next_link_sources H R hH x y hxy A hA
  have her : e.card=3 ∨ e.card=4 := by omega
  have hfr : f.card=3 ∨ f.card=4 := by omega
  rcases her with her | her <;> rcases hfr with hfr | hfr
  · have hd' : Data H x y 3 3 e A f := by simpa only [her,hfr] using hd
    exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨old_of_three hd',hAQ⟩)))
  · have hd' : Data H x y 3 4 e A f := by simpa only [her,hfr] using hd
    exact mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_image.mpr ⟨⟨e,A,f⟩,mem_filter.mpr ⟨mem_of_data hd',hw⟩,rfl⟩)))
  · have hd' : Data H x y 4 3 e A f := by simpa only [her,hfr] using hd
    exact mem_union_left _ (mem_union_right _
      (mem_image.mpr ⟨⟨e,A,f⟩,mem_filter.mpr ⟨mem_of_data hd',hw⟩,rfl⟩))
  · have hd' : Data H x y 4 4 e A f := by simpa only [her,hfr] using hd
    exact mem_union_right _ (mem_image.mpr ⟨⟨e,A,f⟩,mem_filter.mpr ⟨mem_of_data hd',hw⟩,rfl⟩)

/-- Full shared-link update: an old-link survivor term, two one-mark
creation terms, and one two-mark creation term. -/
theorem shared_step (H : Finset (Finset α)) (R : Finset α)
    (hH : ∀ e∈H, e.card≤4) (x y : α) (hxy : x≠y) :
    count (next H R) x y≤GreedyBatchSharedLoss.oldCount H x y R+
      cost H x y 3 4 R+cost H y x 3 4 R+cost H x y 4 4 R := by
  have h0 := card_le_card (next_link_cover H R hH x y hxy)
  have h1 := card_union_le
    (((links H x y).filter (fun A => A⊆carrier H R)∪created H x y 3 4 R)∪created H x y 4 3 R)
    (created H x y 4 4 R)
  have h2 := card_union_le
    ((links H x y).filter (fun A => A⊆carrier H R)∪created H x y 3 4 R)
    (created H x y 4 3 R)
  have h3 := card_union_le ((links H x y).filter (fun A => A⊆carrier H R)) (created H x y 3 4 R)
  have hc1 := created_card H x y 3 4 R
  have hc2 := created_card H x y 4 3 R
  have hc3 := created_card H x y 4 4 R
  rw [cost_swap H x y 4 3 R] at hc2
  unfold count GreedyBatchSharedLoss.oldCount
  omega

#print axioms data_of_residuals
#print axioms next_link_sources
#print axioms next_link_cover
#print axioms shared_step
end
end Erdos773.GreedyBatchSharedStep
