import Submission.SquareCollisionCodegrees

/-!
In a progression-free set of square values, distinct four-root collision
supports intersect in at most two roots. This is a structural input to
selection, not a bound for the maximum Sidon subset.
-/
namespace Erdos773.SquareCollisionIntersections
open Finset SquareCollisionCodegrees
set_option maxHeartbeats 1000000

lemma distinct_of_card_four {a b c d : ℕ} (h : ({a,b,c,d} : Finset ℕ).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [card_insert_eq_ite, card_singleton, mem_insert, mem_singleton] at h
  split_ifs at h <;> simp_all

lemma sum_four_squares {a b c d : ℕ} (h : ({a,b,c,d} : Finset ℕ).card = 4) :
    (∑ n ∈ ({a,b,c,d} : Finset ℕ), n^2) = a^2+b^2+c^2+d^2 := by
  obtain ⟨hab,hac,had,hbc,hbd,hcd⟩ := distinct_of_card_four h
  simp [hab,hac,had,hbc,hbd,hcd,add_assoc]

lemma partner {e : Finset ℕ} (he4 : e.card = 4) {a : ℕ} (ha : a ∈ e)
    (he : ∃ u v w x : ℕ, e = {u,v,w,x} ∧ u^2+v^2=w^2+x^2) :
    ∃ t ∈ e, t ≠ a ∧ (∑ n ∈ e, n^2) = 2*(a^2+t^2) := by
  obtain ⟨u,v,w,x,rfl,hs⟩ := he
  obtain ⟨huv,huw,hux,hvw,hvx,hwx⟩ := distinct_of_card_four he4
  rw [sum_four_squares he4]
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact ⟨v,by simp,huv.symm,by omega⟩
  · exact ⟨u,by simp,huv,by omega⟩
  · exact ⟨x,by simp,hwx.symm,by omega⟩
  · exact ⟨w,by simp,hwx,by omega⟩

/-- The three possible pair partitions of a four-root support. -/
lemma partitions {A : Finset ℕ} {a b c d : ℕ}
    (he : ({a,b,c,d} : Finset ℕ) ∈ edges A) :
    a^2+b^2=c^2+d^2 ∨ a^2+c^2=b^2+d^2 ∨ a^2+d^2=b^2+c^2 := by
  classical
  obtain ⟨_,h4,hbal⟩ := mem_filter.mp he
  obtain ⟨t,ht,hne,hs⟩ := partner h4 (by simp : a ∈ ({a,b,c,d} : Finset ℕ)) hbal
  rw [sum_four_squares h4] at hs
  simp only [mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact (hne rfl).elim
  · omega
  · omega
  · omega

lemma fourth_eq {A : Finset ℕ}
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ))
    {a b c d t : ℕ}
    (he : ({a,b,c,d} : Finset ℕ) ∈ edges A)
    (hf : ({a,b,c,t} : Finset ℕ) ∈ edges A) : d = t := by
  classical
  have heA := mem_powerset.mp (mem_filter.mp he).1
  have hfA := mem_powerset.mp (mem_filter.mp hf).1
  have ha : a^2 ∈ A.image (fun n : ℕ => n^2) := mem_image.mpr ⟨a,heA (by simp),rfl⟩
  have hb : b^2 ∈ A.image (fun n : ℕ => n^2) := mem_image.mpr ⟨b,heA (by simp),rfl⟩
  have hc : c^2 ∈ A.image (fun n : ℕ => n^2) := mem_image.mpr ⟨c,heA (by simp),rfl⟩
  have hd : d^2 ∈ A.image (fun n : ℕ => n^2) := mem_image.mpr ⟨d,heA (by simp),rfl⟩
  have ht : t^2 ∈ A.image (fun n : ℕ => n^2) := mem_image.mpr ⟨t,hfA (by simp),rfl⟩
  have hs : d^2 = t^2 := by
    rcases partitions he with he | he | he <;>
      rcases partitions hf with hf | hf | hf
    all_goals first
    | omega
    | have hh := hAP hd ha ht (by omega); omega
    | have hh := hAP hd hb ht (by omega); omega
    | have hh := hAP hd hc ht (by omega); omega
  exact Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0) hs

lemma complete_triple {e : Finset ℕ} (he : e.card = 4)
    {a b c : ℕ} (hT : ({a,b,c} : Finset ℕ) ⊆ e)
    (hTc : ({a,b,c} : Finset ℕ).card = 3) :
    ∃ d : ℕ, e = {a,b,c,d} := by
  have hdiff : (e \ {a,b,c}).card = 1 := by rw [card_sdiff_of_subset hT,he,hTc]
  obtain ⟨d,hd⟩ := card_eq_one.mp hdiff
  refine ⟨d,?_⟩
  calc
    e = {a,b,c} ∪ (e \ {a,b,c}) := (union_sdiff_of_subset hT).symm
    _ = {a,b,c,d} := by rw [hd]; ext z; simp only [mem_union,mem_insert,mem_singleton]; tauto

/-- In an AP-free square-value family, three common roots force equality
of the two four-root collision supports. -/
theorem eq_of_three_common {A e f : Finset ℕ}
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ))
    (he : e ∈ edges A) (hf : f ∈ edges A) (hcommon : 3 ≤ (e ∩ f).card) : e = f := by
  classical
  obtain ⟨T,hT,hTc⟩ := exists_subset_card_eq hcommon
  obtain ⟨a,b,c,hab,hac,hbc,hTrep⟩ := card_eq_three.mp hTc
  subst T
  have hTe : ({a,b,c} : Finset ℕ) ⊆ e := hT.trans inter_subset_left
  have hTf : ({a,b,c} : Finset ℕ) ⊆ f := hT.trans inter_subset_right
  obtain ⟨d,rfl⟩ := complete_triple (mem_filter.mp he).2.1 hTe hTc
  obtain ⟨t,rfl⟩ := complete_triple (mem_filter.mp hf).2.1 hTf hTc
  rw [fourth_eq hAP he hf]

/-- The exact intersection bound needed before linearizing the hypergraph. -/
theorem intersection_card_le_two {A e f : Finset ℕ}
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ))
    (he : e ∈ edges A) (hf : f ∈ edges A) (hne : e ≠ f) : (e ∩ f).card ≤ 2 := by
  by_contra! hh
  exact hne (eq_of_three_common hAP he hf hh)

#print axioms partitions
#print axioms fourth_eq
#print axioms eq_of_three_common
#print axioms intersection_card_le_two
end Erdos773.SquareCollisionIntersections
