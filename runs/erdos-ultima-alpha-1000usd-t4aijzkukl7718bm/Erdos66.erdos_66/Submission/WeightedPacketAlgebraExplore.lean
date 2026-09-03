import Submission.NaturalLabeledPacketsExplore

/-! Weighted aggregate decomposition for labelled repair packets. Unintended
coarse edges are charged their actual weights, bounded uniformly by two. -/
namespace Erdos66WeightedPacketAlgebra
open Erdos66MultiPacket Erdos66MultiPacketSelection Erdos66NatPairAlgebra
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def fiberSum (D E : Finset ℕ) (w : ℕ → ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ i∈D, ∑ j∈E, if i+j=q then w i j else 0

lemma fiberSum_nonneg (D E : Finset ℕ) (w : ℕ → ℕ → ℝ) (q : ℕ)
    (hw : ∀ i∈D, ∀ j∈E, 0 ≤ w i j) : 0 ≤ fiberSum D E w q := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact hw i hi j hj
  · rfl

lemma fiberSum_bound (D E : Finset ℕ) (w : ℕ → ℕ → ℝ) (q : ℕ) (B : ℝ)
    (hw : ∀ i∈D, ∀ j∈E, w i j ≤ B) :
    fiberSum D E w q ≤ B*(pairs D E q : ℝ) := by
  have he : B*(pairs D E q : ℝ)=∑ i∈D, ∑ j∈E, if i+j=q then B else 0 := by
    simp only [pairs,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
      Finset.product_eq_sprod,Finset.sum_product,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [he]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · exact hw i hi j hj
  · rfl

lemma fiberSum_comm (D E : Finset ℕ) (w : ℕ → ℕ → ℝ) (hw : ∀ i j, w i j=w j i) (q : ℕ) :
    fiberSum D E w q=fiberSum E D w q := by
  unfold fiberSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.add_comm i j,hw i j]

lemma fiberSum_union_self (D E : Finset ℕ) (hDE : Disjoint D E)
    (w : ℕ → ℕ → ℝ) (hw : ∀ i j, w i j=w j i) (q : ℕ) :
    fiberSum (D∪E) (D∪E) w q=fiberSum D D w q+2*fiberSum E D w q+fiberSum E E w q := by
  have hmix := fiberSum_comm D E w hw q
  unfold fiberSum at hmix ⊢
  simp_rw [Finset.sum_union hDE,Finset.sum_add_distrib]
  linarith

lemma fiberSum_of_support (D S : Finset ℕ) (hDS : D ⊆ S) (w : ℕ → ℕ → ℝ)
    (hleft : ∀ i, i∉D → ∀ j, w i j=0) (hright : ∀ j, j∉D → ∀ i, w i j=0) (q : ℕ) :
    fiberSum S S w q=fiberSum D D w q := by
  unfold fiberSum
  calc
    _ = ∑ i∈D, ∑ j∈S, if i+j=q then w i j else 0 := by
      symm
      apply Finset.sum_subset hDS
      intro i hi hiD
      apply Finset.sum_eq_zero
      intro j hj
      simp [hleft i hiD j]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      apply Finset.sum_subset hDS
      intro j hj hjD
      simp [hright j hjD i]

lemma fiberSum_zero_of_pairs_zero (D E : Finset ℕ) (w : ℕ → ℕ → ℝ) (q : ℕ)
    (hz : pairs D E q=0) : fiberSum D E w q=0 := by
  simp only [pairs,Finset.card_eq_zero,Finset.filter_eq_empty_iff] at hz
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have hh : i+j≠q := @hz (i,j) (Finset.mem_product.mpr ⟨hi,hj⟩)
  simp [hh]

section Labels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def labelPairs (d : Label ι → ℕ) (q : ℕ) : Finset (Label ι × Label ι) :=
  Finset.univ.filter (fun p ↦ d p.1+d p.2=q)

lemma fiberSum_image (d : Label ι → ℕ) (hd : Function.Injective d) (w : ℕ → ℕ → ℝ) (q : ℕ) :
    fiberSum (Finset.univ.image d) (Finset.univ.image d) w q=
      ∑ p∈labelPairs d q, w (d p.1) (d p.2) := by
  unfold fiberSum labelPairs
  simp_rw [Finset.sum_image (fun a _ b _ he ↦ hd he)]
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]

lemma off_labelPairs_card (d : Label ι → ℕ) (q : ℕ)
    (hunique : ∀ u v w s : Label ι, ¬Designated u v → ¬Designated w s →
      d u+d v=d w+d s → (u=w ∧ v=s) ∨ (u=s ∧ v=w)) :
    ((labelPairs d q).filter (fun p ↦ ¬Designated p.1 p.2)).card ≤ 2 := by
  let Q := (labelPairs d q).filter (fun p ↦ ¬Designated p.1 p.2)
  by_cases hQ : Q.Nonempty
  · obtain ⟨p,hp⟩ := hQ
    have hp' := Finset.mem_filter.mp hp
    have hps := (Finset.mem_filter.mp hp'.1).2
    have hsub : Q ⊆ {p,(p.2,p.1)} := by
      intro r hr
      obtain ⟨hr,hrn⟩ := Finset.mem_filter.mp hr
      have hrs := (Finset.mem_filter.mp hr).2
      rcases hunique r.1 r.2 p.1 p.2 hrn hp'.2 (hrs.trans hps.symm) with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact Finset.mem_insert.mpr (Or.inl (Prod.ext h₁ h₂))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Prod.ext h₁ h₂)))
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp only [Finset.not_nonempty_iff_eq_empty] at hQ
    change Q.card ≤ 2
    rw [hQ]
    simp

lemma label_designated_sum (d : Label ι → ℕ) (n : ι → ℕ)
    (hcenter : ∀ i, d (i,false)+d (i,true)=n i)
    (w : Label ι → Label ι → ℝ) (q : ℕ) :
    (∑ p∈(labelPairs d q).filter (fun p ↦ Designated p.1 p.2), w p.1 p.2) =
      ∑ i, if n i=q then w (i,false) (i,true)+w (i,true) (i,false) else 0 := by
  have hdes (u v : Label ι) (h : Designated u v) : d u+d v=n u.1 := by
    obtain ⟨i,b⟩ := u
    obtain ⟨j,c⟩ := v
    obtain ⟨he,hbc⟩ := h
    dsimp at he
    subst j
    cases b <;> cases c <;> simp_all [Nat.add_comm]
  let S := (Finset.univ.filter (fun i ↦ n i=q)) ×ˢ (Finset.univ : Finset Bool)
  have he : (∑ p∈S, w p (p.1,!p.2))=
      ∑ p∈(labelPairs d q).filter (fun p ↦ Designated p.1 p.2), w p.1 p.2 := by
    apply Finset.sum_bij (fun p _ ↦ (p,(p.1,!p.2)))
    · intro p hp
      have hn := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
      have hd : Designated p (p.1,!p.2) := by cases hb : p.2 <;> simp [Designated,hb]
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hdes _ _ hd).trans hn⟩,hd⟩
    · intro p hp r hr he
      exact congrArg Prod.fst he
    · intro p hp
      obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hp
      have hn := (hdes p.1 p.2 hd).symm.trans (Finset.mem_filter.mp hp).2
      refine ⟨p.1,Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,Finset.mem_univ _⟩,?_⟩
      obtain ⟨⟨i,b⟩,⟨j,c⟩⟩ := p
      change i=j ∧ b≠c at hd
      obtain ⟨rfl,hbc⟩ := hd
      cases b <;> cases c <;> simp_all
    · intro p hp
      rfl
  rw [←he]
  simp [S,Finset.sum_product,Finset.sum_filter,Fintype.sum_bool,add_comm]

/-- Weighted unintended new/new edges have total mass at most four. -/
theorem weighted_packet_error (d : Label ι → ℕ) (hd : Function.Injective d)
    (n : ι → ℕ) (hcenter : ∀ i, d (i,false)+d (i,true)=n i)
    (hunique : ∀ u v w s : Label ι, ¬Designated u v → ¬Designated w s →
      d u+d v=d w+d s → (u=w ∧ v=s) ∨ (u=s ∧ v=w))
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w (d u) (d v) ∧ w (d u) (d v) ≤ 2) (q : ℕ) :
    0 ≤ fiberSum (Finset.univ.image d) (Finset.univ.image d) w q-
      (∑ i, if n i=q then w (d (i,false)) (d (i,true))+w (d (i,true)) (d (i,false)) else 0) ∧
    fiberSum (Finset.univ.image d) (Finset.univ.image d) w q-
      (∑ i, if n i=q then w (d (i,false)) (d (i,true))+w (d (i,true)) (d (i,false)) else 0) ≤ 4 := by
  rw [fiberSum_image d hd]
  have hs := Finset.sum_filter_add_sum_filter_not (s := labelPairs d q)
    (p := fun p ↦ Designated p.1 p.2) (f := fun p ↦ w (d p.1) (d p.2))
  rw [label_designated_sum d n hcenter (fun u v ↦ w (d u) (d v)) q] at hs
  let Q := (labelPairs d q).filter (fun p ↦ ¬Designated p.1 p.2)
  have hnon : 0 ≤ ∑ p∈Q, w (d p.1) (d p.2) := Finset.sum_nonneg (fun p _ ↦ (hw p.1 p.2).1)
  have hle : (∑ p∈Q, w (d p.1) (d p.2)) ≤ 4 := by
    have hh := Finset.sum_le_sum (s := Q) (fun p _ ↦ (hw p.1 p.2).2)
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    have hc : (Q.card : ℝ) ≤ 2 := by exact_mod_cast off_labelPairs_card d q hunique
    linarith
  constructor <;> linarith

end Labels
end Erdos66WeightedPacketAlgebra
