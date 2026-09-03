import Submission.FractionalSaturation

/-! Transport of finite weighted cycle families and exact removal of a
unit-weight cycle. These operations do not provide an integral rounding rule. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalCycles
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

noncomputable def pushWeight {I : Type*} [Fintype I] {G : SimpleGraph V}
    (C : I → CyclePiece G) (a : I → ℝ) (H : CyclePiece G) : ℝ :=
  ∑ i, if C i = H then a i else 0

lemma pushWeight_sum {I : Type*} [Fintype I] {G : SimpleGraph V}
    (C : I → CyclePiece G) (a : I → ℝ) : ∑ H, pushWeight C a H = ∑ i, a i := by
  simp only [pushWeight]
  rw [Finset.sum_comm]
  simp

lemma pushWeight_nonneg {I : Type*} [Fintype I] {G : SimpleGraph V}
    (C : I → CyclePiece G) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) (H : CyclePiece G) :
    0 ≤ pushWeight C a H := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact ha i
  · exact le_rfl

lemma pushWeight_coverage {I : Type*} [Fintype I] {G : SimpleGraph V}
    (C : I → CyclePiece G) (a : I → ℝ) (e : Sym2 V) :
    (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then pushWeight C a H else 0) =
      ∑ i, if e ∈ (C i).val.edgeSet then a i else 0 := by
  have hh : (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then pushWeight C a H else 0) =
      ∑ H : CyclePiece G, ∑ i, if C i = H then (if e ∈ (C i).val.edgeSet then a i else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro H _
    dsimp only [pushWeight]
    by_cases he : e ∈ H.val.edgeSet
    · rw [if_pos he]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : C i = H
      · simp [h,he]
      · simp [h]
    · rw [if_neg he]
      symm
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : C i = H
      · simp [h,he]
      · simp [h]
  rw [hh,Finset.sum_comm]
  simp

lemma fractional_of_family {I : Type*} [Fintype I] (G : SimpleGraph V)
    (C : I → CyclePiece G) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (he : ∀ e ∈ G.edgeSet, (∑ i, if e ∈ (C i).val.edgeSet then a i else 0) = 1) :
    IsFractionalPartition G (pushWeight C a) :=
  ⟨pushWeight_nonneg C a ha,fun e he' => (pushWeight_coverage C a e).trans (he e he')⟩

lemma coverage_all {G : SimpleGraph V} {t : CyclePiece G → ℝ}
    (ht : IsFractionalPartition G t) (e : Sym2 V) :
    (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then t H else 0) =
      if e ∈ G.edgeSet then 1 else 0 := by
  by_cases he : e ∈ G.edgeSet
  · simp only [if_pos he]
    exact ht.2 e he
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro H _
    exact if_neg (fun heH => he (H.val.edgeSet_subset heH))

def promoteCycle {G A : SimpleGraph V} (h : A ≤ G) (H : CyclePiece A) : CyclePiece G :=
  ⟨promote h H.val, H.property.1, by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using H.property.2 v⟩

@[simp] lemma promoteCycle_edges {G A : SimpleGraph V} (h : A ≤ G) (H : CyclePiece A) :
    (promoteCycle h H).val.edgeSet = H.val.edgeSet := rfl

lemma sum_subtype_indicator {I : Type*} [Fintype I] (p : I → Prop) (f : I → ℝ) :
    (∑ i : {i // p i}, f i.val) = ∑ i, if p i then f i else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm


end Erdos184.FractionalCycles
