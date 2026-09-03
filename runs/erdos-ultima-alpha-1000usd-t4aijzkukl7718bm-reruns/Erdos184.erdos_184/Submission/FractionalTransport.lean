import Submission.FractionalSaturation

/-! Transport of finite weighted cycle families and exact removal of a
unit-weight cycle. These operations do not provide an integral rounding rule. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalCycles
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

/-- Keep graph-indexed sums stable when the graph is instantiated by a
compound expression. -/
noncomputable def cyclePieceFintype (G : SimpleGraph V) : Fintype (CyclePiece G) := inferInstance
attribute [local instance] cyclePieceFintype


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

/-- Adjoin a cycle to an edge-disjoint residual graph. -/
lemma adjoin_disjoint_cycle (G A : SimpleGraph V) (hAG : A ≤ G)
    (H : CyclePiece G) (hdisj : Disjoint H.val.edgeSet A.edgeSet)
    (hcover : G.edgeSet = H.val.edgeSet ∪ A.edgeSet)
    (s : CyclePiece A → ℝ) (hs : IsFractionalPartition A s) :
    ∃ t : CyclePiece G → ℝ, IsFractionalPartition G t ∧
      (∑ J, t J) = 1 + ∑ J, s J ∧ t H = 1 := by
  let C : Option (CyclePiece A) → CyclePiece G :=
    fun i => i.elim H (promoteCycle hAG)
  let a : Option (CyclePiece A) → ℝ := fun i => i.elim 1 s
  have ha : ∀ i, 0 ≤ a i := by intro i; cases i <;> simp [a,hs.1]
  have hc : ∀ e ∈ G.edgeSet, (∑ i, if e ∈ (C i).val.edgeSet then a i else 0) = 1 := by
    intro e he
    rw [Fintype.sum_option]
    change (if e ∈ H.val.edgeSet then 1 else 0) +
      (∑ J : CyclePiece A, if e ∈ J.val.edgeSet then s J else 0) = 1
    rw [coverage_all hs e]
    rw [hcover] at he
    rcases he with he | he
    · have hn := Set.disjoint_left.mp hdisj he
      simp [he,hn]
    · have hn := Set.disjoint_right.mp hdisj he
      simp [he,hn]
  have ht := fractional_of_family G C a ha hc
  refine ⟨pushWeight C a,ht,?_,?_⟩
  · rw [pushWeight_sum,Fintype.sum_option]
    rfl
  · apply le_antisymm (coefficient_le_one G _ ht H)
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun i => if C i = H then a i else 0)
      (by intro i _; dsimp only; split_ifs; exact ha i; exact le_rfl) (Finset.mem_univ none)
    simpa only [C,a,Option.elim_none,if_true] using hh

/-- Restore one removed cycle with coefficient exactly one. -/
lemma extend_removed_cycle (G : SimpleGraph V) (H : CyclePiece G)
    (s : CyclePiece (G \ H.val.spanningCoe) → ℝ)
    (hs : IsFractionalPartition (G \ H.val.spanningCoe) s) :
    ∃ t : CyclePiece G → ℝ, IsFractionalPartition G t ∧
      (∑ J, t J) = 1 + ∑ J, s J ∧ t H = 1 := by
  apply adjoin_disjoint_cycle G (G \ H.val.spanningCoe) sdiff_le H _ _ s hs
  · rw [edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  · rw [edgeSet_sdiff]
    exact (Set.union_diff_cancel H.val.edgeSet_subset).symm

lemma positive_disjoint_from_unit (G : SimpleGraph V) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) (H : CyclePiece G) (hH : t H = 1)
    (K : CyclePiece G) (hne : K ≠ H) (hK : 0 < t K) :
    Disjoint K.val.edgeSet H.val.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e heK heH
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({K,H} : Finset (CyclePiece G)) ⊆ Finset.univ from Finset.subset_univ _)
    (f := fun J : CyclePiece G => if e ∈ J.val.edgeSet then t J else 0)
    (by intro J _ _; dsimp only; split_ifs; exact ht.1 J; exact le_rfl)
  rw [Finset.sum_pair hne,if_pos heK,if_pos heH,hH,ht.2 e (H.val.edgeSet_subset heH)] at hh
  linarith

lemma sum_subtype_indicator {I : Type*} [Fintype I] (p : I → Prop) [DecidablePred p] (f : I → ℝ) :
    (∑ i : {i // p i}, f i.val) = ∑ i, if p i then f i else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

/-- Conversely, a unit coefficient can be removed without disturbing any
other positive cycle, and its fractional cost is exactly one. -/
lemma remove_unit_cycle (G : SimpleGraph V) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) (H : CyclePiece G) (hH : t H = 1) :
    ∃ s : CyclePiece (G \ H.val.spanningCoe) → ℝ,
      IsFractionalPartition (G \ H.val.spanningCoe) s ∧ (∑ J, s J) + 1 = ∑ J, t J := by
  let p (K : CyclePiece G) := K ≠ H ∧ 0 < t K
  let I := {K : CyclePiece G // p K}
  let C : I → CyclePiece (G \ H.val.spanningCoe) := fun K =>
    ⟨{ verts := K.val.val.verts
       Adj := K.val.val.Adj
       adj_sub := by
         intro x y hxy
         refine ⟨K.val.val.adj_sub hxy,?_⟩
         intro hHxy
         exact Set.disjoint_left.mp
           (positive_disjoint_from_unit G t ht H hH K.val K.property.1 K.property.2)
           (show s(x,y) ∈ K.val.val.edgeSet from hxy) hHxy
       symm := K.val.val.symm
       edge_vert := K.val.val.edge_vert },
      K.val.property.1,by
        intro v
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using K.val.property.2 v⟩
  let a : I → ℝ := fun K => t K.val
  have ha : ∀ i, 0 ≤ a i := fun i => ht.1 i.val
  have hc : ∀ e ∈ (G \ H.val.spanningCoe).edgeSet,
      (∑ i, if e ∈ (C i).val.edgeSet then a i else 0) = 1 := by
    intro e he
    rw [edgeSet_sdiff] at he
    change e ∈ G.edgeSet \ H.val.edgeSet at he
    change (∑ i : I, if e ∈ i.val.val.edgeSet then t i.val else 0) = 1
    rw [sum_subtype_indicator p (fun K : CyclePiece G => if e ∈ K.val.edgeSet then t K else 0)]
    have heq : ∀ K : CyclePiece G,
        (if p K then (if e ∈ K.val.edgeSet then t K else 0) else 0) =
          if e ∈ K.val.edgeSet then t K else 0 := by
      intro K
      by_cases hKH : K = H
      · subst K; simp [he.2]
      · by_cases hpos : 0 < t K
        · simp [p,hKH,hpos]
        · have hz : t K = 0 := le_antisymm (by linarith) (ht.1 K)
          simp [hz]
    simp_rw [heq]
    exact ht.2 e he.1
  have hs := fractional_of_family (G \ H.val.spanningCoe) C a ha hc
  refine ⟨pushWeight C a,hs,?_⟩
  rw [pushWeight_sum]
  change (∑ i : I, t i.val) + 1 = ∑ J, t J
  rw [sum_subtype_indicator p t]
  have hpoint : ∀ K : CyclePiece G,
      (if p K then t K else 0) + (if K = H then (1 : ℝ) else 0) = t K := by
    intro K
    by_cases hKH : K = H
    · subst K; simp [p,hH]
    · by_cases hpos : 0 < t K
      · simp [p,hKH,hpos]
      · have hz : t K = 0 := le_antisymm (by linarith) (ht.1 K)
        simp [hz,hKH]
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun K _ => hpoint K)
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh

lemma unit_extension_iff_residual_bound (G : SimpleGraph V) (H : CyclePiece G) (B : ℝ) :
    (∃ t : CyclePiece G → ℝ, IsFractionalPartition G t ∧ (∑ J, t J) ≤ B+1 ∧ t H = 1) ↔
    (∃ s : CyclePiece (G \ H.val.spanningCoe) → ℝ,
      IsFractionalPartition (G \ H.val.spanningCoe) s ∧ (∑ J, s J) ≤ B) := by
  constructor
  · rintro ⟨t,ht,hb,hH⟩
    obtain ⟨s,hs,heq⟩ := remove_unit_cycle G t ht H hH
    exact ⟨s,hs,by linarith⟩
  · rintro ⟨s,hs,hb⟩
    obtain ⟨t,ht,heq,hH⟩ := extend_removed_cycle G H s hs
    exact ⟨t,ht,by linarith,hH⟩

end Erdos184.FractionalCycles
