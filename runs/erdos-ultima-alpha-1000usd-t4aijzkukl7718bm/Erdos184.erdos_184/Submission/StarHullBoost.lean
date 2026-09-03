import Submission.StarDeletion

/-! An additive hull increase for even graphs, proportional to their support.
This is not a fixed relative increase in the decomposition number and does
not establish Erdős184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.StarHullBoost
open Critical
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000
variable {V : Type*} [Fintype V]

lemma exists_leaf_stars (G : SimpleGraph V) (B : Finset V)
    (hB : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v) (hs : ∀ v ∈ B, v ∈ G.support) :
    ∃ M : SimpleGraph V, M ≤ G ∧
      (∀ u v, M.Adj u v → u ∈ B ∨ v ∈ B) ∧
      (∀ v ∈ B, Nat.card (M.neighborSet v) = 1) := by
  have hex (v : V) (hv : v ∈ B) : ∃ w, G.Adj v w := hs v hv
  let f : V → V := fun v => if hv : v ∈ B then Classical.choose (hex v hv) else v
  have hf (v : V) (hv : v ∈ B) : G.Adj v (f v) := by
    dsimp only [f]
    rw [dif_pos hv]
    exact Classical.choose_spec (hex v hv)
  let M : SimpleGraph V := SimpleGraph.fromRel (fun v w => v ∈ B ∧ w = f v)
  have hMG : M ≤ G := by
    intro v w hvw
    rcases hvw.2 with ⟨hv,rfl⟩ | ⟨hw,hv⟩
    · exact hf v hv
    · rw [hv]
      exact (hf w hw).symm
  refine ⟨M,hMG,?_,?_⟩
  · intro u v huv
    exact huv.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · intro v hv
    have heq : M.neighborSet v = {f v} := by
      ext w
      constructor
      · intro hvw
        rcases hvw.2 with h | h
        · exact h.2
        · exact (hB v hv w h.1 (hMG hvw)).elim
      · intro hw
        have hw' : w = f v := hw
        subst w
        exact ⟨(hf v hv).ne,Or.inl ⟨hv,rfl⟩⟩
    rw [heq]
    exact Nat.card_unique

lemma independent_hull_boost (G : SimpleGraph V)
    (he : ∀ v, Even (Nat.card (G.neighborSet v))) (B : Finset V)
    (hB : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v) (hs : ∀ v ∈ B, v ∈ G.support) :
    2 * number G + B.card ≤ 2 * EdgeHull.value G := by
  obtain ⟨M,hMG,hcover,hdeg⟩ := exists_leaf_stars G B hB hs
  exact StarDeletion.hull_stars_boost hMG he B hB hcover hdeg

lemma exists_maximal_matching (G : SimpleGraph V) :
    ∃ M : SimpleGraph V, M ≤ G ∧ (∀ v, Nat.card (M.neighborSet v) ≤ 1) ∧
      ∀ u v, u ∉ M.support → v ∉ M.support → ¬ G.Adj u v := by
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  let P : SimpleGraph V → Prop := fun M => M ≤ G ∧ ∀ v, Nat.card (M.neighborSet v) ≤ 1
  let S : Finset (SimpleGraph V) := Finset.univ.filter P
  have hbot : P ⊥ := by
    refine ⟨bot_le,?_⟩
    intro v
    have h : (⊥ : SimpleGraph V).degree v ≤ 1 := by simp
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h
  have hs : S.Nonempty := ⟨⊥,by simp [S,hbot]⟩
  obtain ⟨M,hM,hmax⟩ := Finset.exists_max_image S (fun M => M.edgeFinset.card) hs
  obtain ⟨hMG,hdM⟩ := (Finset.mem_filter.mp hM).2
  refine ⟨M,hMG,hdM,?_⟩
  intro u v hu hv huv
  have hnu (w : V) : ¬ M.Adj u w := fun h => hu ⟨w,h⟩
  have hnv (w : V) : ¬ M.Adj v w := fun h => hv ⟨w,h⟩
  have huniq (x y z : V) (hy : M.Adj x y) (hz : M.Adj x z) : y = z := by
    exact (Set.ncard_le_one_iff (s := M.neighborSet x)).mp (hdM x) hy hz
  let E : SimpleGraph V := SimpleGraph.fromRel (fun x y => x = u ∧ y = v)
  let N := M ⊔ E
  have hNG : N ≤ G := by
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact hMG hxy
    · rcases hxy.2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact huv
      · exact huv.symm
  have hdN (x : V) : Nat.card (N.neighborSet x) ≤ 1 := by
    apply (Set.ncard_le_one_iff (s := N.neighborSet x)).mpr
    intro y z hy hz
    change M.Adj x y ∨ E.Adj x y at hy
    change M.Adj x z ∨ E.Adj x z at hz
    simp only [E,SimpleGraph.fromRel_adj] at hy hz
    by_cases hxu : x = u
    · subst x
      have hyv : y = v := by
        rcases hy with hy | ⟨_,hy⟩
        · exact (hnu y hy).elim
        · rcases hy with ⟨_,hy⟩ | ⟨_,h⟩
          · exact hy
          · exact (huv.ne h).elim
      have hzv : z = v := by
        rcases hz with hz | ⟨_,hz⟩
        · exact (hnu z hz).elim
        · rcases hz with ⟨_,hz⟩ | ⟨_,h⟩
          · exact hz
          · exact (huv.ne h).elim
      exact hyv.trans hzv.symm
    · by_cases hxv : x = v
      · subst x
        have hyu : y = u := by
          rcases hy with hy | ⟨_,hy⟩
          · exact (hnv y hy).elim
          · rcases hy with ⟨h,_⟩ | ⟨hy,_⟩
            · exact (huv.ne h.symm).elim
            · exact hy
        have hzu : z = u := by
          rcases hz with hz | ⟨_,hz⟩
          · exact (hnv z hz).elim
          · rcases hz with ⟨h,_⟩ | ⟨hz,_⟩
            · exact (huv.ne h.symm).elim
            · exact hz
        exact hyu.trans hzu.symm
      · have hyM : M.Adj x y := hy.elim id (fun h =>
          h.2.elim (fun h => (hxu h.1).elim) (fun h => (hxv h.2).elim))
        have hzM : M.Adj x z := hz.elim id (fun h =>
          h.2.elim (fun h => (hxu h.1).elim) (fun h => (hxv h.2).elim))
        exact huniq x y z hyM hzM
  have hMN : M ≤ N := le_sup_left
  have hNuv : N.Adj u v := Or.inr ⟨huv.ne,Or.inl ⟨rfl,rfl⟩⟩
  have hne : M ≠ N := by
    intro heq
    apply hnu v
    rw [heq]
    exact hNuv
  have hlt := EdgeHull.edge_card_lt_of_ne hMN hne
  have hle := hmax N (by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hNG,hdN⟩)
  omega

lemma matching_support_card {M : SimpleGraph V} (hd : ∀ v, Nat.card (M.neighborSet v) ≤ 1) :
    M.support.ncard = 2 * M.edgeFinset.card := by
  have hs := M.sum_degrees_support_eq_twice_card_edges
  have hdeg (v : V) (hv : v ∈ M.support.toFinset) : Nat.card (M.neighborSet v) = 1 := by
    have hp := (M.degree_pos_iff_mem_support v).mpr (Set.mem_toFinset.mp hv)
    have hh := hd v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hp
    omega
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hs
  have heq : (∑ v ∈ M.support.toFinset, Nat.card (M.neighborSet v)) = M.support.toFinset.card := by
    calc
      _ = ∑ _v ∈ M.support.toFinset, 1 := Finset.sum_congr rfl (fun v hv => hdeg v hv)
      _ = _ := by simp
  rw [heq] at hs
  simpa only [Set.ncard_eq_toFinset_card'] using hs

/-- Every even graph admits an arbitrary-edge subgraph whose decomposition
number exceeds the original by at least one sixth of the supported order. -/
lemma supported_order_boost (G : SimpleGraph V)
    (he : ∀ v, Even (Nat.card (G.neighborSet v))) :
    6 * number G + G.support.ncard ≤ 6 * EdgeHull.value G := by
  obtain ⟨M,hMG,hdM,hmax⟩ := exists_maximal_matching G
  let B := G.support.toFinset \ M.support.toFinset
  have hsub : M.support.toFinset ⊆ G.support.toFinset := by
    intro v hv
    obtain ⟨w,hw⟩ := Set.mem_toFinset.mp hv
    exact Set.mem_toFinset.mpr ⟨w,hMG hw⟩
  have hb : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v := by
    intro u hu v hv
    exact hmax u v (by simpa only [Set.mem_toFinset] using (Finset.mem_sdiff.mp hu).2)
      (by simpa only [Set.mem_toFinset] using (Finset.mem_sdiff.mp hv).2)
  have hs : ∀ v ∈ B, v ∈ G.support := by
    intro v hv
    exact Set.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1
  have hstar := independent_hull_boost G he B hb hs
  have hmatch := MatchingDeletion.hull_matching_boost hMG he hdM
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hmc := matching_support_card hdM
  change B.card + M.support.toFinset.card = G.support.toFinset.card at hcard
  simp only [Set.ncard_eq_toFinset_card'] at hmc ⊢
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hmatch hmc
  omega

/-- A linear bound in the supported order would turn the additive boost into
one fixed relative boost. The linear bound is an explicit hypothesis. -/
lemma relative_boost_of_support_bound (G : SimpleGraph V)
    (he : ∀ v, Even (Nat.card (G.neighborSet v))) (C : ℕ)
    (hC : number G ≤ C * G.support.ncard) :
    (6 * C + 1) * number G ≤ (6 * C) * EdgeHull.value G := by
  have h := Nat.mul_le_mul_left C (supported_order_boost G he)
  nlinarith

end Erdos184Work.StarHullBoost
#print axioms Erdos184Work.StarHullBoost.supported_order_boost
#print axioms Erdos184Work.StarHullBoost.relative_boost_of_support_bound
