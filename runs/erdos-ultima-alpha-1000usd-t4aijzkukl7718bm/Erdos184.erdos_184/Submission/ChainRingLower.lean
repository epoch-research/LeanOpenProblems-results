import Submission.ChainRingResidualBounds

/-! A lower bound for the source graph of the auxiliary compression example. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ChainRing
open Critical Subfamilies
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 10000

lemma family_block_lower (R : SimpleGraph Vertex) (hR : R ≤ base)
    (D : Finset source.Subgraph) (hD : ∀ H ∈ D, IsCycleOrEdge H.coe)
    (hp : Set.PairwiseDisjoint (D : Set source.Subgraph) (fun H => H.edgeSet))
    (hu : (⋃ H ∈ D, H.edgeSet) = R.edgeSet) :
    (∑ i : Fin 3, number (R ⊓ block i)) ≤ D.card := by
  have hle (H) (hH : H ∈ D) : H.spanningCoe ≤ R := by
    intro x y hxy
    have hm : s(x,y) ∈ ⋃ K ∈ D, K.edgeSet :=
      Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,hxy⟩⟩
    rwa [hu] at hm
  have hlocal (H) (hH : H ∈ D) : ∃ i, H.spanningCoe ≤ block i :=
    piece_without_closing_local H (hD H hH) (fun he => base_no_closing (hR (hle H hH he)))
  let f : source.Subgraph → Fin 3 := fun H => if h : H ∈ D then Classical.choose (hlocal H h) else 0
  have hf (H) (hH : H ∈ D) : H.spanningCoe ≤ block (f H) := by
    dsimp only [f]
    rw [dif_pos hH]
    exact Classical.choose_spec (hlocal H hH)
  let A (i : Fin 3) := D.filter (fun H => f H = i)
  have hcover (i : Fin 3) : (⋃ H ∈ A i, H.edgeSet) = (R ⊓ block i).edgeSet := by
    ext e
    induction e using Sym2.ind with | h x y =>
    constructor
    · intro he
      obtain ⟨H,he⟩ := Set.mem_iUnion.mp he
      obtain ⟨hH,heH⟩ := Set.mem_iUnion.mp he
      obtain ⟨hHD,hfi⟩ := Finset.mem_filter.mp hH
      exact ⟨hle H hHD heH,hfi ▸ hf H hHD heH⟩
    · rintro ⟨heR,heB⟩
      have heR' : s(x,y) ∈ ⋃ H ∈ D, H.edgeSet := hu.symm ▸ heR
      obtain ⟨H,he⟩ := Set.mem_iUnion.mp heR'
      obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp he
      have hfi : f H = i := by
        by_contra hn
        exact block_distinct_edges (f H) i hn x y ⟨hf H hHD heH,heB⟩
      exact Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hHD,hfi⟩,heH⟩⟩
  have hn (i : Fin 3) : number (R ⊓ block i) ≤ (A i).card := by
    have hh := number_le (lowerFamily (A i) (hcover i))
      (lowerFamily_property IsCycleOrEdge (A i) (hcover i)
        (fun H hH => hD H (Finset.mem_filter.mp hH).1))
      (lowerFamily_decomposition (A i) (hcover i)
        (fun _ hH _ hK hne => hp (Finset.mem_filter.mp hH).1 (Finset.mem_filter.mp hK).1 hne))
    simpa only [lowerFamily_card] using hh
  calc
    _ ≤ ∑ i : Fin 3, (A i).card := Finset.sum_le_sum (fun i _ => hn i)
    _ = D.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (by
        intro H hH
        exact Finset.mem_univ (f H))

lemma residual_le_base (H : source.Subgraph)
    (he : H.spanningCoe.Adj (.inl 0) (.inl 3)) : residual H ≤ base := by
  rw [← delete_closing]
  intro x y hxy
  refine ⟨hxy.1,?_⟩
  intro hm
  have hm' : s(x,y) = s(Sum.inl 0,Sum.inl 3) := Set.mem_singleton_iff.mp hm.1
  apply hxy.2
  change s(x,y) ∈ H.edgeSet
  rw [hm']
  exact he

lemma source_number_ge_twenty_five : 25 ≤ number source := by
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum source
  have he : s(Sum.inl 0,Sum.inl 3) ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ source_closing
  obtain ⟨H,he⟩ := Set.mem_iUnion.mp he
  obtain ⟨hHD,heH⟩ := Set.mem_iUnion.mp he
  let A := D.erase H
  have hAD : A ⊆ D := Finset.erase_subset _ _
  have hcover : (⋃ K ∈ A, K.edgeSet) = (residual H).edgeSet := by
    rw [residual,SimpleGraph.edgeSet_sdiff]
    ext e
    constructor
    · intro he
      obtain ⟨K,he⟩ := Set.mem_iUnion.mp he
      obtain ⟨hK,heK⟩ := Set.mem_iUnion.mp he
      exact ⟨K.edgeSet_subset heK,fun heH =>
        Set.disjoint_left.mp (hdec.1 (hAD hK) hHD (Finset.mem_erase.mp hK).1) heK heH⟩
    · rintro ⟨heG,heH⟩
      rw [← hdec.2] at heG
      obtain ⟨K,heG⟩ := Set.mem_iUnion.mp heG
      obtain ⟨hK,heK⟩ := Set.mem_iUnion.mp heG
      have hne : K ≠ H := by rintro rfl; exact heH heK
      exact Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨hne,hK⟩,heK⟩⟩
  have hl := family_block_lower (residual H) (residual_le_base H heH) A
    (fun K hK => hD K (hAD hK)) (fun _ hK _ hL hne => hdec.1 (hAD hK) (hAD hL) hne) hcover
  have hs : 24 ≤ ∑ i : Fin 3, number (rowResidual H i) := by
    calc
      _ = ∑ _i : Fin 3, 8 := by decide
      _ ≤ _ := Finset.sum_le_sum (fun i _ => rowResidual_number_ge_eight H (hD H hHD) heH i)
  have hc : A.card + 1 = D.card := Finset.card_erase_add_one hHD
  change (∑ i : Fin 3, number (rowResidual H i)) ≤ A.card at hl
  omega

end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.source_number_ge_twenty_five
