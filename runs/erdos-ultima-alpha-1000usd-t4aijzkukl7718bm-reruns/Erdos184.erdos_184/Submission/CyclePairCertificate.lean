import Submission.CountThreeOrder

/-! Soundness of explicit finite cycle and two-cycle-partition certificates. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CyclePairCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 1000000

def cycleEdges {n : ℕ} (f : Fin (n+3) → V) : Finset (Sym2 V) :=
  Finset.univ.image (fun i => s(f i,f (i+1)))

lemma cycle_of_certificate {G : SimpleGraph V} {n : ℕ} (f : Fin (n+3) → V)
    (hi : Function.Injective f) (ha : ∀ i, G.Adj (f i) (f (i+1))) :
    ∃ P : G.Subgraph, (P.coe.Connected ∧ P.coe.IsRegularOfDegree 2) ∧
      P.edgeSet = (cycleEdges f : Set (Sym2 V)) := by
  let φ : cycleGraph (n+3) →g G :=
    { toFun := f
      map_rel' := by
        intro i j hij
        rcases (cycleGraph_adj_successor i j).mp hij with h | h
        · simpa only [h] using ha i
        · simpa only [h] using (ha j).symm }
  have ht : (⊤ : (cycleGraph (n+3)).Subgraph).coe.Connected ∧
      (⊤ : (cycleGraph (n+3)).Subgraph).coe.IsRegularOfDegree 2 := by
    refine ⟨Subgraph.topIso.connected_iff.mpr cycleGraph_connected,?_⟩
    have hreg : (cycleGraph (n+3)).IsRegularOfDegree 2 := fun _ => cycleGraph_degree_three_le
    have hh := regular_two_of_iso (Subgraph.topIso (G := cycleGraph (n+3))).symm (by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hreg v)
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh v
  have himage := subgraph_image_cycle_of_injective φ hi ⊤ ht.1 (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using ht.2 v)
  refine ⟨(⊤ : (cycleGraph (n+3)).Subgraph).map φ,⟨himage.1,?_⟩,?_⟩
  · intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using himage.2 v
  rw [Subgraph.edgeSet_map,Subgraph.edgeSet_top]
  ext e
  simp only [cycleEdges,Finset.mem_coe,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨d,hd,rfl⟩
    obtain ⟨i,rfl⟩ := cycleGraph_edge_successor hd
    exact ⟨i,rfl⟩
  · intro he
    obtain ⟨i,rfl⟩ := he
    refine ⟨s(i,i+1),?_,rfl⟩
    exact (cycleGraph_adj_successor i (i+1)).mpr (Or.inl rfl)

lemma cycle_pair_decomposition {G : SimpleGraph V} {n m : ℕ}
    (f : Fin (n+3) → V) (g : Fin (m+3) → V)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfa : ∀ i, G.Adj (f i) (f (i+1)))
    (hga : ∀ i, G.Adj (g i) (g (i+1)))
    (hd : Disjoint (cycleEdges f) (cycleEdges g))
    (hc : ((cycleEdges f ∪ cycleEdges g : Finset (Sym2 V)) : Set (Sym2 V)) = G.edgeSet) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ 2 := by
  obtain ⟨P,hp,hPe⟩ := cycle_of_certificate f hf hfa
  obtain ⟨Q,hq,hQe⟩ := cycle_of_certificate g hg hga
  have hdis : Disjoint P.edgeSet Q.edgeSet := by
    rw [hPe,hQe]
    exact_mod_cast hd
  have hcov : P.edgeSet ∪ Q.edgeSet = G.edgeSet := by
    rw [hPe,hQe]
    simpa only [Finset.coe_union] using hc
  refine ⟨{P,Q},?_,⟨?_,?_⟩,(by simpa using Finset.card_insert_le P {Q})⟩
  · intro H hH
    simp only [Finset.mem_insert,Finset.mem_singleton] at hH
    rcases hH with rfl | rfl <;> assumption
  · intro A hA B hB hAB
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
    · exact (hAB rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hAB rfl).elim
  · simpa only [Finset.mem_insert,Finset.mem_singleton,Set.iUnion_iUnion_eq_or_left,
      Set.iUnion_iUnion_eq_left] using hcov

lemma contradict_no_two {G : SimpleGraph V} (hG : EvenCycleCore.NoTwoCycles G)
    {n m : ℕ} (f : Fin (n+3) → V) (g : Fin (m+3) → V)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfa : ∀ i, G.Adj (f i) (f (i+1)))
    (hga : ∀ i, G.Adj (g i) (g (i+1)))
    (hd : Disjoint (cycleEdges f) (cycleEdges g)) : False := by
  obtain ⟨P,hp,hPe⟩ := cycle_of_certificate f hf hfa
  obtain ⟨Q,hq,hQe⟩ := cycle_of_certificate g hg hga
  apply hG P Q hp hq
  rw [hPe,hQe]
  exact_mod_cast hd

lemma cycleEdges_nondiag {n : ℕ} (f : Fin (n+3) → V)
    (hf : Function.Injective f) {e : Sym2 V} (he : e ∈ cycleEdges f) : ¬e.IsDiag := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  rw [Sym2.mk_isDiag_iff]
  intro hh
  have hi := hf hh
  have ha : (cycleGraph (n+3)).Adj i (i+1) :=
    (cycleGraph_adj_successor i (i+1)).mpr (Or.inl rfl)
  exact ha.ne hi

lemma decomposition_of_edge_certificate {n m : ℕ}
    (E : Finset (Sym2 V)) (f : Fin (n+3) → V) (g : Fin (m+3) → V)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hd : Disjoint (cycleEdges f) (cycleEdges g))
    (hc : cycleEdges f ∪ cycleEdges g = E) :
    let G := fromEdgeSet (E : Set (Sym2 V))
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card ≤ 2 := by
  dsimp only
  have hnon : ∀ e ∈ E, ¬e.IsDiag := by
    intro e he
    rw [← hc,Finset.mem_union] at he
    rcases he with he | he
    · exact cycleEdges_nondiag f hf he
    · exact cycleEdges_nondiag g hg he
  have heq : (fromEdgeSet (E : Set (Sym2 V))).edgeSet = E := by
    rw [edgeSet_fromEdgeSet]
    ext e
    exact ⟨And.left,fun he => ⟨he,by simpa only [Sym2.mem_diagSet_iff_isDiag] using hnon e he⟩⟩
  have hfa : ∀ i, (fromEdgeSet (E : Set (Sym2 V))).Adj (f i) (f (i+1)) := by
    intro i
    change s(f i,f (i+1)) ∈ (fromEdgeSet (E : Set (Sym2 V))).edgeSet
    rw [heq,← hc]
    simp only [Finset.mem_coe,Finset.mem_union,cycleEdges,Finset.mem_image,Finset.mem_univ,true_and]
    exact Or.inl ⟨i,rfl⟩
  have hga : ∀ i, (fromEdgeSet (E : Set (Sym2 V))).Adj (g i) (g (i+1)) := by
    intro i
    change s(g i,g (i+1)) ∈ (fromEdgeSet (E : Set (Sym2 V))).edgeSet
    rw [heq,← hc]
    simp only [Finset.mem_coe,Finset.mem_union,cycleEdges,Finset.mem_image,Finset.mem_univ,true_and]
    exact Or.inr ⟨i,rfl⟩
  obtain ⟨D,hD,hdec,hcard⟩ := cycle_pair_decomposition f g hf hg hfa hga hd (by rw [hc,heq])
  refine ⟨D,?_,hdec,hcard⟩
  intro H hH
  refine ⟨(hD H hH).1,?_⟩
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hD H hH).2 v

end Erdos184.CyclePairCertificate
