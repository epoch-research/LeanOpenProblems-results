import Submission.PackingTransfer

/-!
Extracting four-terminal routing states from parity-corrected decompositions.
Two marked edges on different cycles give their original pairing. On one
cycle, their deletion gives a vertex-disjoint complementary pairing.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TerminalRouting
variable {V : Type*} [Fintype V] {G A K : SimpleGraph V}
set_option maxHeartbeats 800000

noncomputable def Route.repath {t t' : Fin 4 → V} {i j : Fin 3}
    (R : Route G A t i) (P : PairedPaths G t' j) (hP : P.edges = R.paths.edges) : Route G A t' j where
  paths := P
  rest := R.rest
  disjoint := by rw [hP]; exact R.disjoint
  cover := by rw [hP]; exact R.cover

lemma route_of_removed_pieces (D : Packing K) (hD : D.edges = K.edgeSet)
    (M : Set (Sym2 V)) (hK : K.edgeSet = A.edgeSet ∪ M) (hAM : Disjoint A.edgeSet M)
    (hAG : A ≤ G) (S : Finset K.Subgraph) (hS : S ⊆ D.pieces)
    (hM : M ⊆ (D.restrict S hS).edges) {t : Fin 4 → V} {i : Fin 3}
    (P : PairedPaths G t i) (hP : P.edges = (D.restrict S hS).edges \ M) :
    ∃ R : Route G A t i, R.paths = P ∧ R.rest.pieces.card + S.card ≤ D.pieces.card := by
  let C := (D.restrict S hS).edges
  have hrem := D.remove_edges S hS
  have hCG : C ⊆ K.edgeSet := by
    intro e he
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp he
    exact H.edgeSet_subset heH
  have hsub : (D.remove S).edges ⊆ G.edgeSet := by
    rw [hrem,hD,hK]
    intro e he
    have heA : e ∈ A.edgeSet := he.1.resolve_right (fun hm => he.2 (hM hm))
    exact edgeSet_mono hAG heA
  obtain ⟨Q,hQ,hcard⟩ := (D.remove S).transfer hsub
  have hQ' : Q.edges = K.edgeSet \ C := by rw [hQ,hrem,hD]
  have hdis : Disjoint Q.edges P.edges := by
    rw [hQ',hP]
    exact Set.disjoint_sdiff_left.mono_right Set.diff_subset
  have hcover : Q.edges ∪ P.edges = A.edgeSet := by
    rw [hQ',hP,hK]
    ext e
    have hdc := Set.disjoint_left.mp hAM
    have hm := hM (a := e)
    have hc := hCG (a := e)
    rw [hK] at hc
    simp only [Set.mem_union,Set.mem_diff] at hm hc ⊢
    constructor
    · rintro (⟨h,hn⟩ | ⟨h,hn⟩)
      · exact h.resolve_right (fun hm' => hn (hm hm'))
      · exact (hc h).resolve_right hn
    · intro he
      by_cases heC : e ∈ C
      · exact Or.inr ⟨heC,hdc he⟩
      · exact Or.inl ⟨Or.inl he,heC⟩
  refine ⟨⟨P,Q,hdis,hcover⟩,rfl,?_⟩
  change Q.pieces.card+S.card ≤ D.pieces.card
  have hh := D.remove_card S hS
  omega

/-- The first canonical correction matching. The two strong alternatives
are the other two pairings of the same four distinct terminals. -/
lemma first_matching_routes (t : Fin 4 → V) (ht : Function.Injective t)
    (hAG : A ≤ G)
    (hK : K.edgeSet = A.edgeSet ∪ {s(t 0,t 1),s(t 2,t 3)})
    (hnot1 : s(t 0,t 1) ∉ A.edgeSet) (hnot2 : s(t 2,t 3) ∉ A.edgeSet)
    (D : Finset K.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition K D) :
    (∃ R : Route G A t 0, R.rest.pieces.card+2 ≤ D.card) ∨
    (∃ R : Route G A t 1, R.paths.Strong ∧ R.rest.pieces.card+1 ≤ D.card) ∨
    (∃ R : Route G A t 2, R.paths.Strong ∧ R.rest.pieces.card+1 ≤ D.card) := by
  let DP : Packing K := ⟨D,hc,hd.1⟩
  have hDP : DP.edges = K.edgeSet := hd.2
  have hAM : Disjoint A.edgeSet {s(t 0,t 1),s(t 2,t 3)} := by
    apply Set.disjoint_left.mpr
    intro e he hm
    rcases hm with rfl | hm
    · exact hnot1 he
    · exact hnot2 (hm ▸ he)
  have he1 : s(t 0,t 1) ∈ K.edgeSet := by rw [hK]; simp
  have he2 : s(t 2,t 3) ∈ K.edgeSet := by rw [hK]; simp
  have hne : s(t 0,t 1) ≠ s(t 2,t 3) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact (by decide : (0 : Fin 4) ≠ 2) (ht h.1)
    · exact (by decide : (0 : Fin 4) ≠ 3) (ht h.1)
  have covered1 := hd.2.symm ▸ he1
  have covered2 := hd.2.symm ▸ he2
  obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp covered1
  obtain ⟨L,hL,heL⟩ := Set.mem_iUnion₂.mp covered2
  have edge_to_G {e : Sym2 V} (he : e ∈ K.edgeSet)
      (hn1 : e ≠ s(t 0,t 1)) (hn2 : e ≠ s(t 2,t 3)) : e ∈ G.edgeSet := by
    rw [hK] at he
    apply edgeSet_mono hAG
    exact he.resolve_right (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using ⟨hn1,hn2⟩)
  by_cases hHL : H = L
  · subst L
    have hS : ({H} : Finset K.Subgraph) ⊆ DP.pieces := by simpa using hH
    have hCE : (DP.restrict {H} hS).edges = H.edgeSet := by
      simp only [Packing.edges,Packing.restrict,Finset.mem_singleton,Set.iUnion_iUnion_eq_left]
    have hM : {s(t 0,t 1),s(t 2,t 3)} ⊆ (DP.restrict {H} hS).edges := by
      rw [hCE]
      intro e he
      rcases he with rfl | he
      · exact heH
      · exact he.symm ▸ heL
    rcases MarkedCyclePaths.cycle_remove_two_edges H (hc H hH).1 (hc H hH).2 heH heL hne with
      ⟨p,q,hp,hq,hpq,hcov,hpv,hqv⟩ | ⟨p,q,hp,hq,hpq,hcov,hpv,hqv⟩
    · have hpG : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
        intro e he
        have hh := (hcov e).mp (Or.inl he)
        exact edge_to_G (H.edgeSet_subset hh.1) hh.2.1 hh.2.2
      have hqG : ∀ e ∈ q.edges, e ∈ G.edgeSet := by
        intro e he
        have hh := (hcov e).mp (Or.inr he)
        exact edge_to_G (H.edgeSet_subset hh.1) hh.2.1 hh.2.2
      let P : PairedPaths G t 2 := {
        p := (q.transfer G hqG).reverse
        q := p.transfer G hpG
        hp := (hq.transfer hqG).reverse
        hq := hp.transfer hpG
        disjoint := by
          apply Set.disjoint_left.mpr
          intro e he hf
          simp only [mem_walkEdges,Walk.edges_reverse,Walk.edges_transfer,List.mem_reverse] at he hf
          induction e using Sym2.ind with
          | h x y => exact hpq (p.fst_mem_support_of_mem_edges hf) (q.fst_mem_support_of_mem_edges he) }
      have hPE : P.edges = (DP.restrict {H} hS).edges \ {s(t 0,t 1),s(t 2,t 3)} := by
        rw [hCE]
        ext e
        simp only [PairedPaths.edges,P,mem_walkEdges,Walk.edges_transfer,Walk.edges_reverse,
          List.mem_reverse,Set.mem_union,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
        have hh := hcov e
        tauto
      obtain ⟨R,hR,hcard⟩ := route_of_removed_pieces DP hDP _ hK hAM hAG {H} hS hM P hPE
      refine Or.inr (Or.inr ⟨R,?_,by simpa using hcard⟩)
      rw [hR]
      change (q.transfer G hqG).reverse.support.Disjoint (p.transfer G hpG).support
      simpa only [Walk.support_reverse,Walk.support_transfer,List.disjoint_reverse_left] using hpq.symm
    · have hpG : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
        intro e he
        have hh := (hcov e).mp (Or.inl he)
        exact edge_to_G (H.edgeSet_subset hh.1) hh.2.1 hh.2.2
      have hqG : ∀ e ∈ q.edges, e ∈ G.edgeSet := by
        intro e he
        have hh := (hcov e).mp (Or.inr he)
        exact edge_to_G (H.edgeSet_subset hh.1) hh.2.1 hh.2.2
      let P : PairedPaths G t 1 := {
        p := (q.transfer G hqG).reverse
        q := p.transfer G hpG
        hp := (hq.transfer hqG).reverse
        hq := hp.transfer hpG
        disjoint := by
          apply Set.disjoint_left.mpr
          intro e he hf
          simp only [mem_walkEdges,Walk.edges_reverse,Walk.edges_transfer,List.mem_reverse] at he hf
          induction e using Sym2.ind with
          | h x y => exact hpq (p.fst_mem_support_of_mem_edges hf) (q.fst_mem_support_of_mem_edges he) }
      have hPE : P.edges = (DP.restrict {H} hS).edges \ {s(t 0,t 1),s(t 2,t 3)} := by
        rw [hCE]
        ext e
        simp only [PairedPaths.edges,P,mem_walkEdges,Walk.edges_transfer,Walk.edges_reverse,
          List.mem_reverse,Set.mem_union,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
        have hh := hcov e
        tauto
      obtain ⟨R,hR,hcard⟩ := route_of_removed_pieces DP hDP _ hK hAM hAG {H} hS hM P hPE
      refine Or.inr (Or.inl ⟨R,?_,by simpa using hcard⟩)
      rw [hR]
      change (q.transfer G hqG).reverse.support.Disjoint (p.transfer G hpG).support
      simpa only [Walk.support_reverse,Walk.support_transfer,List.disjoint_reverse_left] using hpq.symm
  · have hS : ({H,L} : Finset K.Subgraph) ⊆ DP.pieces := by
      intro J hJ
      have hh : J = H ∨ J = L := by simpa using hJ
      rcases hh with rfl | rfl
      · exact hH
      · exact hL
    have hCE : (DP.restrict {H,L} hS).edges = H.edgeSet ∪ L.edgeSet := by
      simp only [Packing.edges,Packing.restrict,Finset.set_biUnion_insert,Finset.set_biUnion_singleton]
    have hM : {s(t 0,t 1),s(t 2,t 3)} ⊆ (DP.restrict {H,L} hS).edges := by
      rw [hCE]
      intro e he
      rcases he with rfl | he
      · exact Or.inl heH
      · exact Or.inr (he.symm ▸ heL)
    have hdis := Set.disjoint_left.mp (hd.1 hH hL hHL)
    obtain ⟨p,hp,hpe,hpv⟩ := TwoTerminalGluing.cycle_complementary_path H (hc H hH).1 (hc H hH).2 heH
    obtain ⟨q,hq,hqe,hqv⟩ := TwoTerminalGluing.cycle_complementary_path L (hc L hL).1 (hc L hL).2 heL
    have hpG : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e he
      have hh := (hpe e).mp he
      exact edge_to_G (H.edgeSet_subset hh.1) hh.2 (fun heq => hdis (heq ▸ hh.1) heL)
    have hqG : ∀ e ∈ q.edges, e ∈ G.edgeSet := by
      intro e he
      have hh := (hqe e).mp he
      exact edge_to_G (L.edgeSet_subset hh.1) (fun heq => hdis heH (heq ▸ hh.1)) hh.2
    let P : PairedPaths G t 0 := {
      p := (p.transfer G hpG).reverse
      q := (q.transfer G hqG).reverse
      hp := (hp.transfer hpG).reverse
      hq := (hq.transfer hqG).reverse
      disjoint := by
        apply Set.disjoint_left.mpr
        intro e he hf
        simp only [mem_walkEdges,Walk.edges_reverse,Walk.edges_transfer,List.mem_reverse] at he hf
        exact hdis ((hpe e).mp he).1 ((hqe e).mp hf).1 }
    have hPE : P.edges = (DP.restrict {H,L} hS).edges \ {s(t 0,t 1),s(t 2,t 3)} := by
      rw [hCE]
      ext e
      simp only [PairedPaths.edges,P,mem_walkEdges,Walk.edges_transfer,Walk.edges_reverse,
        List.mem_reverse,Set.mem_union,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or,hpe,hqe]
      have hnH : e ∈ H.edgeSet → e ≠ s(t 2,t 3) := fun he heq => hdis (heq ▸ he) heL
      have hnL : e ∈ L.edgeSet → e ≠ s(t 0,t 1) := fun he heq => hdis heH (heq ▸ he)
      tauto
    obtain ⟨R,hR,hcard⟩ := route_of_removed_pieces DP hDP _ hK hAM hAG {H,L} hS hM P hPE
    exact Or.inl ⟨R,by simpa only [Finset.card_pair hHL] using hcard⟩

end Erdos184.TerminalRouting
