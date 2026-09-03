import Submission.InseparableCycle

/-! Repeated common cycles under target-only residual connectivity. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.InseparableCycle
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 800000

/-- The connectivity input is tested only on earlier common-cycle packings.
No simultaneous extension to a minimum decomposition is assumed. -/
lemma packing_through_set (he : ∀ x, Even (G.degree x)) (T : Set V) (hT : 2 ≤ T.ncard)
    (r : ℕ)
    (hconn : ∀ P : Finset G.Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) →
      (∀ H ∈ P, T ⊆ H.verts) → P.card < r →
      ∀ S : Set V, S.ncard < T.ncard →
      ∀ a ∈ T, ∀ b ∈ T, ∀ haS : a ∉ S, ∀ hbS : b ∉ S,
        ((G \ unionPieces G P).induce Sᶜ).Reachable ⟨a,haS⟩ ⟨b,hbS⟩) :
    ∃ P : Finset G.Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (∀ H ∈ P, T ⊆ H.verts) ∧ P.card = r := by
  have hex : ∀ n : ℕ, n ≤ r →
      ∃ P : Finset G.Subgraph,
        (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
        (∀ H ∈ P, T ⊆ H.verts) ∧ P.card = n := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨∅,by simp,by simp,by simp,by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨P,hc,hd,hvert,hcard⟩ := ih (by omega)
      let R := G \ unionPieces G P
      obtain ⟨H,hH,hTH⟩ := cycle_through_inseparable_set (G := R)
        (by
          intro x
          simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
            using even_residual_of_cycle_packing G he P hc hd x)
        T hT (hconn P hc hd hvert (by omega))
      let J : G.Subgraph := promote (show R ≤ G from sdiff_le) H
      have hcJ : J.coe.Connected ∧ J.coe.IsRegularOfDegree 2 := by
        refine ⟨hH.1,?_⟩
        intro x
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hH.2 x
      have hdis : ∀ K ∈ P, Disjoint J.edgeSet K.edgeSet := by
        intro K hK
        apply Set.disjoint_left.mpr
        intro e heJ heK
        have heR : e ∈ R.edgeSet := H.edgeSet_subset heJ
        simp only [R,edgeSet_sdiff] at heR
        apply heR.2
        rw [unionPieces_edgeSet]
        exact Set.mem_iUnion₂.mpr ⟨K,hK,heK⟩
      have hnot : J ∉ P := by
        intro hJ
        obtain ⟨e,he⟩ := cycle_edgeSet_nonempty J hcJ.1 hcJ.2
        exact Set.disjoint_left.mp (hdis J hJ) he he
      refine ⟨insert J P,?_,?_,?_,by rw [Finset.card_insert_of_notMem hnot,hcard]⟩
      · intro K hK
        rcases Finset.mem_insert.mp hK with rfl | hK
        · exact hcJ
        · exact hc K hK
      · rw [Finset.coe_insert]
        exact hd.insert (fun K hK _ => hdis K hK)
      · intro K hK
        rcases Finset.mem_insert.mp hK with rfl | hK
        · exact hTH
        · exact hvert K hK
  exact hex r le_rfl

end Erdos184.InseparableCycle
