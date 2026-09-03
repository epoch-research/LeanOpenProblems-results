import Submission.MixedSmoothing
import Submission.GlobalVertexMinimal
import Submission.CriticalTightVertices

/-!
A low-degree vertex with a nonclique neighborhood is reducible. This still
leaves the clique-neighborhood case and the unbounded-degree problem.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace NonCliqueSmoothing
open MatchingSmoothing VertexSmoothing GlobalVertexMinimal
variable {V : Type*}

lemma matching_sup {M N : SimpleGraph V} (hm : IsMatching M) (hn : IsMatching N)
    (hd : Disjoint M.support N.support) : IsMatching (M ⊔ N) := by
  intro u v w huv huw
  rcases huv with huv | huv <;> rcases huw with huw | huw
  · exact hm huv huw
  · exact (Set.disjoint_left.mp hd ⟨v,huv⟩ ⟨w,huw⟩).elim
  · exact (Set.disjoint_left.mp hd ⟨w,huw⟩ ⟨v,huv⟩).elim
  · exact hn huv huw

lemma matching_edge (u w : V) : IsMatching (SimpleGraph.edge u w) := by
  intro x y z hxy hxz
  simp only [SimpleGraph.edge_adj] at hxy hxz
  rcases hxy.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    rcases hxz.1 with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp_all

lemma edge_support {u w : V} (hne : u ≠ w) : (SimpleGraph.edge u w).support = {u,w} := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    rcases (SimpleGraph.edge_adj u w x y).mp hy with ⟨⟨h,_⟩ | ⟨h,_⟩,_⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨w,(SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩⟩
    · exact ⟨u,(SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inr ⟨rfl,rfl⟩,hne.symm⟩⟩

lemma exists_matching_containing [Fintype V] (S : Set V) (he : Even S.ncard)
    {u w : V} (hu : u ∈ S) (hw : w ∈ S) (hne : u ≠ w) :
    ∃ M : SimpleGraph V, IsMatching M ∧ M.support = S ∧ M.Adj u w := by
  have hpair : ({u,w} : Set V) ⊆ S := by
    rintro x (rfl | rfl) <;> assumption
  have hcard := Set.ncard_diff_add_ncard_of_subset hpair
  rw [Set.ncard_pair hne] at hcard
  have herest : Even (S \ {u,w}).ncard := by
    obtain ⟨r,hr⟩ := he
    exact ⟨r-1,by omega⟩
  obtain ⟨N,hn,hN⟩ := exists_matching_support (S \ {u,w}) herest
  have hdis : Disjoint (SimpleGraph.edge u w).support N.support := by
    rw [edge_support hne,hN]
    exact Set.disjoint_sdiff_right
  refine ⟨SimpleGraph.edge u w ⊔ N,matching_sup (matching_edge u w) hn hdis,?_,
    Or.inl ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩)⟩
  have hsup : (SimpleGraph.edge u w ⊔ N).support =
      (SimpleGraph.edge u w).support ∪ N.support := by
    ext x
    simp only [SimpleGraph.mem_support,SimpleGraph.sup_adj,Set.mem_union]
    aesop
  rw [hsup,edge_support hne,hN]
  exact Set.union_diff_cancel hpair

set_option maxHeartbeats 800000 in
lemma nonclique_neighborhood_reduction [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ u, Even (G.degree u)) (v : V)
    (hdeg : G.degree v ≤ 2 * (C+1))
    {a b : V} (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b) (hnab : ¬G.Adj a b)
    (hsmall : ∀ H : SimpleGraph (Without v),
      (∀ u, Even (H.degree u)) → HasCardBound C H) : HasCardBound C G := by
  let A := G.induce {w | w ≠ v}
  let a' : Without v := ⟨a,hva.ne.symm⟩
  let b' : Without v := ⟨b,hvb.ne.symm⟩
  obtain ⟨M,hm,hM,hMab⟩ := exists_matching_containing (neighborsWithout G v)
    (by rw [neighborsWithout_card]; exact he v)
    (show a' ∈ neighborsWithout G v from hva)
    (show b' ∈ neighborsWithout G v from hvb)
    (fun h => hab (congrArg Subtype.val h))
  let f : apex A M ≃g G := apexIso G v M hM
  have hap : ∀ x, Even ((apex A M).degree x) := by
    intro x
    have hd := f.degree_eq x
    have hx := he (f x)
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hx ⊢
    rwa [← hd]
  have het := MixedSmoothing.even_toggled A M hm (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hap x)
  obtain ⟨D,hcD,hdD,hbD⟩ := hsmall (MixedSmoothing.toggled A M) (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using het x)
  have hr : 2 * M.edgeSet.ncard = G.degree v := by
    rw [← hm.support_card,hM,neighborsWithout_card]
  have hne : MixedSmoothing.newPairs A M ≠ ⊥ := by
    intro h
    have hnew : (MixedSmoothing.newPairs A M).Adj a' b' := ⟨hMab,hnab⟩
    simp only [h,bot_adj] at hnew
  have hrbound : M.edgeSet.ncard ≤ C+1 := by
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hr hdeg
    omega
  obtain ⟨E,hcE,hdE,hbE⟩ := MixedSmoothing.bound_apex_of_small_matching C A M hm hne
    hrbound D (by
      intro H hH
      refine ⟨(hcD H hH).1,?_⟩
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using (hcD H hH).2 x) hdD hbD
  apply HasCardBound.of_iso f
  refine ⟨E,?_,hdE,hbE⟩
  intro H hH
  refine ⟨(hcE H hH).1,?_⟩
  intro x
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcE H hH).2 x

universe u
lemma low_degree_neighbors_clique {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    (v : V) (hdeg : G.degree v ≤ 2 * (C+1)) : G.IsClique (G.neighborSet v) := by
  intro a hva b hvb hab
  by_contra hnab
  apply hG.2.1
  apply nonclique_neighborhood_reduction C G hG.1 v hdeg hva hvb hab hnab
  intro H heH
  exact hG.2.2 H (Fintype.card_subtype_lt (x := v) (by simp)) heH

end NonCliqueSmoothing
end Erdos184
