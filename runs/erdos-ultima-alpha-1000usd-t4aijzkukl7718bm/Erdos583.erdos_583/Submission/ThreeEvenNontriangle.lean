import Submission.IndependentTripleSharp

/-! Exactly three even vertices satisfy the sharp floor-half bound whenever
the even-induced graph is not complete. -/
namespace Erdos583ThreeEvenNontriangleDevelopment
open SimpleGraph Erdos583Work Erdos583Work.ComponentDeficit
open Erdos583IndependentTripleSharpDevelopment Erdos583ThreeEvenSharpRestorationDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false

lemma sharp_three_even_nonedge {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hthree : evenCount G=3) (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : Even (Nat.card (G.neighborSet a))) (hb : Even (Nat.card (G.neighborSet b)))
    (hc : Even (Nat.card (G.neighborSet c))) (hnab : ¬G.Adj a b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1 ≤ Fintype.card V := by
  by_cases hca : G.Adj c a
  · exact sharp_three_even_edge_nonedge G hthree b a c hab.symm hbc hca hb ha hc
      (fun hh ↦ hnab hh.symm)
  by_cases hcb : G.Adj c b
  · exact sharp_three_even_edge_nonedge G hthree a b c hab hac hcb ha hb hc hnab
  apply sharp_independent_three G hthree
  have hs := triple_even_set_of_card_three G hthree hab hac hbc ha hb hc
  intro u v hu hv huv
  have hu' : u=a ∨ u=b ∨ u=c := Set.ext_iff.mp hs u |>.mp hu
  have hv' : v=a ∨ v=b ∨ v=c := Set.ext_iff.mp hs v |>.mp hv
  rcases hu' with rfl|rfl|rfl <;> rcases hv' with rfl|rfl|rfl
  all_goals first | exact G.irrefl huv | exact hnab huv | exact hnab huv.symm |
    exact hca huv | exact hca huv.symm | exact hcb huv | exact hcb huv.symm

lemma sharp_three_even_not_clique {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hthree : evenCount G=3) {a b : V} (hab : a ≠ b)
    (ha : Even (Nat.card (G.neighborSet a))) (hb : Even (Nat.card (G.neighborSet b)))
    (hnab : ¬G.Adj a b) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ 2*D.card+1 ≤ Fintype.card V := by
  have hex : ∃ c, Even (Nat.card (G.neighborSet c)) ∧ c ≠ a ∧ c ≠ b := by
    by_contra hn
    have hs : {z | Even (Nat.card (G.neighborSet z))} ⊆ ({a,b} : Set V) := by
      intro z hz
      by_cases hza : z=a
      · exact Or.inl hza
      by_cases hzb : z=b
      · exact Or.inr hzb
      exact (hn ⟨z,hz,hza,hzb⟩).elim
    have hh := Set.ncard_le_ncard hs
    rw [Set.ncard_pair hab] at hh
    change evenCount G ≤ 2 at hh
    omega
  obtain ⟨c,hc,hca,hcb⟩ := hex
  exact sharp_three_even_nonedge G hthree a b c hab hca.symm hcb.symm ha hb hc hnab

end Erdos583ThreeEvenNontriangleDevelopment
