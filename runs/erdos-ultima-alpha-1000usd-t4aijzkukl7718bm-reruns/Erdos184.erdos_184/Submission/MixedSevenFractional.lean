import Submission.MixedSevenWalks
import Submission.FractionalTransport

/-! The seven-vertex mixed-count obstruction has an exact fractional cycle
partition of cost three. This does not bound integral partitions. -/
open SimpleGraph
namespace Erdos184.MixedSevenFractional
open MixedCriticalNonforest MixedSevenWalks FractionalCycles
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def index : Fin 5 → MixedSevenFinite.I := ![0,39,42,97,101]
def mult : Fin 5 → ℕ := ![2,1,1,1,1]

lemma coverage : ∀ u v : V,
    (∑ i : Fin 5, if s(u,v) ∈ (walk (index i)).2.edges then mult i else 0) =
      if G.Adj u v then 2 else 0 := by decide

open scoped Classical BigOperators
attribute [local instance] cyclePieceFintype

noncomputable def C (i : Fin 5) : CyclePiece G :=
  ⟨piece (index i),(piece_cycle (index i)).1,by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (piece_cycle (index i)).2 v⟩

noncomputable def amount (i : Fin 5) : ℝ := (mult i : ℝ)/2
noncomputable def weight : CyclePiece G → ℝ := pushWeight C amount

lemma fractional : IsFractionalPartition G weight := by
  apply fractional_of_family G C amount (fun i => by unfold amount; positivity)
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    have hn := coverage u v
    rw [if_pos (show G.Adj u v from he)] at hn
    have hr : (∑ i : Fin 5, if s(u,v) ∈ (walk (index i)).2.edges then (mult i : ℝ) else 0) = 2 := by
      exact_mod_cast hn
    change (∑ i : Fin 5, if s(u,v) ∈ (walk (index i)).2.toSubgraph.edgeSet then amount i else 0) = 1
    simp only [Walk.edgeSet_toSubgraph,Set.mem_setOf_eq]
    calc
      _ = (∑ i : Fin 5, if s(u,v) ∈ (walk (index i)).2.edges then (mult i : ℝ) else 0) / 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp [amount]
      _ = 1 := by rw [hr]; norm_num

lemma weight_cost : (∑ J, weight J) = 3 := by
  rw [weight,pushWeight_sum]
  norm_num [amount,mult,Fin.sum_univ_succ]

lemma optimal (t : CyclePiece G → ℝ) (ht : IsFractionalPartition G t) :
    3 ≤ ∑ J, t J := by
  have h := degree_lower G t ht 0
  have hd := hub_degrees.1
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h hd
  rw [hd] at h
  norm_num at h
  linarith

lemma integral_gt_twice_fractional : (MixedCritical.number G : ℝ) > 2 * ∑ J, weight J := by
  rw [number_eq,weight_cost]
  norm_num

end Erdos184.MixedSevenFractional
