import Submission.AcyclicDeletion
import Submission.OptimalSingletonForest

/-! A parity-corrected forest deletion inequality. This is an auxiliary
reduction, not a proof of the original Erdős184 conjecture. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.AcyclicDeletion
open Critical
set_option maxHeartbeats 800000
variable {V : Type*} [Fintype V]

/-- A parity correction contained in the deleted forest bounds the loss.
There is no assertion that the correction can be chosen with bounded size. -/
lemma number_le_delete_forest_add (G M T : SimpleGraph V)
    (hTG : T ≤ G) (hTM : T ≤ M)
    (heven : ∀ v, Even (Nat.card ((G \ T).neighborSet v)))
    (hM : M.IsAcyclic) :
    number G ≤ number (G \ M) + Nat.card T.edgeSet := by
  have hdel : (G \ T) \ M = G \ M := by
    ext x y
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, fun ht => h.2 (hTM ht)⟩, h.2⟩
  have hn := number_le_delete_forest (G \ T) M heven hM
  rw [hdel] at hn
  have hs := number_sdiff_add_le G T hTG
  have ht := number_le_edges T
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at ht
  omega

/-- In particular, any forest extending the singleton part of an optimum
can be deleted at a cost of at most the size of that singleton part. -/
lemma optimal_forest_extension {G F M : SimpleGraph V}
    (hF : SingletonExchange.Optimal G F) (hFM : F ≤ M) (hM : M.IsAcyclic) :
    number G ≤ number (G \ M) + Nat.card F.edgeSet :=
  number_le_delete_forest_add G M F hF.1 hFM hF.2.1 hM

end Erdos184Work.AcyclicDeletion
#print axioms Erdos184Work.AcyclicDeletion.number_le_delete_forest_add
#print axioms Erdos184Work.AcyclicDeletion.optimal_forest_extension
