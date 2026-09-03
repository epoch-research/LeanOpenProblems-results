import FormalConjecturesUtil
import Submission.ThetaClusterStructure
import Submission.ThetaClusterMoments
import Submission.ThetaConeGraph

/-! The cluster partition is not a consequence of theta exclusion, even
for a relation realized as a link of an actual forbidden-pattern-free cone. -/
open Finset SimpleGraph
namespace Erdos713ThetaClusterObstruction
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaCluster
open Erdos713ThetaThreePoint Erdos713ThetaConeLinks
set_option maxHeartbeats 2000000

def small (a : Fin 4) (b : Fin 3) : Prop :=
  if a = 3 then b = 1 else b = 0 ∨ b = 2

instance : DecidableRel small := fun a b => by unfold small; infer_instance

lemma small_no_theta : ¬ HasTheta small := by
  rintro ⟨a,b,ha,hb,_⟩
  have hh := Fintype.card_le_of_injective b hb
  norm_num at hh

lemma small_rigid : Rigid3 small := by unfold Rigid3; decide

lemma codegree01 : codegree small 0 1 = 0 := by
  rw [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]
  decide

lemma codegree12 : codegree small 1 2 = 0 := by
  rw [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]
  decide

lemma codegree02 : codegree small 0 2 = 3 := by
  rw [codegree,Nat.card_eq_fintype_card,Fintype.card_subtype]
  decide

lemma no_partition {I : Type*} (τ : Fin 3 → I) :
    ¬ (CrossHeavy small τ ∧ SameLight small τ) := by
  rintro ⟨hH,hL⟩
  have h01 : τ 0 = τ 1 := by
    by_contra hn
    have hh := hH 0 1 hn
    rw [codegree01] at hh
    omega
  have h12 : τ 1 = τ 2 := by
    by_contra hn
    have hh := hH 1 2 hn
    rw [codegree12] at hh
    omega
  have hh := hL 0 2 (by decide) (h01.trans h12)
  rw [codegree02] at hh
  omega

lemma free_cone : Erdos713GlobalTheta.pattern.Free (Erdos713C6.bipGraph (cone small)) :=
  Erdos713ThetaConeGraph.cone_free small_no_theta small_rigid

#print axioms no_partition
#print axioms free_cone
end Erdos713ThetaClusterObstruction
