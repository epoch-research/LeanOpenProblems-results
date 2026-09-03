import FormalConjecturesUtil
import Submission.GlobalThetaLinks
import Submission.ThetaRigidZeroCapped

/-! Actual apex-theta-free cone hosts realizing the local zero-pair
counterexamples. Neither almost-regularity nor exact extremality is claimed. -/
open SimpleGraph
namespace Erdos713ThetaConeGraph
open Erdos713ThetaGram Erdos713ThetaThreePoint Erdos713ThetaConeLinks
open Erdos713ThetaRigidZeroCapped Erdos713ThetaZeroPairs
set_option maxHeartbeats 2000000

lemma cone_free {A B : Type*} {R : A → B → Prop}
    (hR : ¬ HasTheta R) (hRigid : Rigid3 R) :
    Erdos713GlobalTheta.pattern.Free (Erdos713C6.bipGraph (cone R)) := by
  apply (Erdos713GlobalTheta.free_iff_both_links (cone R)).mpr
  exact both_links hR hRigid

/-- The local relation is precisely the punctured link at the added row,
under the canonical bijections on its two vertex sets. -/
lemma link_at_apex {A B : Type*} (R : A → B → Prop) (a : A) (b : B) :
    Erdos713GlobalTheta.link (cone R) none
      ⟨some a,by simp⟩ ⟨b,trivial⟩ ↔ R a b := Iff.rfl

theorem exists_free_cone_counterexample (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      Erdos713GlobalTheta.pattern.Free (Erdos713C6.bipGraph (cone R)) ∧
      (zeroSet R).card ≤ Nat.card A ∧
      (∀ b, Nat.card {a // R a b} ≤ 2*Nat.card B) ∧
      (N : ℝ)*((Nat.card A : ℝ)+(Nat.card B : ℝ)*Real.sqrt (Nat.card A)) <
        (Nat.card {p : A × B // R p.1 p.2} : ℝ) := by
  obtain ⟨A,B,hA,hB,R,hR,hRigid,hZ,hD,hE⟩ := exists_rigid_counterexample N
  exact ⟨A,B,hA,hB,R,cone_free hR hRigid,hZ,hD,hE⟩

#print axioms cone_free
#print axioms exists_free_cone_counterexample
end Erdos713ThetaConeGraph
