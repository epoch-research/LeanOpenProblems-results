import FormalConjecturesUtil
import Submission.UpToSuspension

/-! A verified containment between two unresolved eight-vertex cases.
This does not assert either missing extremal bound. -/
open Filter SimpleGraph Asymptotics
namespace Erdos713EightRefinement
open Erdos713EightCore

lemma seventeen_contained_twenty_three :
    Graph (representative 17) ⊑ Graph (representative 23) :=
  contained_of_map _ _ (Sum.elim
    (fun i => Sum.inl ((![0,1,3,2] : Fin 4 → Fin 4) i))
    (fun j => Sum.inr j)) (by decide) (by decide)

lemma seventeen_rate_of_twenty_three_upper
    (h : (fun n : ℕ => (extremalNumber n (Graph (representative 23)) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)^((3 : ℝ)/2))) :
    Erdos713Rate.HasRate (Graph (representative 17)) ((3 : ℝ)/2) :=
  Erdos713Rate.rate_of_C4_upper
    (middle_containments 17 (by decide) (by decide) (by decide)).1
    ((Erdos713Rate.extremal_mono_bigO seventeen_contained_twenty_three).trans h)

#print axioms seventeen_contained_twenty_three
#print axioms seventeen_rate_of_twenty_three_upper
end Erdos713EightRefinement
