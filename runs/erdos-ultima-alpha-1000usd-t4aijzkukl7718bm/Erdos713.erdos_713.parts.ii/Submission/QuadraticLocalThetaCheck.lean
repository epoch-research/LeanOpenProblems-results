import FormalConjecturesUtil
import Submission.QuadraticLocalObstruction
import Submission.ThetaGram

/-! This distinguishes the full quadratic family from a theta-free family. -/
namespace Erdos713QuadraticLocal
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
lemma five_contains_theta : Erdos713ThetaGram.HasTheta (incidence (F := ZMod 5)) := by
  let a : Fin 3 → Rows (ZMod 5) := ![(0,0,0),(0,-1,1),(-2,1,0)]
  let b : Fin 4 → Cols (ZMod 5) := ![(0,0),(1,0),(2,0),(3,1)]
  refine ⟨a,b,by decide,by decide,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp [incidence,value,a,b]; decide
#print axioms five_contains_theta
end Erdos713QuadraticLocal
