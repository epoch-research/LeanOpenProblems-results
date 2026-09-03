import Submission.DoubledPetersenCertificate

/-! Verification of the circuit-type data in the doubled Petersen certificate. -/
open SimpleGraph
namespace Erdos184
namespace DoubledPetersenCertificate

def ends : Fin 15 → Fin 10 × Fin 10 :=
  ![(0,1),(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9)]

def tours : Fin 72 → List (Fin 10) :=
  ![[0,1,2,3,4],
    [0,1,2,3,4,9,6,8,5],
    [0,1,2,3,4,9,7,5],
    [0,1,2,3,8,5],
    [0,1,2,3,8,5,7,9,4],
    [0,1,2,3,8,6,9,4],
    [0,1,2,3,8,6,9,7,5],
    [0,1,2,7,5],
    [0,1,2,7,5,8,3,4],
    [0,1,2,7,5,8,6,9,4],
    [0,1,2,7,9,4],
    [0,1,2,7,9,4,3,8,5],
    [0,1,2,7,9,6,8,3,4],
    [0,1,2,7,9,6,8,5],
    [0,1,6,8,3,2,7,5],
    [0,1,6,8,3,2,7,9,4],
    [0,1,6,8,3,4],
    [0,1,6,8,3,4,9,7,5],
    [0,1,6,8,5],
    [0,1,6,8,5,7,2,3,4],
    [0,1,6,8,5,7,9,4],
    [0,1,6,9,4],
    [0,1,6,9,4,3,2,7,5],
    [0,1,6,9,4,3,8,5],
    [0,1,6,9,7,2,3,4],
    [0,1,6,9,7,2,3,8,5],
    [0,1,6,9,7,5],
    [0,1,6,9,7,5,8,3,4],
    [0,4,3,2,1,6,8,5],
    [0,4,3,2,1,6,9,7,5],
    [0,4,3,2,7,5],
    [0,4,3,2,7,9,6,8,5],
    [0,4,3,8,5],
    [0,4,3,8,6,1,2,7,5],
    [0,4,3,8,6,9,7,5],
    [0,4,9,6,1,2,3,8,5],
    [0,4,9,6,1,2,7,5],
    [0,4,9,6,8,3,2,7,5],
    [0,4,9,6,8,5],
    [0,4,9,7,2,1,6,8,5],
    [0,4,9,7,2,3,8,5],
    [0,4,9,7,5],
    [1,2,3,4,9,6],
    [1,2,3,4,9,7,5,8,6],
    [1,2,3,8,5,7,9,6],
    [1,2,3,8,6],
    [1,2,7,5,8,3,4,9,6],
    [1,2,7,5,8,6],
    [1,2,7,9,4,3,8,6],
    [1,2,7,9,6],
    [2,3,4,9,6,8,5,7],
    [2,3,4,9,7],
    [2,3,8,5,7],
    [2,3,8,6,9,7],
    [3,4,9,6,8],
    [3,4,9,7,5,8],
    [5,7,9,6,8],
    [0,1],
    [0,4],
    [0,5],
    [1,2],
    [1,6],
    [2,3],
    [2,7],
    [3,4],
    [3,8],
    [4,9],
    [5,7],
    [5,8],
    [6,8],
    [6,9],
    [7,9]]

def cycleEdges (i : Fin 72) : List (Sym2 (Fin 10)) :=
  ((tours i).zip ((tours i).tail ++ [(tours i).headD 0])).map (fun p => s(p.1,p.2))

lemma tours_nodup (i : Fin 72) : (tours i).Nodup := by revert i; decide

lemma tours_length (i : Fin 72) : 2 ≤ (tours i).length ∧ (tours i).length ≤ 9 := by
  revert i; decide

set_option maxRecDepth 10000 in
lemma cycleEdges_valid (i : Fin 72) :
    ∀ e ∈ cycleEdges i, ∃ j : Fin 15, e = s((ends j).1,(ends j).2) := by
  revert i; decide

set_option maxRecDepth 10000 in
lemma digit_eq_edge_count (i : Fin 72) (e : Fin 15) :
    digit i e = (cycleEdges i).count s((ends e).1,(ends e).2) := by
  revert i e; decide

end DoubledPetersenCertificate
end Erdos184
