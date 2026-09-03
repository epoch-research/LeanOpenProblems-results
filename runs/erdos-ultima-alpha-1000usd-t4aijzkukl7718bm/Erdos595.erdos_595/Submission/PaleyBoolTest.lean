import Submission.TriangleHit
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option profiler true

def adjacentTinyB (a b : Fin 17) : Prop :=
  (a.val + 17 - b.val) % 17 ∈ ([1, 2, 4, 8, 9, 13, 15, 16] : List ℕ)
instance : DecidableRel adjacentTinyB := fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List ℕ)))
def vs : List (Fin 17) := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]
example : vs.all (fun a => vs.all (fun b => vs.all (fun c => vs.all (fun d =>
    decide (¬(adjacentTinyB a b ∧ adjacentTinyB a c ∧ adjacentTinyB a d ∧
      adjacentTinyB b c ∧ adjacentTinyB b d ∧ adjacentTinyB c d)))))) = true := by decide +kernel
