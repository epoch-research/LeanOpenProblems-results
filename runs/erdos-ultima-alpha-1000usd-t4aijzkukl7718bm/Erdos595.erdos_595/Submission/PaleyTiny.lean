import Submission.TriangleHit
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option profiler true

def adjacentTiny (a b : Fin 17) : Prop :=
  (a.val + 17 - b.val) % 17 ∈ ([1, 2, 4, 8, 9, 13, 15, 16] : List ℕ)
#check adjacentTiny
instance : DecidableRel adjacentTiny := fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List ℕ)))
#check adjacentTiny
example : ∀ a b, adjacentTiny a b → adjacentTiny b a := by decide +kernel
#check adjacentTiny
