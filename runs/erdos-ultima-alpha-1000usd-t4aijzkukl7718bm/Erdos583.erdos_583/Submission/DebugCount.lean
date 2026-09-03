import Submission.RootLocality
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
set_option maxHeartbeats 1600000
example {G : SimpleGraph (Fin 11)} (S : TrailFamily G 2) {i j : Fin 2} (hij : i ≠ j)
    {v : Fin 11} (hq : S.quota v=1)
    (hi : v=S.start i ∨ v=S.finish i) (hj : v=S.start j ∨ v=S.finish j) : False := by
  have hs := quota_eq_sum_endpoints S v
  rw [hq,Fin.sum_univ_two] at hs
  fin_cases i <;> fin_cases j
  all_goals try exact hij rfl
  all_goals rcases hi with hi|hi <;> rcases hj with hj|hj
  all_goals trace_state
  all_goals simp only [←hi,←hj,↓reduceIte] at hs; omega
#check Nat.eq_of_mul_eq_mul_left
#check Finset.sum_insert
