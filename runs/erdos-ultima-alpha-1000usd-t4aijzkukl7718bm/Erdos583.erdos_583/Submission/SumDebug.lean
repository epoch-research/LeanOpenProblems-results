import Submission.Work
open SimpleGraph Erdos583Work
open scoped Classical
example (p : Fin 11 → Prop) :
    (∑ w ∈ ({2,4,9} : Finset (Fin 11)), if p w then 1 else 0 : ℕ)=
      (if p 2 then 1 else 0)+((if p 4 then 1 else 0)+(if p 9 then 1 else 0)) := by
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
example (p : Fin 11 → Prop) :
    (∑ w ∈ ({2,4,9} : Finset (Fin 11)), if p w then 1 else 0 : ℕ)=
      (if p 2 then 1 else 0)+((if p 4 then 1 else 0)+(if p 9 then 1 else 0)) := by
  simp [-Finset.sum_boole]
