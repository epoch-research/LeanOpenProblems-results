import FormalConjecturesUtil
open Finset
#check ite_and
#check ite_mul
#check mul_ite
#check ite_congr
#check ite_mul_zero
#check mul_ite_zero
#print ite_and
example {V : Type*} [Fintype V] (P Q R : V → Prop) :
    (by classical exact ∑ v, if P v ∧ Q v ∧ R v then 1 else 0 : ℕ) =
    (by classical exact ∑ v, (if P v then 1 else 0)*(if Q v then 1 else 0)*(if R v then 1 else 0) : ℕ) := by
  classical
  simp only [ite_and, ite_mul, mul_ite, zero_mul, one_mul, mul_zero, mul_one]
