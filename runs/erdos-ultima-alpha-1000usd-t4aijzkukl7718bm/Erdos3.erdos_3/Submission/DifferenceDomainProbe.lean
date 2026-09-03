import Submission.UniformLocalQuadraticInverse
open Finset
open scoped Pointwise
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
example (A B C D : Finset G) : (A-B)+(C-D)=(A+C)-(B+D) := by
  simp only [sub_eq_add_neg,neg_add_rev,add_assoc,add_comm,add_left_comm]
#check neg_nsmul
#check neg_nsmul_comm
#synth AddCommMonoid (Finset G)
example (A : Finset G) (n : ℕ) : n • (A-A) = n • A-n • A := by
  rw [sub_eq_add_neg,sub_eq_add_neg,nsmul_add]
  congr 1
  induction n with
  | zero => simp
  | succ n ih => simpa only [add_nsmul,one_nsmul,neg_add_rev,ih] using add_comm (n • -A) (-A)
