import Submission.LabelKernelEmbedding
#synth Fintype (Equiv.Perm (Fin 4))
example : ∀ p : Equiv.Perm (Fin 4), p 0 ≠ p 1 := by decide +kernel
example : ∀ p : Equiv.Perm (Fin 3), ∀ j, p j ≠ p (j+1) := by decide +kernel
#print Equiv.Perm.fintype
