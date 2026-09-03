import Submission.PaleyData
example : (Fin.succ (2 : Fin 15)).succ = (4 : Fin 17) := rfl
example (f : Fin 17 → ℝ) : f (Fin.succ (2 : Fin 15)).succ = f 4 := by rfl
example (f : Fin 17 → ℝ) : f (Fin.succ (2 : Fin 15)).succ = f 4 := by ring!
#check Fin.ofNat'
#check Fin.mk_val
#check Fin.succ_mk
#check Fin.mk_ofNat
