import FormalConjecturesUtil
example (m : ℕ) (j : Fin (m+2)) : j-1+1=j := by
  exact sub_add_cancel j 1
example (m : ℕ) (j : Fin (m+2)) (h : j-1=j) : j=j+1 := by
  have h' := congrArg (fun x : Fin (m+2) => x+1) h
  simpa only [sub_add_cancel] using h'
