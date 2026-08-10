import FormalConjectures.Util.ProblemImports

#check Part.get_eq_get
#check Part.get_mem
#check Part.eq_get_iff_mem
#check Part.dom_iff_mem
#check Part.some.inj
#print Part
#print Part.Mem

-- Test if suspicious theorem can equate two different `some`s.
example : Part.some (0 : ℕ) = Part.some 1 := by
  apply Part.get_eq_get (a := Part.some (0:ℕ)) (b := Part.some 1)
  · simp
  · simp

example : False := by
  have h : Part.some (0 : ℕ) = Part.some 1 := by
    apply Part.get_eq_get (a := Part.some (0:ℕ)) (b := Part.some 1)
    · simp
    · simp
  have hval : (0 : ℕ) = 1 := by
    simpa using congrArg (fun p => p.get (by simpa [h])) h
  norm_num at hval
