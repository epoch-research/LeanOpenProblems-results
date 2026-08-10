import FormalConjectures.Util.ProblemImports

example : False := by
  let rec inst : Subsingleton Prop := { allEq := fun P Q => @Subsingleton.elim Prop inst P Q }
  letI := inst
  have h : True = False := Subsingleton.elim True False
  exact Eq.mp h trivial
