import FormalConjectures.Util.ProblemImports

example : False := by
  have h : (True : Prop) = False := by
    -- should be impossible: propext needs iff
    fail_if_success exact propext (Iff.intro (fun _ => False.elim (by contradiction)) (fun h => trivial))
    aesop
  cases h
