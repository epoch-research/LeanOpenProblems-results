import FormalConjectures.Util.ProblemImports
macro "round " x:term : term => `(Int.ofNat 0)
#check round (3:ℝ)
#check (round (3:ℝ)).toNat
example : (round (3:ℝ)).toNat = 0 := rfl
