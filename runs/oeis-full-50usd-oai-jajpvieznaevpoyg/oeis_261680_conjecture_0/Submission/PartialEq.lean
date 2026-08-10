import FormalConjectures.Util.ProblemImports
partial def countdown (n : Nat) : Nat := if n = 0 then 0 else countdown (n-1)
#check countdown.eq_def
#check countdown
#print countdown
