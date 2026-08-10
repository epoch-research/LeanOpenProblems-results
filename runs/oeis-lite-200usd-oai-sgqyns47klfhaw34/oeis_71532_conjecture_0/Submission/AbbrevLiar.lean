import FormalConjectures.Util.ProblemImports

-- Direct abbreviations / definitions
abbrev L : Prop := ¬ L
#check L
example : False := Mathlib.Tactic.CC.false_of_a_eq_not_a (a:=L) rfl
