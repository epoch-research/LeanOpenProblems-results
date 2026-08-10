import FormalConjectures.Util.ProblemImports
-- Try indexed inductives with impossible indices and recursors
inductive Bad : Nat → Prop where
| mk : Bad 1

example : ¬ Bad 0 := by intro h; cases h
-- no contradiction directly

-- Can noConfusion produce arbitrary prop from equality of constructors? no
#check Bad.noConfusion
