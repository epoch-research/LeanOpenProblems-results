import FormalConjectures.Util.ProblemImports
-- all of these should be rejected if negative/self references are unsafe
inductive Bad1 : Prop where
| intro : (Bad1 → False) → Bad1

inductive Bad2 : Prop where
| intro : ((Bad2 → False) → False) → Bad2

inductive Bad3 : Type where
| intro : (Bad3 → Empty) → Bad3
