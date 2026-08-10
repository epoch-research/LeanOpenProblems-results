import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

example (P : Prop) : P := by
  letI : Decidable P := loopDec P
  try decide
  try simp
  try by_cases h : P
  · try assumption
  · try contradiction
  all_goals trace_state
  all_goals sorry

example (P : Prop) : ¬ P := by
  letI : Decidable P := loopDec P
  try decide
  try simp
  try by_cases h : P
  · try assumption
  · try contradiction
  all_goals trace_state
  all_goals sorry
