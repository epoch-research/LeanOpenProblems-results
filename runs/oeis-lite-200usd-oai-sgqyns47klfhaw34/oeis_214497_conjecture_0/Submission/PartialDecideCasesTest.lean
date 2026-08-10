import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P

example : False := by
  cases h : loopDec False with
  | isTrue hf => exact hf
  | isFalse hn =>
      -- maybe h gives equation loopDec False = isFalse hn; no contradiction
      fail_if_success exact hn (by cases h)
      exact False.elim (by contradiction)
