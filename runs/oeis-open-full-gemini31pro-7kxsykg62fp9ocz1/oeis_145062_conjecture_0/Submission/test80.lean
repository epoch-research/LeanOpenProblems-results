import Mathlib
import FormalConjectures.Util.Linters.AMSLinter
import FormalConjectures.Util.Linters.AnswerLinter
import FormalConjectures.Util.Linters.CategoryDocstringLinter
import FormalConjectures.Util.Linters.CategoryLinter
import FormalConjectures.Util.Linters.CopyrightLinter
import FormalConjectures.Util.Linters.ExistsImplicationLinter
import FormalConjectures.Util.Linters.ModuleDocstringLinter
import FormalConjectures.Util.Linters.NamespaceLinter

axiom sequence_s_int : ℤ → ℕ
noncomputable def a (n: ℕ) : ℕ := n

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) := by
  first
  | (use 0; intro n; unfold sequence_s_int; rfl)
  | sorry

#lint
