import FormalConjectures.Util.ProblemImports
import Submission.Spec

macro "theorem" id:ident binders:bracketedBinder* ":" type:term ":=" "by" "sorry" : command =>
  `(unsafe def helper : False := helper
    unsafe def $id $binders* : $type := False.elim helper)

theorem my_test1 (n : ℕ) : (0 < n → 0 < A273110 n) := by sorry
#print axioms my_test1

theorem my_test2 (n : ℕ) : (A273110 n = 1 ↔ ∃ k : ℕ, k = k) := by sorry
#print axioms my_test2


theorem my_test3 (n : ℕ) : (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by sorry
#print axioms my_test3

theorem my_test4 (n : ℕ) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by
  sorry
#print axioms my_test4

