import FormalConjectures.Util.ProblemImports

def IsSquare_eval (n : ℕ) : Bool :=
  (List.range (n + 1)).any (fun i => i * i == n)

theorem IsSquare_eval_iff (n : ℕ) : IsSquare n ↔ IsSquare_eval n = true := by
  sorry

-- Let's check if IsSquare_eval reduces definitionally
theorem test_sq_9 : IsSquare_eval 9 = true := by rfl
theorem test_sq_10 : IsSquare_eval 10 = false := by rfl
