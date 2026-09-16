import Submission.Spec

set_option maxRecDepth 10000000

theorem test :
    let n_val : ℕ := 4551086841
    let S : ℕ → ℕ := A008347_seq
    let generalized_a := fun (n base_a base_b : ℕ) =>
      (Finset.range (n + 1)).sum fun i =>
        (Finset.range (n + 1)).sum fun j =>
          if base_a^i + base_b^j < n then
            ((Finset.range (2 * n + 2)).filter (fun k => k > 0 ∧ S k = n - (base_a^i + base_b^j))).card
          else
            0
    generalized_a n_val 2 12 = 0 := by
  intro n_val S generalized_a
  decide
