import Submission.Scratch

-- Here, "a" refers to the original "a", because local notation is not exported.
#check a

-- Let's see if we can assign the theorem to the expected type using the original "a".
example : a 254602 = -1 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 254602 → a n ≠ -1) := oeis_a108129_conjecture_0
