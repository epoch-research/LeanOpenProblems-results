def bad (n : Nat) : Empty := bad (n + 1)
termination_by n
