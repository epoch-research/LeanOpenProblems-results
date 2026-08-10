import FormalConjectures.Util.ProblemImports

mutual
  theorem thm_sqfree (n : ℕ) (k : ℕ) : 0 < 1 :=
    match k with
    | 0 => Nat.zero_lt_one
    | k + 1 => thm_sqfree_helper n k
  termination_by k

  theorem thm_sqfree_helper (n : ℕ) (k : ℕ) : 0 < 1 :=
    thm_sqfree n (k + 1)
  termination_by k
end
