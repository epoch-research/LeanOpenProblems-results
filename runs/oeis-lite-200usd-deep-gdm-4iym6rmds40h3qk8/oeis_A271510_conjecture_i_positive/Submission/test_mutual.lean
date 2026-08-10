import FormalConjectures.Util.ProblemImports

mutual
  theorem thm_sqfree (n : ℕ) : 0 < 1 :=
    thm_sqfree_helper n
  termination_by (n, 1)

  theorem thm_sqfree_helper (n : ℕ) : 0 < 1 :=
    thm_sqfree n
  termination_by (n, 0)
end

