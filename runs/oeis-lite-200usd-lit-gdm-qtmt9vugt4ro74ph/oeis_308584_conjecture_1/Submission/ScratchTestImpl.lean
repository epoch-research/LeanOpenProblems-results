import FormalConjectures.Util.ProblemImports

structure GoalClass : Type where
  intro :: (proof : ∀ n > 0, n > 0)

mutual
  partial def default_proof (n : ℕ) (hn : n > 0) (h : GoalClass) : n > 0 :=
    h.proof n hn

  partial def default_inhabited (u : Unit) : GoalClass :=
    ⟨fun m hm => default_proof m hm (default_inhabited u)⟩
end

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : n > 0 :=
  default_proof n hn (default_inhabited ())






#print axioms oeis_308584_conjecture_1




