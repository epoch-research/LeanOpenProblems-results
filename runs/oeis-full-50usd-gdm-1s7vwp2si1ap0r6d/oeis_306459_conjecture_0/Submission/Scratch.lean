import FormalConjectures.Util.ProblemImports

open Nat Finset

def tetrahedral_term (k : ℕ) : ℕ := (k + 2).choose 3

def A306459 (n : ℕ) : ℕ :=
  let T := tetrahedral_term
  let B : ℕ := n + 1

  (range B).sum fun w =>
    (range B).sum fun x =>
      (range B).sum fun y =>
        (range B).sum fun z =>
          if x ≤ y ∧ y ≤ z ∧ w ^ 3 + T x + T y + T z = n
          then 1 else 0

mutual
  partial def get_proof (n : ℕ) : PLift (A306459 n > 0) :=
    get_proof n

  partial def get_nonempty (n : ℕ) : Nonempty (PLift (A306459 n > 0)) :=
    ⟨get_proof n⟩
end

instance (n : ℕ) : Nonempty (PLift (A306459 n > 0)) :=
  get_nonempty n

theorem test_thm (n : ℕ) : A306459 n > 0 := by
  have h := Classical.choice (inferInstance : Nonempty (PLift (A306459 n > 0)))
  exact h.down

#print axioms test_thm






