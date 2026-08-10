import FormalConjectures.Util.ProblemImports
open Nat

def good (n k : ℕ) : Prop :=
  Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

instance (n k : ℕ) : Decidable (good n k) := by unfold good; infer_instance

-- Bounded exhaustive search is definable.
def findWitness? (n : ℕ) : Option ℕ :=
  ((List.range (3 ^ n + 1)).find? (fun k => good n k))

#eval findWitness? 1
#eval findWitness? 2
#eval findWitness? 10

-- If the search returns a value, proving the theorem is easy.
lemma exists_of_findWitness?_eq_some {n k : ℕ} (h : findWitness? n = some k) : ∃ k, good n k := by
  unfold findWitness? at h
  have hm := List.find?_some.mp h
  exact ⟨k, hm.2⟩

-- But proving it returns `some` for every positive n is exactly the conjecture.
#check exists_of_findWitness?_eq_some
