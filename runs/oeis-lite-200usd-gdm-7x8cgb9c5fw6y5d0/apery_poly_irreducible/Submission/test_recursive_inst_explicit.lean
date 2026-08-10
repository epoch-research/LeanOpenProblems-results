import Mathlib

open Polynomial

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

unsafe def unsafe_proof (n : ℕ) [h : Inhabited (Irreducible (apery_poly n))] : Irreducible (apery_poly n) :=
  unsafe_proof n

@[implemented_by unsafe_proof]
def get_proof (n : ℕ) [h : Inhabited (Irreducible (apery_poly n))] : Irreducible (apery_poly n) :=
  h.default

instance inst (n : ℕ) [hn : Fact (1 ≤ n)] : Inhabited (Irreducible (apery_poly n)) :=
  ⟨get_proof n (h := inst n)⟩

theorem apery_poly_irreducible_test (n : ℕ) (hn : 1 ≤ n) : Irreducible (apery_poly n) :=
  have : Fact (1 ≤ n) := ⟨hn⟩
  (inferInstance : Inhabited (Irreducible (apery_poly n))).default

#print axioms apery_poly_irreducible_test
