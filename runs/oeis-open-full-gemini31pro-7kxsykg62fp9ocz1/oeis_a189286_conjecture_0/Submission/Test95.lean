import Submission.Spec
open Nat Finset

lemma type_of_lemma_proof : (type_of% @oeis_a189286_conjecture_0) = ∀ (n : ℕ),
  if n = 0 then True else
    have numerator_int : ℤ := ∑ k ∈ Finset.range (n + 1), ↑(T_term k) * ↑(T_term (n - k));
    have denominator : ℤ := (2 * ↑n - 1) * ↑((3 * n).choose n);
    denominator ∣ numerator_int := rfl

theorem disproof_test : ¬ (type_of% @oeis_a189286_conjecture_0) := by
  -- Can we prove this?
  -- We know the conjecture is TRUE up to n=199,999.
  -- Wait! Is it TRUE for all n?
  -- A189286: Sun conjectured this. Zhi-Wei Sun proved many congruences.
  -- This is a well-known conjecture. Did anyone prove it?
  sorry
