import Submission.IntervalRecursiveSieve

/-! A finite kernel-checked test of the interval-aware recurrence. It bounds
this particular set of fifty primes, not all sets with fifty prime factors. -/
namespace Erdos970.IntervalRescaling

private def examplePrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
   83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
   173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229]

private def exampleModulus (i : ℕ) : ℕ := examplePrimes.getD i 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first_fifty_interval_envelope_positive :
    0 < (intervalEnvelope exampleModulus 0 id id
      (fun k m => decide (k < m)) 50 5000).1 := by
  decide +kernel

/-- The rescaling theorem and the computed envelope give an actual survivor for
these fifty specified primes and every choice of their residues. -/
theorem first_fifty_interval_survivor (r : ℕ → ℕ) :
    ∃ x < 5000, ∀ i < 50, ¬x ≡ r i [MOD exampleModulus i] := by
  have hmod : ∀ i : Fin 50, 0 < exampleModulus i ∧
      ∀ j : Fin 50, j.val < i.val → (exampleModulus i).Coprime (exampleModulus j) := by
    decide +kernel
  exact survivor_of_positive_intervalEnvelope exampleModulus 0 id id
    (fun k m => decide (k < m))
    (by intros; simp [count]) (by intros; simp [count]) 50 (by omega)
    (fun i hi => (hmod ⟨i, hi⟩).1)
    (fun i hi j hj => (hmod ⟨i, hi⟩).2 ⟨j, hj.trans hi⟩ hj) 5000
    first_fifty_interval_envelope_positive r

#print axioms first_fifty_interval_envelope_positive
#print axioms first_fifty_interval_survivor
end Erdos970.IntervalRescaling
