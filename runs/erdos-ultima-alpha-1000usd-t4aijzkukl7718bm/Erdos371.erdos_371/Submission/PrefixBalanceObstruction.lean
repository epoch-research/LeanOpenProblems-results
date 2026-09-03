import Submission.Explore

/-! A finite check ruling out a possible prefix-monotonicity shortcut.
This is not a disproof of the density conjecture. -/

namespace Erdos371

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prefix_3913_counts : risingCount 3913 = 1955 ∧ fallingCount 3913 = 1958 := by
  decide +kernel

/-- The signed comparison count is not nonnegative at every endpoint.
The range here includes n=0, as in the original density formulation. -/
lemma not_all_prefixes_rise_dominant : ¬ ∀ N, fallingCount N ≤ risingCount N := by
  intro h
  have hb := h 3913
  rw [prefix_3913_counts.1,prefix_3913_counts.2] at hb
  omega


/-- Four prime labels can already give a prefix discrepancy larger than four.
This concerns the finite prime-cutoff model, not the original comparison. -/
lemma cutoff_210_prefix_45_counts :
    ((Finset.range 45).filter fun n => cutoffPrime 210 n < cutoffPrime 210 (n + 1)).card = 25 ∧
    ((Finset.range 45).filter fun n => cutoffPrime 210 (n + 1) < cutoffPrime 210 n).card = 20 ∧
    (210 : ℕ).primeFactors.card = 4 := by
  decide +kernel

/-- The discrepancy bound by the number of prime labels is false, even for
positive even squarefree moduli. No density claim is negated here. -/
lemma not_cutoff_prefix_bound_by_prime_count :
    ¬ ∀ M N : ℕ, 0 < M → 2 ∣ M → Squarefree M →
      (((Finset.range N).filter fun n => cutoffPrime M n < cutoffPrime M (n + 1)).card : ℤ) -
        (((Finset.range N).filter fun n => cutoffPrime M (n + 1) < cutoffPrime M n).card : ℤ) ≤
          M.primeFactors.card := by
  intro h
  have he := h 210 45 (by decide) (by decide) (by decide +kernel)
  rw [cutoff_210_prefix_45_counts.1, cutoff_210_prefix_45_counts.2.1,
    cutoff_210_prefix_45_counts.2.2] at he
  norm_num at he

#print axioms cutoff_210_prefix_45_counts
#print axioms not_cutoff_prefix_bound_by_prime_count

#print axioms prefix_3913_counts
#print axioms not_all_prefixes_rise_dominant
end Erdos371
