import Submission.PrimeTupleSmoothness

/-! Independent type and axiom checks for prime-input tuple smoothness. -/

example (A : Finset ℕ) (k : ℕ) (hk : 2 ≤ k) :
    {p : ℕ | ∃ a ∈ A, ∃ q : ℕ, q.Prime ∧ p=a*q+1 ∧
      (p-1+1).Prime ∧ ∀ r ∈ (p-1).primeFactors, r^k ≤ p-1}.Finite := by
  exact Erdos821.finite_root_smooth_prime_input_successors A k hk

example (a q j k : ℕ) (hq : q.Prime) (ha : a ≤ q^j)
    (hp : (a*q+1).Prime) (hs : ∀ r ∈ (a*q).primeFactors, r^k ≤ a*q) :
    k ≤ j+1 :=
  Erdos821.root_smooth_prime_input_order_bound a q j k hq ha ⟨hp, hs⟩

#print axioms Erdos821.root_smooth_prime_input_multiplier_bound
#print axioms Erdos821.root_smooth_prime_input_le_multiplier
#print axioms Erdos821.root_smooth_prime_input_successor_bound
#print axioms Erdos821.finite_root_smooth_prime_input_successors
#print axioms Erdos821.root_smooth_prime_input_order_bound
#print axioms Erdos821.root_smooth_successor_above_cutoff_power
