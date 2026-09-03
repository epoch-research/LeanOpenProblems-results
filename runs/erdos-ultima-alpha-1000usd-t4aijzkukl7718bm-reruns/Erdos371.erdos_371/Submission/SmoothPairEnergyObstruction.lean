import FormalConjecturesUtil

/-! A finite counterexample to an energy bound based only on S-unit support.
It is not a counterexample to the Erdős 371 density conjecture. -/

namespace Erdos371SmoothPairEnergyObstruction

abbrev P := Nat.maxPrimeFac

def pairs (s : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n =>
    0 < n ∧ n.primeFactors ⊆ s ∧ (n+1).primeFactors ⊆ s

def group (s : Finset ℕ) (p N : ℕ) : ℤ :=
  ∑ n ∈ pairs s N, if max (P n) (P (n+1)) = p then
    (if P n < P (n+1) then 1 else -1) else 0

def energy (s : Finset ℕ) (N : ℕ) : ℤ := ∑ p ∈ s, (group s p N)^2

lemma pairs_257 : pairs {2,5,7} 50 = {1,4,7,49} := by decide +kernel

lemma groups_257 : group {2,5,7} 2 50 = 1 ∧
    group {2,5,7} 5 50 = 1 ∧ group {2,5,7} 7 50 = -2 := by
  decide +kernel

lemma energy_257 : energy {2,5,7} 50 = 6 := by decide +kernel

lemma total_257_zero : (∑ p ∈ ({2,5,7} : Finset ℕ), group {2,5,7} p 50) = 0 := by
  decide +kernel

/-- S-unit support alone does not bound the energy by the number of pairs. -/
theorem support_energy_bound_fails :
    ¬ ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∀ N : ℕ,
      energy s N ≤ (pairs s N).card := by
  intro h
  have hh := h {2,5,7} (by decide +kernel) 50
  rw [energy_257, pairs_257] at hh
  norm_num at hh

end Erdos371SmoothPairEnergyObstruction

#print axioms Erdos371SmoothPairEnergyObstruction.pairs_257
#print axioms Erdos371SmoothPairEnergyObstruction.support_energy_bound_fails
