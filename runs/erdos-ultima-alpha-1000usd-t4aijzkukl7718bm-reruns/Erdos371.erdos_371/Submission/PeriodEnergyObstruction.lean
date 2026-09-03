import FormalConjecturesUtil

/-! A finite obstruction to a uniform linear energy bound for arbitrary sets of
prime periods. This is not a counterexample to Erdős 371 or to an energy bound
for the actual largest-prime-factor function. -/

namespace Erdos371PeriodEnergyObstruction

def periods : Finset ℕ :=
  {2, 3, 503, 509, 521, 557, 563, 569, 587, 593, 599, 617, 641, 647, 653,
    659, 677, 683, 701, 719, 743, 761, 773, 797, 809, 821, 827, 839, 857,
    863, 881, 887, 911, 929, 941, 947, 953, 971, 977, 983}

def height (s : Finset ℕ) (n : ℕ) : ℕ :=
  if n = 0 then 0 else max 1 ((s.filter fun p => p ∣ n).sup id)

def sign (s : Finset ℕ) (n : ℕ) : ℤ :=
  if height s n < height s (n+1) then 1
  else if height s (n+1) < height s n then -1 else 0

def group (s : Finset ℕ) (p N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N,
    if max (height s n) (height s (n+1)) = p then sign s n else 0

def energy (s : Finset ℕ) (N : ℕ) : ℤ := ∑ p ∈ s, (group s p N)^2

lemma periods_prime : ∀ p ∈ periods, p.Prime := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
lemma group_two : group periods 2 985 = 38 := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
lemma group_three : group periods 3 985 = -38 := by decide +kernel

lemma two_large_groups_cancel : group periods 2 985 + group periods 3 985 = 0 := by
  rw [group_two, group_three]
  norm_num

lemma energy_exceeds_range : (985 : ℤ) < energy periods 985 := by
  have hh : (group periods 2 985)^2 ≤ energy periods 985 := by
    apply Finset.single_le_sum (f := fun p => (group periods p 985)^2)
    · intro p hp
      exact sq_nonneg _
    · decide +kernel
  rw [group_two] at hh
  norm_num at hh
  omega

/-- Prime periods alone do not give a uniform bound `energy ≤ N`. -/
theorem not_uniform_linear_energy :
    ¬ ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∀ N : ℕ, energy s N ≤ N := by
  intro h
  exact (not_le_of_gt energy_exceeds_range) (h periods periods_prime 985)

end Erdos371PeriodEnergyObstruction

#print axioms Erdos371PeriodEnergyObstruction.group_two
#print axioms Erdos371PeriodEnergyObstruction.group_three
#print axioms Erdos371PeriodEnergyObstruction.not_uniform_linear_energy
