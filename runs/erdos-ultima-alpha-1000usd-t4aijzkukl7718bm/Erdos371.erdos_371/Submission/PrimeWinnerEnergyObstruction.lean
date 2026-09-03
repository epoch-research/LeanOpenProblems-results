import FormalConjecturesUtil

/-! A reordered-prime example. The maximum-under-multiplication identity alone
does not give the candidate energy bound with constant one. This is not an
example for the natural ordering of primes and does not disprove Erdős 371. -/

namespace Erdos371.PrimeWinnerEnergyObstruction

/-- The prime 3 is placed above small primes congruent to 2 modulo 3, and
below every prime congruent to 1 modulo 3. -/
def rank (p : ℕ) : ℕ :=
  if p = 3 then 10243 else if p % 3 = 1 then 2 * (5122 + p) + 1 else 2 * p

lemma rank_injective : Function.Injective rank := by
  intro p q h
  unfold rank at h
  split_ifs at h <;> omega

def label (n : ℕ) : ℕ := n.primeFactors.sup rank

lemma label_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    label (a * b) = max (label a) (label b) := by
  simp only [label, Nat.primeFactors_mul ha hb, Finset.sup_union]

def groupRises (p N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => max (label n) (label (n + 1)) = rank p ∧
    label n < label (n + 1)).card

def groupFalls (p N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => max (label n) (label (n + 1)) = rank p ∧
    label (n + 1) < label n).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma group_three_counts : groupRises 3 5121 = 319 ∧ groupFalls 3 5121 = 247 := by
  decide +kernel

/-- One group already exceeds the entire proposed energy budget N. -/
lemma single_group_energy_exceeds_N :
    ((groupRises 3 5121 : ℤ) - groupFalls 3 5121) ^ 2 > 5121 := by
  rw [group_three_counts.1, group_three_counts.2]
  norm_num

#print axioms rank_injective
#print axioms label_mul
#print axioms group_three_counts
#print axioms single_group_energy_exceeds_N

end Erdos371.PrimeWinnerEnergyObstruction
