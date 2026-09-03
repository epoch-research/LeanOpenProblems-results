import FormalConjecturesUtil

/-! A finite test of a proposed bound using only max-under-multiplication.
All prime factors are included; only their ranks are changed. This is not
a counterexample to the conjecture with the natural ordering of primes. -/

namespace Erdos371.FullRankingPrefixCheck

def rank (p : ℕ) : ℕ :=
  if p=11 then 13 else if p=31 then 12 else if p=41 then 11 else
  if p=5 then 10 else if p=29 then 9 else if p=7 then 8 else
  if p=13 then 7 else if p=19 then 6 else if p=37 then 5 else
  if p=3 then 4 else if p=17 then 3 else if p=2 then 2 else
  if p=23 then 1 else p+14

def label (n : ℕ) : ℕ := n.primeFactors.sup rank

lemma label_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    label (a*b) = max (label a) (label b) := by
  simp only [label, Nat.primeFactors_mul ha hb, Finset.sup_union]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rank_injective : Function.Injective rank := by
  have hs : Function.Injective (fun p : Fin 42 => rank p) := by decide +kernel
  have hb : ∀ p : Fin 42, rank p < 56 := by decide +kernel
  have hl (p : ℕ) (hp : 42 ≤ p) : rank p = p + 14 := by
    simp only [rank, if_neg (show p ≠ 11 by omega),
      if_neg (show p ≠ 31 by omega), if_neg (show p ≠ 41 by omega),
      if_neg (show p ≠ 5 by omega), if_neg (show p ≠ 29 by omega),
      if_neg (show p ≠ 7 by omega), if_neg (show p ≠ 13 by omega),
      if_neg (show p ≠ 19 by omega), if_neg (show p ≠ 37 by omega),
      if_neg (show p ≠ 3 by omega), if_neg (show p ≠ 17 by omega),
      if_neg (show p ≠ 2 by omega), if_neg (show p ≠ 23 by omega)]
  intro p q h
  by_cases hp : p < 42 <;> by_cases hq : q < 42
  · exact congrArg Fin.val (hs (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩) h)
  · have := hb ⟨p, hp⟩
    rw [hl q (by omega)] at h
    dsimp only at this
    omega
  · have := hb ⟨q, hq⟩
    rw [hl p (by omega)] at h
    dsimp only at this
    omega
  · rw [hl p (by omega), hl q (by omega)] at h
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma full_ranking_prefix_counts :
    ((Finset.range 40).filter (fun n => label (n+1) < label (n+2))).card = 28 ∧
    ((Finset.range 40).filter (fun n => label (n+2) < label (n+1))).card = 12 ∧
    (42 : ℕ).primesBelow.card = 13 := by
  decide +kernel

/-- The discrepancy exceeds the number of all available prime labels,
not merely the number in a truncated factorization model. -/
lemma full_ranking_discrepancy_exceeds_prime_count :
    (((Finset.range 40).filter (fun n => label (n+1) < label (n+2))).card : ℤ) -
      ((Finset.range 40).filter (fun n => label (n+2) < label (n+1))).card >
        (42 : ℕ).primesBelow.card := by
  rw [full_ranking_prefix_counts.1, full_ranking_prefix_counts.2.1,
    full_ranking_prefix_counts.2.2]
  norm_num

#print axioms rank_injective
#print axioms full_ranking_discrepancy_exceeds_prime_count
end Erdos371.FullRankingPrefixCheck
