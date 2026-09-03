import FormalConjecturesUtil

/-! A finite obstruction to a proposed universal descent estimate for positive
completely additive functions. This is NOT a counterexample to Erdős 371.
It also does not refute an asymptotic half-bound or an allowance with an
arbitrary larger constant multiplying the prime count. -/

namespace Erdos371PositiveAdditiveFiniteObstruction

/-- Explicit positive integer weights. All unlisted prime weights are one. -/
def weight : ℕ → ℕ
  | 2 => 16
  | 3 => 15
  | 5 => 1
  | 7 => 10
  | 11 => 5
  | 13 => 36
  | 17 => 55
  | 19 => 41
  | 23 => 13
  | 29 => 39
  | 31 => 29
  | 37 => 58
  | 41 => 43
  | 43 => 39
  | 47 => 27
  | 53 => 62
  | 59 => 49
  | 61 => 46
  | 67 => 88
  | 71 => 79
  | 73 => 75
  | 79 => 66
  | 83 => 58
  | 89 => 48
  | 97 => 37
  | _ => 1

lemma weight_pos (p : ℕ) : 0 < weight p := by
  unfold weight
  split <;> norm_num

/-- The completely additive extension of the specified prime weights. -/
def height (n : ℕ) : ℕ := (n.primeFactorsList.map weight).sum

lemma height_one : height 1 = 0 := by
  simp [height]

lemma height_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    height (a*b) = height a + height b := by
  have h := ((Nat.perm_primeFactorsList_mul ha hb).map weight).sum_eq
  simpa [height, List.map_append] using h

lemma height_prime {p : ℕ} (hp : p.Prime) : height p = weight p := by
  simp [height, Nat.primeFactorsList_prime hp]

lemma height_prime_pos {p : ℕ} (hp : p.Prime) : 0 < height p := by
  rw [height_prime hp]
  exact weight_pos p

/-- Count the comparisons `f(n+1) < f(n)` for `1 ≤ n < N`. -/
def descents (f : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 (N-1)).filter fun n => f (n+1) < f n).card

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
lemma descents_hundred : descents height 100 = 79 := by
  decide +kernel

lemma primeCounting_hundred : Nat.primeCounting 100 = 25 := by
  decide +kernel

/-- The exact finite discrepancy is greater than twice the prime count. -/
theorem excess_gt_prime_allowance :
    100-1 + 2*Nat.primeCounting 100 < 2*descents height 100 := by
  rw [descents_hundred, primeCounting_hundred]
  norm_num

/-- Even with strictly positive values at all primes, the proposed universal
finite bound `descents ≤ (N-1)/2 + π(N)` is false. This is a statement about
arbitrary completely additive functions, not largest prime factors. -/
theorem not_uniform_half_plus_prime_count :
    ¬ ∀ f : ℕ → ℕ,
      f 1 = 0 →
      (∀ a b : ℕ, a ≠ 0 → b ≠ 0 → f (a*b) = f a + f b) →
      (∀ p : ℕ, p.Prime → 0 < f p) →
      ∀ N : ℕ, 2*descents f N ≤ N-1 + 2*Nat.primeCounting N := by
  intro h
  have hh := h height height_one (fun _ _ ha hb => height_mul ha hb)
    (fun _ hp => height_prime_pos hp) 100
  exact (not_le_of_gt excess_gt_prime_allowance) hh

end Erdos371PositiveAdditiveFiniteObstruction

#print axioms Erdos371PositiveAdditiveFiniteObstruction.descents_hundred
#print axioms Erdos371PositiveAdditiveFiniteObstruction.not_uniform_half_plus_prime_count
