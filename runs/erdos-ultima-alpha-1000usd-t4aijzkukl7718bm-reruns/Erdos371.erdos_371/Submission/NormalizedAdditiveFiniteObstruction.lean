import FormalConjecturesUtil

/-! A finite obstruction to bounding the normalized skew of an arbitrary
positive completely additive function by the prime count with constant one.
This does not refute a larger-constant bound or Erdos 371. -/

namespace Erdos371NormalizedAdditiveFiniteObstruction

/-- Positive integer weights. They are not monotone in the numerical primes. -/
def weight : ℕ → ℕ
  | 2 => 1
  | 3 => 8
  | 5 => 524288
  | 7 => 1024
  | 11 => 16384
  | 13 => 1048576
  | 17 => 262144
  | 19 => 4096
  | 23 => 4194304
  | 29 => 8192
  | 31 => 8388608
  | 37 => 512
  | 41 => 32
  | 43 => 2048
  | 47 => 2
  | 53 => 16777216
  | 59 => 32768
  | 61 => 2097152
  | 67 => 65536
  | 71 => 4
  | 73 => 64
  | 79 => 16
  | 83 => 256
  | 89 => 131072
  | 97 => 128
  | _ => 1

lemma weight_pos (p : ℕ) : 0 < weight p := by
  unfold weight
  split <;> norm_num

def height (n : ℕ) : ℕ := (n.primeFactorsList.map weight).sum

lemma height_one : height 1 = 0 := by simp [height]

lemma height_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    height (a*b) = height a + height b := by
  have h := ((Nat.perm_primeFactorsList_mul ha hb).map weight).sum_eq
  simpa [height, List.map_append] using h

lemma height_prime {p : ℕ} (hp : p.Prime) : height p = weight p := by
  simp [height, Nat.primeFactorsList_prime hp]

lemma height_prime_pos {p : ℕ} (hp : p.Prime) : 0 < height p := by
  rw [height_prime hp]
  exact weight_pos p

def normalizedSum (f : ℕ → ℕ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc 1 (N-1),
    ((f (n+1) : ℚ) - f n) / ((f (n+1) : ℚ) + f n)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
lemma normalizedSum_hundred_gt : 25 < normalizedSum height 100 := by
  decide +kernel

lemma primeCounting_hundred : Nat.primeCounting 100 = 25 := by
  decide +kernel

/-- Constant one in this proposed finite bound is false, even when all
prime values are strictly positive. No monotonicity of those values is asserted. -/
theorem not_normalized_sum_le_prime_count :
    ¬ ∀ f : ℕ → ℕ,
      f 1 = 0 →
      (∀ a b : ℕ, a ≠ 0 → b ≠ 0 → f (a*b) = f a + f b) →
      (∀ p : ℕ, p.Prime → 0 < f p) →
      ∀ N : ℕ, normalizedSum f N ≤ (Nat.primeCounting N : ℚ) := by
  intro h
  have hh := h height height_one (fun _ _ ha hb => height_mul ha hb)
    (fun _ hp => height_prime_pos hp) 100
  rw [primeCounting_hundred] at hh
  exact (not_le_of_gt normalizedSum_hundred_gt) hh

end Erdos371NormalizedAdditiveFiniteObstruction

#print axioms Erdos371NormalizedAdditiveFiniteObstruction.normalizedSum_hundred_gt
#print axioms Erdos371NormalizedAdditiveFiniteObstruction.not_normalized_sum_le_prime_count
