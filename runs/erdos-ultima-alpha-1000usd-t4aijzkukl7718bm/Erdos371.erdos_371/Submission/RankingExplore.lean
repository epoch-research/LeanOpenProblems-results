import FormalConjecturesUtil

/-! A finite obstruction to a proposed abstract prime-label counting bound.
This does not concern the natural ordering of primes in Erdős 371. -/

namespace Erdos371.RankingObstruction

def rank (p : ℕ) : ℕ :=
  match p with
  | 2 => 2
  | 17 => 3
  | 47 => 4
  | 3 => 5
  | 7 => 6
  | 37 => 7
  | 19 => 8
  | 29 => 9
  | 5 => 10
  | 43 => 11
  | 11 => 12
  | 13 => 13
  | 23 => 14
  | 31 => 15
  | 41 => 16
  | 53 => 17
  | 59 => 18
  | _ => p + 100

def rankedFactor (n : ℕ) : ℕ :=
  if n = 1 then 1 else n.primeFactors.sup rank

lemma rank_pos (p : ℕ) : 1 ≤ rank p := by
  unfold rank
  split <;> omega

lemma rankedFactor_pos (n : ℕ) (hn : 0 < n) : 1 ≤ rankedFactor n := by
  by_cases h1 : n = 1
  · simp [rankedFactor, h1]
  · have hn1 : 1 < n := by omega
    obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn1
    rw [rankedFactor, if_neg h1]
    exact (rank_pos p).trans (Finset.le_sup (f := rank) hp)

/-- This reordered example retains the maximum-under-multiplication identity. -/
lemma rankedFactor_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    rankedFactor (m * n) = max (rankedFactor m) (rankedFactor n) := by
  by_cases hm1 : m = 1
  · subst m
    rw [one_mul, show rankedFactor 1 = 1 by rfl, max_eq_right (rankedFactor_pos n hn)]
  by_cases hn1 : n = 1
  · subst n
    rw [mul_one, show rankedFactor 1 = 1 by rfl, max_eq_left (rankedFactor_pos m hm)]
  have hmn : m * n ≠ 1 := by
    have hm2 : 2 ≤ m := by omega
    have hn2 : 2 ≤ n := by omega
    nlinarith
  simp only [rankedFactor, if_neg hm1, if_neg hn1, if_neg hmn,
    Nat.primeFactors_mul hm.ne' hn.ne', Finset.sup_union]

/-- The explicit ranking has forty rises in sixty comparisons. -/
lemma rankedFactor_count_60 :
    ((Finset.range 60).filter fun n => rankedFactor n < rankedFactor (n + 1)).card = 40 := by
  decide +kernel

lemma rankedFactor_no_ties_60 :
    ∀ n ∈ Finset.range 60, rankedFactor n ≠ rankedFactor (n + 1) := by
  decide +kernel

lemma prime_labels_count_60 : (Nat.primesBelow 61).card = 17 := by
  decide +kernel

/-- Even an additive allowance of two does not make the proposed label-count
bound valid for all reordered prime selectors. -/
lemma rankedFactor_imbalance_exceeds_labels :
    (2 : ℤ) * ((Finset.range 60).filter fun n => rankedFactor n < rankedFactor (n + 1)).card - 60 >
      (Nat.primesBelow 61).card + 2 := by
  rw [rankedFactor_count_60, prime_labels_count_60]
  norm_num

#print axioms rankedFactor_mul
#print axioms rankedFactor_imbalance_exceeds_labels

end Erdos371.RankingObstruction
