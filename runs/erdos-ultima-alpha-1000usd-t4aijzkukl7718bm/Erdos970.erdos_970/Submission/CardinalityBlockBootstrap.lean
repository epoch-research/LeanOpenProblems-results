import Submission.CardinalityBootstrap

/-! Repeated-block count consequences of smaller-cardinality Jacobsthal bounds.
These are conditional count estimates, not a quadratic induction step. -/
namespace Erdos970.CardinalityBootstrap
open OptimalCoverCore

/-- Natural representative for subtracting the starting point modulo each prime. -/
def shiftResidues (r : ℕ → ℕ) (a : ℕ) (p : ℕ) : ℕ := r p + (p - 1) * a

lemma modEq_shift_iff (r : ℕ → ℕ) (a i p : ℕ) (hp : 0 < p) :
    a + i ≡ r p [MOD p] ↔ i ≡ shiftResidues r a p [MOD p] := by
  have hbase : a + shiftResidues r a p ≡ r p [MOD p] := by
    have he : a + shiftResidues r a p = r p + p * a := by
      dsimp [shiftResidues]
      have hh : p - 1 + 1 = p := by omega
      nlinarith
    rw [he]
    simp
  constructor
  · intro h
    exact Nat.ModEq.add_left_cancel' a (h.trans hbase.symm)
  · intro h
    exact (h.add_left a).trans hbase

/-- Exact translated partition of survivor counts. -/
theorem survivor_count_add (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (a n : ℕ) :
    (survivors (a + n) P r).card = (survivors a P r).card +
      (survivors n P (shiftResidues r a)).card := by
  classical
  let f : ℕ → Prop := fun i => ∀ p ∈ P, ¬i ≡ r p [MOD p]
  have hf : (fun i => f (a + i)) =
      (fun i => ∀ p ∈ P, ¬i ≡ shiftResidues r a p [MOD p]) := by
    funext i
    apply propext
    constructor
    · intro h p hp hi
      exact h p hp ((modEq_shift_iff r a i p (hP p hp).pos).mpr hi)
    · intro h p hp hi
      exact h p hp ((modEq_shift_iff r a i p (hP p hp).pos).mp hi)
  simp only [survivors, ← Nat.count_eq_card_filter_range]
  change Nat.count f (a + n) = Nat.count f a +
    Nat.count (fun i => ∀ p ∈ P, ¬i ≡ shiftResidues r a p [MOD p]) n
  rw [Nat.count_add]
  simp only [hf]

/-- Every block can use the fresh-prime budget count, with its own translated
residue vector. -/
theorem count_lower_repeated_blocks {j g : ℕ} (h : IsJacobsthalBound j g)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ) (t : ℕ) :
    t * (j + 1 - P.card) ≤ (survivors (t * g) P r).card := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [Nat.succ_mul]
    rw [survivor_count_add P hP r (t * g) g]
    exact Nat.add_le_add ih (count_lower_of_bound h le_rfl P hP (shiftResidues r (t * g)))

/-- Floor-many disjoint blocks give the repeated-block lower profile. -/
theorem count_lower_floor_blocks {j g m : ℕ} (h : IsJacobsthalBound j g)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ) :
    (m / g) * (j + 1 - P.card) ≤ (survivors m P r).card := by
  have hh := count_lower_repeated_blocks h P hP r (m / g)
  apply hh.trans
  apply Finset.card_le_card
  intro i hi
  obtain ⟨him, hip⟩ := (mem_survivors _ _ _ _).mp hi
  exact (mem_survivors _ _ _ _).mpr
    ⟨him.trans_le (Nat.div_mul_le_self m g), hip⟩

/-- Conditional form used in a proposed strong induction. The terminal
cardinality `K` is explicitly excluded from the assumptions. -/
theorem count_lower_repeated_smaller_quadratic {C K : ℕ}
    (h : ∀ j, 0 < j → j < K → IsJacobsthalBound j (C * j ^ 2))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ)
    (j m : ℕ) (hj : 0 < j) (hjK : j < K) :
    (m / (C * j ^ 2)) * (j + 1 - P.card) ≤ (survivors m P r).card :=
  count_lower_floor_blocks (h j hj hjK) P hP r

/-- A block of cost j² and gain j+1-i has efficiency at most1/(4(i-1)).
This bounds the block construction, NOT the actual survivor count. -/
lemma block_profit_efficiency (i j : ℕ) (hi : 1 ≤ i) :
    4 * (i - 1) * (j + 1 - i) ≤ j ^ 2 := by
  by_cases hj : i ≤ j + 1
  · have he : (i - 1 : ℕ) + (j + 1 - i) = j := by omega
    have he' : ((i - 1 : ℕ) : ℤ) + (j + 1 - i : ℕ) = (j : ℤ) := by exact_mod_cast he
    have hh := sq_nonneg (((i - 1 : ℕ) : ℤ) - (j + 1 - i : ℕ))
    have hle : (4 : ℤ) * (i - 1 : ℕ) * (j + 1 - i : ℕ) ≤ (j : ℤ) ^ 2 := by
      nlinarith
    exact_mod_cast hle
  · have he : j + 1 - i = 0 := by omega
    simp [he]

/-- Even an arbitrary finite mixture of repeated quadratic blocks obeys this
profit budget. It is not a limitation theorem for all sieve arguments. -/
theorem block_profit_budget (J : Finset ℕ) (t : ℕ → ℕ) (C i m : ℕ)
    (hi : 1 ≤ i) (hcost : (∑ j ∈ J, t j * (C * j ^ 2)) ≤ m) :
    4 * C * (i - 1) * (∑ j ∈ J, t j * (j + 1 - i)) ≤ m := by
  apply le_trans _ hcost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hh := Nat.mul_le_mul_left (C * t j) (block_profit_efficiency i j hi)
  convert hh using 1 <;> ring

#print axioms block_profit_budget
#print axioms count_lower_floor_blocks
#print axioms count_lower_repeated_smaller_quadratic
end Erdos970.CardinalityBootstrap
