import Mathlib

/-!
# Independent divisor-lattice lemmas for the Erdős 322 amplification attempt

These are finite-set counting lemmas, not a proof or disproof of Erdős 322.
`Spec.lean` and its admitted declarations are not imported or used.
The application to primitive power-sum representations is proved in the
accompanying mathematical note, not asserted as a formal theorem here.
-/

namespace Erdos322GlobalMultiplicityProgress

open scoped BigOperators

variable {α : Type*}

/-- Points whose positive common denominators divide the selected scale.
The general lemma also permits a denominator label zero. -/
def covered (s : Finset α) (den : α → ℕ) (m : ℕ) : Finset α :=
  s.filter (fun x ↦ den x ∣ m)

section Lattice

variable [DecidableEq α]

lemma covered_inter (s : Finset α) (den : α → ℕ) (a b : ℕ) :
    covered s den a ∩ covered s den b = covered s den (Nat.gcd a b) := by
  ext x
  simp [covered, Nat.dvd_gcd_iff, and_assoc, and_left_comm, and_comm]

lemma covered_union_subset (s : Finset α) (den : α → ℕ) (a b : ℕ) :
    covered s den a ∪ covered s den b ⊆ covered s den (Nat.lcm a b) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_filter.mp hx with ⟨hxs, hxa⟩
    exact Finset.mem_filter.mpr ⟨hxs, hxa.trans (Nat.dvd_lcm_left a b)⟩
  · rcases Finset.mem_filter.mp hx with ⟨hxs, hxb⟩
    exact Finset.mem_filter.mpr ⟨hxs, hxb.trans (Nat.dvd_lcm_right a b)⟩

/-- Exact gcd intersections imply an additive lcm-supermodular inequality;
there is no product of representation counts on the right-hand side. -/
theorem covered_card_supermodular (s : Finset α) (den : α → ℕ) (a b : ℕ) :
    (covered s den a).card + (covered s den b).card ≤
      (covered s den (Nat.lcm a b)).card + (covered s den (Nat.gcd a b)).card := by
  have hle := Finset.card_le_card (covered_union_subset s den a b)
  have heq := Finset.card_union_add_card_inter (covered s den a) (covered s den b)
  rw [covered_inter] at heq
  calc
    (covered s den a).card + (covered s den b).card =
        (covered s den a ∪ covered s den b).card +
          (covered s den (Nat.gcd a b)).card := heq.symm
    _ ≤ (covered s den (Nat.lcm a b)).card +
          (covered s den (Nat.gcd a b)).card := Nat.add_le_add_right hle _

end Lattice

/-- Pooling at a common denominator is exactly a sum over denominator fibers. -/
theorem covered_card_sum (s : Finset α) (den : α → ℕ) {m : ℕ} (hm : m ≠ 0) :
    (covered s den m).card =
      ∑ d ∈ m.divisors, (s.filter (fun x ↦ den x = d)).card := by
  have hfilter : s.filter (fun x ↦ den x ∈ m.divisors) = covered s den m := by
    ext x
    simp [covered, Nat.mem_divisors, hm]
  have h := Finset.sum_card_fiberwise_eq_card_filter s m.divisors den
  rw [hfilter] at h
  exact h.symm

/-- A common scale has at most tau(m) fibers, uniformly in all other data. -/
theorem covered_card_le_divisors_mul (s : Finset α) (den : α → ℕ)
    {m K : ℕ} (hm : m ≠ 0)
    (hK : ∀ d ∈ m.divisors, (s.filter (fun x ↦ den x = d)).card ≤ K) :
    (covered s den m).card ≤ m.divisors.card * K := by
  rw [covered_card_sum s den hm]
  calc
    (∑ d ∈ m.divisors, (s.filter (fun x ↦ den x = d)).card) ≤
        ∑ _d ∈ m.divisors, K := Finset.sum_le_sum hK
    _ = m.divisors.card * K := by simp

/-- If pooling exceeds the divisor-factor threshold, an individual primitive
(or denominator) layer must already exceed the proposed bound. -/
theorem large_fiber_of_large_pool (s : Finset α) (den : α → ℕ)
    {m K : ℕ} (hm : m ≠ 0)
    (hlarge : m.divisors.card * K < (covered s den m).card) :
    ∃ d ∈ m.divisors, K < (s.filter (fun x ↦ den x = d)).card := by
  by_contra! h
  have hbound := covered_card_le_divisors_mul s den hm h
  omega

#print axioms covered_card_supermodular
#print axioms covered_card_sum
#print axioms covered_card_le_divisors_mul
#print axioms large_fiber_of_large_pool

end Erdos322GlobalMultiplicityProgress
