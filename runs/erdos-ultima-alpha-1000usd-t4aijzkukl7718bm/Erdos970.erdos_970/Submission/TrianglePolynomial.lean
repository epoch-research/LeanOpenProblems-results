import Submission.TriangleMultipliers

/-! Shared-core triangle cuts have a four-monomial form. -/
namespace Erdos970.PatternPacking
attribute [local instance] Classical.propDecidable

/-- Three patterns that hit a core and two of three distinguished primes. -/
def sharedCoreFamily (D : Finset ℕ) (p q s : ℕ) : Finset (Finset ℕ) :=
  {D ∪ {p, q}, D ∪ {p, s}, D ∪ {q, s}}

noncomputable def hitIndicator (P : Finset ℕ) (f : ℕ → Prop) : ℝ :=
  if ∀ p ∈ P, f p then 1 else 0

lemma sharedCore_indicator (D : Finset ℕ) (p q s : ℕ) (f : ℕ → Prop) :
    hitIndicator (D ∪ {p, q}) f + hitIndicator (D ∪ {p, s}) f +
      hitIndicator (D ∪ {q, s}) f - 2 * hitIndicator (D ∪ {p, q, s}) f =
    if ∃ A ∈ sharedCoreFamily D p q s, ∀ t ∈ A, f t then 1 else 0 := by
  classical
  unfold hitIndicator sharedCoreFamily
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left, Finset.forall_mem_union, forall_eq_or_imp, forall_eq]
  by_cases hD : ∀ t ∈ D, f t <;>
    by_cases hp : f p <;> by_cases hq : f q <;> by_cases hs : f s <;>
    simp [hD, hp, hq, hs] <;> simp only [if_pos hD] <;> norm_num

/-- The polynomial sums to precisely the count governed by the triangle bound. -/
lemma sharedCore_sum_eq (m : ℕ) (D : Finset ℕ) (p q s : ℕ) (r : ℕ → ℕ) :
    (∑ i ∈ Finset.range m,
      (hitIndicator (D ∪ {p, q}) (fun t => i ≡ r t [MOD t]) +
      hitIndicator (D ∪ {p, s}) (fun t => i ≡ r t [MOD t]) +
      hitIndicator (D ∪ {q, s}) (fun t => i ≡ r t [MOD t]) -
      2 * hitIndicator (D ∪ {p, q, s}) (fun t => i ≡ r t [MOD t]))) =
    (patternCount m (sharedCoreFamily D p q s) r : ℝ) := by
  classical
  simp_rw [sharedCore_indicator]
  simp only [patternCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> rfl

/-- A four-monomial positional cut. The no-triangle hypothesis is indispensable;
in particular this theorem does not assert transfer under increasing primes. -/
theorem sharedCore_sum_le_two (m : ℕ) (D : Finset ℕ) (p q s : ℕ)
    (hprime : ∀ A ∈ sharedCoreFamily D p q s, ∀ t ∈ A, t.Prime)
    (hno : NoTriangle m (sharedCoreFamily D p q s)) (r : ℕ → ℕ) :
    (∑ i ∈ Finset.range m,
      (hitIndicator (D ∪ {p, q}) (fun t => i ≡ r t [MOD t]) +
      hitIndicator (D ∪ {p, s}) (fun t => i ≡ r t [MOD t]) +
      hitIndicator (D ∪ {q, s}) (fun t => i ≡ r t [MOD t]) -
      2 * hitIndicator (D ∪ {p, q, s}) (fun t => i ≡ r t [MOD t]))) ≤ 2 := by
  rw [sharedCore_sum_eq]
  exact_mod_cast patternCount_le_two_of_noTriangle m _ hprime hno r

#print axioms sharedCore_sum_le_two
end Erdos970.PatternPacking
