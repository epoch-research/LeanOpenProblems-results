import FormalConjecturesUtil

/-! A finite obstruction to the proposed previous-residue matching for the
p = 2 affine prefix sum. This does not disprove either a cumulative bound or
Erdős 371. -/

namespace Erdos371AffineMatchingObstruction

abbrev P := Nat.maxPrimeFac

def positiveInput (a : ℕ) : Prop := P (2*a-1) < P a

instance (a : ℕ) : Decidable (positiveInput a) :=
  inferInstanceAs (Decidable (P (2*a-1) < P a))

/-- For an odd largest prime q dividing a, this is the last b < a with
q dividing 2*b-1. -/
def previousRoot (a : ℕ) : ℕ := a - (P a - 1) / 2

lemma input_values : P 63 = 7 ∧ P 125 = 5 ∧ P 68 = 17 ∧ P 135 = 5 := by
  decide +kernel

lemma two_positive_inputs : positiveInput 63 ∧ positiveInput 68 := by
  decide +kernel

lemma same_previous_root : previousRoot 63 = 60 ∧ previousRoot 68 = 60 := by
  decide +kernel

lemma target_is_negative : P 60 < P (2*60-1) := by
  decide +kernel

/-- Both positive inputs are sent to the same negative input. Therefore the
previous-residue map cannot itself certify a cardinality inequality. -/
theorem previousRoot_not_injOn_positive :
    ¬Set.InjOn previousRoot {a | positiveInput a} := by
  intro h
  have he := h two_positive_inputs.1 two_positive_inputs.2
    (same_previous_root.1.trans same_previous_root.2.symm)
  norm_num at he


/-- A stronger obstruction: allowing every residue root in the prefix still
leaves only one negative target for two positive inputs of largest prime factor 47. -/
def negativeTargets : Finset ℕ :=
  (Finset.Icc 1 94).filter fun b => 47 ∣ 2*b-1 ∧ P b < P (2*b-1)

lemma two_inputs_at_forty_seven :
    positiveInput 47 ∧ positiveInput 94 ∧ P 47 = 47 ∧ P 94 = 47 := by
  decide +kernel

lemma all_negative_targets : negativeTargets = {24} := by
  decide +kernel

/-- This disproves a proposed prime-divisibility matching, not the desired
prefix inequality and not Erdős 371. -/
theorem no_prime_divisibility_matching :
    ¬ ∃ f : ℕ → ℕ,
      Set.InjOn f {a | 1 ≤ a ∧ a ≤ 94 ∧ positiveInput a} ∧
      (∀ a, 1 ≤ a → a ≤ 94 → positiveInput a →
        f a ∈ Finset.Icc 1 94 ∧ P a ∣ 2*f a-1 ∧ P (f a) < P (2*f a-1)) := by
  rintro ⟨f, hinj, htarget⟩
  have h47 := htarget 47 (by omega) (by omega) two_inputs_at_forty_seven.1
  have h94 := htarget 94 (by omega) (by omega) two_inputs_at_forty_seven.2.1
  have hm47 : f 47 ∈ negativeTargets := by
    apply Finset.mem_filter.mpr
    refine ⟨h47.1, ?_, h47.2.2⟩
    simpa only [two_inputs_at_forty_seven.2.2.1] using h47.2.1
  have hm94 : f 94 ∈ negativeTargets := by
    apply Finset.mem_filter.mpr
    refine ⟨h94.1, ?_, h94.2.2⟩
    simpa only [two_inputs_at_forty_seven.2.2.2] using h94.2.1
  rw [all_negative_targets, Finset.mem_singleton] at hm47 hm94
  have he := hinj
    (show 47 ∈ {a | 1 ≤ a ∧ a ≤ 94 ∧ positiveInput a} from
      ⟨by omega, by omega, two_inputs_at_forty_seven.1⟩)
    (show 94 ∈ {a | 1 ≤ a ∧ a ≤ 94 ∧ positiveInput a} from
      ⟨by omega, by omega, two_inputs_at_forty_seven.2.1⟩)
    (hm47.trans hm94.symm)
  omega

end Erdos371AffineMatchingObstruction

#print axioms Erdos371AffineMatchingObstruction.previousRoot_not_injOn_positive

#print axioms Erdos371AffineMatchingObstruction.no_prime_divisibility_matching
