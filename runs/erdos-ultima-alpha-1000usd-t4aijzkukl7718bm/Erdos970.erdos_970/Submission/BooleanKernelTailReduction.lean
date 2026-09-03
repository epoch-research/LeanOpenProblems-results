import Submission.BooleanKernelUpperWeights

/-! Coordinates of expected hit mass at most one can be removed from the exact
Boolean upper-weight problem. The reduction preserves admissibility and never
increases the objective. It is not an interval-survivor estimate. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def restrictBooleanCoefficient (S : Finset ι) (a : Finset ι → ℝ)
    (T : Finset ι) : ℝ := if T ⊆ S then a T else 0

def restrictBooleanPattern (S : Finset ι) (ω : ι → Bool) (i : ι) : Bool :=
  if i ∈ S then ω i else false

omit [Fintype ι] in
lemma hitMonomial_restrict (S T : Finset ι) (ω : ι → Bool) :
    hitMonomial T (restrictBooleanPattern S ω) = if T ⊆ S then hitMonomial T ω else 0 := by
  by_cases hTS : T ⊆ S
  · rw [if_pos hTS]
    unfold hitMonomial
    apply prod_congr rfl
    intro i hi
    simp only [restrictBooleanPattern, if_pos (hTS hi)]
  · rw [if_neg hTS]
    obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
    apply prod_eq_zero hiT
    simp [restrictBooleanPattern, hiS]

lemma booleanValue_restrict (S : Finset ι) (a : Finset ι → ℝ) (ω : ι → Bool) :
    booleanValue (restrictBooleanCoefficient S a) ω =
      booleanValue a (restrictBooleanPattern S ω) := by
  unfold booleanValue
  apply sum_congr rfl
  intro T hT
  rw [hitMonomial_restrict]
  by_cases hTS : T ⊆ S <;> simp [restrictBooleanCoefficient, hTS]

omit [Fintype ι] in
lemma restrictBooleanPattern_empty (S : Finset ι) :
    restrictBooleanPattern S (fun _ => false) = fun _ => false := by
  funext i
  simp [restrictBooleanPattern]

omit [DecidableEq ι] in
lemma booleanObjective_eq_sum (q : ι → ℝ) (X : ℝ) (a : Finset ι → ℝ) :
    booleanObjective q X a =
      ∑ T : Finset ι, (X * (∏ i ∈ T, q i) * a T + |a T|) := by
  simp only [booleanObjective, mul_sum, sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro T hT
  ring

omit [Fintype ι] in
lemma expected_monomial_le_one (q : ι → ℝ) (X : ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hX : 0 ≤ X)
    (S T : Finset ι) (hsmall : ∀ i ∉ S, X * q i ≤ 1) (hTS : ¬T ⊆ S) :
    X * (∏ i ∈ T, q i) ≤ 1 := by
  obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
  have hrest : (∏ j ∈ T.erase i, q j) ≤ 1 :=
    prod_le_one (fun j _ => (hq j).1) (fun j _ => (hq j).2)
  have hprod : (∏ j ∈ T, q j) ≤ q i := by
    rw [← prod_erase_mul T q hiT]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrest (hq i).1
  exact (mul_le_mul_of_nonneg_left hprod hX).trans (hsmall i hiS)

lemma coefficient_term_nonneg (u a : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) :
    0 ≤ u * a + |a| := by
  have h1 : 0 ≤ u * (a + |a|) := mul_nonneg hu.1 (by linarith [neg_abs_le a])
  have h2 : 0 ≤ (1 - u) * |a| := mul_nonneg (sub_nonneg.mpr hu.2) (abs_nonneg a)
  nlinarith

/-- All removed monomials contribute nonnegatively to mean-plus-L1-cost. -/
theorem booleanObjective_restrict_le (q : ι → ℝ) (X : ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hX : 0 ≤ X)
    (S : Finset ι) (hsmall : ∀ i ∉ S, X * q i ≤ 1) (a : Finset ι → ℝ) :
    booleanObjective q X (restrictBooleanCoefficient S a) ≤ booleanObjective q X a := by
  rw [booleanObjective_eq_sum, booleanObjective_eq_sum]
  apply sum_le_sum
  intro T hT
  by_cases hTS : T ⊆ S
  · simp [restrictBooleanCoefficient, hTS]
  · simp only [restrictBooleanCoefficient, if_neg hTS, mul_zero, abs_zero, add_zero]
    apply coefficient_term_nonneg
    exact ⟨mul_nonneg hX (prod_nonneg (fun i _ => (hq i).1)),
      expected_monomial_le_one q X hq hX S T hsmall hTS⟩

/-- Admissibility is preserved because the polynomial is restricted to a subcube. -/
theorem admissible_upper_restrict (S : Finset ι) (a : Finset ι → ℝ)
    (ha : ∀ ω, 0 ≤ booleanValue a ω) (h0 : booleanValue a (fun _ => false) = 1) :
    (∀ ω, 0 ≤ booleanValue (restrictBooleanCoefficient S a) ω) ∧
    booleanValue (restrictBooleanCoefficient S a) (fun _ => false) = 1 ∧
    ∀ T, restrictBooleanCoefficient S a T ≠ 0 → T ⊆ S := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    rw [booleanValue_restrict]
    exact ha _
  · rw [booleanValue_restrict, restrictBooleanPattern_empty, h0]
  · intro T hT
    by_contra hn
    simp [restrictBooleanCoefficient, hn] at hT

/-- Exact equivalence at every objective threshold: rare coordinates can be
ignored without losing a better normalized nonnegative upper weight. -/
theorem exists_upper_below_iff_restricted (q : ι → ℝ) (X B : ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hX : 0 ≤ X)
    (S : Finset ι) (hsmall : ∀ i ∉ S, X * q i ≤ 1) :
    (∃ a : Finset ι → ℝ, (∀ ω, 0 ≤ booleanValue a ω) ∧
      booleanValue a (fun _ => false) = 1 ∧ booleanObjective q X a < B) ↔
    (∃ a : Finset ι → ℝ, (∀ ω, 0 ≤ booleanValue a ω) ∧
      booleanValue a (fun _ => false) = 1 ∧
      (∀ T, a T ≠ 0 → T ⊆ S) ∧ booleanObjective q X a < B) := by
  constructor
  · rintro ⟨a, ha, h0, hB⟩
    obtain ⟨hb, hb0, hbS⟩ := admissible_upper_restrict S a ha h0
    exact ⟨restrictBooleanCoefficient S a, hb, hb0, hbS,
      (booleanObjective_restrict_le q X hq hX S hsmall a).trans_lt hB⟩
  · rintro ⟨a, ha, h0, _, hB⟩
    exact ⟨a, ha, h0, hB⟩

/-- The remaining coordinates are exactly those with expected hit mass >1. -/
noncomputable def booleanActiveCore (q : ι → ℝ) (X : ℝ) : Finset ι :=
  univ.filter (fun i => 1 < X * q i)

omit [DecidableEq ι] in
lemma activeCore_small (q : ι → ℝ) (X : ℝ) (i : ι)
    (hi : i ∉ booleanActiveCore q X) : X * q i ≤ 1 := by
  simpa only [booleanActiveCore, mem_filter, mem_univ, true_and, not_lt] using hi

/-- In the prime case, only primes strictly below X need occur in an upper weight. -/
theorem prime_upper_below_iff_active (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (X B : ℝ) (hX : 0 ≤ X) :
    (∃ a : Finset ι → ℝ, (∀ ω, 0 ≤ booleanValue a ω) ∧
      booleanValue a (fun _ => false) = 1 ∧
      booleanObjective (fun i => 1 / (p i : ℝ)) X a < B) ↔
    (∃ a : Finset ι → ℝ, (∀ ω, 0 ≤ booleanValue a ω) ∧
      booleanValue a (fun _ => false) = 1 ∧
      (∀ T, a T ≠ 0 → ∀ i ∈ T, (p i : ℝ) < X) ∧
      booleanObjective (fun i => 1 / (p i : ℝ)) X a < B) := by
  classical
  let S := univ.filter (fun i => (p i : ℝ) < X)
  have hq (i : ι) : 0 ≤ 1 / (p i : ℝ) ∧ 1 / (p i : ℝ) ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ p i := by exact_mod_cast (hp i).one_le
    exact ⟨by positivity, (div_le_one (by positivity)).mpr hp1⟩
  have hsmall (i : ι) (hi : i ∉ S) : X * (1 / (p i : ℝ)) ≤ 1 := by
    have hle : X ≤ p i := by simpa [S] using hi
    rw [mul_one_div]
    exact (div_le_one (by exact_mod_cast (hp i).pos)).mpr hle
  have he := exists_upper_below_iff_restricted (fun i => 1 / (p i : ℝ)) X B hq hX S hsmall
  simpa only [S, subset_iff, mem_filter, mem_univ, true_and] using he

#print axioms booleanObjective_restrict_le
#print axioms exists_upper_below_iff_restricted
#print axioms prime_upper_below_iff_active
end Erdos970.FiniteSelberg
