import Submission.SparseSmoothPrimeChains

/-!
# Testing a pointwise largest-factor parent-mass contraction

The coefficient set below is locally admissible for the simultaneous prime
forms q and a*q+1. If all these forms are prime and q>=73, the reciprocal mass
of the corresponding largest-factor parents is greater than 1/q.

No infinitude of this prime pattern is asserted. These results do not disprove
Erdos 821. They test a proposed, substantially stronger pointwise estimate.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 2000000

def canonicalTestCoefficients : Finset ℕ := {2, 6, 8, 12, 20, 30, 42, 56, 72}

lemma canonicalTestCoefficients_card : canonicalTestCoefficients.card = 9 := by decide

lemma canonicalTestCoefficients_bounds (a : ℕ) (ha : a ∈ canonicalTestCoefficients) :
    0 < a ∧ a ≤ 72 := by
  simp only [canonicalTestCoefficients, mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

lemma canonicalTestCoefficients_reciprocal_sum :
    (∑ a ∈ canonicalTestCoefficients, (1 : ℚ)/a) = 73/72 := by
  norm_num [canonicalTestCoefficients]

lemma exists_residue_avoiding_linear_forms (S : Finset ℕ) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hsize : S.card+1 < ℓ) :
    ∃ r : ℕ, ¬ℓ ∣ r ∧ ∀ a ∈ S, ¬ℓ ∣ a*r+1 := by
  classical
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let bad : Finset (ZMod ℓ) := insert 0 (S.image (fun a : ℕ => -(a : ZMod ℓ)⁻¹))
  have hbad : bad.card ≤ S.card+1 :=
    (card_insert_le (0 : ZMod ℓ) _).trans
      (Nat.add_le_add_right (card_image_le (s := S) (f := fun a : ℕ => -(a : ZMod ℓ)⁻¹)) 1)
  have hcard : bad.card < (univ : Finset (ZMod ℓ)).card := by
    simpa only [Finset.card_univ, ZMod.card] using hbad.trans_lt hsize
  obtain ⟨z, _, hz⟩ := exists_mem_notMem_of_card_lt_card hcard
  have hz0 : z ≠ 0 := fun h => hz (by simp [bad, h])
  refine ⟨z.val, ?_, ?_⟩
  · simpa only [← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val] using hz0
  · intro a ha hd
    have he : (a : ZMod ℓ)*z+1 = 0 := by
      have h := (ZMod.natCast_eq_zero_iff (a*z.val+1) ℓ).mpr hd
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val] using h
    have ha0 : (a : ZMod ℓ) ≠ 0 := by
      intro ha0
      simp only [ha0, zero_mul, zero_add, one_ne_zero] at he
    have heq : z = -(a : ZMod ℓ)⁻¹ := by
      apply mul_left_cancel₀ ha0
      rw [mul_neg, mul_inv_cancel₀ ha0]
      exact eq_neg_of_add_eq_zero_left he
    exact hz (mem_insert_of_mem (mem_image.mpr ⟨a, ha, heq.symm⟩))

/-- Local admissibility includes the primality of q itself. -/
theorem canonicalTestCoefficients_admissible (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ r : ℕ, ¬ℓ ∣ r ∧ ∀ a ∈ canonicalTestCoefficients, ¬ℓ ∣ a*r+1 := by
  by_cases hsmall : ℓ ≤ 10
  · refine ⟨191, ?_⟩
    interval_cases ℓ <;> try norm_num at hℓ
    all_goals norm_num [canonicalTestCoefficients]
  · exact exists_residue_avoiding_linear_forms canonicalTestCoefficients ℓ hℓ
      (by rw [canonicalTestCoefficients_card]; omega)

noncomputable def canonicalTestNormalizedSum (x : ℝ) : ℝ :=
  ∑ a ∈ canonicalTestCoefficients, x/((a : ℝ)*x+1)

lemma canonicalTestNormalizedSum_seventy_three :
    1 < canonicalTestNormalizedSum 73 := by
  norm_num [canonicalTestNormalizedSum, canonicalTestCoefficients]

lemma canonicalTestNormalizedSum_gt_one (x : ℝ) (hx : 73 ≤ x) :
    1 < canonicalTestNormalizedSum x := by
  refine canonicalTestNormalizedSum_seventy_three.trans_le ?_
  apply sum_le_sum
  intro a ha
  have hx0 : 0 < x := by linarith
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ)*73+1)
    (by positivity : (0 : ℝ) < (a : ℝ)*x+1)).mpr
  nlinarith only [hx]

/-- Strict root-rough parents for which q is the largest predecessor factor.
The primality of q is supplied by the lemmas using this finset. -/
noncomputable def canonicalRoughParentFinset (k q : ℕ) : Finset ℕ :=
  (range (q^k+1)).filter (fun p => p.Prime ∧ q ∣ p-1 ∧ p-1 < q^k ∧
    ∀ r ∈ (p-1).primeFactors, r ≤ q)

noncomputable def canonicalParentReciprocalMass (k q : ℕ) : ℝ :=
  ∑ p ∈ canonicalRoughParentFinset k q, 1/(p : ℝ)

lemma canonicalRoughParent_unique (k p q r : ℕ) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ∈ canonicalRoughParentFinset k q)
    (hpr : p ∈ canonicalRoughParentFinset k r) : q = r := by
  simp only [canonicalRoughParentFinset, mem_filter] at hpq hpr
  obtain ⟨_, hp, hqd, _, hqmax⟩ := hpq
  obtain ⟨_, _, hrd, _, hrmax⟩ := hpr
  have hp0 : p-1 ≠ 0 := by have := hp.two_le; omega
  exact Nat.le_antisymm (hrmax q (hq.mem_primeFactors hqd hp0))
    (hqmax r (hr.mem_primeFactors hrd hp0))

lemma canonicalTestForm_mem_parent (k q a : ℕ) (hk : 2 ≤ k) (hq : q.Prime)
    (hqlarge : 73 ≤ q) (ha : a ∈ canonicalTestCoefficients)
    (hp : (a*q+1).Prime) : a*q+1 ∈ canonicalRoughParentFinset k q := by
  have hab := canonicalTestCoefficients_bounds a ha
  have haq : a < q := by omega
  have hmul : a*q < q^2 := by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right haq hq.pos
  have hpow : q^2 ≤ q^k := Nat.pow_le_pow_right hq.pos hk
  have hbound : a*q < q^k := hmul.trans_le hpow
  simp only [canonicalRoughParentFinset, mem_filter]
  refine ⟨mem_range.mpr (by omega), hp, ?_, ?_, ?_⟩
  · simp only [Nat.add_sub_cancel]
    exact dvd_mul_left q a
  · simpa only [Nat.add_sub_cancel] using hbound
  · intro r hr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrd : r ∣ a*q := by simpa only [Nat.add_sub_cancel] using Nat.dvd_of_mem_primeFactors hr
    rcases hrp.dvd_mul.mp hrd with hra | hrq
    · exact (Nat.le_of_dvd hab.1 hra).trans haq.le
    · exact Nat.le_of_dvd hq.pos hrq

/-- A realization of the locally admissible pattern makes the normalized
largest-factor parent mass strictly greater than one, already when k=2. -/
theorem canonicalParentReciprocalMass_gt_of_test_pattern (k q : ℕ)
    (hk : 2 ≤ k) (hq : q.Prime) (hqlarge : 73 ≤ q)
    (Hpattern : ∀ a ∈ canonicalTestCoefficients, (a*q+1).Prime) :
    1 < (q : ℝ)*canonicalParentReciprocalMass k q := by
  have hinj : Function.Injective (fun a : ℕ => a*q+1) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_right hq.pos (Nat.add_right_cancel hab)
  have hsubset : canonicalTestCoefficients.image (fun a => a*q+1) ⊆
      canonicalRoughParentFinset k q := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hp
    exact canonicalTestForm_mem_parent k q a hk hq hqlarge ha (Hpattern a ha)
  have hmass : (∑ a ∈ canonicalTestCoefficients, (1 : ℝ)/(a*q+1 : ℕ)) ≤
      canonicalParentReciprocalMass k q := by
    rw [← sum_image (f := fun p : ℕ => (1 : ℝ)/(p : ℝ)) (by
      intro a _ b _ hab
      exact hinj hab)]
    exact sum_le_sum_of_subset_of_nonneg hsubset
      (fun p _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))
  have hnorm : canonicalTestNormalizedSum (q : ℝ) =
      (q : ℝ)*(∑ a ∈ canonicalTestCoefficients, (1 : ℝ)/(a*q+1 : ℕ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    push_cast
    ring
  refine (canonicalTestNormalizedSum_gt_one (q : ℝ) (by exact_mod_cast hqlarge)).trans_le ?_
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg q)

/-- Thus eventual pointwise contraction would force this admissible prime
pattern to have only finitely many realizations. Its infinitude is not assumed
or proved in this file. -/
theorem eventual_canonical_contraction_forces_finite_test_patterns (k : ℕ)
    (hk : 2 ≤ k) (c : ℝ) (hc : c < 1)
    (Hcontract : ∀ᶠ q : ℕ in atTop, q.Prime →
      canonicalParentReciprocalMass k q ≤ c/(q : ℝ)) :
    {q : ℕ | q.Prime ∧ ∀ a ∈ canonicalTestCoefficients, (a*q+1).Prime}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp Hcontract
  apply (Set.finite_Iio (max N 73)).subset
  intro q hq
  by_contra hqsmall
  have hqmax : max N 73 ≤ q := by simpa using hqsmall
  have hqN : N ≤ q := (le_max_left _ _).trans hqmax
  have hqlarge : 73 ≤ q := (le_max_right _ _).trans hqmax
  have hlow := canonicalParentReciprocalMass_gt_of_test_pattern k q hk hq.1 hqlarge hq.2
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.1.ne_zero
  have hhigh := mul_le_mul_of_nonneg_left (hN q hqN hq.1) (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hid : (q : ℝ)*(c/(q : ℝ)) = c := by field_simp
  rw [hid] at hhigh
  linarith

end Erdos821
