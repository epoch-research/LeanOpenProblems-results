import Submission.QuarticMomentFiber

/-! Common translations of quartic representations. Distinct lower-moment
profiles can agree at at most two nonzero translations. This controls each
pair of profiles, not the total number of representations. -/
namespace Erdos322Research.QuarticTranslationCollisions

open Polynomial
set_option Elab.async false

abbrev Tuple := Fin 4 → ℤ

def powerSum (a : Tuple) (j : ℕ) : ℤ := ∑ i, a i ^ j

def translatedValue (a : Tuple) (t : ℤ) : ℤ := ∑ i, (a i + t) ^ 4

def lowerProfile (a : Tuple) : ℤ × ℤ × ℤ :=
  (powerSum a 1, powerSum a 2, powerSum a 3)

/-- After removing the common zero-translation value and the factor `t`,
the difference is a polynomial of degree at most two. -/
noncomputable def differenceQuotient (a b : Tuple) : Polynomial ℤ :=
  C (4 * (powerSum a 1 - powerSum b 1)) * X ^ 2 +
  C (6 * (powerSum a 2 - powerSum b 2)) * X +
  C (4 * (powerSum a 3 - powerSum b 3))

theorem translated_difference (a b : Tuple) (t : ℤ) :
    translatedValue a t - translatedValue b t =
      powerSum a 4 - powerSum b 4 + t * (differenceQuotient a b).eval t := by
  simp only [translatedValue, differenceQuotient, powerSum, Fin.sum_univ_four,
    eval_add, eval_mul, eval_C, eval_pow, eval_X, pow_one]
  ring

lemma differenceQuotient_degree (a b : Tuple) :
    (differenceQuotient a b).natDegree ≤ 2 := by
  unfold differenceQuotient
  apply natDegree_add_le_of_degree_le
  · apply natDegree_add_le_of_degree_le
    · exact natDegree_C_mul_X_pow_le _ _
    · have h := natDegree_C_mul_X_pow_le (6 * (powerSum a 2 - powerSum b 2)) 1
      simp only [pow_one] at h
      exact h.trans (by omega)
  · simp only [natDegree_C]; omega

lemma differenceQuotient_eq_zero_iff (a b : Tuple) :
    differenceQuotient a b = 0 ↔ lowerProfile a = lowerProfile b := by
  constructor
  · intro h
    have h0 := congrArg (fun p : Polynomial ℤ => p.coeff 0) h
    have h1 := congrArg (fun p : Polynomial ℤ => p.coeff 1) h
    have h2 := congrArg (fun p : Polynomial ℤ => p.coeff 2) h
    simp only [differenceQuotient, coeff_add, coeff_C_mul_X_pow,
      coeff_C_mul_X, coeff_C, coeff_zero] at h0 h1 h2
    norm_num at h0 h1 h2
    have he1 : powerSum a 1 = powerSum b 1 := by omega
    have he2 : powerSum a 2 = powerSum b 2 := by omega
    have he3 : powerSum a 3 = powerSum b 3 := by omega
    simp [lowerProfile, he1, he2, he3]
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun p : ℤ × ℤ × ℤ => p.2.1) h
    have h3 := congrArg (fun p : ℤ × ℤ × ℤ => p.2.2) h
    simp only [lowerProfile] at h1 h2 h3
    simp [differenceQuotient, h1, h2, h3]

/-- Two original representations with distinct lower-moment profiles have
at most two nonzero common shifts at which their targets still agree. -/
theorem collision_card_le_two (a b : Tuple) (S : Finset ℤ)
    (h4 : powerSum a 4 = powerSum b 4)
    (hp : lowerProfile a ≠ lowerProfile b)
    (hS : ∀ t ∈ S, t ≠ 0 ∧ translatedValue a t = translatedValue b t) :
    S.card ≤ 2 := by
  by_contra hc
  have heval (t : ℤ) (ht : t ∈ S) : (differenceQuotient a b).eval t = 0 := by
    obtain ⟨ht0, htab⟩ := hS t ht
    have h := translated_difference a b t
    rw [h4, htab] at h
    have hz : t * (differenceQuotient a b).eval t = 0 := by omega
    exact (mul_eq_zero.mp hz).resolve_left ht0
  have hz := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (differenceQuotient a b) S heval
    (lt_of_le_of_lt (differenceQuotient_degree a b) (by omega))
  exact hp ((differenceQuotient_eq_zero_iff a b).mp hz)

/-- Agreement at three distinct nonzero shifts forces agreement of all
three lower moments. This conclusion alone does not bound how many profiles
occur at a given original target. -/
theorem three_shifts_force_profile (a b : Tuple) (S : Finset ℤ)
    (h4 : powerSum a 4 = powerSum b 4) (hcard : 3 ≤ S.card)
    (hS : ∀ t ∈ S, t ≠ 0 ∧ translatedValue a t = translatedValue b t) :
    lowerProfile a = lowerProfile b := by
  by_contra hp
  have h := collision_card_le_two a b S h4 hp hS
  omega

/-- Joint fibers of the original target and three distinct nonzero translated
targets have a uniform subpolynomial bound. This does not bound the number of
such joint fibers inside one original quartic fiber. -/
theorem joint_translation_fiber_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ (S : Finset (Fin 4 → ℕ)) (T : Finset ℤ) (n : ℕ),
      1 ≤ n → 3 ≤ T.card → (∀ t ∈ T, t ≠ 0) →
      (∀ a ∈ S, ∑ i, a i ^ 4 = n) →
      (∀ a ∈ S, ∀ b ∈ S, ∀ t ∈ T,
        translatedValue (fun i => (a i : ℤ)) t =
          translatedValue (fun i => (b i : ℤ)) t) →
      (S.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  obtain ⟨C, hC, hbound⟩ := QuarticMomentFiber.fiber_subpolynomial ε hε
  refine ⟨C, hC, ?_⟩
  intro S T n hn hT hT0 hsum hshift
  by_cases hS : S.Nonempty
  · obtain ⟨b, hb⟩ := hS
    have hprofile (a : Fin 4 → ℕ) (ha : a ∈ S) :
        lowerProfile (fun i => (a i : ℤ)) = lowerProfile (fun i => (b i : ℤ)) := by
      apply three_shifts_force_profile _ _ T
      · dsimp only [powerSum]
        exact_mod_cast (hsum a ha).trans (hsum b hb).symm
      · exact hT
      · intro t ht
        exact ⟨hT0 t ht, hshift a ha b hb t ht⟩
    apply hbound S (∑ i, b i) (∑ i, b i ^ 2) n hn
    · intro a ha
      have h := congrArg Prod.fst (hprofile a ha)
      simp only [lowerProfile, powerSum, pow_one] at h
      exact_mod_cast h
    · intro a ha
      have h := congrArg (fun p : ℤ × ℤ × ℤ => p.2.1) (hprofile a ha)
      simp only [lowerProfile, powerSum] at h
      exact_mod_cast h
    · exact hsum
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hz, Finset.card_empty, Nat.cast_zero]
    positivity

end Erdos322Research.QuarticTranslationCollisions
