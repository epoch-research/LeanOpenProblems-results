import Submission.EssentialCoverProbability
import Submission.CompetingCoverVariance

/-! A covered phase creates a cylinder of low-count phases by allowing a set
of residue coordinates to vary. Its probability is the reciprocal product of
only the retained moduli. This gives stronger conditional tail and moment
criteria; it does not assert the low-tail estimates needed for a quadratic
Jacobsthal bound. -/
namespace Erdos970.GapAverages
open Finset Real

/-- Agreement on the retained coordinates, with all other residues free. -/
def AgreesOn (P Q : Finset ℕ) (r s : Phase P) : Prop :=
  ∀ p : P, p.val ∈ Q → s p = r p

instance (P Q : Finset ℕ) (r s : Phase P) : Decidable (AgreesOn P Q r s) :=
  inferInstanceAs (Decidable (∀ p : P, p.val ∈ Q → s p = r p))

lemma matchingWeight_agrees (P Q : Finset ℕ) (r s : Phase P) :
    matchingWeight P Q (phaseResidues P r) s = if AgreesOn P Q r s then 1 else 0 := by
  classical
  by_cases h : AgreesOn P Q r s
  · rw [if_pos h]
    unfold matchingWeight
    apply prod_eq_one
    intro p hp
    by_cases hpQ : p.val ∈ Q
    · simp only [hpQ, if_true, phaseResidues_mem, Nat.mod_eq_of_lt (r p).isLt, h p hpQ]
    · simp only [hpQ, if_false]
  · rw [if_neg h]
    have hn : ∃ p : P, p.val ∈ Q ∧ s p ≠ r p := by
      simpa only [AgreesOn, not_forall, Classical.not_imp, exists_prop] using h
    obtain ⟨p, hpQ, hpne⟩ := hn
    unfold matchingWeight
    apply prod_eq_zero (mem_univ p)
    have hv : (s p).val ≠ (r p).val := fun he => hpne (Fin.ext he)
    simp only [hpQ, if_true, phaseResidues_mem, Nat.mod_eq_of_lt (r p).isLt,
      hv, if_false]

/-- A general cylinder lower bound, before choosing a tail statistic. -/
theorem phaseMean_lower_of_cylinder (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (r : Phase P) (F : Phase P → ℝ) (b : ℝ)
    (hF : ∀ s, 0 ≤ F s) (hb : ∀ s, AgreesOn P Q r s → b ≤ F s) :
    b * (∏ p ∈ Q, (p : ℝ)⁻¹) ≤ phaseMean P F := by
  have hpoint (s : Phase P) : b * matchingWeight P Q (phaseResidues P r) s ≤ F s := by
    rw [matchingWeight_agrees]
    split_ifs with hs
    · simpa only [mul_one] using hb s hs
    · simpa only [mul_zero] using hF s
  have hh := phaseMean_mono P hpoint
  rwa [phaseMean_mul, phaseMean_matchingWeight P Q hQP hP] at hh

/-- An absolute budget for the positions exposed when the other primes are
allowed to change residues. It counts old hits with multiplicity. -/
noncomputable def deletionBudget (P Q : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ p ∈ P \ Q, ((m : ℝ) / p + 1)

lemma deletionBudget_nonneg (P Q : Finset ℕ) (m : ℕ) : 0 ≤ deletionBudget P Q m := by
  unfold deletionBudget
  positivity

lemma residueHits_le_real (m p : ℕ) (hp : 0 < p) (a : Fin p) :
    (residueHits m p a : ℝ) ≤ (m : ℝ) / p + 1 := by
  rw [residueHits_eq m p hp a]
  have hh : ((m / p : ℕ) : ℝ) ≤ (m : ℝ) / p := Nat.cast_div_le
  split_ifs <;> push_cast <;> linarith only [hh]

/-- Every phase agreeing with a covered phase on Q has a small survivor
count. No independence between survivor rows is needed. -/
theorem count_le_deletionBudget (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m : ℕ) (r : Phase P) (hr : intervalCount P m r = 0)
    (s : Phase P) (hs : AgreesOn P Q r s) :
    intervalCount P m s ≤ deletionBudget P Q m := by
  classical
  have hpoint (x : ℕ) (hx : x < m) :
      point P x s ≤ ∑ p ∈ P \ Q,
        if x % p = phaseResidues P r p then (1 : ℝ) else 0 := by
    by_cases ha : ∀ p : P, x % p.val ≠ (s p).val
    · obtain ⟨p, hp⟩ := cover_of_count_zero P m r hr x hx
      have hpQ : p.val ∉ Q := by
        intro hpQ
        exact ha p (by rw [hs p hpQ]; exact hp)
      have hpR : p.val ∈ P \ Q := mem_sdiff.mpr ⟨p.property, hpQ⟩
      have hhit : x % p.val = phaseResidues P r p.val := by rw [phaseResidues_mem]; exact hp
      have ht := single_le_sum (s := P \ Q)
        (f := fun q => if x % q = phaseResidues P r q then (1 : ℝ) else 0)
        (fun q _ => by dsimp only; split_ifs <;> norm_num) hpR
      rw [CoverFibers.point_eq_avoidance_indicator, if_pos ha]
      simpa only [hhit, if_true] using ht
    · rw [CoverFibers.point_eq_avoidance_indicator, if_neg ha]
      exact sum_nonneg (fun p _ => by split_ifs <;> norm_num)
  have hh := sum_le_sum (fun x (hx : x ∈ range m) => hpoint x (mem_range.mp hx))
  change intervalCount P m s ≤ _ at hh
  rw [sum_comm] at hh
  apply hh.trans
  unfold deletionBudget
  apply sum_le_sum
  intro p hp
  let p' : P := ⟨p, (mem_sdiff.mp hp).1⟩
  have he : phaseResidues P r p = (r p').val := phaseResidues_mem P r p'
  rw [he, ← residueHits_cast]
  exact residueHits_le_real m p (hP p p'.property).pos (r p')

noncomputable def lowCountFraction (P : Finset ℕ) (m : ℕ) (B : ℝ) : ℝ :=
  phaseMean P (fun r => if intervalCount P m r ≤ B then 1 else 0)

/-- A cover forces low-count probability at least the reciprocal product of
the retained primes, rather than of all primes. -/
theorem reciprocal_le_lowCountFraction (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (B : ℝ)
    (hB : deletionBudget P Q m ≤ B) (r : Phase P) (hr : intervalCount P m r = 0) :
    (∏ p ∈ Q, (p : ℝ)⁻¹) ≤ lowCountFraction P m B := by
  have hh := phaseMean_lower_of_cylinder P Q hQP hP r
    (fun s => if intervalCount P m s ≤ B then (1 : ℝ) else 0) 1
    (fun s => by dsimp only; split_ifs <;> norm_num) (fun s hs => by
      dsimp only
      rw [if_pos ((count_le_deletionBudget P Q hP m r hr s hs).trans hB)])
  simpa only [one_mul] using hh

/-- A sub-mean lower-tail moment. The centre A need not be the mean. -/
noncomputable def lowerTailMoment (P : Finset ℕ) (m : ℕ) (A : ℝ) (d : ℕ) : ℝ :=
  phaseMean P (fun r => max (A - intervalCount P m r) 0 ^ d)

/-- The same cylinder estimate for all nonnegative integer moment orders. -/
theorem moment_lower_of_cover (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (A B : ℝ) (d : ℕ)
    (hB : deletionBudget P Q m ≤ B) (hBA : B ≤ A)
    (r : Phase P) (hr : intervalCount P m r = 0) :
    (A - B) ^ d * (∏ p ∈ Q, (p : ℝ)⁻¹) ≤ lowerTailMoment P m A d := by
  apply phaseMean_lower_of_cylinder P Q hQP hP r
  · intro s
    exact pow_nonneg (le_max_right _ _) _
  · intro s hs
    have hc := (count_le_deletionBudget P Q hP m r hr s hs).trans hB
    exact pow_le_pow_left₀ (sub_nonneg.mpr hBA)
      ((sub_le_sub_left hc A).trans (le_max_left _ _)) d

/-- A moment estimate below this explicit threshold excludes every covered
phase. Establishing that estimate is a separate analytic problem. -/
theorem survivor_of_deleted_moment (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (A B : ℝ) (d : ℕ)
    (hB : deletionBudget P Q m ≤ B) (hBA : B ≤ A)
    (hM : lowerTailMoment P m A d < (A - B) ^ d * (∏ p ∈ Q, (p : ℝ)⁻¹))
    (r : ℕ → ℕ) : ∃ x < m, ∀ p ∈ P, ¬x ≡ r p [MOD p] := by
  classical
  by_contra hbad
  push_neg at hbad
  let s : Phase P := fun p => ⟨r p.val % p.val, Nat.mod_lt _ (hP p.val p.property).pos⟩
  have hs : intervalCount P m s = 0 := by
    apply count_zero_of_cover
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hbad x hx
    exact ⟨⟨p, hp⟩, hxp⟩
  exact hM.not_ge (moment_lower_of_cover P Q hQP hP m A B d hB hBA s hs)

/-- The exponential threshold now charges only the retained coordinates. -/
theorem exponent_le_retained_log_of_cover (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (B b : ℝ)
    (hB : deletionBudget P Q m ≤ B)
    (htail : lowCountFraction P m B ≤ exp (-b))
    (r : Phase P) (hr : intervalCount P m r = 0) :
    b ≤ ∑ p ∈ Q, log (p : ℝ) := by
  have hpos : 0 < ∏ p ∈ Q, (p : ℝ)⁻¹ := prod_pos
    (fun p hp => inv_pos.mpr (by exact_mod_cast (hP p (hQP hp)).pos))
  have hh := log_le_log hpos
    ((reciprocal_le_lowCountFraction P Q hQP hP m B hB r hr).trans htail)
  rw [prod_inv_distrib, log_inv, log_prod
    (fun p hp => by exact_mod_cast (hP p (hQP hp)).ne_zero), log_exp] at hh
  linarith only [hh]

/-- A low-count tail bound can exclude a cover at a smaller entropy threshold
than a bound aimed only at the zero-count event. -/
theorem survivor_of_deleted_lowCount_tail (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (B b : ℝ)
    (hB : deletionBudget P Q m ≤ B)
    (htail : lowCountFraction P m B ≤ exp (-b))
    (hb : (∑ p ∈ Q, log (p : ℝ)) < b) (r : ℕ → ℕ) :
    ∃ x < m, ∀ p ∈ P, ¬x ≡ r p [MOD p] := by
  classical
  by_contra hbad
  push_neg at hbad
  let s : Phase P := fun p => ⟨r p.val % p.val, Nat.mod_lt _ (hP p.val p.property).pos⟩
  have hs : intervalCount P m s = 0 := by
    apply count_zero_of_cover
    intro x hx
    obtain ⟨p, hp, hxp⟩ := hbad x hx
    exact ⟨⟨p, hp⟩, hxp⟩
  exact hb.not_ge (exponent_le_retained_log_of_cover P Q hQP hP m B b hB htail s hs)

lemma deletionBudget_le_of_lower (P Q : Finset ℕ) (m : ℕ) (y : ℝ) (hy : 0 < y)
    (hp : ∀ p ∈ P \ Q, y ≤ (p : ℝ)) :
    deletionBudget P Q m ≤ ((P \ Q).card : ℝ) * ((m : ℝ) / y + 1) := by
  unfold deletionBudget
  calc
    _ ≤ ∑ _p ∈ P \ Q, ((m : ℝ) / y + 1) := by
      apply sum_le_sum
      intro p hpR
      exact add_le_add (div_le_div_of_nonneg_left (Nat.cast_nonneg m) hy (hp p hpR)) le_rfl
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

lemma prime_log_sum_le_cutoff (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (y : ℕ) (hy : ∀ p ∈ Q, p ≤ y) :
    (∑ p ∈ Q, log (p : ℝ)) ≤ log 4 * y := by
  apply le_trans _ (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg y))
  unfold Chebyshev.theta
  rw [Nat.floor_natCast]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hQ p hp).pos, hy p hp⟩, hQ p hp⟩
  · intro p hp hpQ
    exact log_natCast_nonneg p

/-- Retaining only primes up to y makes the entropy at most (log 4)y,
regardless of the number or size of freed tail primes. The stated low-count
estimate and its deletion budget are still necessary hypotheses. -/
theorem survivor_of_cutoff_lowCount_tail (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (m y : ℕ) (B b : ℝ)
    (hB : deletionBudget P (P.filter (fun p => p ≤ y)) m ≤ B)
    (htail : lowCountFraction P m B ≤ exp (-b)) (hb : log 4 * y < b)
    (r : ℕ → ℕ) : ∃ x < m, ∀ p ∈ P, ¬x ≡ r p [MOD p] := by
  apply survivor_of_deleted_lowCount_tail P (P.filter (fun p => p ≤ y))
    (filter_subset _ _) hP m B b hB htail _ r
  exact (prime_log_sum_le_cutoff _ (fun p hp => hP p (mem_filter.mp hp).1)
    y (fun p hp => (mem_filter.mp hp).2)).trans_lt hb

#print axioms survivor_of_cutoff_lowCount_tail
#print axioms count_le_deletionBudget
#print axioms reciprocal_le_lowCountFraction
#print axioms survivor_of_deleted_moment
end Erdos970.GapAverages
