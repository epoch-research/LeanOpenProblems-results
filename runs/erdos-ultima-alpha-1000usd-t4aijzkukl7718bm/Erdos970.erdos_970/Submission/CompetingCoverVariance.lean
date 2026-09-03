import Submission.CompetingCoverFibers

/-!
A variance estimate for the total concentration probability over competing
large candidate primes. The probability of one old survivor is kept explicit.
No nonlinear concentration assumption or worst-case quadratic bound is used.
-/
namespace Erdos970.CoverFibers
open Finset Real Erdos970.GapAverages

lemma point_eq_avoidance_indicator (P : Finset ℕ) (x : ℕ) (r : Phase P) :
    point P x r = if ∀ p : P, x % p.val ≠ (r p).val then 1 else 0 := by
  classical
  by_cases h : ∀ p : P, x % p.val ≠ (r p).val
  · simp [point, h]
  · push_neg at h
    obtain ⟨p, hp⟩ := h
    rw [point_zero_of_hit P x r p hp]
    have hn : ¬∀ q : P, x % q.val ≠ (r q).val := fun h => h p hp
    simp only [hn, if_false]

lemma phaseSurvivors_card (P : Finset ℕ) (m : ℕ) (r : Phase P) :
    ((phaseSurvivors P m r).card : ℝ) = intervalCount P m r := by
  classical
  unfold phaseSurvivors intervalCount
  simp_rw [point_eq_avoidance_indicator]
  exact (sum_boole _ _).symm

/-- Any concentrated subset fits into one balanced residue class of the
underlying interval. This is an absolute, not a relative, count bound. -/
lemma concentrated_card_le (U : Finset ℕ) (m p : ℕ) (hp : 0 < p)
    (hUm : U ⊆ range m) (hc : Concentrated U p) :
    (U.card : ℝ) ≤ (m : ℝ) / p + 1 := by
  obtain ⟨x, hx⟩ := hc.1
  let a : Fin p := ⟨x % p, Nat.mod_lt _ hp⟩
  have hs : U ⊆ (range m).filter (fun y => y % p = a.val) := by
    intro y hy
    exact mem_filter.mpr ⟨hUm hy, hc.2 y hy x hx⟩
  have hn : U.card ≤ m / p + 1 := by
    have hh : U.card ≤ residueHits m p a := card_le_card hs
    rw [residueHits_eq m p hp a] at hh
    split_ifs at hh <;> omega
  have hnR : (U.card : ℝ) ≤ (m / p : ℕ) + 1 := by exact_mod_cast hn
  have hd : ((m / p : ℕ) : ℝ) ≤ (m : ℝ) / p := Nat.cast_div_le
  exact hnR.trans (add_le_add hd le_rfl)

lemma competing_count_variance_pointwise (P R : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime) (m : ℕ)
    (hprod : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → m ≤ p * q)
    (b : ℝ) (hb : 0 < b)
    (hsize : ∀ p ∈ R, (m : ℝ) / p + 1 ≤ (m : ℝ) * density P - b)
    (r : Phase P) :
    (∑ p ∈ R, if Concentrated (phaseSurvivors P m r) p then (1 : ℝ) else 0) ≤
      (intervalCount P m r - (m : ℝ) * density P) ^ 2 / b ^ 2 +
      (R.card : ℝ) * (if (phaseSurvivors P m r).card = 1 then 1 else 0) := by
  classical
  let U := phaseSurvivors P m r
  have hUm : U ⊆ range m := filter_subset _ _
  have hv : 0 ≤ (intervalCount P m r - (m : ℝ) * density P) ^ 2 / b ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases hs : U.card = 1
  · have hc : ∀ p, Concentrated U p := concentrated_of_card_one U hs
    simpa only [show phaseSurvivors P m r = U from rfl, hc, hs, if_true, sum_const,
      nsmul_eq_mul, mul_one] using le_add_of_nonneg_left hv
  · have hc : (R.filter (fun p => Concentrated U p)).card ≤ 1 := by
      by_cases he : U = ∅
      · simp [he, Concentrated]
      · have ht : 2 ≤ U.card := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr he); omega
        exact concentrated_candidates_card_le_one U R m hUm ht hR hprod
    by_cases hn : (R.filter (fun p => Concentrated U p)).Nonempty
    · obtain ⟨p, hp⟩ := hn
      have hpp := (mem_filter.mp hp).1
      have hcU := (mem_filter.mp hp).2
      have hcount : intervalCount P m r ≤ (m : ℝ) * density P - b := by
        rw [← phaseSurvivors_card]
        exact (concentrated_card_le U m p (hR p hpp).pos hUm hcU).trans (hsize p hpp)
      have hv1 : 1 ≤ (intervalCount P m r - (m : ℝ) * density P) ^ 2 / b ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
        have hh : b ≤ (m : ℝ) * density P - intervalCount P m r := by linarith
        nlinarith [mul_self_le_mul_self hb.le hh]
      have hcardR : ((R.filter (fun p => Concentrated U p)).card : ℝ) ≤ 1 := by
        exact_mod_cast hc
      simp only [show phaseSurvivors P m r = U from rfl, hs, if_false,
        mul_zero, add_zero, sum_boole]
      exact hcardR.trans hv1
    · have he := not_nonempty_iff_eq_empty.mp hn
      simpa only [show phaseSurvivors P m r = U from rfl, hs, if_false,
        mul_zero, add_zero, sum_boole, he, card_empty, Nat.cast_zero] using hv

/-- Simultaneous concentration outside the singleton case is controlled by
one variance term, not one separate variance error for every candidate prime. -/
theorem concentratedFraction_sum_le_variance (P R : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (m : ℕ)
    (hprod : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → m ≤ p * q)
    (b : ℝ) (hb : 0 < b)
    (hsize : ∀ p ∈ R, (m : ℝ) / p + 1 ≤ (m : ℝ) * density P - b) :
    (∑ p ∈ R, concentratedFraction P p m) ≤
      ((m : ℝ) * density P * (1 - density P)) / b ^ 2 +
        (R.card : ℝ) * singletonFraction P m := by
  have h := phaseMean_mono (P := P)
    (competing_count_variance_pointwise P R hR m hprod b hb hsize)
  rw [phaseMean_sum, phaseMean_add, phaseMean_mul] at h
  have hd : phaseMean P (fun r =>
      (intervalCount P m r - (m : ℝ) * density P) ^ 2 / b ^ 2) =
      phaseMean P (fun r => (intervalCount P m r - (m : ℝ) * density P) ^ 2) / b ^ 2 := by
    unfold phaseMean
    rw [← sum_div]
    ring
  rw [hd] at h
  exact h.trans (add_le_add (div_le_div_of_nonneg_right
    (phase_variance_le P hP m) (sq_nonneg b)) le_rfl)

/-- A convenient half-mean specialization, still with all size hypotheses
and the exceptional singleton term displayed. -/
theorem concentratedFraction_sum_le_half_mean (P R : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ p ∈ R, p.Prime) (m : ℕ) (hm : 0 < m)
    (hprod : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → m ≤ p * q)
    (hsize : ∀ p ∈ R, (m : ℝ) / p + 1 ≤ (m : ℝ) * density P / 2) :
    (∑ p ∈ R, concentratedFraction P p m) ≤
      4 * (1 - density P) / ((m : ℝ) * density P) +
        (R.card : ℝ) * singletonFraction P m := by
  have hmu : 0 < (m : ℝ) * density P :=
    mul_pos (by exact_mod_cast hm) (density_pos P hP)
  have h := concentratedFraction_sum_le_variance P R hP hR m hprod
    ((m : ℝ) * density P / 2) (by positivity)
    (fun p hp => by have hh := hsize p hp; linarith)
  convert h using 1
  congr 1
  field_simp
  ring

#print axioms phaseSurvivors_card
#print axioms concentrated_card_le
#print axioms concentratedFraction_sum_le_variance
#print axioms concentratedFraction_sum_le_half_mean
end Erdos970.CoverFibers
