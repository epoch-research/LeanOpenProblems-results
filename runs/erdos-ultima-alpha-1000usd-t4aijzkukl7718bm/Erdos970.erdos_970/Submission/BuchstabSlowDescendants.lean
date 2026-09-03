import Submission.BuchstabSlowCutoff

/-! Exact embedding of strict indexed descendants into finite prime sums. Every
retained lower-node unit and the upper root unit remain in the bound. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real Finset WeightedMertens
set_option maxHeartbeats 2000000

noncomputable def slowPrimeRow (p : ℕ) (D : ℝ) : ℝ :=
  exp (2/3 : ℝ)*(1/(p : ℝ))*∑ q ∈ (p+1).primesBelow,
    exp (-(2/3 : ℝ)*(log D-log (p : ℝ))/log (q : ℝ))/((q : ℝ)*log (q : ℝ))

lemma slowPrimeRow_nonneg (p : ℕ) (D : ℝ) : 0 ≤ slowPrimeRow p D := by
  unfold slowPrimeRow
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro q hq
  exact div_nonneg (exp_pos _).le (mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _))

lemma slow_descendant_identity (i j : ℕ) (D : ℝ) (hD : 0 < D) :
    slowLevelShape j ((D*primeMarginal i)*primeMarginal j) =
      D*exp (2/3 : ℝ)*(1/(nthPrime i : ℝ))*
        (exp (-(2/3 : ℝ)*(log D-log (nthPrime i : ℝ))/log (nthPrime j : ℝ))/
          ((nthPrime j : ℝ)*log (nthPrime j : ℝ))) := by
  have hpi : (0 : ℝ) < nthPrime i := by exact_mod_cast (nthPrime_prime i).pos
  have hpj : (0 : ℝ) < nthPrime j := by exact_mod_cast (nthPrime_prime j).pos
  have hlj : 0 < log (nthPrime j : ℝ) := log_pos (by exact_mod_cast (nthPrime_prime j).one_lt)
  unfold slowLevelShape primeMarginal
  simp only [mul_one_div,log_div (div_pos hD hpi).ne' hpj.ne',log_div hD.ne' hpi.ne']
  have he : (-2/3 : ℝ)*(log D-log (nthPrime i : ℝ)-log (nthPrime j : ℝ))/log (nthPrime j : ℝ) =
      2/3+(-(2/3 : ℝ)*(log D-log (nthPrime i : ℝ))/log (nthPrime j : ℝ)) := by
    field_simp
    ring
  rw [he,exp_add]
  field_simp

lemma slow_descendant_row_le (i : ℕ) (D : ℝ) (hD : 0 < D) :
    (∑ j : Fin i, slowLevelShape j.val ((D*primeMarginal i)*primeMarginal j.val)) ≤
      D*slowPrimeRow (nthPrime i) D := by
  simp_rw [slow_descendant_identity _ _ D hD]
  rw [← mul_sum,nthPrime_prefix_sum (fun p =>
    exp (-(2/3 : ℝ)*(log D-log (nthPrime i : ℝ))/log (p : ℝ))/((p : ℝ)*log (p : ℝ))) i]
  unfold slowPrimeRow
  rw [← mul_assoc,← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpi,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega,hpp⟩
  · intro p hp hnot
    exact div_nonneg (exp_pos _).le (mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _))

lemma kept_grandchild_admissible (i : ℕ) (D : ℝ)
    (hkeep : primeKeep nthPrime i (D*primeMarginal i)) (j : Fin i) :
    (nthPrime j.val : ℝ) ≤ (D*primeMarginal i)*primeMarginal j.val := by
  have hpj : (0 : ℝ) < nthPrime j.val := by exact_mod_cast (nthPrime_prime j.val).pos
  have hji : (nthPrime j.val : ℝ) ≤ nthPrime i := by exact_mod_cast (nthPrime_strictMono j.isLt).le
  have hh : (nthPrime i : ℝ)^2 ≤ D*primeMarginal i := hkeep
  simp only [primeMarginal,mul_one_div] at hh ⊢
  apply (le_div_iff₀ hpj).mpr
  nlinarith only [hh,hji,hpj]

/-- A single complete two-step error branch is bounded by its root and child
units plus the arithmetic double-prime sum. -/
theorem slow_double_step_le (F : ℕ → ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ j E, (nthPrime j : ℝ) ≤ E → F j E ≤ B*slowLevelShape j E)
    (k : ℕ) (D : ℝ) (hD : 0 < D) :
    1+(∑ i : Fin k, lowerErrorStep primeMarginal (primeKeep nthPrime) F i.val (D*primeMarginal i.val)) ≤
      1+(slowOuterCutoff k D : ℝ)+B*D*primeDoubleSlowSum (slowOuterCutoff k D) (log D) := by
  classical
  let S : Finset (Fin k) := univ.filter (fun i => primeKeep nthPrime i.val (D*primeMarginal i.val))
  have hS (i : Fin k) (hi : i ∈ S) : primeKeep nthPrime i.val (D*primeMarginal i.val) := (mem_filter.mp hi).2
  have hpi (i : Fin k) (hi : i ∈ S) : nthPrime i.val ≤ slowOuterCutoff k D :=
    kept_child_le_slowOuterCutoff k i D (hS i hi)
  have hcard : S.card ≤ slowOuterCutoff k D := by
    have hh := card_le_card_of_injOn (s := S) (t := range (slowOuterCutoff k D)) Fin.val (by
      intro i hi
      have hh := nthPrime_strictMono.add_le_nat i.val 0
      have h2 := (nthPrime_prime 0).two_le
      have hp := hpi i hi
      rw [Nat.add_zero] at hh
      exact mem_range.mpr (by omega)) Fin.val_injective.injOn
    simpa only [card_range] using hh
  have hrows : (∑ i ∈ S, slowPrimeRow (nthPrime i.val) D) ≤
      primeDoubleSlowSum (slowOuterCutoff k D) (log D) := by
    have hinj : Function.Injective (fun i : Fin k => nthPrime i.val) :=
      nthPrime_strictMono.injective.comp Fin.val_injective
    rw [← sum_image (f := fun p => slowPrimeRow p D) (s := S) hinj.injOn]
    calc
      _ ≤ ∑ p ∈ (slowOuterCutoff k D+1).primesBelow, slowPrimeRow p D := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
          exact mem_primes.mpr ⟨nthPrime_prime i.val,hpi i hi⟩
        · intro p hp hnot
          exact slowPrimeRow_nonneg p D
      _ = _ := by
        unfold slowPrimeRow primeDoubleSlowSum
        rw [mul_sum]
        apply sum_congr rfl
        intro p hp
        ring
  have hsumF : (∑ i ∈ S, ∑ j : Fin i.val, F j.val ((D*primeMarginal i.val)*primeMarginal j.val)) ≤
      B*D*primeDoubleSlowSum (slowOuterCutoff k D) (log D) := by
    calc
      _ ≤ ∑ i ∈ S, B*(D*slowPrimeRow (nthPrime i.val) D) := by
        apply sum_le_sum
        intro i hi
        calc
          _ ≤ ∑ j : Fin i.val, B*slowLevelShape j.val ((D*primeMarginal i.val)*primeMarginal j.val) :=
            sum_le_sum (fun j hj => hF j.val _ (kept_grandchild_admissible i.val D (hS i hi) j))
          _ = B*(∑ j : Fin i.val, slowLevelShape j.val ((D*primeMarginal i.val)*primeMarginal j.val)) := (mul_sum ..).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (slow_descendant_row_le i.val D hD) hB
      _ = B*D*(∑ i ∈ S, slowPrimeRow (nthPrime i.val) D) := by simp only [mul_sum,mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrows (mul_nonneg hB hD.le)
  have he : (∑ i : Fin k, lowerErrorStep primeMarginal (primeKeep nthPrime) F i.val (D*primeMarginal i.val)) =
      (S.card : ℝ)+(∑ i ∈ S, ∑ j : Fin i.val, F j.val ((D*primeMarginal i.val)*primeMarginal j.val)) := by
    simp only [lowerErrorStep]
    rw [← sum_filter]
    change (∑ i ∈ S, (1+(∑ j : Fin i.val, F j.val ((D*primeMarginal i.val)*primeMarginal j.val)))) = _
    rw [sum_add_distrib]
    simp only [sum_const,nsmul_eq_mul,mul_one]
  rw [he]
  have hc : (S.card : ℝ) ≤ slowOuterCutoff k D := by exact_mod_cast hcard
  linarith only [hsumF,hc]

#print axioms slow_double_step_le
end Erdos970.RecursiveSieve.Buchstab
