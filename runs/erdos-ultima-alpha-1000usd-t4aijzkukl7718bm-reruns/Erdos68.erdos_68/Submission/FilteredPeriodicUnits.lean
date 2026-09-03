import Submission.FilteredWindowGcd

/-!
Periodic prime-unit coefficients for fixed binomial filters. These are
auxiliary arithmetic statements, not a proof of Erdős Problem 68.
-/

namespace FilteredPeriodicUnits

open Erdos68Development LambertPrimePowerScaling BinomialFilteredLambert

/-- A prime divides the interior binomial coefficients below a power of
that prime even when the top index is an arbitrary multiple of the power. -/
lemma choose_dvd_of_pow_mul (p r m k : ℕ) (hp : p.Prime)
    (hk : 0 < k) (hkr : k < p^r) : p ∣ (p^r*m).choose k := by
  letI : Fact p.Prime := ⟨hp⟩
  induction r generalizing k with
  | zero => simp only [pow_zero] at hkr; omega
  | succ r ih =>
    have ht : p^(r+1)*m = p*(p^r*m) := by rw [pow_succ']; ring
    rw [ht]
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := p) (n := p*(p^r*m)) (k := k)
    simp only [Nat.mul_mod_right, Nat.mul_div_right _ hp.pos] at hl
    by_cases hmod : k % p = 0
    · have hkp : p ≤ k := Nat.le_of_dvd hk (Nat.dvd_of_mod_eq_zero hmod)
      have hdivpos : 0 < k/p := Nat.div_pos hkp hp.pos
      have hdivlt : k/p < p^r := by
        apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
        simpa only [pow_succ] using hkr
      have hi := ih (k/p) hdivpos hdivlt
      have hz : Nat.ModEq p ((p*(p^r*m)).choose k) 0 := by
        simpa only [hmod, Nat.choose_zero_right, one_mul] using
          hl.trans (by
            simpa only [hmod, Nat.choose_zero_right, one_mul] using
              Nat.modEq_zero_iff_dvd.mpr hi)
      exact Nat.modEq_zero_iff_dvd.mp hz
    · have hz : Nat.ModEq p ((p*(p^r*m)).choose k) 0 := by
        simpa only [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hmod), zero_mul] using hl
      exact Nat.modEq_zero_iff_dvd.mp hz

/-- The prime-power scaling congruence and the predecessor congruence
combine to give units on this arithmetic progression. -/
lemma lambertCoeff_periodic_unit (p r t : ℕ) (hp : p.Prime) :
    Nat.ModEq p (lambertCoeff (p^(r+1)*(p*t+1))) 1 := by
  have hs := lambertCoeff_prime_pow_scaling p r (p*t+1) hp (by omega)
  by_cases ht : t=0
  · subst t
    simpa using lambertCoeff_prime_power_modEq_one p r hp
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have hpm : p ≤ p*t+1 := by
      have := Nat.le_mul_of_pos_right p htpos
      omega
    have hm : 2 ≤ p*t+1 := hp.two_le.trans hpm
    have hc : Nat.ModEq p (lambertCoeff (p*t+1)) 1 :=
      (lambertCoeff_modEq_pred hm).of_dvd (by simp)
    have hf : Nat.ModEq p (p*t+1).factorial 0 :=
      Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_factorial hp.pos hpm)
    simpa only [Nat.add_zero] using hs.trans (hc.add hf)

/-- For any fixed positive filter degrees, the coefficient is one modulo p
at every index p^(r+1)*(p*t+1), once p^(r+1) exceeds all the degrees. -/
theorem filtered_periodic_unit (ks : List ℕ) (p r t : ℕ) (hp : p.Prime)
    (hks : ∀ k ∈ ks, 0 < k ∧ k < p^(r+1)) :
    Int.ModEq p (filtered ks (p^(r+1)*(p*t+1))) 1 := by
  apply (filterSteps_modEq ks p (p^(r+1)*(p*t+1))
    (fun n => (lambertCoeff n : ℤ))
    (fun k hk => choose_dvd_of_pow_mul p (r+1) (p*t+1) k hp
      (hks k hk).1 (hks k hk).2)).trans
  exact Int.natCast_modEq_iff.mpr (lambertCoeff_periodic_unit p r t hp)

lemma filterSteps_zero (ks : List ℕ) (a : ℕ → ℤ) (ha : a 0=0) :
    filterSteps ks a 0 = 0 := by
  induction ks with
  | nil => exact ha
  | cons k ks ih => simp only [filterSteps, filterStep, Nat.zero_sub, ih, mul_zero, sub_zero]

/-- At a prime-power index no upper bound on the positive filter degrees
is needed: a degree equal to the index multiplies the zero constant term. -/
theorem filtered_prime_power_unrestricted (ks : List ℕ) (p r : ℕ) (hp : p.Prime)
    (hks : ∀ k ∈ ks, 0 < k) :
    Int.ModEq p (filtered ks (p^(r+1))) 1 := by
  have ha0 : (fun n => (lambertCoeff n : ℤ)) 0 = 0 := by simp [lambertCoeff]
  induction ks with
  | nil =>
    exact Int.natCast_modEq_iff.mpr (lambertCoeff_prime_power_modEq_one p r hp)
  | cons k ks ih =>
    have hz := filterSteps_zero ks (fun n => (lambertCoeff n : ℤ)) ha0
    have hi := ih (fun j hj => hks j (by simp [hj]))
    by_cases hk : k < p^(r+1)
    · exact (filterStep_modEq p k (p^(r+1))
        (filterSteps ks (fun n => (lambertCoeff n : ℤ)))
        (hp.dvd_choose_pow (hks k (by simp)).ne' (ne_of_lt hk))).trans hi
    · have he : filtered (k::ks) (p^(r+1)) = filtered ks (p^(r+1)) := by
        simp only [filtered, filterSteps, filterStep]
        by_cases heq : k=p^(r+1)
        · simp only [heq, Nat.sub_self, hz, mul_zero, sub_zero]
        · simp only [Nat.choose_eq_zero_of_lt (by omega : p^(r+1)<k),
            Int.natCast_zero, zero_mul, sub_zero]
      rw [he]
      exact hi

open FilteredCoefficientGcd FilteredWindowGcd

lemma window_valuation_le_quotient (a : ℕ → ℤ) (p H N u : ℕ) (hp : p.Prime)
    (hu : u ∈ Finset.Icc H N) (hunit : Int.ModEq p (a u) 1) :
    (windowGcd a H N).factorization p ≤ (N.factorial/u.factorial).factorization p := by
  have habs := modEq_one_not_dvd hp hunit
  have habs0 : (a u).natAbs ≠ 0 := by
    intro hz
    exact habs (hz ▸ dvd_zero p)
  have hqpos := factorial_quotient_pos u N (Finset.mem_Icc.mp hu).2
  have hs : scaledCoeff a N u ≠ 0 := mul_ne_zero habs0 hqpos.ne'
  have hle := (Nat.factorization_le_iff_dvd
    (windowGcd_pos a H N).ne' hs).mpr (windowGcd_dvd_scaled a H N u hu)
  have hpoint := hle p
  simpa only [scaledCoeff, Nat.factorization_mul habs0 hqpos.ne',
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd habs, zero_add] using hpoint

lemma exists_progression_index (p r H N : ℕ) (hp : p.Prime)
    (hHN : H+p^(r+2) ≤ N) :
    ∃ t, let u := p^(r+1)*(p*t+1)
      u ∈ Finset.Icc H N ∧ N-u < p^(r+2) := by
  have hp0 := hp.pos
  let B := p^(r+1)
  let L := p^(r+2)
  have hB : 0 < B := by dsimp [B]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hBL : B ≤ L := by
    dsimp [B, L]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hBN : B ≤ N := by change H+L ≤ N at hHN; omega
  let t := (N-B)/L
  have hrem := Nat.mod_lt (N-B) hL
  have hdecomp := Nat.mod_add_div (N-B) L
  have he : p^(r+1)*(p*t+1) = B+L*t := by
    dsimp [B, L]
    rw [show r+2=(r+1)+1 by omega, pow_succ]
    ring
  refine ⟨t, ?_⟩
  dsimp only
  rw [he]
  change H+L ≤ N at hHN
  change (N-B)%L+L*t=N-B at hdecomp
  constructor
  · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · omega

lemma factorial_quotient_le_pow (u N : ℕ) (hu : u ≤ N) :
    N.factorial/u.factorial ≤ N^(N-u) := by
  have he := Nat.descFactorial_eq_div (Nat.sub_le N u)
  rw [Nat.sub_sub_self hu] at he
  rw [← he]
  exact Nat.descFactorial_le_pow N (N-u)

/-- For each fixed filter and prime this is a logarithmic valuation bound
in a sufficiently long late window. It does not bound Bézout weights. -/
theorem filtered_window_small_prime_bound (ks : List ℕ) (p r H N : ℕ)
    (hp : p.Prime) (hHN : H+p^(r+2) ≤ N)
    (hks : ∀ k ∈ ks, 0 < k ∧ k < p^(r+1)) :
    (windowGcd (filtered ks) H N).factorization p ≤
      p^(r+2) * Nat.clog p N := by
  obtain ⟨t, hu, hgap⟩ := exists_progression_index p r H N hp hHN
  let u := p^(r+1)*(p*t+1)
  change u ∈ Finset.Icc H N at hu
  change N-u < p^(r+2) at hgap
  have hunit := filtered_periodic_unit ks p r t hp hks
  have hval := window_valuation_le_quotient (filtered ks) p H N u hp hu hunit
  apply hval.trans
  apply Nat.factorization_le_of_le_pow
  calc
    N.factorial/u.factorial ≤ N^(N-u) := factorial_quotient_le_pow u N
      (Finset.mem_Icc.mp hu).2
    _ ≤ (p^Nat.clog p N)^(N-u) :=
      Nat.pow_le_pow_left (Nat.le_pow_clog hp.one_lt N) _
    _ = p^((N-u)*Nat.clog p N) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ p^(p^(r+2)*Nat.clog p N) :=
      Nat.pow_le_pow_right hp.pos (Nat.mul_le_mul_right _ hgap.le)

end FilteredPeriodicUnits

#print axioms FilteredPeriodicUnits.choose_dvd_of_pow_mul
#print axioms FilteredPeriodicUnits.filtered_periodic_unit
#print axioms FilteredPeriodicUnits.filtered_prime_power_unrestricted
#print axioms FilteredPeriodicUnits.filtered_window_small_prime_bound
