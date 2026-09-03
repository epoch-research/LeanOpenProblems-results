import Submission.DyadicPrimeCriticalCriterion

/-! A reciprocal-rate comparison of winner and loser critical energies on
fixed-ratio harmonic windows. This estimates their difference only. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def primeLoserWindowCurrent (a N p : ℕ) : ℝ :=
  rawPrimeLoserHarmonic p (a*N)-rawPrimeLoserHarmonic p N

noncomputable def primeLoserWindowMass (a N p : ℕ) : ℝ :=
  ∑ n ∈ (Ico N (a*N)).filter (fun n => primeLoser n=p), (1 : ℝ)/n

lemma primeLoserWindowCurrent_eq_sum_filter (a N p : ℕ) (ha : 1≤a) :
    primeLoserWindowCurrent a N p =
      ∑ n ∈ (Ico N (a*N)).filter (fun n => primeLoser n=p), factorSign n/n := by
  unfold primeLoserWindowCurrent rawPrimeLoserHarmonic
  rw [← sum_Ico_eq_sub _ (show N≤a*N by nlinarith),sum_filter]
  rfl

lemma primeLoserWindowCurrent_abs_le_mass (a N p : ℕ) (ha : 1≤a) :
    |primeLoserWindowCurrent a N p|≤primeLoserWindowMass a N p := by
  rw [primeLoserWindowCurrent_eq_sum_filter a N p ha]
  have h := norm_sum_le ((Ico N (a*N)).filter (fun n => primeLoser n=p))
    (fun n => factorSign n/(n : ℝ))
  simp only [norm_div,factorSign_norm,Real.norm_natCast] at h
  simpa only [Real.norm_eq_abs,primeLoserWindowMass] using h

lemma primeLoser_window_card_bound (L U p : ℕ) (hL : 0<L) :
    ((Ico L U).filter (fun n => primeLoser n=p)).card ≤ 2*(U/p) := by
  let S := (range (U+1)).filter fun n => n≠0 ∧ p ∣ n
  let T := (range U).filter fun n => p ∣ n+1
  have hs : (Ico L U).filter (fun n => primeLoser n=p) ⊆ S ∪ T := by
    intro n hn
    obtain ⟨hn,he⟩ := mem_filter.mp hn
    obtain ⟨hnL,hnU⟩ := mem_Ico.mp hn
    have hcase : Nat.maxPrimeFac n=p ∨ Nat.maxPrimeFac (n+1)=p := by
      rcases min_cases (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) with h|h
      · exact Or.inl (h.1.symm.trans he)
      · exact Or.inr (h.1.symm.trans he)
    rcases hcase with h|h
    · apply mem_union_left
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),by omega,by
        rw [← h]; exact Nat.maxPrimeFac_dvd⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨mem_range.mpr hnU,by
        rw [← h]; exact Nat.maxPrimeFac_dvd⟩
  have hh := (card_le_card hs).trans (card_union_le S T)
  simpa only [S,T,Nat.card_multiples',Nat.card_multiples,two_mul] using hh

lemma primeLoserWindowMass_mul_label_bound (a N p : ℕ) (hN : 0<N) :
    (p : ℝ)*primeLoserWindowMass a N p≤2*a := by
  let S := (Ico N (a*N)).filter fun n => primeLoser n=p
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hb : primeLoserWindowMass a N p≤(S.card : ℝ)/N := by
    unfold primeLoserWindowMass
    calc
      _ ≤ ∑ _n ∈ S, (1 : ℝ)/N := by
        apply sum_le_sum
        intro n hn
        apply one_div_le_one_div_of_le hNr
        exact_mod_cast (mem_Ico.mp (mem_filter.mp hn).1).1
      _ = _ := by simp only [sum_const,nsmul_eq_mul,mul_one_div]
  have hc : p*S.card≤2*(a*N) := by
    have h := primeLoser_window_card_bound N (a*N) p hN
    have hd := Nat.mul_div_le (a*N) p
    dsimp only [S]
    nlinarith
  have hcr : (p : ℝ)*S.card≤2*((a*N : ℕ) : ℝ) := by exact_mod_cast hc
  calc
    _ ≤ (p : ℝ)*((S.card : ℝ)/N) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg p)
    _ = ((p : ℝ)*S.card)/N := by ring
    _ ≤ (2*((a*N : ℕ) : ℝ))/N := div_le_div_of_nonneg_right hcr hNr.le
    _ = 2*a := by push_cast; field_simp

/-- Both incident-label choices have the same uniform spacing bound. -/
lemma primeWindowCurrent_pair_label_bound (a N p : ℕ) (ha : 1≤a) (hN : 0<N) :
    (p : ℝ)*|primeWindowCurrent a N p|≤2*a ∧
      (p : ℝ)*|primeLoserWindowCurrent a N p|≤2*a := by
  constructor
  · exact (mul_le_mul_of_nonneg_left (primeWindowCurrent_abs_le_mass a N p ha)
      (Nat.cast_nonneg p)).trans (primeWindowMass_mul_label_bound a N p hN)
  · exact (mul_le_mul_of_nonneg_left (primeLoserWindowCurrent_abs_le_mass a N p ha)
      (Nat.cast_nonneg p)).trans (primeLoserWindowMass_mul_label_bound a N p hN)

/-- Critical-energy replacement is uniform in the finite set of labels.
The estimate does NOT bound either energy by a quantity tending to zero. -/
theorem primeWindow_critical_energy_difference_bound
    (a N : ℕ) (P : Finset ℕ) (ha : 1≤a) (hN : 2≤N) :
    |(∑ p ∈ P, (p : ℝ)*(primeWindowCurrent a N p)^2)-
      (∑ p ∈ P, (p : ℝ)*(primeLoserWindowCurrent a N p)^2)| ≤
      4*a*(2/(((a*N : ℕ) : ℝ)-1)+2/((N : ℝ)-1)) := by
  have hAN : 2≤a*N := by nlinarith
  have hterm (p : ℕ) (_hp : p∈P) :
      |(p : ℝ)*(primeWindowCurrent a N p)^2-
        (p : ℝ)*(primeLoserWindowCurrent a N p)^2| ≤
      4*a*|primeWindowCurrent a N p-primeLoserWindowCurrent a N p| := by
    obtain ⟨hw,hl⟩ := primeWindowCurrent_pair_label_bound a N p ha (by omega)
    have hb : |(p : ℝ)*primeWindowCurrent a N p+
        (p : ℝ)*primeLoserWindowCurrent a N p| ≤ 4*a := by
      have hh := abs_add_le ((p : ℝ)*primeWindowCurrent a N p)
        ((p : ℝ)*primeLoserWindowCurrent a N p)
      simp only [abs_mul,abs_of_nonneg (show (0 : ℝ)≤p from Nat.cast_nonneg p)] at hh
      linarith
    have he : (p : ℝ)*(primeWindowCurrent a N p)^2-
        (p : ℝ)*(primeLoserWindowCurrent a N p)^2 =
        (primeWindowCurrent a N p-primeLoserWindowCurrent a N p)*
          ((p : ℝ)*primeWindowCurrent a N p+(p : ℝ)*primeLoserWindowCurrent a N p) := by ring
    rw [he,abs_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb
      (abs_nonneg (primeWindowCurrent a N p-primeLoserWindowCurrent a N p))
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ P, |(p : ℝ)*(primeWindowCurrent a N p)^2-
        (p : ℝ)*(primeLoserWindowCurrent a N p)^2| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, 4*a*|primeWindowCurrent a N p-primeLoserWindowCurrent a N p| :=
      sum_le_sum hterm
    _ = 4*a*∑ p ∈ P, |primeWindowCurrent a N p-primeLoserWindowCurrent a N p| :=
      (mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [primeWindowCurrent,primeLoserWindowCurrent,Real.norm_eq_abs] using
        primeHarmonicWindow_flux_bound P N (a*N) hN hAN

noncomputable def dyadicPrimeLoserCriticalEnergy (N : ℕ) : ℝ :=
  ∑ p ∈ range (2*N+1), (p : ℝ)*(primeLoserWindowCurrent 2 N p)^2

lemma dyadicPrimeLoserCriticalEnergy_nonneg (N : ℕ) :
    0≤dyadicPrimeLoserCriticalEnergy N := by
  unfold dyadicPrimeLoserCriticalEnergy
  positivity

/-- A uniform reciprocal endpoint rate for energy replacement. -/
theorem dyadicPrimeCriticalEnergy_difference_bound (N : ℕ) (hN : 2≤N) :
    |dyadicPrimeCriticalEnergy N-dyadicPrimeLoserCriticalEnergy N|≤64/(N : ℝ) := by
  have hh := primeWindow_critical_energy_difference_bound 2 N (range (2*N+1)) (by omega) hN
  simp only [dyadicPrimeCriticalEnergy,primeWindowWeightedEnergy,one_mul,dyadicPrimeLoserCriticalEnergy]
  have hNr : (2 : ℝ)≤N := by exact_mod_cast hN
  have hpos : (0 : ℝ)<N := by linarith
  have hden : (0 : ℝ)<N-1 := by linarith
  have hden2 : (0 : ℝ)<2*N-1 := by linarith
  have hb1 : (2 : ℝ)/(N-1)≤4/N := by
    apply (div_le_div_iff₀ hden hpos).mpr
    linarith
  have hb2 : (2 : ℝ)/(2*N-1)≤4/N := by
    apply (div_le_div_iff₀ hden2 hpos).mpr
    linarith
  push_cast at hh
  rw [show (64 : ℝ)/N=16*(4/(N : ℝ)) by ring]
  linarith

theorem dyadicPrimeCriticalEnergy_difference_zero :
    Tendsto (fun N => dyadicPrimeCriticalEnergy N-dyadicPrimeLoserCriticalEnergy N)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (64 : ℝ))
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  simpa only [Real.norm_eq_abs] using dyadicPrimeCriticalEnergy_difference_bound N hN

/-- Both limits remain unproved; the conservation correction cannot be the
source of a failure of critical-energy decay. -/
theorem dyadicPrimeCriticalEnergy_zero_iff_loser :
    Tendsto dyadicPrimeCriticalEnergy atTop (𝓝 0) ↔
      Tendsto dyadicPrimeLoserCriticalEnergy atTop (𝓝 0) := by
  constructor
  · intro h
    simpa only [sub_sub_cancel,sub_zero] using
      h.sub dyadicPrimeCriticalEnergy_difference_zero
  · intro h
    simpa only [sub_add_cancel,add_zero] using
      dyadicPrimeCriticalEnergy_difference_zero.add h

#print axioms primeWindow_critical_energy_difference_bound
#print axioms dyadicPrimeCriticalEnergy_difference_bound
#print axioms dyadicPrimeCriticalEnergy_zero_iff_loser
end Erdos371
