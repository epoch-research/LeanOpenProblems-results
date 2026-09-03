import Submission.GrowingSubsetMoments

/-!
# Logarithmic bounds for reciprocal-totient prime mass

A finite Euler product gives the sharp leading lower coefficient. A
Chebyshev dyadic argument supplies a sufficient (not sharp) upper bound.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def primeTotientMass (H : ℕ) : ℝ := poolTotientMass (H+1).primesBelow

lemma primeTotientMass_mono : Monotone primeTotientMass := by
  intro H J hHJ
  unfold primeTotientMass poolTotientMass
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpH,hp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega,hp⟩
  · intro p _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)

lemma harmonic_le_exp_primeTotientMass (H : ℕ) :
    (harmonic H : ℝ) ≤ Real.exp (primeTotientMass H) := by
  apply (Sieve.harmonic_le_prime_euler_product H).trans
  calc
    _ = ∏ p ∈ (H+1).primesBelow, (1+(p.totient : ℝ)⁻¹) := by
      apply prod_congr rfl
      intro p hp
      have hp' := (Nat.mem_primesBelow.mp hp).2
      have hpR : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
      rw [Nat.totient_prime hp',Nat.cast_sub hp'.one_lt.le,Nat.cast_one]
      field_simp [show (p : ℝ) ≠ 0 by linarith,show (p : ℝ)-1 ≠ 0 by linarith]
      ring
    _ ≤ ∏ p ∈ (H+1).primesBelow, Real.exp ((p.totient : ℝ)⁻¹) := by
      apply Finset.prod_le_prod
      · intro p hp; positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp ((p.totient : ℝ)⁻¹)
    _ = _ := (Real.exp_sum _ _).symm

/-- A lower bound with leading coefficient one, without a prime number theorem. -/
lemma primeTotientMass_scale_power_lower (E A : ℕ) (hE : 1 ≤ E) :
    (A : ℝ)*Real.log E ≤ primeTotientMass (progressionScaleN (E^A)) := by
  let H := progressionScaleN (E^A)
  have hEA : (0 : ℝ) < E^A := by exact_mod_cast Nat.pow_pos (by omega : 0 < E)
  have hlow : (E : ℝ)^A ≤ (harmonic H : ℝ) := by
    have h := log_progression_scale_ge (E^A)
    have hlog := log_nat_mono (Nat.le_succ H)
    have hh := log_add_one_le_harmonic H
    change ((E^A : ℕ) : ℝ) ≤ Real.log H at h
    push_cast at h hh hlog
    linarith only [h,hlog,hh]
  have h := Real.log_le_log hEA (hlow.trans (harmonic_le_exp_primeTotientMass H))
  rw [Real.log_pow,Real.log_exp] at h
  exact h

noncomputable def dyadicReciprocalPrimes (j : ℕ) : Finset ℕ :=
  (2^(j+1)+1).primesBelow.filter (fun p => 2^j < p)

lemma dyadicReciprocalPrimes_mass_upper (j : ℕ) (hj : 1 ≤ j) :
    poolTotientMass (dyadicReciprocalPrimes j) ≤ 8/(j : ℝ) := by
  let P := dyadicReciprocalPrimes j
  let D : ℝ := (2 : ℝ)^j*(j : ℝ)*Real.log 2
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hD : 0 < D := by dsimp [D]; positivity
  have hpoint (p : ℕ) (hp : p ∈ P) :
      (p.totient : ℝ)⁻¹ ≤ 2*Real.log p/D := by
    obtain ⟨hp,hpL⟩ := mem_filter.mp hp
    have hp' := (Nat.mem_primesBelow.mp hp).2
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp'.pos
    have hL : (2 : ℝ)^j ≤ p := by exact_mod_cast hpL.le
    have hlog : (j : ℝ)*Real.log 2 ≤ Real.log p := by
      simpa only [Real.log_pow] using Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^j) hL
    have hrec := prime_reciprocal_totient_le_twice_inv (2^j) p (by positivity) hp' hpL.le
    have hrec' : (p.totient : ℝ)⁻¹ ≤ 2/(2 : ℝ)^j := by exact_mod_cast hrec
    apply hrec'.trans
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^j) hD).mpr
    dsimp [D]
    nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*(2 : ℝ)^j by positivity)]
  have hsum : (∑ p ∈ P, Real.log p) ≤ Real.log 4*((2 : ℝ)^(j+1)) := by
    apply le_trans _ (Chebyshev.theta_le_log4_mul_x (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(j+1)))
    rw [show (2 : ℝ)^(j+1) = ((2^(j+1) : ℕ) : ℝ) by simp, Sieve.theta_nat_eq_sum_primesBelow]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p _ _ => Real.log_natCast_nonneg p)
  calc
    _ ≤ ∑ p ∈ P, 2*Real.log p/D := sum_le_sum hpoint
    _ = 2*(∑ p ∈ P, Real.log p)/D := by rw [← sum_div,← mul_sum]
    _ ≤ 2*(Real.log 4*((2 : ℝ)^(j+1)))/D := by gcongr
    _ = _ := by
      rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow,pow_succ]
      dsimp [D]
      field_simp
      ring

lemma primeTotientMass_dyadic_step (j : ℕ) :
    primeTotientMass (2^(j+1)) = primeTotientMass (2^j)+
      poolTotientMass (dyadicReciprocalPrimes j) := by
  have hfilter : (2^(j+1)+1).primesBelow.filter (fun p => p ≤ 2^j) = (2^j+1).primesBelow := by
    ext p
    simp only [mem_filter,Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨_,hp⟩,hpL⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨hpL,hp⟩
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ j)
      exact ⟨⟨by omega,hp⟩,by omega⟩
  have h := sum_filter_add_sum_filter_not (2^(j+1)+1).primesBelow (fun p => p ≤ 2^j)
    (fun p => (p.totient : ℝ)⁻¹)
  rw [hfilter] at h
  simpa only [primeTotientMass,poolTotientMass,dyadicReciprocalPrimes,Nat.not_le] using h.symm

lemma primeTotientMass_two : primeTotientMass 2 = 1 := by
  have h : (2+1).primesBelow = {2} := by decide
  simp [primeTotientMass,poolTotientMass,h]

lemma primeTotientMass_two_pow_upper (j : ℕ) :
    primeTotientMass (2^(j+1)) ≤ 1+8*(harmonic j : ℝ) := by
  induction j with
  | zero => simpa using (primeTotientMass_two.le)
  | succ j ih =>
    have h := dyadicReciprocalPrimes_mass_upper (j+1) (by omega)
    rw [primeTotientMass_dyadic_step (j+1)]
    have hh : (harmonic (j+1) : ℝ) = (harmonic j : ℝ)+((j+1 : ℕ) : ℝ)⁻¹ := by
      rw [harmonic_succ]; push_cast; rfl
    rw [hh]
    simp only [div_eq_mul_inv] at h
    linarith only [ih,h]

/-- A deliberately coarse upper coefficient is sufficient for interval mass. -/
lemma primeTotientMass_scale_upper (E : ℕ) (hE : 1 ≤ E) :
    primeTotientMass (progressionScaleN E) ≤ 1024+8*Real.log E := by
  have he : 64*E-1+1=64*E := by omega
  have h := primeTotientMass_two_pow_upper (64*E-1)
  rw [he] at h
  have hH := (harmonic_real_mono (Nat.sub_le (64*E) 1)).trans (harmonic_le_one_add_log (64*E))
  have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
  have hlog64 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 64)
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) hE0.ne'] at hH
  change primeTotientMass (progressionScaleN E) ≤ _ at h
  norm_num only at hlog64
  linarith only [h,hH,hlog64]

noncomputable def powerPrimePool (A E : ℕ) : Finset ℕ :=
  (progressionScaleN (E^A)+1).primesBelow.filter (fun p => progressionScaleN E ≤ p)

lemma powerPrimePool_prime_bounds (A E p : ℕ) (hp : p ∈ powerPrimePool A E) :
    p.Prime ∧ progressionScaleN E ≤ p ∧ p ≤ progressionScaleN (E^A) := by
  obtain ⟨hp,hL⟩ := mem_filter.mp hp
  obtain ⟨hpH,hp⟩ := Nat.mem_primesBelow.mp hp
  exact ⟨hp,hL,by omega⟩

lemma powerPrimePool_mass_lower (A E : ℕ) (hE : 1 ≤ E) :
    ((A : ℝ)-8)*Real.log E-1024 ≤ poolTotientMass (powerPrimePool A E) := by
  let H := progressionScaleN (E^A)
  let L := progressionScaleN E
  have htotal := primeTotientMass_scale_power_lower E A hE
  have hsmall := primeTotientMass_scale_upper E hE
  have hsplit := sum_filter_add_sum_filter_not (H+1).primesBelow (fun p => L ≤ p)
    (fun p => (p.totient : ℝ)⁻¹)
  have hsub : (H+1).primesBelow.filter (fun p => ¬L ≤ p) ⊆ (L+1).primesBelow := by
    intro p hp
    obtain ⟨hp,hpL⟩ := mem_filter.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega,(Nat.mem_primesBelow.mp hp).2⟩
  have hs := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p => (p.totient : ℝ)⁻¹) (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  change (A : ℝ)*Real.log E ≤ ∑ p ∈ (H+1).primesBelow, (p.totient : ℝ)⁻¹ at htotal
  change (∑ p ∈ (L+1).primesBelow, (p.totient : ℝ)⁻¹) ≤ 1024+8*Real.log E at hsmall
  change _ ≤ ∑ p ∈ (H+1).primesBelow.filter (fun p => L ≤ p), (p.totient : ℝ)⁻¹
  nlinarith only [htotal,hsmall,hsplit,hs]

end Erdos821
