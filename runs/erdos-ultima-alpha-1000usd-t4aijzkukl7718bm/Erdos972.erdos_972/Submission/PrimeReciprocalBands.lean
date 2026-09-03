import Submission.PrimeIntervalCounts

/-! Fixed positive reciprocal-prime mass in separated power bands, using
only dyadic prime counts from qualitative PNT. -/
namespace Erdos972PrimeReciprocalBands

open Finset Filter
open scoped Topology
open Erdos972PrimeIntervalCounts

noncomputable def reciprocalPrimeMass (a b : ℕ) : ℝ :=
  ∑ p ∈ primesBetween a b, (1 : ℝ)/p

lemma reciprocalPrimeMass_nonneg (a b : ℕ) : 0 ≤ reciprocalPrimeMass a b :=
  sum_nonneg (fun _ _ => by positivity)

lemma reciprocalPrimeMass_add {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    reciprocalPrimeMass a b+reciprocalPrimeMass b c = reciprocalPrimeMass a c := by
  simpa only [reciprocalPrimeMass, primesBetween, sum_filter] using
    sum_Ioc_consecutive (fun p : ℕ => if p.Prime then (1 : ℝ)/p else 0) hab hbc

lemma reciprocalPrimeMass_dyadic {x : ℕ} (hx : 0 < x)
    (hcount : (x : ℝ)/(2*Real.log (2*x : ℕ)) ≤ (primesBetween x (2*x)).card) :
    1/(4*Real.log (2*x : ℕ)) ≤ reciprocalPrimeMass x (2*x) := by
  have hxR : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  have hlog : 0 < Real.log (2*x : ℕ) := Real.log_pos (by exact_mod_cast (show 1 < 2*x by omega))
  calc
    _ = ((x : ℝ)/(2*Real.log (2*x : ℕ)))/(2*x : ℕ) := by push_cast; field_simp; ring
    _ ≤ ((primesBetween x (2*x)).card : ℝ)/(2*x : ℕ) :=
      div_le_div_of_nonneg_right hcount (Nat.cast_nonneg _)
    _ = ∑ p ∈ primesBetween x (2*x), (1 : ℝ)/(2*x : ℕ) := by simp; ring
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      obtain ⟨_, hpx, hprime⟩ := mem_primesBetween.mp hp
      exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hprime.pos) (Nat.cast_le.mpr hpx)

lemma reciprocalPrimeMass_power_bands {a b : ℕ} (hab : a ≤ b) (_hb : 0 < b)
    (hcount : ∀ x : ℕ, 2^a ≤ x →
      (x : ℝ)/(2*Real.log (2*x : ℕ)) ≤ (primesBetween x (2*x)).card) :
    ((b-a : ℕ) : ℝ)/(4*b) ≤ reciprocalPrimeMass (2^a) (2^b) := by
  have hstep (j : ℕ) (hj : j ∈ Ico a b) :
      1/(4*(b : ℝ)) ≤ reciprocalPrimeMass (2^j) (2^(j+1)) := by
    obtain ⟨haj, hjb⟩ := mem_Ico.mp hj
    have hx : 0 < (2 : ℕ)^j := by positivity
    have hh := reciprocalPrimeMass_dyadic hx (hcount _ (Nat.pow_le_pow_right (by norm_num) haj))
    have he : 2*(2 : ℕ)^j = 2^(j+1) := by rw [pow_succ]; omega
    rw [he] at hh
    apply le_trans _ hh
    apply one_div_le_one_div_of_le
    · have hl : 0 < Real.log ((2 : ℕ)^(j+1)) :=
        Real.log_pos (by exact_mod_cast (Nat.one_lt_pow (by omega : j+1 ≠ 0) (by norm_num : 1 < (2 : ℕ))))
      simpa only [Nat.cast_pow] using mul_pos (by norm_num : (0:ℝ)<4) hl
    · rw [Nat.cast_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      have hl : Real.log 2 ≤ 1 := by simpa only [show (2 : ℝ)-1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      have hlog : ((j+1 : ℕ) : ℝ)*Real.log 2 ≤ b :=
        (mul_le_of_le_one_right (Nat.cast_nonneg _) hl).trans (Nat.cast_le.mpr (by omega))
      linarith only [hlog]
  have hsum : (∑ j ∈ Ico a b, reciprocalPrimeMass (2^j) (2^(j+1))) =
      reciprocalPrimeMass (2^a) (2^b) := by
    clear _hb hstep
    induction b, hab using Nat.le_induction with
    | base => simp [reciprocalPrimeMass, primesBetween]
    | succ b hab ih =>
      rw [sum_Ico_succ_top hab, ih]
      exact reciprocalPrimeMass_add (Nat.pow_le_pow_right (by norm_num) hab)
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ b))
  calc
    _ = ∑ j ∈ Ico a b, (1 : ℝ)/(4*b) := by simp; ring
    _ ≤ ∑ j ∈ Ico a b, reciprocalPrimeMass (2^j) (2^(j+1)) := sum_le_sum hstep
    _ = _ := hsum

/-- Both intervals contain a fixed positive reciprocal-prime mass. The
intervals are disjoint; their product lies above a smaller Vaughan cutoff. -/
theorem eventually_two_reciprocal_bands :
    ∀ᶠ k : ℕ in atTop,
      (1/24 : ℝ) ≤ reciprocalPrimeMass (2^(5*k)) (2^(6*k)) ∧
      (1/28 : ℝ) ≤ reciprocalPrimeMass (2^(6*k)) (2^(7*k)) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp eventually_prime_interval_counts
  filter_upwards [eventually_ge_atTop (max B 1)] with k hk
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 1) ((le_max_right B 1).trans hk)
  have hkp : k ≤ (2 : ℕ)^(5*k) := by
    exact (Nat.le_of_lt (Nat.lt_two_pow_self (n := k))).trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hcount (x : ℕ) (hx : 2^(5*k) ≤ x) := (hB x ((le_max_left B 1).trans (hk.trans (hkp.trans hx)))).2.2
  have h₁ := reciprocalPrimeMass_power_bands (by omega : 5*k ≤ 6*k) (by omega : 0 < 6*k) hcount
  have h₂ := reciprocalPrimeMass_power_bands (by omega : 6*k ≤ 7*k) (by omega : 0 < 7*k)
    (fun x hx => hcount x ((Nat.pow_le_pow_right (by norm_num) (by omega : 5*k ≤ 6*k)).trans hx))
  have he₁ : 6*k-5*k = k := by omega
  have he₂ : 7*k-6*k = k := by omega
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0.ne'
  constructor
  · convert h₁ using 1
    rw [he₁, Nat.cast_mul]
    field_simp
    ring
  · convert h₂ using 1
    rw [he₂, Nat.cast_mul]
    field_simp
    ring

#print axioms eventually_two_reciprocal_bands

end Erdos972PrimeReciprocalBands
