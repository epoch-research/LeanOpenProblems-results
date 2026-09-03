import Submission.TwoLinearSieve
import Submission.PrimeHarmonicBounds

/-! A fully specified pure Brun bound for two prime-producing linear forms.
Its constants and truncation degree are intentionally coarse. -/

namespace Erdos371
namespace FiniteSieve
open Finset

noncomputable def slopePrimeMass (m : ℕ) : ℝ :=
  ∑ p ∈ m.primeFactors, (1 : ℝ)/p

noncomputable def slopeSieveFactor (m : ℕ) : ℝ := Real.exp (2*slopePrimeMass m)

def goodSievingPrimes (z m : ℕ) : Finset ℕ :=
  (z+1).primesBelow.filter fun p => ¬p ∣ m

def brunDegree (z : ℕ) : ℕ := 72*(Nat.log 2 (Nat.log 2 z)+2)

lemma mem_goodSievingPrimes {z m p : ℕ} :
    p ∈ goodSievingPrimes z m ↔ p.Prime ∧ p ≤ z ∧ ¬p ∣ m := by
  simp only [goodSievingPrimes, mem_filter, Nat.mem_primesBelow, Nat.lt_succ_iff]
  tauto

lemma goodSievingPrimes_card_le (z m : ℕ) : (goodSievingPrimes z m).card ≤ z := by
  have hs : goodSievingPrimes z m ⊆ Icc 1 z := by
    intro p hp
    obtain ⟨hpp, hpz, _⟩ := mem_goodSievingPrimes.mp hp
    exact mem_Icc.mpr ⟨hpp.one_le, hpz⟩
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hs

lemma goodSievingPrimes_mass_le (z m : ℕ) :
    (∑ p ∈ goodSievingPrimes z m, (1 : ℝ)/p) ≤ primeHarmonic z :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)

lemma goodSievingPrimes_mass_lower (z m : ℕ) (hm : m ≠ 0) :
    primeHarmonic z - slopePrimeMass m ≤ ∑ p ∈ goodSievingPrimes z m, (1 : ℝ)/p := by
  have hsplit := sum_filter_add_sum_filter_not (z+1).primesBelow (fun p => ¬p ∣ m)
    (fun p : ℕ => (1 : ℝ)/p)
  simp only [not_not] at hsplit
  have hbad : (∑ p ∈ (z+1).primesBelow with p ∣ m, (1 : ℝ)/p) ≤ slopePrimeMass m := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp, hpm⟩ := mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesBelow.mp hp).2, hpm, hm⟩
    · intros; positivity
  change (∑ p ∈ goodSievingPrimes z m, (1 : ℝ)/p) + _ = primeHarmonic z at hsplit
  linarith

lemma brunDegree_sufficient (z m : ℕ) :
    6 * (∑ p ∈ goodSievingPrimes z m, (1 : ℝ)/p) ≤
      (2*brunDegree z+1 : ℕ) * Real.log 2 := by
  have hmass := (goodSievingPrimes_mass_le z m).trans (primeHarmonic_le_double_log z)
  have hl : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ (2*brunDegree z+1 : ℕ) by positivity)
  simp only [brunDegree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h ⊢
  nlinarith

lemma goodSievingPrimes_exp_bound (z m : ℕ) (hz : 1 ≤ z) (hm : m ≠ 0) :
    Real.exp (-2 * (∑ p ∈ goodSievingPrimes z m, (1 : ℝ)/p)) ≤
      Real.exp 2 * slopeSieveFactor m / (Real.log (z+1 : ℝ))^2 := by
  have hmass := goodSievingPrimes_mass_lower z m hm
  calc
    _ ≤ Real.exp (-2*primeHarmonic z + 2*slopePrimeMass m) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-2*primeHarmonic z) * slopeSieveFactor m := by rw [Real.exp_add]; rfl
    _ ≤ (Real.exp 2 / (Real.log (z+1 : ℝ))^2) * slopeSieveFactor m :=
      mul_le_mul_of_nonneg_right (exp_neg_two_primeHarmonic_le z hz) (Real.exp_nonneg _)
    _ = _ := by ring

/-- Uniform, quantitative upper bound for two simultaneous prime values
with determinant `±1`. No distribution theorem for prime pairs is assumed. -/
theorem twoLinear_prime_count_log_bound (a b c d N z : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hz : 1 ≤ z)
    (hdet : a*d+1=b*c ∨ b*c+1=a*d) :
    (((range N).filter fun n =>
      (a*n+b).Prime ∧ (c*n+d).Prime ∧ z < a*n+b ∧ z < c*n+d).card : ℝ) ≤
      2*Real.exp 2 * slopeSieveFactor (a*c) * N / (Real.log (z+1 : ℝ))^2 +
        (2*brunDegree z+1 : ℕ) * (z : ℝ)^(4*brunDegree z) := by
  have hS (p : ℕ) (hp : p ∈ goodSievingPrimes z (a*c)) : p.Prime :=
    (mem_goodSievingPrimes.mp hp).1
  have hcop (p : ℕ) (hp : p ∈ goodSievingPrimes z (a*c)) : a.Coprime p ∧ c.Coprime p := by
    obtain ⟨hpp, _, hnot⟩ := mem_goodSievingPrimes.mp hp
    have hpa : ¬p ∣ a := fun h => hnot (dvd_mul_of_dvd_left h c)
    have hpc : ¬p ∣ c := fun h => hnot (dvd_mul_of_dvd_right h a)
    exact ⟨((hpp.coprime_iff_not_dvd).mpr hpa).symm, ((hpp.coprime_iff_not_dvd).mpr hpc).symm⟩
  have h := twoLinear_prime_count_le (goodSievingPrimes z (a*c)) a b c d N (brunDegree z) z
    hS (fun p hp => (hcop p hp).1) (fun p hp => (hcop p hp).2) hdet
    (brunDegree_sufficient z (a*c)) hz (goodSievingPrimes_card_le z (a*c))
    (fun p hp => (mem_goodSievingPrimes.mp hp).2.1)
  have hexp := goodSievingPrimes_exp_bound z (a*c) hz (Nat.mul_pos ha hc).ne'
  have hmul := mul_le_mul_of_nonneg_left hexp (show (0 : ℝ) ≤ 2*N by positivity)
  refine h.trans (add_le_add ?_ le_rfl)
  convert hmul using 1; ring

#print axioms twoLinear_prime_count_log_bound
end FiniteSieve
end Erdos371
