import Submission.ProductCutoffSelberg
import Submission.ComparableSlopeMean

/-! A two-linear-form prime sieve with a full squared-logarithmic denominator
and a polynomial rounding error. -/

namespace Erdos371
namespace FiniteSieve
open Finset

lemma twoLinear_selberg_upper_bound (S : Finset ℕ) (a b c d N z : ℕ)
    (hz : 1 ≤ z) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p ∧ p ≤ z)
    (ha : ∀ p ∈ S, a.Coprime p) (hc : ∀ p ∈ S, c.Coprime p)
    (hdet : a*d+1=b*c ∨ b*c+1=a*d) :
    (avoidanceCount (range N) (fun p n => p ∣ a*n+b ∨ p ∣ c*n+d) S : ℝ) ≤
      2*N*Real.exp (-2*(∑ p ∈ S, (1 : ℝ)/p)) + 2*(z+1 : ℝ)^64 := by
  have hlocal (p : ℕ) (hp : p ∈ S) : (twoLinearResidues p a b c d).card = 2 :=
    twoLinearResidues_card p a b c d (hS p hp).1.one_lt (ha p hp) (hc p hp) hdet
  have hcop : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hS p hp).1 (hS q hq).1).mpr hpq
  have hZ : (1 : ℝ) < (z+1 : ℝ)^16 := one_lt_pow₀ (by exact_mod_cast (show 1 < z+1 by omega)) (by decide)
  have hmass : (∑ p ∈ S, ((twoLinearResidues p a b c d).card : ℝ)/(p : ℝ)) =
      2*(∑ p ∈ S, (1 : ℝ)/p) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [hlocal p hp]
    push_cast
    ring
  have hm : (∑ p ∈ S, Real.log p*((twoLinearResidues p a b c d).card : ℝ)/(p : ℝ)) ≤
      Real.log ((z+1 : ℝ)^16)/2 := by
    have hsmall : (∑ p ∈ S, Real.log p/(p : ℝ)) ≤ 4*Real.log (z+1 : ℝ) := by
      calc
        _ ≤ ∑ p ∈ (z+1).primesBelow, Real.log p/((p : ℝ)-1) := by
          apply (sum_le_sum ?_).trans
            (sum_le_sum_of_subset_of_nonneg (t := (z+1).primesBelow) ?_ ?_)
          · intro p hp
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
            exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) (by linarith) (by linarith)
          · intro p hp
            exact Nat.mem_primesBelow.mpr ⟨by have := (hS p hp).2.2; omega,(hS p hp).1⟩
          · intro p hp _
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
            exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
        _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using prime_log_div_pred_sum_le (z+1)
    have he : (∑ p ∈ S, Real.log p*((twoLinearResidues p a b c d).card : ℝ)/(p : ℝ)) =
        2*(∑ p ∈ S, Real.log p/(p : ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [hlocal p hp]
      push_cast
      ring
    rw [he,Real.log_pow]
    norm_num
    linarith
  have h := residue_selberg_upper_bound S id (fun p => twoLinearResidues p a b c d)
    (fun p hp => (hS p hp).1.ne_zero) hcop
    (fun p _ => twoLinearResidues_subset p a b c d)
    (fun p hp => by rw [hlocal p hp]; exact ⟨by decide,(hS p hp).2.1⟩)
    ((z+1 : ℝ)^16) hZ hm N
  have havoid : avoidanceCount (range N) (fun p n => n%p ∈ twoLinearResidues p a b c d) S =
      avoidanceCount (range N) (fun p n => p ∣ a*n+b ∨ p ∣ c*n+d) S := by
    unfold avoidanceCount
    congr 1
    ext n
    simp only [mem_filter]
    apply and_congr_right
    intro hn
    exact forall₂_congr fun p hp => not_congr (mod_mem_twoLinearResidues p a b c d n (hS p hp).1.pos)
  simp only [id_eq] at h
  rw [havoid,hmass] at h
  simpa only [neg_mul,← pow_mul,Nat.reduceMul] using h

lemma twoLinear_prime_count_le_avoidance (S : Finset ℕ) (a b c d N z : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ z) :
    ((range N).filter (fun n => (a*n+b).Prime ∧ (c*n+d).Prime ∧ z<a*n+b ∧ z<c*n+d)).card ≤
      avoidanceCount (range N) (fun p n => p ∣ a*n+b ∨ p ∣ c*n+d) S := by
  classical
  unfold avoidanceCount
  conv_rhs => rw [filter_congr_decidable]
  apply card_le_card
  intro n hn
  obtain ⟨hn,h1,h2,hz1,hz2⟩ := mem_filter.mp hn
  apply mem_filter.mpr ⟨hn,?_⟩
  intro p hp hbad
  rcases hbad with hd | hd
  · rcases (Nat.dvd_prime h1).mp hd with he | he
    · exact (hS p hp).1.ne_one he
    · have := (hS p hp).2
      omega
  · rcases (Nat.dvd_prime h2).mp hd with he | he
    · exact (hS p hp).1.ne_one he
    · have := (hS p hp).2
      omega

/-- The polynomial error allows a fixed power of the endpoint as a sieve
cutoff, unlike the earlier degree-truncated Brun estimate. -/
theorem twoLinear_prime_count_selberg_bound (a b c d N z : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hz : 1 ≤ z)
    (hdet : a*d+1=b*c ∨ b*c+1=a*d) :
    (((range N).filter (fun n => (a*n+b).Prime ∧ (c*n+d).Prime ∧ z<a*n+b ∧ z<c*n+d)).card : ℝ) ≤
      2*Real.exp 2*slopeSieveFactor (2*(a*c))*N/(Real.log (z+1 : ℝ))^2 + 2*(z+1 : ℝ)^64 := by
  let S := goodSievingPrimes z (2*(a*c))
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ 2 < p ∧ p ≤ z := by
    obtain ⟨hpp,hpz,hnot⟩ := mem_goodSievingPrimes.mp hp
    refine ⟨hpp,?_,hpz⟩
    have hne : p ≠ 2 := by intro he; subst p; exact hnot (dvd_mul_right 2 (a*c))
    have := hpp.two_le
    omega
  have hcop (p : ℕ) (hp : p ∈ S) : a.Coprime p ∧ c.Coprime p := by
    obtain ⟨hpp,_,hnot⟩ := mem_goodSievingPrimes.mp hp
    have hpa : ¬p ∣ a := fun h => hnot (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h c) 2)
    have hpc : ¬p ∣ c := fun h => hnot (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h a) 2)
    exact ⟨((hpp.coprime_iff_not_dvd).mpr hpa).symm,((hpp.coprime_iff_not_dvd).mpr hpc).symm⟩
  have hcount := twoLinear_prime_count_le_avoidance S a b c d N z
    (fun p hp => ⟨(hS p hp).1,(hS p hp).2.2⟩)
  have hb := twoLinear_selberg_upper_bound S a b c d N z hz hS
    (fun p hp => (hcop p hp).1) (fun p hp => (hcop p hp).2) hdet
  have he := goodSievingPrimes_exp_bound z (2*(a*c)) hz (by positivity)
  have hm := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 2*N by positivity)
  apply ((Nat.cast_le (α := ℝ)).mpr hcount).trans
  apply hb.trans
  apply add_le_add _ le_rfl
  convert hm using 1 <;> ring

#print axioms twoLinear_prime_count_selberg_bound
end FiniteSieve
end Erdos371
