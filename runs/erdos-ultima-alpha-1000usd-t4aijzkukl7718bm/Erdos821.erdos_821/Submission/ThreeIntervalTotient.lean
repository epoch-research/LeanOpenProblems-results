import Submission.LocalDenominatorComparison
import Submission.TightIntervalTotient

/-!
# Retaining the prime-three correction in the cofactor average

The corrected even reciprocal-totient interval coefficient is 39/35.
The interval error is no larger than in the uncorrected product estimate.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Sieve
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma threeCorrection_mul_of_not_dvd (d k : ℕ) (hd : ¬3 ∣ d) :
    threeCorrection (d*k) = threeCorrection k := by
  simp only [threeCorrection,Nat.prime_three.dvd_mul,hd,false_or]

lemma threeCorrection_two_mul (n : ℕ) : threeCorrection (2*n) = threeCorrection n :=
  threeCorrection_mul_of_not_dvd 2 n (by decide)

noncomputable def threePrimeWeight (p : ℕ) : ℝ := if p=3 then 1 else 1/((p : ℝ)-1)

lemma threePrimeWeight_nonneg (p : ℕ) (hp : p.Prime) : 0 ≤ threePrimeWeight p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  unfold threePrimeWeight
  split_ifs
  · norm_num
  · exact div_nonneg (by norm_num) (sub_nonneg.mpr hp1.le)

lemma three_prime_product_eq (Q : Finset ℕ) :
    (3/4 : ℝ)*(∏ p ∈ Q, (1+threePrimeWeight p)) =
      (if 3 ∈ Q then 1 else 3/4)*(∏ p ∈ Q, (1+1/((p : ℝ)-1))) := by
  by_cases h3 : 3 ∈ Q
  · rw [if_pos h3,← prod_erase_mul _ _ h3,← prod_erase_mul Q (fun p : ℕ => (1 : ℝ)+1/((p : ℝ)-1)) h3]
    have he : (∏ p ∈ Q.erase 3, (1+threePrimeWeight p)) =
        ∏ p ∈ Q.erase 3, (1+1/((p : ℝ)-1)) := by
      apply prod_congr rfl
      intro p hp
      simp only [threePrimeWeight,if_neg (mem_erase.mp hp).1]
    rw [he]
    norm_num [threePrimeWeight]
    ring
  · rw [if_neg h3]
    congr 1
    apply prod_congr rfl
    intro p hp
    have hp3 : p ≠ 3 := fun he => h3 (he ▸ hp)
    simp only [threePrimeWeight,if_neg hp3]

lemma corrected_odd_euler_product_upper (B : ℕ) :
    (3/4 : ℝ)*(∏ p ∈ (B+1).primesBelow.erase 2, (1+threePrimeWeight p/(p : ℝ))) ≤ 39/35 := by
  let Q := (B+1).primesBelow.erase 2
  by_cases hB : 3 ≤ B
  · have h3 : 3 ∈ Q := mem_erase.mpr ⟨by decide,Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_three⟩⟩
    have hh := odd_reciprocal_totient_euler_le_thirteen_tenths B
    change (∏ p ∈ Q, (1+1/((p : ℝ)*((p : ℝ)-1)))) ≤ 13/10 at hh
    rw [← prod_erase_mul _ _ h3] at hh ⊢
    have he : (∏ p ∈ Q.erase 3, (1+threePrimeWeight p/(p : ℝ))) =
        ∏ p ∈ Q.erase 3, (1+1/((p : ℝ)*((p : ℝ)-1))) := by
      apply prod_congr rfl
      intro p hp
      simp only [threePrimeWeight,if_neg (mem_erase.mp hp).1,div_div,mul_comm]
    rw [he]
    norm_num [threePrimeWeight] at hh ⊢
    linarith only [hh]
  · have he : Q=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp2,hpp⟩ := mem_erase.mp hp
      have hh := Nat.mem_primesBelow.mp hpp
      have := hh.2.two_le
      omega
    change (3/4 : ℝ)*(∏ p ∈ Q, (1+threePrimeWeight p/(p : ℝ))) ≤ _
    rw [he,prod_empty]
    norm_num

lemma corrected_odd_product_le_exp_mass (B : ℕ) :
    (3/4 : ℝ)*(∏ p ∈ (B+1).primesBelow.erase 2, (1+threePrimeWeight p)) ≤
      Real.exp (primeTotientMass B) := by
  rw [three_prime_product_eq]
  apply le_trans _ (odd_totient_product_le_exp_mass B)
  have hprod : 0 ≤ ∏ p ∈ (B+1).primesBelow.erase 2, (1+1/((p : ℝ)-1)) := by
    apply prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.mem_primesBelow.mp (mem_erase.mp hp).2).2.one_lt
    exact add_nonneg (by norm_num) (div_nonneg (by norm_num) (sub_nonneg.mpr hp1.le))
  split_ifs <;> nlinarith only [hprod]

lemma corrected_reciprocal_totient_double_eq (n : ℕ) (hn : 0<n) :
    threeCorrection (2*n)/((2*n).totient : ℝ) =
      (3/4 : ℝ)*(∏ p ∈ n.primeFactors.erase 2, (1+threePrimeWeight p))/(n : ℝ) := by
  have h3 : 3 ∈ n.primeFactors.erase 2 ↔ 3 ∣ n := by
    constructor
    · intro h
      exact Nat.dvd_of_mem_primeFactors (mem_erase.mp h).2
    · intro h
      exact mem_erase.mpr ⟨by decide,Nat.prime_three.mem_primeFactors h hn.ne'⟩
  rw [three_prime_product_eq,threeCorrection_two_mul]
  have hh := reciprocal_totient_double_eq_odd_product n hn
  simp only [threeCorrection,h3]
  rw [div_eq_mul_one_div,hh]
  ring

lemma corrected_reciprocal_totient_double_interval (A B : ℕ) (hA : 0<A) (hAB : A ≤ B) :
    (∑ n ∈ Icc (A+1) B, threeCorrection (2*n)/((2*n).totient : ℝ)) ≤
      (39/35 : ℝ)*Real.log ((B : ℝ)/A)+Real.exp (primeTotientMass B)/(A : ℝ) := by
  let Q := (B+1).primesBelow.erase 2
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime := (Nat.mem_primesBelow.mp (mem_erase.mp hp).2).2
  have heq (n : ℕ) (hn : n ∈ Icc (A+1) B) :
      threeCorrection (2*n)/((2*n).totient : ℝ) =
        (3/4 : ℝ)*(∏ p ∈ Q with p ∣ n, (1+threePrimeWeight p))/(n : ℝ) := by
    have hn0 : 0<n := by have := (mem_Icc.mp hn).1; omega
    rw [corrected_reciprocal_totient_double_eq n hn0]
    have hset : n.primeFactors.erase 2 = Q.filter (fun p => p ∣ n) := by
      ext p
      constructor
      · intro hp
        obtain ⟨hp2,hpn⟩ := mem_erase.mp hp
        have hpl : p ≤ n := Nat.le_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hpn)
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨hp2,Nat.mem_primesBelow.mpr
          ⟨by have := (mem_Icc.mp hn).2; omega,Nat.prime_of_mem_primeFactors hpn⟩⟩,
          Nat.dvd_of_mem_primeFactors hpn⟩
      · intro hp
        obtain ⟨hpQ,hpn⟩ := mem_filter.mp hp
        exact mem_erase.mpr ⟨(mem_erase.mp hpQ).1,(hQ p hpQ).mem_primeFactors hpn hn0.ne'⟩
    rw [hset]
  have havg := mul_le_mul_of_nonneg_left (interval_prime_product_average A B hA hAB Q hQ
    threePrimeWeight (fun p hp => threePrimeWeight_nonneg p (hQ p hp))) (by norm_num : (0 : ℝ) ≤ 3/4)
  have hlog : 0 ≤ Real.log ((B : ℝ)/A) :=
    Real.log_nonneg ((one_le_div (by exact_mod_cast hA : (0 : ℝ)<A)).mpr (by exact_mod_cast hAB))
  calc
    _ = (3/4 : ℝ)*∑ n ∈ Icc (A+1) B, (∏ p ∈ Q with p ∣ n, (1+threePrimeWeight p))/(n : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl (fun n hn => by rw [heq n hn]; ring)
    _ ≤ _ := havg
    _ = Real.log ((B : ℝ)/A)*((3/4 : ℝ)*(∏ p ∈ Q, (1+threePrimeWeight p/(p : ℝ))))+
        (1/(A : ℝ))*((3/4 : ℝ)*(∏ p ∈ Q, (1+threePrimeWeight p))) := by ring
    _ ≤ Real.log ((B : ℝ)/A)*(39/35 : ℝ)+(1/(A : ℝ))*Real.exp (primeTotientMass B) :=
      add_le_add (mul_le_mul_of_nonneg_left (corrected_odd_euler_product_upper B) hlog)
        (mul_le_mul_of_nonneg_left (corrected_odd_product_le_exp_mass B) (by positivity))
    _ = _ := by ring

end Erdos821.Sieve
