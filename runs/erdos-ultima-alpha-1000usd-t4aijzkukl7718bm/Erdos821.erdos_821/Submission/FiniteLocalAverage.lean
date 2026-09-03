import Submission.FiniteLocalProducts
import Submission.RestrictedHarmonicWeights

/-! # Cofactor averages with a tail constant tending to one -/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

noncomputable def retainedPrimePool (D : ℕ) : Finset ℕ := (D+1).primesBelow.erase 2

noncomputable def localAverageConstant (D : ℕ) : ℝ := (D : ℝ)/((D : ℝ)-1)

lemma retainedPrimePool_properties (D q : ℕ) (hq : q ∈ retainedPrimePool D) :
    q.Prime ∧ 2<q ∧ q ≤ D := by
  obtain ⟨hq2,hqP⟩ := mem_erase.mp hq
  obtain ⟨hqD,hpr⟩ := Nat.mem_primesBelow.mp hqP
  have := hpr.two_le
  exact ⟨hpr,by omega,by omega⟩

lemma retainedPrimePool_mono : Monotone retainedPrimePool := by
  intro A B hAB q hq
  obtain ⟨hp,hp2,hpA⟩ := retainedPrimePool_properties A q hq
  exact mem_erase.mpr ⟨by omega,Nat.mem_primesBelow.mpr ⟨by omega,hp⟩⟩

lemma localAverageConstant_one_le (D : ℕ) (hD : 2 ≤ D) : 1 ≤ localAverageConstant D := by
  have hd : (2 : ℝ) ≤ D := by exact_mod_cast hD
  unfold localAverageConstant
  exact (one_le_div (by linarith)).mpr (by linarith)

lemma retained_average_product_upper (D B : ℕ) (hD : 2 ≤ D) (hDB : D ≤ B) :
    finiteLocalBase (retainedPrimePool D)*
      (∏ p ∈ retainedPrimePool B, (1+finiteLocalPrimeWeight (retainedPrimePool D) p/(p : ℝ))) ≤
        localAverageConstant D := by
  rw [finiteLocalPrimeWeight_average_product _ _
    (fun q hq => (retainedPrimePool_properties D q hq).2.1) (retainedPrimePool_mono hDB)]
  let P := retainedPrimePool B \ retainedPrimePool D
  have hP (p : ℕ) (hp : p ∈ P) : D<p ∧ p ≤ B ∧ p.Prime := by
    obtain ⟨hpB,hpD⟩ := mem_sdiff.mp hp
    obtain ⟨hpr,hp2,hpB'⟩ := retainedPrimePool_properties B p hpB
    have hpgt : D<p := by
      by_contra h
      exact hpD (mem_erase.mpr ⟨by omega,Nat.mem_primesBelow.mpr ⟨by omega,hpr⟩⟩)
    exact ⟨hpgt,hpB',hpr⟩
  have hsum : (∑ p ∈ P, 1/((p : ℝ)*((p : ℝ)-1))) ≤ 1/(D : ℝ) := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (show P ⊆ Icc (D+1) (B+1) by
      intro p hp
      obtain ⟨hlo,hhi,_⟩ := hP p hp
      exact mem_Icc.mpr ⟨hlo,by omega⟩) (fun p hp _ => ?_))
      (sum_reciprocal_successive_tail D (B+1) (by omega))
    have hpR : (1 : ℝ) < p := by
      have := (mem_Icc.mp hp).1
      exact_mod_cast (show 1<p by omega)
    exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
  calc
    _ ≤ ∏ p ∈ P, Real.exp (1/((p : ℝ)*((p : ℝ)-1))) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpR : (1 : ℝ) < p := by exact_mod_cast (hP p hp).2.2.one_lt
        exact add_nonneg (by norm_num) (div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith)))
      · intro p _hp
        simpa only [add_comm] using Real.add_one_le_exp (1/((p : ℝ)*((p : ℝ)-1)))
    _ = Real.exp (∑ p ∈ P, 1/((p : ℝ)*((p : ℝ)-1))) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1/(D : ℝ)) := Real.exp_le_exp.mpr hsum
    _ ≤ localAverageConstant D := by
      have h0 : (0 : ℝ) ≤ 1/(D : ℝ) := by positivity
      have h1 : 1/(D : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      apply (Real.exp_bound_div_one_sub_of_interval h0 h1).trans_eq
      unfold localAverageConstant
      have hd0 : (D : ℝ) ≠ 0 := ne_of_gt (by linarith)
      field_simp

lemma retained_endpoint_product_upper (D B : ℕ) :
    finiteLocalBase (retainedPrimePool D)*
      (∏ p ∈ retainedPrimePool B, (1+finiteLocalPrimeWeight (retainedPrimePool D) p)) ≤
        Real.exp (Erdos821.primeTotientMass B) := by
  apply (finiteLocalPrimeWeight_product_le _ _
    (fun q hq => (retainedPrimePool_properties D q hq).2.1)
    (fun p hp => (retainedPrimePool_properties B p hp).1)).trans
  exact odd_totient_product_le_exp_mass B

lemma finite_corrected_double_eq_filter (D B n : ℕ) (hn : 0<n) (hnB : n ≤ B) :
    finiteLocalCorrection (retainedPrimePool D) (2*n)/((2*n).totient : ℝ) =
      finiteLocalBase (retainedPrimePool D)*
        (∏ p ∈ retainedPrimePool B with p ∣ n, (1+finiteLocalPrimeWeight (retainedPrimePool D) p))/(n : ℝ) := by
  rw [finite_corrected_reciprocal_totient_double_eq _
    (fun q hq => ⟨(retainedPrimePool_properties D q hq).1,(retainedPrimePool_properties D q hq).2.1⟩) n hn]
  have he : n.primeFactors.erase 2=(retainedPrimePool B).filter (fun p => p ∣ n) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp2,hpn⟩ := mem_erase.mp hp
      have hpl := (Nat.le_of_dvd hn (Nat.dvd_of_mem_primeFactors hpn)).trans hnB
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨hp2,Nat.mem_primesBelow.mpr
        ⟨by omega,Nat.prime_of_mem_primeFactors hpn⟩⟩,Nat.dvd_of_mem_primeFactors hpn⟩
    · intro hp
      obtain ⟨hpB,hpn⟩ := mem_filter.mp hp
      exact mem_erase.mpr ⟨(mem_erase.mp hpB).1,
        (retainedPrimePool_properties B p hpB).1.mem_primeFactors hpn hn.ne'⟩
  rw [he]

lemma finite_corrected_double_interval (D A B : ℕ) (hD : 2 ≤ D) (hDB : D ≤ B)
    (hA : 0<A) (hAB : A ≤ B) :
    (∑ n ∈ Icc (A+1) B, finiteLocalCorrection (retainedPrimePool D) (2*n)/((2*n).totient : ℝ)) ≤
      localAverageConstant D*Real.log ((B : ℝ)/A)+Real.exp (Erdos821.primeTotientMass B)/(A : ℝ) := by
  let Q := retainedPrimePool D
  let P := retainedPrimePool B
  have hQ (q : ℕ) (hq : q ∈ Q) : 2<q := (retainedPrimePool_properties D q hq).2.1
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := (retainedPrimePool_properties B p hp).1
  have havg := mul_le_mul_of_nonneg_left (interval_prime_product_average A B hA hAB P hP
    (finiteLocalPrimeWeight Q) (fun p hp => finiteLocalPrimeWeight_nonneg Q hQ p (hP p hp)))
    (finiteLocalBase_pos Q hQ).le
  have hlog : 0 ≤ Real.log ((B : ℝ)/A) :=
    Real.log_nonneg ((one_le_div (by exact_mod_cast hA : (0 : ℝ)<A)).mpr (by exact_mod_cast hAB))
  calc
    _ = finiteLocalBase Q*∑ n ∈ Icc (A+1) B,
        (∏ p ∈ P with p ∣ n, (1+finiteLocalPrimeWeight Q p))/(n : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      rw [finite_corrected_double_eq_filter D B n (by have := (mem_Icc.mp hn).1; omega) (mem_Icc.mp hn).2]
      ring
    _ ≤ _ := havg
    _ = Real.log ((B : ℝ)/A)*(finiteLocalBase Q*(∏ p ∈ P, (1+finiteLocalPrimeWeight Q p/(p : ℝ))))+
        (1/(A : ℝ))*(finiteLocalBase Q*(∏ p ∈ P, (1+finiteLocalPrimeWeight Q p))) := by ring
    _ ≤ Real.log ((B : ℝ)/A)*localAverageConstant D+(1/(A : ℝ))*Real.exp (Erdos821.primeTotientMass B) :=
      add_le_add (mul_le_mul_of_nonneg_left (retained_average_product_upper D B hD hDB) hlog)
        (mul_le_mul_of_nonneg_left (retained_endpoint_product_upper D B) (by positivity))
    _ = _ := by ring

lemma finite_corrected_double_prefix (D B : ℕ) (hD : 2 ≤ D) (hDB : D ≤ B) :
    (∑ n ∈ Icc 1 B, finiteLocalCorrection (retainedPrimePool D) (2*n)/((2*n).totient : ℝ)) ≤
      localAverageConstant D*(harmonic B : ℝ) := by
  let Q := retainedPrimePool D
  let P := retainedPrimePool B
  have hQ (q : ℕ) (hq : q ∈ Q) : 2<q := (retainedPrimePool_properties D q hq).2.1
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := (retainedPrimePool_properties B p hp).1
  have havg := mul_le_mul_of_nonneg_left (harmonic_average_restricted_prime_product B P hP
    (finiteLocalPrimeWeight Q) (fun p hp => finiteLocalPrimeWeight_nonneg Q hQ p (hP p hp)))
    (finiteLocalBase_pos Q hQ).le
  have hH : 0 ≤ (harmonic B : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact sum_nonneg (fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  calc
    _ = finiteLocalBase Q*∑ n ∈ Icc 1 B,
        (∏ p ∈ P with p ∣ n, (1+finiteLocalPrimeWeight Q p))/(n : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      rw [finite_corrected_double_eq_filter D B n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2]
      ring
    _ ≤ _ := havg
    _ = (harmonic B : ℝ)*(finiteLocalBase Q*(∏ p ∈ P, (1+finiteLocalPrimeWeight Q p/(p : ℝ)))) := by ring
    _ ≤ (harmonic B : ℝ)*localAverageConstant D :=
      mul_le_mul_of_nonneg_left (retained_average_product_upper D B hD hDB) hH
    _ = _ := by ring

end Erdos821.Sieve
