import Submission.IntervalPrimeWeights

/-!
# Reciprocal totient estimates on even-cofactor intervals

A direct prime-product expansion retains the coefficient 4/3 with the
logarithm of the endpoint ratio and a separately controlled endpoint error.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

lemma reciprocal_totient_double_eq_odd_product (n : ℕ) (hn : 0 < n) :
    1/((2*n).totient : ℝ) =
      (∏ p ∈ n.primeFactors.erase 2, (1+1/((p : ℝ)-1)))/(n : ℝ) := by
  have hfac : (2*n).primeFactors = insert 2 (n.primeFactors.erase 2) := by
    rw [Nat.primeFactors_mul (by decide) hn.ne',Nat.prime_two.primeFactors]
    ext p
    simp only [mem_union,mem_singleton,mem_insert,mem_erase]
    tauto
  have hh := totient_ratio_eq_prime_product (2*n) (by positivity)
  rw [hfac,prod_insert (by simp),Nat.cast_mul,Nat.cast_ofNat] at hh
  norm_num only [sub_self,add_sub_cancel_left,show (2 : ℝ)-1=1 by norm_num,div_one] at hh
  have he : (∏ p ∈ n.primeFactors.erase 2, (p : ℝ)/((p : ℝ)-1)) =
      ∏ p ∈ n.primeFactors.erase 2, (1+1/((p : ℝ)-1)) := by
    apply prod_congr rfl
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2).one_lt
    have hpne : (p : ℝ)-1 ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
    field_simp [hpne]
    ring
  rw [he] at hh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hphi : (0 : ℝ) < (2*n).totient := by exact_mod_cast Nat.totient_pos.mpr (by positivity : 0 < 2*n)
  apply (div_eq_div_iff hphi.ne' hnR.ne').mpr
  have hc := (div_eq_iff hphi.ne').mp hh
  nlinarith only [hc]

lemma odd_reciprocal_totient_euler_le (B : ℕ) :
    (∏ p ∈ (B+1).primesBelow.erase 2, (1+1/((p : ℝ)*((p : ℝ)-1)))) ≤ (4/3 : ℝ) := by
  by_cases hB : 2 ≤ B
  · have htwo : 2 ∈ (B+1).primesBelow := Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩
    have hh := reciprocal_totient_euler_product_le_two B
    rw [← prod_erase_mul _ _ htwo] at hh
    norm_num only [show 1+1/((2 : ℝ)*(2-1))=3/2 by norm_num] at hh
    linarith only [hh]
  · have he : (B+1).primesBelow.erase 2 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have h := Nat.mem_primesBelow.mp (mem_erase.mp hp).2
      have := h.2.two_le
      omega
    rw [he,prod_empty]
    norm_num

lemma odd_totient_product_le_exp_mass (B : ℕ) :
    (∏ p ∈ (B+1).primesBelow.erase 2, (1+1/((p : ℝ)-1))) ≤
      Real.exp (primeTotientMass B) := by
  let Q := (B+1).primesBelow.erase 2
  have hp1 (p : ℕ) (hp : p ∈ Q) : (1 : ℝ) < p := by
    exact_mod_cast (Nat.mem_primesBelow.mp (mem_erase.mp hp).2).2.one_lt
  have hmass : (∑ p ∈ Q, 1/((p : ℝ)-1)) ≤ primeTotientMass B := by
    calc
      _ = ∑ p ∈ Q, (p.totient : ℝ)⁻¹ := by
        apply sum_congr rfl
        intro p hp
        have hp' := (Nat.mem_primesBelow.mp (mem_erase.mp hp).2).2
        rw [Nat.totient_prime hp',Nat.cast_sub hp'.one_lt.le,Nat.cast_one,one_div]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
  calc
    _ ≤ ∏ p ∈ Q, Real.exp (1/((p : ℝ)-1)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact add_nonneg (by norm_num) (div_nonneg (by norm_num)
          (sub_nonneg.mpr (hp1 p hp).le))
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (1/((p : ℝ)-1))
    _ = Real.exp (∑ p ∈ Q, 1/((p : ℝ)-1)) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hmass

/-- The endpoint error is explicit and involves only the small-prime Euler
product. There is no subtraction of prefix upper bounds in this proof. -/
theorem reciprocal_totient_double_interval_le (A B : ℕ) (hA : 0 < A) (hAB : A ≤ B) :
    (∑ n ∈ Icc (A+1) B, 1/((2*n).totient : ℝ)) ≤
      (4/3 : ℝ)*Real.log ((B : ℝ)/A)+Real.exp (primeTotientMass B)/(A : ℝ) := by
  let Q := (B+1).primesBelow.erase 2
  let w : ℕ → ℝ := fun p => 1/((p : ℝ)-1)
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime := (Nat.mem_primesBelow.mp (mem_erase.mp hp).2).2
  have hw (p : ℕ) (hp : p ∈ Q) : 0 ≤ w p := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hQ p hp).one_lt
    dsimp [w]
    exact div_nonneg (by norm_num) (sub_nonneg.mpr hp1.le)
  have heq (n : ℕ) (hn : n ∈ Icc (A+1) B) :
      1/((2*n).totient : ℝ) = (∏ p ∈ Q with p ∣ n, (1+w p))/(n : ℝ) := by
    have hn0 : 0 < n := by have := (mem_Icc.mp hn).1; omega
    rw [reciprocal_totient_double_eq_odd_product n hn0]
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
  have hmain : (∏ p ∈ Q, (1+w p/(p : ℝ))) ≤ (4/3 : ℝ) := by
    convert odd_reciprocal_totient_euler_le B using 1
    apply prod_congr rfl
    intro p hp
    dsimp [w]
    rw [div_div,mul_comm]
  have hlog : 0 ≤ Real.log ((B : ℝ)/A) :=
    Real.log_nonneg ((one_le_div (by exact_mod_cast hA : (0 : ℝ) < A)).mpr (by exact_mod_cast hAB))
  calc
    _ = ∑ n ∈ Icc (A+1) B, (∏ p ∈ Q with p ∣ n, (1+w p))/(n : ℝ) := sum_congr rfl heq
    _ ≤ _ := interval_prime_product_average A B hA hAB Q hQ w hw
    _ ≤ Real.log ((B : ℝ)/A)*(4/3 : ℝ)+(1/(A : ℝ))*Real.exp (primeTotientMass B) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain hlog)
        (mul_le_mul_of_nonneg_left (odd_totient_product_le_exp_mass B) (by positivity))
    _ = _ := by ring

lemma even_reciprocal_totient_interval_eq (A B : ℕ) :
    (∑ n ∈ Icc (2*A+1) (2*B) with Even n, 1/(n.totient : ℝ)) =
      ∑ n ∈ Icc (A+1) B, 1/((2*n).totient : ℝ) := by
  have hset : (Icc (2*A+1) (2*B)).filter (fun n => Even n) =
      (Icc (A+1) B).image (fun n => 2*n) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnI,hne⟩ := mem_filter.mp hn
      have hmod := Nat.even_iff.mp hne
      refine mem_image.mpr ⟨n/2,mem_Icc.mpr ⟨?_,?_⟩,?_⟩ <;>
        have := mem_Icc.mp hnI <;> omega
    · intro hn
      obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
      have hm' := mem_Icc.mp hm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,⟨m,by omega⟩⟩
  rw [hset,sum_image (by intro a ha b hb he; dsimp at he; omega)]

/-- Even-cofactor mass on an interval, with the logarithmic ratio retained. -/
theorem even_reciprocal_totient_interval_le (A B : ℕ) (hA : 0 < A) (hAB : A ≤ B) :
    (∑ n ∈ Icc (2*A+1) (2*B) with Even n, 1/(n.totient : ℝ)) ≤
      (4/3 : ℝ)*Real.log ((B : ℝ)/A)+Real.exp (primeTotientMass B)/(A : ℝ) := by
  rw [even_reciprocal_totient_interval_eq]
  exact reciprocal_totient_double_interval_le A B hA hAB

end Erdos821.Sieve
