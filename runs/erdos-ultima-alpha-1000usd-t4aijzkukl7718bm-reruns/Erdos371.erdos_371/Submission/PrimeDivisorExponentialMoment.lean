import FormalConjecturesUtil
import Submission.PrimeDivisorSecondMoment
import Submission.SieveEulerProduct

/-! A finite exponential-moment bound for prime-divisibility counts. -/

namespace Erdos371PrimeDivisorExponentialMoment

open Finset Erdos371PrimeDivisorSecondMoment Erdos371SmallPrimeAveraging
open Erdos371SieveEulerProduct

lemma two_pow_count (s : Finset ℕ) (m : ℕ) :
    (2:ℝ)^(divisorCount s m) = ∏ p ∈ s, (1+if p∣m then (1:ℝ) else 0) := by
  have he : (∏ p ∈ s, (1+if p∣m then (1:ℝ) else 0)) =
      ∏ p ∈ s, if p∣m then (2:ℝ) else 1 := by
    apply prod_congr rfl
    intro p _
    split_ifs <;> norm_num
  rw [he,← prod_filter]
  simp [divisorCount]

lemma mean_pow_le_euler (s : Finset ℕ) (hs : ∀ p∈s,p.Prime) (N : ℕ) :
    (∑ n ∈ range N, (2:ℝ)^(divisorCount s (n+1))) ≤
      (N:ℝ)*∏ p ∈ s, (1+1/(p:ℝ)) := by
  simp_rw [two_pow_count,prod_one_add]
  rw [sum_comm,mul_sum]
  apply sum_le_sum
  intro t ht
  have htprime : ∀ p∈t,p.Prime := fun p hp => hs p (mem_powerset.mp ht hp)
  have he (n : ℕ) : (∏ p ∈ t, if p∣n+1 then (1:ℝ) else 0)=
      if (∏ p ∈ t,p)∣n+1 then 1 else 0 := by
    simp only [prod_boole,product_dvd_iff htprime]
  simp_rw [he]
  calc
    _ = ((N/(∏ p ∈ t,p):ℕ):ℝ) := by simp [Nat.card_multiples]
    _ ≤ (N:ℝ)/((∏ p ∈ t,p:ℕ):ℝ) := Nat.cast_div_le
    _ = _ := by simp [Nat.cast_prod,prod_inv_distrib,div_eq_mul_inv]

lemma euler_le_exp_mass (s : Finset ℕ) :
    (∏ p ∈ s, (1+1/(p:ℝ))) ≤ Real.exp (mass s) := by
  rw [mass,Real.exp_sum]
  apply prod_le_prod
  · intro p _
    positivity
  · intro p _
    simpa [add_comm] using Real.add_one_le_exp (1/(p:ℝ))

/-- The upper bound holds for every finite prime set and every prefix. -/
theorem exponential_moment_bound (s : Finset ℕ) (hs : ∀ p∈s,p.Prime) (N : ℕ) :
    (∑ n ∈ range N, (2:ℝ)^(divisorCount s (n+1))) ≤ (N:ℝ)*Real.exp (mass s) :=
  (mean_pow_le_euler s hs N).trans
    (mul_le_mul_of_nonneg_left (euler_le_exp_mass s) (Nat.cast_nonneg N))

lemma badFactors_exponential_bound (s : Finset ℕ) (hs : ∀ p∈s,p.Prime) (K N : ℕ) :
    ((badFactors s K N).card:ℝ) ≤ (N:ℝ)*Real.exp (mass s)/(2:ℝ)^K := by
  have hmarkov : ((badFactors s K N).card:ℝ)*(2:ℝ)^K ≤
      ∑ n ∈ range N, (2:ℝ)^(divisorCount s (n+1)) := by
    rw [badFactors_card]
    calc
      _ = ∑ n ∈ range N, if K ≤ divisorCount s (n+1) then (2:ℝ)^K else 0 := by
        rw [← sum_filter]
        simp
      _ ≤ _ := by
        apply sum_le_sum
        intro n _
        split_ifs with h
        · exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h
        · positivity
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2^K)).mpr
  exact hmarkov.trans (exponential_moment_bound s hs N)

lemma exp_eight_mul_bound (k : ℕ) :
    Real.exp (8*(k+1:ℕ):ℝ)/(2:ℝ)^(32*(k+1)) ≤ 1/(2:ℝ)^(2*k) := by
  have he : Real.exp (8*(k+1:ℕ):ℝ)=(Real.exp 1)^(8*(k+1)) := by
    simpa using Real.exp_nat_mul 1 (8*(k+1))
  have h3 : Real.exp (8*(k+1:ℕ):ℝ) ≤ (3:ℝ)^(8*(k+1)) := by
    rw [he]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _
  have h34 : (3:ℝ)^(8*(k+1)) ≤ (2:ℝ)^(16*(k+1)) := by
    calc
      _ ≤ (4:ℝ)^(8*(k+1)) := by gcongr; norm_num
      _ = _ := by
        rw [show (4:ℝ)=2^2 by norm_num,← pow_mul]
        congr 1
        omega
  have hp : (0:ℝ)<2^(32*(k+1)) := by positivity
  have hq : (0:ℝ)<2^(2*k) := by positivity
  apply (div_le_div_iff₀ hp hq).mpr
  rw [one_mul]
  calc
    _ ≤ (2:ℝ)^(16*(k+1))*(2:ℝ)^(2*k) :=
      mul_le_mul_of_nonneg_right (h3.trans h34) hq.le
    _ = (2:ℝ)^(16*(k+1)+2*k) := (pow_add _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)

/-- An exponential tail at a linear multiple of the reciprocal-prime mass. -/
theorem linear_threshold_bound (s : Finset ℕ) (hs : ∀ p∈s,p.Prime)
    {k : ℕ} (hM : mass s ≤ 8*(k+1:ℕ)) (N : ℕ) :
    ((badFactors s (32*(k+1)) N).card:ℝ) ≤ (N:ℝ)/(2:ℝ)^(2*k) := by
  have he : Real.exp (mass s) ≤ Real.exp (8*(k+1:ℕ):ℝ) := Real.exp_le_exp.mpr hM
  calc
    _ ≤ _ := badFactors_exponential_bound s hs (32*(k+1)) N
    _ ≤ (N:ℝ)*Real.exp (8*(k+1:ℕ):ℝ)/(2:ℝ)^(32*(k+1)) := by gcongr
    _ = (N:ℝ)*(Real.exp (8*(k+1:ℕ):ℝ)/(2:ℝ)^(32*(k+1))) := by ring
    _ ≤ (N:ℝ)*(1/(2:ℝ)^(2*k)) :=
      mul_le_mul_of_nonneg_left (exp_eight_mul_bound k) (Nat.cast_nonneg N)
    _ = _ := by ring

end Erdos371PrimeDivisorExponentialMoment

#print axioms Erdos371PrimeDivisorExponentialMoment.exponential_moment_bound
#print axioms Erdos371PrimeDivisorExponentialMoment.linear_threshold_bound
