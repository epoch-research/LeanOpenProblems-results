import Submission.TightReciprocalTotient

/-! # Direct interval cofactor mass with coefficient 13/10

This uses a direct interval estimate, not a difference of prefix upper bounds.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.Sieve
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma odd_reciprocal_totient_euler_le_thirteen_tenths (B : ℕ) :
    (∏ p ∈ (B+1).primesBelow.erase 2, (1+1/((p : ℝ)*((p : ℝ)-1)))) ≤ (13/10 : ℝ) := by
  by_cases hB : 2 ≤ B
  · have htwo : 2 ∈ (B+1).primesBelow := Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩
    have hh := reciprocal_totient_euler_product_le_thirty_nine_twentieths B
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
theorem reciprocal_totient_double_interval_le_thirteen_tenths (A B : ℕ) (hA : 0 < A) (hAB : A ≤ B) :
    (∑ n ∈ Icc (A+1) B, 1/((2*n).totient : ℝ)) ≤
      (13/10 : ℝ)*Real.log ((B : ℝ)/A)+Real.exp (primeTotientMass B)/(A : ℝ) := by
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
  have hmain : (∏ p ∈ Q, (1+w p/(p : ℝ))) ≤ (13/10 : ℝ) := by
    convert odd_reciprocal_totient_euler_le_thirteen_tenths B using 1
    apply prod_congr rfl
    intro p hp
    dsimp [w]
    rw [div_div,mul_comm]
  have hlog : 0 ≤ Real.log ((B : ℝ)/A) :=
    Real.log_nonneg ((one_le_div (by exact_mod_cast hA : (0 : ℝ) < A)).mpr (by exact_mod_cast hAB))
  calc
    _ = ∑ n ∈ Icc (A+1) B, (∏ p ∈ Q with p ∣ n, (1+w p))/(n : ℝ) := sum_congr rfl heq
    _ ≤ _ := interval_prime_product_average A B hA hAB Q hQ w hw
    _ ≤ Real.log ((B : ℝ)/A)*(13/10 : ℝ)+(1/(A : ℝ))*Real.exp (primeTotientMass B) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain hlog)
        (mul_le_mul_of_nonneg_left (odd_totient_product_le_exp_mass B) (by positivity))
    _ = _ := by ring
/-- Even-cofactor mass on an interval, with the logarithmic ratio retained. -/
theorem even_reciprocal_totient_interval_le_thirteen_tenths (A B : ℕ) (hA : 0 < A) (hAB : A ≤ B) :
    (∑ n ∈ Icc (2*A+1) (2*B) with Even n, 1/(n.totient : ℝ)) ≤
      (13/10 : ℝ)*Real.log ((B : ℝ)/A)+Real.exp (primeTotientMass B)/(A : ℝ) := by
  rw [even_reciprocal_totient_interval_eq]
  exact reciprocal_totient_double_interval_le_thirteen_tenths A B hA hAB
lemma evenBlockMass_upper_thirteen_tenths (a b m : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : 1 ≤ m) :
    evenBlockMass a b m ≤
      (13/10 : ℝ)*64*((b : ℝ)-a)*m*Real.log 2 +
        (Real.exp 1024*(b : ℝ)^8)*((m : ℝ)^8/(2 : ℝ)^m) := by
  let A : ℕ := 2^(64*a*m-1)
  let B : ℕ := 2^(64*b*m-1)
  have ham : m ≤ a*m := Nat.le_mul_of_pos_left m ha
  have hbm : m ≤ b*m := ham.trans (Nat.mul_le_mul_right m hab)
  have haexp : 1 ≤ 64*a*m := by nlinarith only [ham,hm]
  have hbexp : 1 ≤ 64*b*m := by nlinarith only [hbm,hm]
  have hAB : A ≤ B := by
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_right m (Nat.mul_le_mul_left 64 hab)) 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have htwoA : 2*A=2^(64*a*m) := two_mul_pow_pred_eq _ haexp
  have htwoB : 2*B=2^(64*b*m) := two_mul_pow_pred_eq _ hbexp
  have hlog : Real.log ((B : ℝ)/A) = 64*((b : ℝ)-a)*m*Real.log 2 := by
    rw [Real.log_div (by exact_mod_cast hB.ne' : (B : ℝ) ≠ 0)
      (by exact_mod_cast hA.ne' : (A : ℝ) ≠ 0)]
    simp only [A,B,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,
      Nat.cast_sub haexp,Nat.cast_sub hbexp,Nat.cast_mul,Nat.cast_one]
    ring
  have hBcap : B ≤ progressionScaleN (b*m) := by
    change 2^(64*b*m-1) ≤ 2^(64*(b*m))
    apply Nat.pow_le_pow_right (by decide)
    simpa only [mul_assoc] using Nat.sub_le (64*b*m) 1
  have hmass : Real.exp (primeTotientMass B) ≤ Real.exp 1024*(b : ℝ)^8*(m : ℝ)^8 := by
    have h := (Real.exp_le_exp.mpr (primeTotientMass_mono hBcap)).trans
      (exp_primeTotientMass_scale_upper (b*m) (by omega))
    simpa only [Nat.cast_mul,mul_pow,mul_assoc] using h
  have hApow : (2 : ℝ)^m ≤ A := by
    have hn : 2^m ≤ A := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp only [A]
      have hs := Nat.sub_add_cancel haexp
      nlinarith only [ham,hm,hs]
    exact_mod_cast hn
  have herr : Real.exp (primeTotientMass B)/(A : ℝ) ≤
      (Real.exp 1024*(b : ℝ)^8)*((m : ℝ)^8/(2 : ℝ)^m) := by
    calc
      _ ≤ (Real.exp 1024*(b : ℝ)^8*(m : ℝ)^8)/(2 : ℝ)^m := by
        exact div_le_div₀ (by positivity) hmass (by positivity) hApow
      _ = _ := by ring
  have hh := even_reciprocal_totient_interval_le_thirteen_tenths A B hA hAB
  rw [htwoA,htwoB,hlog] at hh
  change evenBlockMass a b m ≤ _ at hh
  exact hh.trans (by nlinarith only [herr])

lemma eventually_evenBlockMass_upper_thirteen_tenths (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      evenBlockMass a b m ≤ (13/10 : ℝ)*64*((b : ℝ)-a)*m*Real.log 2+η := by
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt 8
    (by norm_num : (1 : ℝ) < 2)).const_mul (Real.exp 1024*(b : ℝ)^8)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually (eventually_le_nhds hη),eventually_ge_atTop 1] with m he hm
  exact (evenBlockMass_upper_thirteen_tenths a b m ha hab hm).trans (_root_.add_le_add le_rfl he)

end Erdos821.Sieve
