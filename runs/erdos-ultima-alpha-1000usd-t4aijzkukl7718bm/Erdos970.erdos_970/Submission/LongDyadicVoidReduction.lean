import Submission.WeakerVoidReduction

/-! A restricted, explicitly conditional route to the exact quadratic target.
The doubling estimate is only assumed for intervals at least as long as the
prime budget. It is NOT proved here and is not the unrestricted inequality
refuted by large-prime dilution. -/
namespace Erdos970.GapAverages
open Finset Real Filter

/-- This remains an UNPROVED hypothesis, even when A=1. -/
def LongDyadicVoidBound (A : ℝ) : Prop :=
  ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m : ℕ, P.card ≤ m →
    coveredFraction P (2*m) ≤ A * coveredFraction P m ^ 2

lemma void_nonneg (P : Finset ℕ) (m : ℕ) : 0 ≤ coveredFraction P m := by
  unfold coveredFraction phaseMean
  exact div_nonneg (sum_nonneg (fun r _ => by split_ifs <;> norm_num)) (by positivity)

lemma long_dyadic_iteration {A : ℝ} (hA : 0 ≤ A) (h : LongDyadicVoidBound A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k : ℕ) (hk : P.card ≤ k) (j : ℕ) :
    A * coveredFraction P (2^j*k) ≤ (A*coveredFraction P k)^(2^j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hkj : k ≤ 2^j*k := Nat.le_mul_of_pos_left k (by positivity)
    have hh := mul_le_mul_of_nonneg_left (h P hP (2^j*k) (hk.trans hkj)) hA
    have hh' : A * coveredFraction P (2*(2^j*k)) ≤
        (A*coveredFraction P (2^j*k))^2 := by nlinarith only [hh]
    have hp := pow_le_pow_left₀ (mul_nonneg hA (void_nonneg P _)) ih 2
    have he : ((A*coveredFraction P k)^(2^j))^2 =
        (A*coveredFraction P k)^(2^(j+1)) := by rw [← pow_mul, pow_succ]
    rw [he] at hp
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh'.trans hp

/-- The verified variance and Mertens bounds give a polynomially small base
probability, uniformly over all sets of at most k primes. -/
lemma eventually_scaled_void_base (A : ℝ) (hA : 1 ≤ A) :
    ∀ᶠ k : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      A * coveredFraction P k ≤ exp (-log ((k : ℝ)+2)/2) := by
  let d := exp (-WeightedMertens.reciprocalConstant-1)
  have hd : 0 < d := exp_pos _
  have hA0 : 0 < A := by linarith
  have hE : 0 < d^2/A^2 := div_pos (sq_pos_of_pos hd) (sq_pos_of_pos hA0)
  filter_upwards [eventually_entropy_small hE, eventually_ge_atTop 1] with k hsmall hk1
  intro P hP hPk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  let L := log ((k : ℝ)+2)
  have hL : 0 < L := log_pos (by linarith)
  have hδ := density_pos P hP
  have hdens : d/L ≤ density P := by
    simpa only [d, L, density, one_div] using WeightedMertens.prime_set_density_lower P hP k hPk
  have hden : d ≤ density P * L := (div_le_iff₀ hL).mp hdens
  have hvar := coveredFraction_bound P hP k (by omega)
  have hv0 := void_nonneg P k
  have hvupper : coveredFraction P k ≤ L/(d*k) := by
    apply (le_div_iff₀ (mul_pos hd hk0)).mpr
    have hb := mul_le_mul_of_nonneg_right hden (mul_nonneg hk0.le hv0)
    have hc := mul_le_mul_of_nonneg_right (show (k : ℝ)*density P*coveredFraction P k ≤ 1 by linarith) hL.le
    nlinarith only [hb, hc]
  have hupper : A*coveredFraction P k ≤ (A*L)/(d*k) := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hvupper hA0.le
  have hlogs : 12*L^2*A^2 < d^2*k := by
    have hh := (lt_div_iff₀ (sq_pos_of_pos hA0)).mp
      (show 12*L^2 < (d^2*k)/A^2 by simpa only [div_mul_eq_mul_div] using hsmall)
    exact hh
  have hlogk := mul_lt_mul_of_pos_right hlogs hk0
  have hnum : (A*L)^2*((k : ℝ)+2) ≤ (d*k)^2 := by
    have hh := mul_le_mul_of_nonneg_left (show (k : ℝ)+2 ≤ 3*k by linarith)
      (show 0 ≤ (A*L)^2 by positivity)
    nlinarith only [hlogk, hh, mul_nonneg (sq_nonneg d) (sq_nonneg (k : ℝ))]
  have hratio : ((A*L)/(d*k))^2 ≤ 1/((k : ℝ)+2) := by
    rw [div_pow]
    exact (div_le_div_iff₀ (sq_pos_of_pos (mul_pos hd hk0)) (by positivity)).mpr (by simpa only [one_mul] using hnum)
  have hex : (exp (-log ((k : ℝ)+2)/2))^2 = 1/((k : ℝ)+2) := by
    rw [← exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show 2*(-log ((k : ℝ)+2)/2) = -log ((k : ℝ)+2) by ring,
      exp_neg, exp_log (by positivity), one_div]
  have hr0 : 0 ≤ (A*L)/(d*k) := by positivity
  have he0 := exp_pos (-log ((k : ℝ)+2)/2)
  have hr : (A*L)/(d*k) ≤ exp (-log ((k : ℝ)+2)/2) := by nlinarith only [hratio, hex, hr0, he0]
  exact hupper.trans hr

lemma long_dyadic_tail {A : ℝ} (hA : 1 ≤ A) (h : LongDyadicVoidBound A)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (k j : ℕ) (hk : P.card ≤ k)
    (hbase : A*coveredFraction P k ≤ exp (-log ((k : ℝ)+2)/2)) :
    coveredFraction P (2^j*k) ≤ exp (-(log ((k : ℝ)+2)*(2 : ℝ)^j/2)) := by
  have hi := long_dyadic_iteration (by linarith : 0 ≤ A) h P hP k hk j
  have hp := pow_le_pow_left₀ (mul_nonneg (by linarith : 0 ≤ A) (void_nonneg P k)) hbase (2^j)
  have hv := mul_le_mul_of_nonneg_right hA (void_nonneg P (2^j*k))
  simp only [one_mul] at hv
  calc
    _ ≤ (A*coveredFraction P k)^(2^j) := hv.trans hi
    _ ≤ (exp (-log ((k : ℝ)+2)/2))^(2^j) := hp
    _ = _ := by rw [← exp_nat_mul]; congr 1; push_cast; ring

/-- CONDITIONAL: only long-interval doubling, with any fixed multiplicative
loss A>=1, is needed to obtain the precise unchanged conjecture. -/
theorem eventually_quadratic_of_long_dyadic {A : ℝ} (hA : 1 ≤ A)
    (h : LongDyadicVoidBound A) :
    ∀ᶠ k : ℕ in atTop, jacobsthalFunction k ≤ 128*k^2 := by
  filter_upwards [eventually_scaled_void_base A hA, eventually_ge_atTop 128] with k hbase hk128
  have hk : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let j := Nat.log 2 (128*k)
  have hlow : 128*k < 2^(j+1) := Nat.lt_pow_succ_log_self (by norm_num) (128*k)
  have hupp : 2^j ≤ 128*k := Nat.pow_log_le_self 2 (by positivity : 128*k ≠ 0)
  have hlow' : 64*k < 2^j := by rw [pow_succ] at hlow; omega
  let m := 2^j*k
  have hm : m ≤ 128*k^2 := by dsimp [m]; nlinarith
  apply (jacobsthalFunction_le_iff k (128*k^2)).mpr
  by_contra hbad
  obtain ⟨P,hP,hPk,r,hcov⟩ := (not_isJacobsthalBound_iff_cover k (128*k^2)).mp hbad
  obtain ⟨Q,s,hQ,hQk,hcap,hcov'⟩ := BoundedPrimeCover.normalize hP hPk hcov
  have htail := long_dyadic_tail hA h Q hQ k j hQk (hbase Q hQ hQk)
  have hL : 0 < log ((k : ℝ)+2) := log_pos (by linarith)
  have hbudget : (k : ℝ)*log (((k : ℝ)+2)^14) <
      log ((k : ℝ)+2)*(2 : ℝ)^j/2 := by
    have hl : 64*(k : ℝ) < (2 : ℝ)^j := by exact_mod_cast hlow'
    have hh := mul_lt_mul_of_pos_right hl hL
    rw [log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_pos hkR hL]
  obtain ⟨x,hx,havoid⟩ := survivor_of_exponential_tail_of_cap hQ hQk
    (one_le_pow₀ (by linarith : (1 : ℝ) ≤ (k : ℝ)+2))
    (fun q hq => scaled_quadratic_cap hk128 (hcap q hq)) htail hbudget s
  obtain ⟨q,hq,hxq⟩ := hcov' x (hx.trans_le hm)
  exact havoid q hq hxq

theorem quadratic_bound_of_long_dyadic {A : ℝ} (hA : 1 ≤ A)
    (h : LongDyadicVoidBound A) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C*k^2 :=
  quadratic_bound_of_eventually_scaled (by norm_num : 0 < (128 : ℕ))
    (eventually_quadratic_of_long_dyadic hA h)

#print axioms long_dyadic_iteration
#print axioms eventually_scaled_void_base
#print axioms quadratic_bound_of_long_dyadic
end Erdos970.GapAverages
