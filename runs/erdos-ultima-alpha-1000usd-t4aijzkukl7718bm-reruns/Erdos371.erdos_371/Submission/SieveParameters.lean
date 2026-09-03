import FormalConjecturesUtil
import Submission.SieveEulerProduct
import Submission.PrimeHarmonicBlocks

/-! Explicit discrete parameters for the finite two-linear-form sieve. -/

namespace Erdos371SieveParameters

open Finset Erdos371PrimeHarmonicBlocks Erdos371SieveEulerProduct
open Erdos371TwoLinearSieve

noncomputable def primeMass (z : ℕ) : ℝ := ∑ p ∈ z.primesBelow, 1/(p:ℝ)

def cutoff (k : ℕ) : ℕ := 2^(2^k)
def depth (k : ℕ) : ℕ := 256*(k+1)^2
def threshold (k : ℕ) : ℕ := (cutoff k)^(12*depth k)

lemma cutoff_two_le (k : ℕ) : 2 ≤ cutoff k := by
  exact Nat.le_pow (by positivity)

lemma depth_pos (k : ℕ) : 0 < depth k := by unfold depth; positivity
lemma index_le_depth (k : ℕ) : k ≤ depth k := by unfold depth; nlinarith

lemma primeMass_mono {a b : ℕ} (hab : a ≤ b) : primeMass a ≤ primeMass b := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hpr⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨hp.trans_le hab, hpr⟩
  · intro p _ _
    positivity

lemma primesBelow_power_union (k : ℕ) :
    (2^(k+1)).primesBelow = (2^k).primesBelow ∪ block k := by
  ext p
  simp only [Finset.mem_union, Nat.mem_primesBelow, mem_block]
  have hpow : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
  constructor
  · rintro ⟨hlt, hp⟩
    by_cases hlow : p < 2^k
    · exact Or.inl ⟨hlow, hp⟩
    · exact Or.inr ⟨hp, by omega, hlt⟩
  · rintro (⟨hlt, hp⟩ | ⟨hp, hge, hlt⟩)
    · exact ⟨hlt.trans_le hpow, hp⟩
    · exact ⟨hlt, hp⟩

lemma primesBelow_disjoint_block (k : ℕ) : Disjoint (2^k).primesBelow (block k) := by
  apply Finset.disjoint_left.mpr
  intro p hp hb
  exact (not_le_of_gt (Nat.mem_primesBelow.mp hp).1) (mem_block.mp hb).2.1

lemma primeMass_power_succ (k : ℕ) : primeMass (2^(k+1)) ≤ 4*(harmonic k:ℝ) := by
  induction k with
  | zero => norm_num [primeMass, show (2:ℕ).primesBelow=∅ from by decide]
  | succ k ih =>
    have he : primeMass (2^((k+1)+1)) = primeMass (2^(k+1)) + blockMass (k+1) := by
      unfold primeMass blockMass
      rw [primesBelow_power_union, Finset.sum_union (primesBelow_disjoint_block _)]
    rw [he, harmonic_succ]
    push_cast
    have hb := blockMass_le (by omega : 0<k+1)
    push_cast at hb
    rw [div_eq_mul_inv] at hb
    linarith

lemma primeMass_power (k : ℕ) : primeMass (2^k) ≤ 4*(harmonic k:ℝ) := by
  exact (primeMass_mono (Nat.pow_le_pow_right (by decide) (by omega))).trans
    (primeMass_power_succ k)

lemma primeMass_cutoff (k : ℕ) : primeMass (cutoff k) ≤ 4*((k:ℝ)+1) := by
  have hh := harmonic_le_one_add_log (2^k)
  push_cast at hh
  rw [Real.log_pow] at hh
  have hl : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hmul := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg k : (0:ℝ)≤k)
  have hp := primeMass_power (2^k)
  change primeMass (cutoff k) ≤ _ at hp
  nlinarith

lemma density_sum_le (k a c : ℕ) :
    (∑ p ∈ (cutoff k).primesBelow, linearDensity a c p) ≤ 8*((k:ℝ)+1) := by
  calc
    _ ≤ ∑ p ∈ (cutoff k).primesBelow, 2/(p:ℝ) :=
      Finset.sum_le_sum (fun _ _ => linearDensity_le_two_div)
    _ = 2*primeMass (cutoff k) := by simp [primeMass, Finset.mul_sum, div_eq_mul_inv]
    _ ≤ _ := by linarith [primeMass_cutoff k]

lemma depth_large (k a c : ℕ) :
    4*(∑ p ∈ (cutoff k).primesBelow, linearDensity a c p)^2 ≤ (depth k:ℝ) := by
  have hnonneg : 0 ≤ ∑ p ∈ (cutoff k).primesBelow, linearDensity a c p :=
    Finset.sum_nonneg (fun _ _ => linearDensity_nonneg)
  have hh := density_sum_le k a c
  have hs := sq_le_sq₀ hnonneg (by positivity : (0:ℝ)≤8*((k:ℝ)+1)) |>.mpr hh
  unfold depth
  push_cast
  nlinarith

lemma euler_cutoff_le (k : ℕ) : euler (cutoff k).primesBelow ≤ 2/(2:ℝ)^k := by
  have hp : 1 < cutoff k := by have := cutoff_two_le k; omega
  have hl : Real.log (cutoff k) = (2:ℝ)^k * Real.log 2 := by
    simp [cutoff, Real.log_pow]
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  calc
    _ ≤ 1/Real.log (cutoff k) := euler_le_inverse_log hp
    _ ≤ 1/((2:ℝ)^k * (1/2)) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [hl]
      exact mul_le_mul_of_nonneg_left hl2 (by positivity)
    _ = _ := by ring

lemma euler_cutoff_sq_le (k : ℕ) : (euler (cutoff k).primesBelow)^2 ≤ 4/(4:ℝ)^k := by
  have hpos := (euler_pos (fun p (hp : p ∈ (cutoff k).primesBelow) =>
    (Nat.mem_primesBelow.mp hp).2)).le
  calc
    _ ≤ (2/(2:ℝ)^k)^2 := pow_le_pow_left₀ hpos (euler_cutoff_le k) 2
    _ = _ := by rw [div_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul]; norm_num

lemma one_le_weight {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (m : ℕ) :
    1 ≤ weight s m := by
  calc
    _ = ∏ _p ∈ s, (1:ℝ) := by simp
    _ ≤ weight s m := by
      apply Finset.prod_le_prod (fun _ _ => by norm_num)
      intro p hp
      split_ifs
      · exact (one_le_inv₀ (prime_factor_pos (hs p hp))).mpr prime_factor_le_one
      · rfl

lemma linear_main_le (k a c : ℕ) :
    (∏ p ∈ (cutoff k).primesBelow, (1-linearDensity a c p)) + (1/4:ℝ)^(depth k) ≤
      5 * weight (cutoff k).primesBelow a * weight (cutoff k).primesBelow c / (4:ℝ)^k := by
  let s := (cutoff k).primesBelow
  have hs : ∀ p ∈ s, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have h1 := one_le_weight hs a
  have h2 := one_le_weight hs c
  have hw : 1 ≤ weight s a * weight s c := by nlinarith
  have hmain : (∏ p ∈ s, (1-linearDensity a c p)) ≤
      (4/(4:ℝ)^k) * (weight s a * weight s c) := by
    calc
      _ ≤ (euler s)^2 * weight s (a*c) := linear_euler_le hs a c
      _ ≤ (4/(4:ℝ)^k) * (weight s a * weight s c) :=
        mul_le_mul (euler_cutoff_sq_le k) (weight_mul_le hs a c)
          (weight_nonneg hs (a*c)) (by positivity)
  have htail : (1/4:ℝ)^(depth k) ≤ 1/(4:ℝ)^k := by
    rw [← one_div_pow]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (index_le_depth k)
  have hwdiv := div_le_div_of_nonneg_right hw (by positivity : (0:ℝ)≤(4:ℝ)^k)
  change (∏ p ∈ s, (1-linearDensity a c p)) + _ ≤ _
  dsimp [s] at *
  simp only [div_eq_mul_inv] at *
  nlinarith

lemma primesBelow_card_le (z : ℕ) : z.primesBelow.card ≤ z := by
  have hh := Finset.card_filter_le (s := Finset.range z) (p := Nat.Prime)
  simpa only [Nat.primesBelow, Finset.card_range] using hh

lemma sieve_error_bound (k : ℕ) :
    (2*depth k+1:ℕ) * (2*(max 1 (cutoff k).primesBelow.card):ℝ)^(2*depth k) ≤
      (cutoff k:ℝ)^(6*depth k) := by
  let r := depth k
  let z := cutoff k
  have hz : 2 ≤ z := cutoff_two_le k
  have hz' : (2:ℝ) ≤ z := by exact_mod_cast hz
  have hc : max 1 z.primesBelow.card ≤ z := max_le (by omega) (primesBelow_card_le z)
  have hbase : (2*(max 1 z.primesBelow.card):ℝ) ≤ (z:ℝ)^2 := by
    have hh : ((max 1 z.primesBelow.card:ℕ):ℝ) ≤ z := by exact_mod_cast hc
    nlinarith
  have hcoef : (2*r+1:ℕ) ≤ z^(2*r) := by
    exact (Nat.succ_le_of_lt (Nat.lt_two_pow_self)).trans
      (Nat.pow_le_pow_left hz (2*r))
  calc
    _ ≤ (z:ℝ)^(2*r) * ((z:ℝ)^2)^(2*r) := by
      apply mul_le_mul
      · exact_mod_cast hcoef
      · exact pow_le_pow_left₀ (by positivity) hbase _
      · positivity
      · positivity
    _ = _ := by
      rw [← pow_mul, ← pow_add]
      apply congrArg (fun n : ℕ => (z:ℝ)^n)
      dsimp only [r]
      omega

lemma error_le_scaled_length (k N : ℕ) (hN : threshold k ≤ N) :
    (cutoff k:ℝ)^(6*depth k) ≤ (N:ℝ)/(4:ℝ)^k := by
  let z := cutoff k
  let r := depth k
  have hz : (2:ℝ) ≤ z := by exact_mod_cast cutoff_two_le k
  have hkr : 2*k ≤ 6*r := by have := index_le_depth k; dsimp [r]; omega
  have h4 : (4:ℝ)^k ≤ (z:ℝ)^(6*r) := by
    calc
      _ = (2:ℝ)^(2*k) := by rw [pow_mul]; norm_num
      _ ≤ (z:ℝ)^(2*k) := pow_le_pow_left₀ (by norm_num) hz _
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hkr
  have hN' : (z:ℝ)^(12*r) ≤ N := by exact_mod_cast hN
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(4:ℝ)^k)).mpr
  calc
    _ ≤ (z:ℝ)^(6*r) * (z:ℝ)^(6*r) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (z:ℝ)^(12*r) := by
      rw [← pow_add]
      apply congrArg (fun n : ℕ => (z:ℝ)^n)
      omega
    _ ≤ _ := hN'

/-- A discrete logarithmic-strength bound for two prime linear forms. The
  cutoff threshold is explicit; its size is independent of the coefficients. -/
theorem two_linear_prime_quantitative (k N : ℕ) (hN : threshold k ≤ N)
    {a b c d : ℕ} (hdet : determinantOne a b c d) :
    (primeInputs (cutoff k).primesBelow a b c d N).card ≤
      6*(N:ℝ)*weight (cutoff k).primesBelow a * weight (cutoff k).primesBelow c / (4:ℝ)^k := by
  let s := (cutoff k).primesBelow
  have hs : ∀ p ∈ s, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hraw := two_linear_prime_upper hs hdet N (depth_pos k) (depth_large k a c)
  have hmain := mul_le_mul_of_nonneg_left (linear_main_le k a c) (Nat.cast_nonneg N : (0:ℝ)≤N)
  have herr := (sieve_error_bound k).trans (error_le_scaled_length k N hN)
  have h1 := one_le_weight hs a
  have h2 := one_le_weight hs c
  have hw : (N:ℝ)/(4:ℝ)^k ≤ (N:ℝ)*(weight s a * weight s c)/(4:ℝ)^k := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hw : 1 ≤ weight s a * weight s c := by nlinarith
    exact le_mul_of_one_le_right (Nat.cast_nonneg N) hw
  dsimp [s] at *
  simp only [div_eq_mul_inv] at *
  nlinarith

end Erdos371SieveParameters

#print axioms Erdos371SieveParameters.primeMass_cutoff
#print axioms Erdos371SieveParameters.two_linear_prime_quantitative
