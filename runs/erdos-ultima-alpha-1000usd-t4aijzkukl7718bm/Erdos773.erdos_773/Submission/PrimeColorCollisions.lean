import Submission.WeakSidonExtraction
import Submission.PrimorialSquareSieve
import Submission.QuantitativeSquareSieve

/-!
Finite-color obstructions among prime roots, derived from the verified Sidon
upper bounds. These do not disprove the near-linear exponent conjecture.
-/
namespace Erdos773.PrimeColorCollisions
open Finset Filter WeakSidonExtraction
set_option maxHeartbeats 1000000

/-- A monochromatic collision with four distinct roots. -/
def FourCollision {κ : Type*} (A : Finset ℕ) (f : ℕ → κ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, ∃ d ∈ A,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 ∧ f a = f b ∧ f a = f c ∧ f a = f d

/-- Any coloring with too few colors has a four-distinct-root collision. -/
theorem four_collision_of_card {κ : Type*} [Fintype κ] (A : Finset ℕ) (N : ℕ)
    (hA : A ⊆ Icc 1 N) (f : ℕ → κ)
    (hc : 4 * (Fintype.card κ : ℝ) *
      (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ) < A.card) :
    FourCollision A f := by
  classical
  have hk : (0 : ℝ) < Fintype.card κ := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨f 0⟩)
  have hf : ∀ a ∈ A, f a ∈ (univ : Finset κ) := by simp
  have havg : (univ : Finset κ).card • ((A.card : ℝ) / Fintype.card κ) ≤ A.card := by
    simp only [card_univ, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ hk.ne']
  obtain ⟨j, hj, hjc⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to hf
    (show (univ : Finset κ).Nonempty from ⟨f 0, mem_univ _⟩) havg
  let B := A.filter (fun a => f a = j)
  let S := B.image (fun n : ℕ => n ^ 2)
  have hSB : S.card = B.card :=
    card_image_of_injective _ (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0))
  have hS : S ⊆ (Icc 1 N).image (fun n : ℕ => n ^ 2) :=
    image_subset_image ((filter_subset _ _).trans hA)
  have hnot : ¬WeakSidon (S : Set ℕ) := by
    intro hw
    have hh := card_le_four_max hS hw
    rw [hSB] at hh
    have ha : (A.card : ℝ) ≤ B.card * Fintype.card κ :=
      (div_le_iff₀ hk).mp hjc
    have hm := mul_le_mul_of_nonneg_right hh hk.le
    nlinarith only [ha,hm,hc]
  simp only [WeakSidon, not_forall] at hnot
  obtain ⟨a, ha, b, hb, c, hc', d, hd, he, hnt⟩ := hnot
  have hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hh <;> apply hnt <;> omega
  obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
  obtain ⟨c', hc'', rfl⟩ := mem_image.mp hc'
  obtain ⟨d', hd', rfl⟩ := mem_image.mp hd
  obtain ⟨haA, hfa⟩ := mem_filter.mp ha'
  obtain ⟨hbA, hfb⟩ := mem_filter.mp hb'
  obtain ⟨hcA, hfc⟩ := mem_filter.mp hc''
  obtain ⟨hdA, hfd⟩ := mem_filter.mp hd'
  refine ⟨a', haA, b', hbA, c', hcA, d', hdA,
    ?_, ?_, ?_, ?_, ?_, ?_, he, hfa.trans hfb.symm, hfa.trans hfc.symm, hfa.trans hfd.symm⟩
  all_goals intro hh; subst_vars; simp_all

private lemma log_two_bounds : (1/2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  have h1 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h1 h2 ⊢
  exact ⟨by linarith, by linarith⟩

private lemma bitlength_cost_tendsto (r : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ) + 1) ^ r *
      Real.exp (-Real.sqrt (((m : ℝ) + 1) * Real.log 2) / 8)) atTop (nhds 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : Tendsto (fun m : ℕ => Real.sqrt (((m : ℝ) + 1) * Real.log 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const hlog)
  have hz := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((2*r : ℕ) : ℝ) (1/8) (by norm_num)).comp ht
  have hz' := hz.const_mul ((Real.log 2 ^ r)⁻¹)
  simp only [mul_zero] at hz'
  apply hz'.congr'
  filter_upwards with m
  dsimp only [Function.comp_def]
  rw [Real.rpow_natCast]
  have hsq := Real.sq_sqrt (show 0 ≤ ((m : ℝ) + 1) * Real.log 2 by positivity)
  rw [pow_mul, hsq, mul_pow]
  have hne : Real.log 2 ^ r ≠ 0 := pow_ne_zero _ hlog.ne'
  have hexp : -(1/8 : ℝ) * Real.sqrt (((m : ℝ) + 1) * Real.log 2) =
      -Real.sqrt (((m : ℝ) + 1) * Real.log 2) / 8 := by ring
  rw [hexp]
  field_simp

/-- Eventually every coloring of primes up to 2^(m+1) with at most (m+1)^r
colors has a four-distinct-root square collision. The degree r is fixed. -/
theorem eventually_prime_color_collision (r : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (κ : Type) [Fintype κ],
      Fintype.card κ ≤ (m + 1) ^ r → ∀ f : ℕ → κ,
        FourCollision (sievePrimes (2 ^ m)) f := by
  have hsmall := Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1/256)
    (bitlength_cost_tendsto (r + 1))
  filter_upwards [hsmall, eventually_ge_atTop 8] with m hsmall hm
  intro κ _ hκ f
  have hn : 128 ≤ (2 : ℕ) ^ m := by
    calc
      _ = 2 ^ 7 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hN : 512 ≤ 2 * (2 : ℕ) ^ m := by
    have hh : (2 : ℕ) ^ 8 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    norm_num at hh
    omega
  have hA : sievePrimes (2 ^ m) ⊆ Icc 1 (2 * 2 ^ m) := by
    intro p hp
    obtain ⟨hp, hprime, h5⟩ := mem_filter.mp hp
    have hp' := mem_range.mp hp
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  apply four_collision_of_card (sievePrimes (2 ^ m)) (2 * 2 ^ m) hA f
  have hp := sievePrimes_card_log_lower (2 ^ m) hn
  have hs := square_sidon_stretched_exponential_upper (2 * 2 ^ m) hN
  have hlog : Real.log ((2 * 2 ^ m : ℕ) : ℝ) = ((m : ℝ) + 1) * Real.log 2 := by
    push_cast
    rw [← pow_succ', Real.log_pow]
    push_cast
    rfl
  have hlogn : Real.log ((2 ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
  rw [hlog] at hs
  rw [hlogn] at hp
  push_cast at hs hp
  have hκR : (Fintype.card κ : ℝ) ≤ ((m : ℝ) + 1) ^ r := by exact_mod_cast hκ
  let E : ℝ := Real.exp (-Real.sqrt (((m : ℝ) + 1) * Real.log 2) / 8)
  have hE : 0 < E := Real.exp_pos _
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hlogbounds := log_two_bounds
  have hm1 : (m : ℝ) * Real.log 2 ≤ (m : ℝ) + 1 := by nlinarith
  have hlogpos : 0 < (m : ℝ) * Real.log 2 := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hcost : 256 * (Fintype.card κ : ℝ) * ((m : ℝ) * Real.log 2) * E < 1 := by
    have hh := mul_le_mul hκR hm1 (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_right hh hE.le
    have heq : ((m : ℝ) + 1) ^ r * ((m : ℝ) + 1) = ((m : ℝ) + 1) ^ (r+1) := by
      rw [pow_succ]
    rw [heq] at hh'
    change ((m : ℝ) + 1) ^ (r+1) * E < 1/256 at hsmall
    nlinarith only [hh',hsmall]
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hb : 4 * (Fintype.card κ : ℝ) *
      (Finset.maxSidonSubsetCard ((Icc 1 (2*2^m)).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
      32 * Fintype.card κ * 2 ^ m * E := by
    have hh := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 4 * Fintype.card κ by positivity)
    dsimp [E]
    nlinarith only [hh]
  have hstrict : 32 * (Fintype.card κ : ℝ) * 2 ^ m * E *
      ((m : ℝ) * Real.log 2) < (2 : ℝ) ^ m / 8 := by
    have hh := mul_lt_mul_of_pos_right hcost hpow
    nlinarith only [hh]
  have hh := lt_of_mul_lt_mul_right (hstrict.trans_le hp) hlogpos.le
  exact hb.trans_lt hh


set_option exponentiation.threshold 1024 in
/-- A finite entropy criterion using the stronger primorial upper bound. -/
theorem prime_color_collision_of_entropy (m : ℕ) (hm : 895 ≤ m)
    (κ : Type) [Fintype κ] (f : ℕ → κ)
    (hcost : 128 * (Fintype.card κ : ℝ) * ((m : ℝ) + 1) *
      Real.exp (-(((m : ℝ) + 1) * Real.log 2) /
        (512 * Real.log (((m : ℝ) + 1) * Real.log 2))) < 1) :
    FourCollision (sievePrimes (2 ^ m)) f := by
  have hn : 128 ≤ (2 : ℕ) ^ m := by
    calc
      _ = 2 ^ 7 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hN : 128 ^ 128 ≤ 2 * (2 : ℕ) ^ m := by
    calc
      _ = (2 ^ 7) ^ 128 := by norm_num
      _ = 2 ^ 896 := by rw [← pow_mul]
      _ ≤ 2 ^ (m+1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = _ := by rw [pow_succ']
  have hA : sievePrimes (2 ^ m) ⊆ Icc 1 (2 * 2 ^ m) := by
    intro p hp
    obtain ⟨hp, hprime, h5⟩ := mem_filter.mp hp
    have hp' := mem_range.mp hp
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  apply four_collision_of_card (sievePrimes (2 ^ m)) (2 * 2 ^ m) hA f
  have hp := sievePrimes_card_log_lower (2 ^ m) hn
  have hs := square_sidon_primorial_upper (2 * 2 ^ m) hN
  have hlog : Real.log ((2 * 2 ^ m : ℕ) : ℝ) = ((m : ℝ) + 1) * Real.log 2 := by
    push_cast
    rw [← pow_succ', Real.log_pow]
    push_cast
    rfl
  have hlogn : Real.log ((2 ^ m : ℕ) : ℝ) = (m : ℝ) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
  rw [hlog] at hs
  rw [hlogn] at hp
  push_cast at hs hp
  let E : ℝ := Real.exp (-(((m : ℝ) + 1) * Real.log 2) /
    (512 * Real.log (((m : ℝ) + 1) * Real.log 2)))
  have hE : 0 < E := Real.exp_pos _
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hlogbounds := log_two_bounds
  have hm1 : (m : ℝ) * Real.log 2 ≤ (m : ℝ) + 1 := by nlinarith
  have hlogpos : 0 < (m : ℝ) * Real.log 2 := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have hcost' : 128 * (Fintype.card κ : ℝ) * ((m : ℝ) * Real.log 2) * E < 1 := by
    have hh := mul_le_mul_of_nonneg_left hm1
      (show (0 : ℝ) ≤ 128 * Fintype.card κ by positivity)
    exact (mul_le_mul_of_nonneg_right hh hE.le).trans_lt hcost
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hb : 4 * (Fintype.card κ : ℝ) *
      (Finset.maxSidonSubsetCard ((Icc 1 (2*2^m)).image (fun n : ℕ => n ^ 2)) : ℝ) ≤
      16 * Fintype.card κ * 2 ^ m * E := by
    have hh := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 4 * Fintype.card κ by positivity)
    dsimp [E]
    nlinarith only [hh]
  have hstrict : 16 * (Fintype.card κ : ℝ) * 2 ^ m * E *
      ((m : ℝ) * Real.log 2) < (2 : ℝ) ^ m / 8 := by
    have hh := mul_lt_mul_of_pos_right hcost' hpow
    nlinarith only [hh]
  have hh := lt_of_mul_lt_mul_right (hstrict.trans_le hp) hlogpos.le
  exact hb.trans_lt hh

#print axioms prime_color_collision_of_entropy

#print axioms four_collision_of_card
#print axioms eventually_prime_color_collision
end Erdos773.PrimeColorCollisions
