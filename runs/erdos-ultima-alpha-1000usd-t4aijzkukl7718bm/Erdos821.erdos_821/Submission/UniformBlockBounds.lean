import Submission.UniformBlockSieve

/-!
# Uniform block main terms and error budgets on bounded-ratio intervals

The main-term coefficient is unchanged by a fixed multiplicative enlargement
of the cutoff. The associated power-saving constants may depend on that ratio.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma sharpBlockSieveMainAt_nonneg (X b h m : ℕ) : 0 ≤ sharpBlockSieveMainAt X b h m := by
  unfold sharpBlockSieveMainAt sharpBlockUnitMainAt
  exact sum_nonneg (fun _ _ => by positivity)

lemma sharpBlockSieveMainAt_eq_scale (t X b h m : ℕ) :
    sharpBlockSieveMainAt X b h m =
      ((X : ℝ)/(independentN t m : ℝ))*sharpBlockSieveMain t b h m := by
  have hN : (independentN t m : ℝ) ≠ 0 := by unfold independentN; positivity
  have he : (X : ℝ) = (independentN t m : ℝ)*((X : ℝ)/(independentN t m : ℝ)) :=
    (mul_div_cancel₀ (X : ℝ) hN).symm
  unfold sharpBlockSieveMainAt sharpBlockSieveMain
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  have hh := congrArg (fun z : ℝ => (13/5100 : ℝ)*z*(1+64*(m : ℝ)*Real.log 2)/
    ((independentJ (blockCutoff b h j) m : ℝ)*Real.log 2)^2) he
  convert hh using 1
  dsimp only [sharpBlockUnitMainAt,sharpBlockUnitMain]
  ring

lemma sharpBlockSieveMainAt_normalized (q t b h m X : ℕ)
    (heq : q+b+h=t) (hb : 2 ≤ b) (hm : 1 ≤ m) :
    Real.log (independentN t m : ℝ)*sharpBlockSieveMainAt X b h m =
      (sharpBlockMainLimit t b h+(117/136 : ℝ)*blockMainRemainder t b h/(m : ℝ))*(X : ℝ) := by
  have hh := block_sieve_main_normalized q t b h m heq hb hm
  have hN : (independentN t m : ℝ) ≠ 0 := by unfold independentN; positivity
  rw [sharpBlockSieveMainAt_eq_scale,sharpBlockSieveMain_eq_scale]
  calc
    _ = ((X : ℝ)/(independentN t m : ℝ))*(117/136 : ℝ)*
        (Real.log (independentN t m : ℝ)*blockSieveMain t b h m) := by ring
    _ = _ := by
      rw [hh]
      unfold sharpBlockMainLimit
      field_simp

lemma log_cutoff_le_enlarged_scale (t K m X : ℕ) (ht : 1 ≤ t) (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hlo : independentN t m ≤ X) (hhi : X ≤ K*independentN t m) :
    Real.log (X : ℝ) ≤
      (1+(Real.log (K : ℝ)/(64*(t : ℝ)*Real.log 2))/(m : ℝ))*Real.log (independentN t m : ℝ) := by
  have hN : (0 : ℝ) < independentN t m := by unfold independentN; positivity
  have hX : (0 : ℝ) < X := hN.trans_le (by exact_mod_cast hlo)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne'
  have hh := Real.log_le_log hX (show (X : ℝ) ≤ (K : ℝ)*independentN t m by exact_mod_cast hhi)
  rw [Real.log_mul hKR.ne' hN.ne'] at hh
  apply hh.trans_eq
  simp only [independentN,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul]
  field_simp
  ring

lemma eventually_uniform_sharp_block_main (q t b h K : ℕ)
    (heq : q+b+h=t) (hb : 2 ≤ b) (hK : 1 ≤ K)
    (a : ℝ) (ha : sharpBlockMainLimit t b h < a) :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ,
      independentN t m ≤ X → X ≤ K*independentN t m →
      Real.log (X : ℝ)*sharpBlockSieveMainAt X b h m ≤ a*X := by
  let e := Real.log (K : ℝ)/(64*(t : ℝ)*Real.log 2)
  let R := (117/136 : ℝ)*blockMainRemainder t b h
  have hE : Tendsto (fun m : ℕ => 1+e/(m : ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hR : Tendsto (fun m : ℕ => sharpBlockMainLimit t b h+R/(m : ℝ)) atTop
      (𝓝 (sharpBlockMainLimit t b h)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlim := hE.mul hR
  simp only [one_mul] at hlim
  filter_upwards [hlim.eventually (eventually_le_nhds ha),eventually_ge_atTop 1] with m hm hm1
  intro X hlo hhi
  have hlog := log_cutoff_le_enlarged_scale t K m X (by omega) hK hm1 hlo hhi
  calc
    _ ≤ ((1+e/(m : ℝ))*Real.log (independentN t m : ℝ))*sharpBlockSieveMainAt X b h m :=
      mul_le_mul_of_nonneg_right hlog (sharpBlockSieveMainAt_nonneg _ _ _ _)
    _ = ((1+e/(m : ℝ))*(sharpBlockMainLimit t b h+R/(m : ℝ)))*X := by
      rw [mul_assoc,sharpBlockSieveMainAt_normalized q t b h m X heq hb hm1]
      dsimp [R]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg X)

lemma log_fixed_cutoff_upper (t K m X : ℕ) (hK : 1 ≤ K) (hX : X ≤ K*independentN t m) :
    Real.log (X : ℝ) ≤ ((K+64*t : ℕ) : ℝ)*((m : ℝ)+1) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hN0 : (0 : ℝ) < independentN t m := by unfold independentN; positivity
  by_cases hx0 : X=0
  · subst X
    simp only [Nat.cast_zero,Real.log_zero]
    positivity
  have hh := Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hx0))
    (show (X : ℝ) ≤ (K : ℝ)*independentN t m by exact_mod_cast hX)
  rw [Real.log_mul hK0.ne' hN0.ne'] at hh
  have hlogK := Real.log_le_sub_one_of_pos hK0
  have hlogN := independent_log_upper t m
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) K,Nat.cast_nonneg (α := ℝ) m]

lemma sqrt_fixed_cutoff_upper (t K m X : ℕ) (ht : 1 ≤ t) (hK : 1 ≤ K)
    (hX : X ≤ K*independentN t m) :
    Real.sqrt (X : ℝ) ≤ (K : ℝ)*(2 : ℝ)^((64*t-1)*m) := by
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hXr : (X : ℝ) ≤ (K : ℝ)*independentN t m := by exact_mod_cast hX
  have hKsq : (K : ℝ)*independentN t m ≤ ((K : ℝ)*Real.sqrt (independentN t m))^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (independentN t m))]
    exact mul_le_mul_of_nonneg_right (by nlinarith : (K : ℝ) ≤ (K : ℝ)^2) (Nat.cast_nonneg _)
  have hh : Real.sqrt (X : ℝ) ≤ (K : ℝ)*Real.sqrt (independentN t m) :=
    Real.sqrt_le_iff.mpr ⟨by positivity,hXr.trans hKsq⟩
  exact hh.trans (mul_le_mul_of_nonneg_left (independent_sqrt_pow_bound t m ht) (Nat.cast_nonneg K))

lemma eventually_uniform_block_total_error (M : ℕ → Finset ℕ) (q t b h K I W : ℕ)
    (heq : q+b+h=t) (hb : 2 ≤ b) (hK : 1 ≤ K) (hW : 0 < W)
    (hM : ∀ m, (M m).card ≤ independentN q m) :
    ∀ᶠ m : ℕ in atTop, ∀ X : ℕ, X ≤ K*independentN t m →
      Real.log (X : ℝ)*(familyBlockError (M m) b h m+2*(I : ℝ)*Real.sqrt X) ≤
        (independentN t m : ℝ)/(W : ℝ) := by
  let C := (K+64*t)*(3*h+2*I*K)
  filter_upwards [eventually_power_saving_le_divisor t C 1 W (by omega) hW] with m hm
  intro X hX
  have herror := family_block_error_pow_bound (M m) q t b h m heq hb (hM m)
  have herror0 : 0 ≤ familyBlockError (M m) b h m := by
    unfold familyBlockError
    positivity
  have hsqrt := sqrt_fixed_cutoff_upper t K m X (by omega) hK hX
  have hlog := log_fixed_cutoff_upper t K m X hK hX
  have hbound : Real.log (X : ℝ)*(familyBlockError (M m) b h m+2*(I : ℝ)*Real.sqrt X) ≤
      (C : ℝ)*((m : ℝ)+1)*(2 : ℝ)^((64*t-1)*m) := by
    calc
      _ ≤ (((K+64*t : ℕ) : ℝ)*((m : ℝ)+1))*
          ((3*(h : ℝ))*(2 : ℝ)^((64*t-1)*m)+2*(I : ℝ)*((K : ℝ)*(2 : ℝ)^((64*t-1)*m))) := by
        gcongr
      _ = _ := by dsimp [C]; push_cast; ring
  exact hbound.trans (by simpa only [pow_one] using hm)

end Erdos821
