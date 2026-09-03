import Submission.EvenCompositeGain

/-!
# Keeping the endpoint correction in the prime-pair bound

The uniform coefficient cap is large enough for the existing structured
scales. It allows the additive endpoint correction to use the otherwise
unused 2^(16J) error budget, instead of doubling the main term.
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 3000000

lemma exists_totient_ratio_power_bound (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℕ, 0 < a →
      ((a : ℝ)/(a.totient : ℝ))^(k+1) ≤ C*(a : ℝ) := by
  let C : ℝ := (((2^(k+1) : ℕ).factorial)^k : ℕ)
  refine ⟨C,Nat.cast_nonneg _,?_⟩
  intro a ha
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hφ : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  have hinput : (a : ℝ)^k ≤ C*(a.totient : ℝ)^(k+1) := by
    dsimp only [C]
    exact_mod_cast input_pow_le_totient_pow a k hk
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hφ _)).mpr
  have h := mul_le_mul_of_nonneg_left hinput haR.le
  convert h using 1
  · rw [pow_succ]
    ring
  · ring

lemma eventually_totient_ratio_box :
    ∀ᶠ J : ℕ in atTop, ∀ a : ℕ, 0 < a → a ≤ 2^(256*J) →
      (a : ℝ)/(a.totient : ℝ) ≤ (2 : ℝ)^(16*J) := by
  obtain ⟨C,hC,hbound⟩ := exists_totient_ratio_power_bound 31 (by decide)
  have hlarge : ∀ᶠ J : ℕ in atTop, C ≤ (2 : ℝ)^(256*J) := by
    have h := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
      (eventually_ge_atTop C)
    filter_upwards [h] with J hJ
    exact hJ.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  filter_upwards [hlarge] with J hJ
  intro a ha hcap
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hφ : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  have hratio : ((a : ℝ)/(a.totient : ℝ))^32 ≤ C*(a : ℝ) := hbound a ha
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (32 : ℕ) ≠ 0)).mp
  apply hratio.trans
  calc
    C*(a : ℝ) ≤ (2 : ℝ)^(256*J)*(2 : ℝ)^(256*J) := by
      apply mul_le_mul hJ _ (Nat.cast_nonneg a) (by positivity)
      exact_mod_cast hcap
    _ = ((2 : ℝ)^(16*J))^32 := by
      rw [← pow_add, ← pow_mul]
      congr 1
      omega

def EndpointPairAt (J : ℕ) : Prop :=
  ∀ X a : ℕ, 0 < a → a ≤ X → a ≤ 2^(256*J) →
    (primePairCofactorCount X a : ℝ) ≤
      (X : ℝ)/(450*(a.totient : ℝ)*((J : ℝ)*Real.log 2)^2) +
        ((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1)

lemma eventually_endpoint_pair_at : ∀ᶠ J : ℕ in atTop, EndpointPairAt J := by
  filter_upwards [Sieve.eventually_prime_pair_mixed_explicit_all,
    eventually_totient_ratio_box, eventually_ge_atTop 1] with J hpair hratio hJ
  intro X a ha haX hcap
  let D : ℝ := ((J : ℝ)*Real.log 2)^2
  have hJlog : (1/2 : ℝ) ≤ (J : ℝ)*Real.log 2 := by
    have hlog : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  have hD : 1 ≤ 450*D := by
    dsimp [D]
    nlinarith [sq_nonneg ((J : ℝ)*Real.log 2 - 1/2)]
  have hD0 : 0 < D := by nlinarith
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hφ : (0 : ℝ) < a.totient := by exact_mod_cast Nat.totient_pos.mpr ha
  have hN : ((X/a+1 : ℕ) : ℝ) ≤ (X : ℝ)/a+1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using add_le_add Nat.cast_div_le (le_refl (1 : ℝ))
  have hb := hpair (X/a+1) a ha
  have hcorr : (a : ℝ)/(450*(a.totient : ℝ)*D) ≤ (2 : ℝ)^(16*J) := by
    calc
      _ = ((a : ℝ)/(a.totient : ℝ))/(450*D) := by ring
      _ ≤ (a : ℝ)/(a.totient : ℝ) := (div_le_self (by positivity) hD)
      _ ≤ _ := hratio a ha hcap
  have hmain : 2*((X/a+1 : ℕ) : ℝ)/(900*((Nat.totient a : ℝ)/a*D)) ≤
      (X : ℝ)/(450*(a.totient : ℝ)*D)+(2 : ℝ)^(16*J) := by
    calc
      _ ≤ 2*((X : ℝ)/a+1)/(900*((Nat.totient a : ℝ)/a*D)) := by gcongr
      _ = (X : ℝ)/(450*(a.totient : ℝ)*D)+(a : ℝ)/(450*(a.totient : ℝ)*D) := by
        field_simp
        ring
      _ ≤ _ := _root_.add_le_add le_rfl hcorr
  change (primePairCofactorCount X a : ℝ) ≤ _ at hb
  change (primePairCofactorCount X a : ℝ) ≤ (X : ℝ)/(450*(a.totient : ℝ)*D)+_
  linarith only [hb,hmain]

end Erdos821.AnalyticSieve
