import Submission.ScaledProductBands

/-!
# A sixteen-band rejected-prime estimate

The cutoff is 17664000/40000020. This is a fixed-ratio estimate, not an
arbitrary-root smooth-predecessor result.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma hyperbolic_card_le_fine_bands (d H m k : ℕ) :
    (hyperbolicPrimePairPool d H (2^(128*scaledBandEndpoint 0*m)) H).card ≤
      (∑ i ∈ range k, (hyperbolicPrimePairPool d H
        (2^(128*scaledBandEndpoint i*m)) (2^(128*scaledBandEndpoint (i+1)*m))).card)+
          (hyperbolicPrimePairPool d H (2^(128*scaledBandEndpoint k*m)) H).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have hh := hyperbolic_prime_pair_card_split d H
      (2^(128*scaledBandEndpoint k*m)) (2^(128*scaledBandEndpoint (k+1)*m)) H
    omega

lemma eventually_scaled_band_short_tail :
    ∀ᶠ m : ℕ in atTop, ∀ X d : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      independentN 20000000 m ≤ d → d ≤ independentN 20000004 m →
        Real.log (X : ℝ)*((hyperbolicPrimePairPool d (X/d) (2^(128*10000007*m)) (X/d)).card : ℝ) ≤
          (11/62500 : ℝ)*(X : ℝ)/(d.totient : ℝ) := by
  filter_upwards [eventually_scaledProductShortBudget,
    eventually_short_cofactor_dyadic_bound 10000011 10000007 (by decide) (by decide),
    eventually_scaled_product_tail_error,eventually_ge_atTop 1] with m hTB hShort hTail hm1
  intro X d hXlo hXhi hdlo hdhi
  have hd : 0 < d := (by unfold independentN; positivity : 0 < independentN 20000000 m).trans_le hdlo
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  let H := X/d
  let F : ℝ := (d : ℝ)/(d.totient : ℝ)
  let L : ℝ := 64*40000021*(m : ℝ)*Real.log 2
  have hH := scaled_supply_quotient_bounds m X d hXlo hXhi hdlo hdhi
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hF1 : 1 ≤ F := (one_le_div hφ).mpr (by exact_mod_cast Nat.totient_le d)
  have hHF : (H : ℝ)*F ≤ (X : ℝ)/(d.totient : ℝ) := by
    have hh : ((X/d : ℕ) : ℝ)*(d : ℝ) ≤ X := by exact_mod_cast Nat.div_mul_le_self X d
    simpa only [H,F,mul_div_assoc] using div_le_div_of_nonneg_right hh hφ.le
  have hHX : (H : ℝ) ≤ (X : ℝ)/(d.totient : ℝ) :=
    (le_mul_of_one_le_right (Nat.cast_nonneg H) hF1).trans hHF
  have hlog : Real.log (X : ℝ) ≤ L := scaled_supply_log_upper m X hXhi
  let V : ℝ := (1/75)*(1+512*(m : ℝ)*Real.log 2)/((10000007 : ℝ)*m*Real.log 2)^2
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hshort0 := hShort d H H hd hH.2
  have hshort : ((hyperbolicPrimePairPool d H (2^(128*10000007*m)) H).card : ℝ) ≤
      (H : ℝ)*F*V+scaledProductTailError m := by
    convert hshort0 using 1; dsimp [F,V,scaledProductTailError]; norm_num; ring
  have hh := mul_le_mul_of_nonneg_left hshort (Real.log_natCast_nonneg X)
  rw [mul_add] at hh
  have hmain := mul_le_mul_of_nonneg_right hlog (show 0 ≤ (H : ℝ)*F*V by positivity)
  have hid : L*V=scaledProductShortBudget m := scaledProductShortBudget_identity m hm1
  have he : L*((H : ℝ)*F*V)=(H : ℝ)*F*scaledProductShortBudget m := by rw [← hid]; ring
  rw [he] at hmain
  have hmain' := hmain.trans (mul_le_mul_of_nonneg_left hTB (show 0 ≤ (H : ℝ)*F by positivity))
  have ht := hTail X H hXhi hH.1
  have h1 := mul_le_mul_of_nonneg_left hHF (show (0 : ℝ) ≤ 7/40000 by norm_num)
  have h2 := div_le_div_of_nonneg_right hHX (show (0 : ℝ) ≤ 10000 by norm_num)
  change Real.log X*((hyperbolicPrimePairPool d H (2^(128*10000007*m)) H).card : ℝ) ≤ _
  simp only [div_eq_mul_inv] at hh hmain' ht h1 h2 ⊢
  nlinarith only [hh,hmain',ht,h1,h2]

/-- A strictly smaller smoothness cutoff, using sixteen long-cofactor bands. -/
theorem eventually_scaled_band_rough_bound :
    ∀ᶠ m : ℕ in atTop, ∀ X d : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      independentN 20000000 m ≤ d → d ≤ independentN 20000004 m →
      d ∈ Nat.smoothNumbers (independentN 17664000 m) →
        Real.log (X : ℝ)*((roughProgressionPrimes d (independentN 17664000 m) X).card : ℝ) ≤
          (1999/2000 : ℝ)*(X : ℝ)/(d.totient : ℝ) := by
  filter_upwards [eventually_all_scaled_band_bands,eventually_scaled_band_short_tail,
    eventually_ge_atTop 1] with m hBand hTail hm
  intro X d hXlo hXhi hdlo hdhi hds
  have hd : 0 < d := (by unfold independentN; positivity : 0 < independentN 20000000 m).trans_le hdlo
  have hnp : ¬(independentN 17664000 m).Prime := not_prime_two_pow _ (by omega)
  have hY : independentN 17664000 m=2^(128*scaledBandEndpoint 0*m) := rfl
  have hrough := rough_progression_card_le_hyperbolic d (independentN 17664000 m) X hd hds hnp
  rw [hY] at hrough
  have hpartition := hrough.trans (hyperbolic_card_le_fine_bands d (X/d) m 16)
  have hsum : Real.log (X : ℝ)*
      (∑ i : Fin 16, ((hyperbolicPrimePairPool d (X/d)
        (2^(128*scaledBandEndpoint i*m)) (2^(128*scaledBandEndpoint (i+1)*m))).card : ℝ)) ≤
          (998489/1000000 : ℝ)*(X : ℝ)/(d.totient : ℝ) := by
    rw [mul_sum]
    apply (sum_le_sum (fun i _ => hBand i X d hXlo hXhi hdlo hdhi)).trans_eq
    rw [← sum_div,← sum_mul,scaledBand_budget_sum]
  have ht := hTail X d hXlo hXhi hdlo hdhi
  have hp : ((roughProgressionPrimes d (independentN 17664000 m) X).card : ℝ) ≤
      (∑ i : Fin 16, ((hyperbolicPrimePairPool d (X/d)
        (2^(128*scaledBandEndpoint i*m)) (2^(128*scaledBandEndpoint (i+1)*m))).card : ℝ))+
        ((hyperbolicPrimePairPool d (X/d) (2^(128*10000007*m)) (X/d)).card : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      ((hyperbolicPrimePairPool d (X/d)
        (2^(128*scaledBandEndpoint i*m)) (2^(128*scaledBandEndpoint (i+1)*m))).card : ℝ))]
    exact_mod_cast hpartition
  have hh := mul_le_mul_of_nonneg_left hp (Real.log_natCast_nonneg X)
  rw [mul_add] at hh
  have hnonneg : 0 ≤ (X : ℝ)/(d.totient : ℝ) := by positivity
  simp only [div_eq_mul_inv] at hh hsum ht hnonneg ⊢
  nlinarith only [hh,hsum,ht,hnonneg]

end Erdos821.AnalyticSieve
