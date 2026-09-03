import Submission.ScaledProductBudget

/-!
# Finer long-cofactor ranges in the product sieve

These estimates refine a fixed smoothness ratio only. They do not prove the
arbitrary-root prime supply required for the original conjecture.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma eventually_scaled_band_threshold (t l v : ℕ) (ht : 1 ≤ t)
    (hv : v ≤ 10000008) (hscale : l*v < t*(10000008-v)) :
    ∀ᶠ m : ℕ in atTop, ∀ H : ℕ, 2^(128*10000008*m) ≤ H →
      cofactorScale l (2*cofactorDyadicIndex t (128*v*m)) ≤ H/2^(128*v*m) := by
  filter_upwards [eventually_ge_atTop (4*l*t)] with m hm
  intro H hH
  have hb := (cofactorDyadicIndex_bounds t (128*v*m) ht).2
  have he : 512*l*cofactorDyadicIndex t (128*v*m) ≤ 128*(10000008-v)*m := by
    have hmul := Nat.mul_le_mul_left l hb
    have hgap := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr hscale)
    have ht0 : 0 < t := by omega
    apply Nat.le_of_mul_le_mul_left (c := t) _ ht0
    nlinarith only [hm,hmul,hgap]
  apply (show cofactorScale l (2*cofactorDyadicIndex t (128*v*m)) ≤
      2^(128*(10000008-v)*m) by
    rw [cofactorScale_eq]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [he]).trans
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2^(128*v*m))).mpr
  apply le_trans _ hH
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have hcancel := Nat.sub_add_cancel hv
  nlinarith only [congrArg (fun n : ℕ => 128*n*m) hcancel]

noncomputable def scaledBandCoefficient (t b : ℕ) : ℝ :=
  (2*(t : ℝ)/(b : ℝ))*(1+1/(2 : ℝ)^10)

lemma eventually_scaled_band_band (u v t b l : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ 10000008)
    (hhalf : 10000011 ≤ 2*u) (hb : 1 ≤ b) (hbt : b+1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t) (hl : 3 ≤ l)
    (hscale : l*v < t*(10000008-v)) (J : ℝ) (hJ : 0 ≤ J)
    (hlimit : scaledProductLongLimit (scaledBandCoefficient t b) u v < J) :
    ∀ᶠ m : ℕ in atTop, ∀ X d : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      independentN 20000000 m ≤ d → d ≤ independentN 20000004 m →
      Real.log (X : ℝ)*
          ((hyperbolicPrimePairPool d (X/d) (2^(128*u*m)) (2^(128*v*m))).card : ℝ) ≤
        J*(X : ℝ)/(d.totient : ℝ) := by
  obtain ⟨C,hC,K₀,hbound⟩ := exists_product_cofactor_hyperbolic_bound 1 b t l 10
    (by decide) hb hbt hlevel hl (1/1000000) (by norm_num)
  have hbudget : ∀ᶠ m : ℕ in atTop,
      scaledProductLongBudget (scaledBandCoefficient t b) u v C m ≤ J :=
    (tendsto_scaledProductLongBudget _ C u v hu (hu.trans huv)).eventually
      (eventually_le_nhds hlimit)
  filter_upwards [hbudget,eventually_scaled_band_threshold t l v (by omega) hv hscale,
    eventually_ge_atTop (max 1 K₀)] with m hm hthreshold hmK
  intro X d hXlo hXhi hdlo hdhi
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hmK
  have hK : K₀ ≤ m := (le_max_right _ _).trans hmK
  have hd : 0 < d := (by unfold independentN; positivity : 0 < independentN 20000000 m).trans_le hdlo
  have hH := scaled_supply_quotient_bounds m X d hXlo hXhi hdlo hdhi
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hHF : ((X/d : ℕ) : ℝ)*((d : ℝ)/(d.totient : ℝ)) ≤ (X : ℝ)/(d.totient : ℝ) := by
    have hh : ((X/d : ℕ) : ℝ)*(d : ℝ) ≤ X := by exact_mod_cast Nat.div_mul_le_self X d
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hh hφ.le
  have hsum : 128*u*m+128*(v-u)*m=128*v*m := by
    have hh := congrArg (fun n : ℕ => 128*n*m) (Nat.add_sub_of_le huv)
    nlinarith only [hh]
  have hraw := hbound (128*u*m) (128*(v-u)*m) d (X/d) (by nlinarith) (by nlinarith) hd
    (hH.2.trans (Nat.pow_le_pow_right (by decide) (by nlinarith only [hhalf])))
    (by rw [hsum]; exact hthreshold (X/d) hH.1)
  rw [hsum] at hraw
  have heq : 128*(u : ℝ)*m+128*((v-u : ℕ) : ℝ)*m=128*(v : ℝ)*m := by
    rw [Nat.cast_sub huv]
    ring
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hraw
  rw [heq] at hraw
  apply scaled_product_long_weighted_budget d (X/d) X u v m (scaledBandCoefficient t b) C J _
    hd hu huv hm1 (by unfold scaledBandCoefficient; positivity) hC.le hJ (Nat.cast_nonneg _)
    hHF (scaled_supply_log_upper m X hXhi) hraw hm

/-- Seventeen endpoints defining sixteen adjacent bands. -/
def scaledBandEndpoint : ℕ → ℕ
  | 0 => 8832000
  | 1 => 8905000
  | 2 => 8978000
  | 3 => 9051000
  | 4 => 9124000
  | 5 => 9197000
  | 6 => 9270000
  | 7 => 9343000
  | 8 => 9416000
  | 9 => 9489000
  | 10 => 9562000
  | 11 => 9635000
  | 12 => 9708000
  | 13 => 9781000
  | 14 => 9854000
  | 15 => 9927000
  | _ => 10000007

def scaledBandT (i : Fin 16) : ℕ := if i.val = 15 then 40000003 else 20000003

def scaledBandB (i : Fin 16) : ℕ :=
  ![11229655,11138347,11048512,10960114,10873120,10787495,10703209,10620229,10538527,10458072,10378836,10300791,10223912,10148171,10073545,20000002] i

def scaledBandL (i : Fin 16) : ℕ :=
  ![2459309,2276693,2097022,1920227,1746238,1574989,1406416,1240457,1077052,916142,757670,601581,447822,296341,147088,3] i

noncomputable def scaledBandBudget (i : Fin 16) : ℝ :=
  ![66188,65646,65112,64587,64070,63562,63061,62568,62083,61606,61135,60672,60216,59766,59324,58893] i / 1000000

lemma scaledBand_band_parameters (i : Fin 16) :
    1 ≤ scaledBandEndpoint i ∧ scaledBandEndpoint i ≤ scaledBandEndpoint (i+1) ∧
    scaledBandEndpoint (i+1) ≤ 10000008 ∧ 10000011 ≤ 2*scaledBandEndpoint i ∧
    1 ≤ scaledBandB i ∧ scaledBandB i+1 ≤ scaledBandT i ∧
    2*scaledBandB i+1 ≤ scaledBandL i+scaledBandT i ∧ 3 ≤ scaledBandL i ∧
    scaledBandL i*scaledBandEndpoint (i+1) < scaledBandT i*(10000008-scaledBandEndpoint (i+1)) ∧
    0 ≤ scaledBandBudget i := by
  fin_cases i <;> norm_num [scaledBandEndpoint,scaledBandT,scaledBandB,scaledBandL,scaledBandBudget]

lemma scaledBand_band_limit (i : Fin 16) :
    scaledProductLongLimit (scaledBandCoefficient (scaledBandT i) (scaledBandB i))
      (scaledBandEndpoint i) (scaledBandEndpoint (i+1)) < scaledBandBudget i := by
  have hh := productSupply_log_error_coefficient
  fin_cases i <;>
    norm_num [scaledProductLongLimit,scaledBandCoefficient,scaledBandEndpoint,
      scaledBandT,scaledBandB,scaledBandBudget] <;>
    nlinarith only [hh]

lemma scaledBand_budget_sum : (∑ i : Fin 16, scaledBandBudget i) = 998489/1000000 := by
  norm_num [scaledBandBudget,Fin.sum_univ_succ]

lemma eventually_all_scaled_band_bands :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin 16, ∀ X d : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      independentN 20000000 m ≤ d → d ≤ independentN 20000004 m →
      Real.log (X : ℝ)*
        ((hyperbolicPrimePairPool d (X/d)
          (2^(128*scaledBandEndpoint i*m)) (2^(128*scaledBandEndpoint (i+1)*m))).card : ℝ) ≤
          scaledBandBudget i*(X : ℝ)/(d.totient : ℝ) := by
  rw [Filter.eventually_all]
  intro i
  obtain ⟨hu,huv,hv,hhalf,hb,hbt,hlevel,hl,hscale,hJ⟩ := scaledBand_band_parameters i
  exact eventually_scaled_band_band _ _ _ _ _ hu huv hv hhalf hb hbt hlevel hl hscale _ hJ
    (scaledBand_band_limit i)

end Erdos821.AnalyticSieve
