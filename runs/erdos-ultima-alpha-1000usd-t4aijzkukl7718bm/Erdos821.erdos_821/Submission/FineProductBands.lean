import Submission.ProductSupplyRoughBound

/-!
# Finer long-cofactor ranges in the product sieve

These estimates refine a fixed smoothness ratio only. They do not prove the
arbitrary-root prime supply required for the original conjecture.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma eventually_fine_product_threshold (t l v : ℕ) (ht : 1 ≤ t)
    (hv : v ≤ 100008) (hscale : l*v < t*(100008-v)) :
    ∀ᶠ m : ℕ in atTop, ∀ H : ℕ, 2^(128*100008*m) ≤ H →
      cofactorScale l (2*cofactorDyadicIndex t (128*v*m)) ≤ H/2^(128*v*m) := by
  filter_upwards [eventually_ge_atTop (4*l*t)] with m hm
  intro H hH
  have hb := (cofactorDyadicIndex_bounds t (128*v*m) ht).2
  have he : 512*l*cofactorDyadicIndex t (128*v*m) ≤ 128*(100008-v)*m := by
    have hmul := Nat.mul_le_mul_left l hb
    have hgap := Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr hscale)
    have ht0 : 0 < t := by omega
    apply Nat.le_of_mul_le_mul_left (c := t) _ ht0
    nlinarith only [hm,hmul,hgap]
  apply (show cofactorScale l (2*cofactorDyadicIndex t (128*v*m)) ≤
      2^(128*(100008-v)*m) by
    rw [cofactorScale_eq]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [he]).trans
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2^(128*v*m))).mpr
  apply le_trans _ hH
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have hcancel := Nat.sub_add_cancel hv
  nlinarith only [congrArg (fun n : ℕ => 128*n*m) hcancel]

noncomputable def fineProductCoefficient (t b : ℕ) : ℝ :=
  (2*(t : ℝ)/(b : ℝ))*(1+1/(2 : ℝ)^10)

lemma eventually_fine_product_band (u v t b l : ℕ)
    (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ 100008)
    (hhalf : 100011 ≤ 2*u) (hb : 1 ≤ b) (hbt : b+1 ≤ t)
    (hlevel : 2*b+1 ≤ l+t) (hl : 3 ≤ l)
    (hscale : l*v < t*(100008-v)) (J : ℝ) (hJ : 0 ≤ J)
    (hlimit : productSupplyLongLimit (fineProductCoefficient t b) u v < J) :
    ∀ᶠ m : ℕ in atTop, ∀ X d : ℕ,
      independentN 400020 m ≤ X → X ≤ independentN 400021 m →
      independentN 200000 m ≤ d → d ≤ independentN 200004 m →
      Real.log (X : ℝ)*
          ((hyperbolicPrimePairPool d (X/d) (2^(128*u*m)) (2^(128*v*m))).card : ℝ) ≤
        J*(X : ℝ)/(d.totient : ℝ) := by
  obtain ⟨C,hC,K₀,hbound⟩ := exists_product_cofactor_hyperbolic_bound 1 b t l 10
    (by decide) hb hbt hlevel hl (1/1000000) (by norm_num)
  have hbudget : ∀ᶠ m : ℕ in atTop,
      productSupplyLongBudget (fineProductCoefficient t b) u v C m ≤ J :=
    (tendsto_productSupplyLongBudget _ C u v hu (hu.trans huv)).eventually
      (eventually_le_nhds hlimit)
  filter_upwards [hbudget,eventually_fine_product_threshold t l v (by omega) hv hscale,
    eventually_ge_atTop (max 1 K₀)] with m hm hthreshold hmK
  intro X d hXlo hXhi hdlo hdhi
  have hm1 : 1 ≤ m := (le_max_left _ _).trans hmK
  have hK : K₀ ≤ m := (le_max_right _ _).trans hmK
  have hd : 0 < d := (by unfold independentN; positivity : 0 < independentN 200000 m).trans_le hdlo
  have hH := successor_supply_quotient_bounds m X d hXlo hXhi hdlo hdhi
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
  apply product_long_weighted_budget d (X/d) X u v m (fineProductCoefficient t b) C J _
    hd hu huv hm1 (by unfold fineProductCoefficient; positivity) hC.le hJ (Nat.cast_nonneg _)
    hHF (successor_supply_log_upper m X hXhi) hraw hm

/-- Ten endpoints defining nine adjacent bands. -/
def fineProductEndpoint : ℕ → ℕ
  | 0 => 88600
  | 1 => 89700
  | 2 => 91000
  | 3 => 92300
  | 4 => 93600
  | 5 => 94900
  | 6 => 96200
  | 7 => 97500
  | 8 => 98800
  | _ => 100007

def fineProductT (i : Fin 9) : ℕ := if i.val = 8 then 400003 else 200003

def fineProductB (i : Fin 9) : ℕ :=
  ![111492,109899,108351,106846,105383,103958,102572,101223,200002] i

def fineProductL (i : Fin 9) : ℕ :=
  ![22982,19797,16701,13691,10764,7915,5143,2444,3] i

noncomputable def fineProductBudget (i : Fin 9) : ℝ :=
  ![995,1161,1144,1128,1113,1097,1083,1068,979] i / 10000

lemma fineProduct_band_parameters (i : Fin 9) :
    1 ≤ fineProductEndpoint i ∧ fineProductEndpoint i ≤ fineProductEndpoint (i+1) ∧
    fineProductEndpoint (i+1) ≤ 100008 ∧ 100011 ≤ 2*fineProductEndpoint i ∧
    1 ≤ fineProductB i ∧ fineProductB i+1 ≤ fineProductT i ∧
    2*fineProductB i+1 ≤ fineProductL i+fineProductT i ∧ 3 ≤ fineProductL i ∧
    fineProductL i*fineProductEndpoint (i+1) < fineProductT i*(100008-fineProductEndpoint (i+1)) ∧
    0 ≤ fineProductBudget i := by
  fin_cases i <;> norm_num [fineProductEndpoint,fineProductT,fineProductB,fineProductL,fineProductBudget]

lemma fineProduct_band_limit (i : Fin 9) :
    productSupplyLongLimit (fineProductCoefficient (fineProductT i) (fineProductB i))
      (fineProductEndpoint i) (fineProductEndpoint (i+1)) < fineProductBudget i := by
  have hh := productSupply_log_error_coefficient
  fin_cases i <;>
    norm_num [productSupplyLongLimit,fineProductCoefficient,fineProductEndpoint,
      fineProductT,fineProductB,fineProductBudget] <;>
    nlinarith only [hh]

lemma fineProduct_budget_sum : (∑ i : Fin 9, fineProductBudget i) = 1221/1250 := by
  norm_num [fineProductBudget,Fin.sum_univ_succ]

lemma eventually_all_fine_product_bands :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin 9, ∀ X d : ℕ,
      independentN 400020 m ≤ X → X ≤ independentN 400021 m →
      independentN 200000 m ≤ d → d ≤ independentN 200004 m →
      Real.log (X : ℝ)*
        ((hyperbolicPrimePairPool d (X/d)
          (2^(128*fineProductEndpoint i*m)) (2^(128*fineProductEndpoint (i+1)*m))).card : ℝ) ≤
          fineProductBudget i*(X : ℝ)/(d.totient : ℝ) := by
  rw [Filter.eventually_all]
  intro i
  obtain ⟨hu,huv,hv,hhalf,hb,hbt,hlevel,hl,hscale,hJ⟩ := fineProduct_band_parameters i
  exact eventually_fine_product_band _ _ _ _ _ hu huv hv hhalf hb hbt hlevel hl hscale _ hJ
    (fineProduct_band_limit i)

end Erdos821.AnalyticSieve
