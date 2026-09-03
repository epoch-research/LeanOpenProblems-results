import Submission.PoolBandBounds

/-!
# Thirty-six retained-pool bands

These improve a fixed cutoff. They do not remove the independent
half-level restriction on the initial progression-prime supply.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

def finePoolEndpoint : ℕ → ℕ
  | 0 => 7800000
  | 1 => 7861111
  | 2 => 7922222
  | 3 => 7983333
  | 4 => 8044445
  | 5 => 8105556
  | 6 => 8166667
  | 7 => 8227779
  | 8 => 8288890
  | 9 => 8350001
  | 10 => 8411113
  | 11 => 8472224
  | 12 => 8533335
  | 13 => 8594446
  | 14 => 8655558
  | 15 => 8716669
  | 16 => 8777780
  | 17 => 8838892
  | 18 => 8900003
  | 19 => 8961114
  | 20 => 9022226
  | 21 => 9083337
  | 22 => 9144448
  | 23 => 9205560
  | 24 => 9266671
  | 25 => 9327782
  | 26 => 9388893
  | 27 => 9450005
  | 28 => 9511116
  | 29 => 9572227
  | 30 => 9633339
  | 31 => 9694450
  | 32 => 9755561
  | 33 => 9816673
  | 34 => 9877784
  | 35 => 9938895
  | _ => 10000007

def finePoolB (i : Fin 36) : ℕ :=
  ![127207210,126225950,125259712,124308140,123370932,122447750,121538266,120642209,119759267,118889141,118031581,117186305,116353049,115531546,114721575,113922882,113135221,112358389,111592152,110836283,110090597,109354878,108628915,107912539,107205550,106507764,105818991,105139081,104467852,103805129,103150771,102504612,101866487,101236269,100613800,99998930] i

def finePoolL (i : Fin 36) : ℕ := 2*finePoolB i-100000000+1

noncomputable def finePoolBudget (i : Fin 36) : ℝ :=
  ![3140060,3115650,3091616,3068000,3044643,3021689,2999126,2976802,2954855,2933277,2911917,2890913,2870210,2849848,2829681,2809842,2790326,2770988,2751961,2733239,2714681,2696417,2678441,2660616,2643070,2625754,2608706,2591794,2575141,2558743,2542469,2526442,2510657,2494986,2479550,2464345] i / 100000000

lemma finePool_band_parameters (i : Fin 36) :
    1 ≤ finePoolEndpoint i ∧ finePoolEndpoint i ≤ finePoolEndpoint (i+1) ∧
    finePoolEndpoint (i+1) ≤ 10000007 ∧ 20000011 ≤ 3*finePoolEndpoint i ∧
    1 ≤ finePoolB i ∧ finePoolB i < 200000000 ∧ 1 ≤ finePoolL i ∧
    2*finePoolB i+1 ≤ finePoolL i+100000000 ∧
    finePoolL i*finePoolEndpoint (i+1) < 100000000*(20000009-finePoolEndpoint (i+1)) ∧
    finePoolB i*finePoolEndpoint (i+1) < 100000000*10000000 := by
  fin_cases i <;> norm_num [finePoolEndpoint,finePoolB,finePoolL]

lemma finePool_band_limit (i : Fin 36) :
    scaledProductLongLimit (poolBandCoefficient (finePoolB i))
      (finePoolEndpoint i) (finePoolEndpoint (i+1)) < finePoolBudget i := by
  have hh := productSupply_log_error_coefficient
  fin_cases i <;>
    norm_num [scaledProductLongLimit,poolBandCoefficient,finePoolEndpoint,finePoolB,finePoolBudget] <;>
    nlinarith only [hh]

lemma finePool_budget_sum : (∑ i : Fin 36, finePoolBudget i) = 99926455/100000000 := by
  norm_num [finePoolBudget,Fin.sum_univ_succ]

lemma eventually_all_fine_pool_bands :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin 36, ∀ X : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      Real.log (X : ℝ)*(∑ c ∈ widePairPool 10000000 m,
        ((hyperbolicPrimePairPool c (X/c)
          (2^(128*finePoolEndpoint i*m)) (2^(128*finePoolEndpoint (i+1)*m))).card : ℝ)) ≤
            finePoolBudget i*(X : ℝ)*poolTotientMass (widePairPool 10000000 m) := by
  rw [Filter.eventually_all]
  intro i
  obtain ⟨hu,huv,hv,hu3,hb,hbt,hl,hlevel,hscale,hrough⟩ := finePool_band_parameters i
  exact eventually_pool_band_rejection_bound _ _ _ _ hu huv hv hu3 hb hbt hl hlevel hscale hrough _
    (finePool_band_limit i)

end Erdos821.AnalyticSieve
