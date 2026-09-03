import Submission.CertifiedPoolBands

/-!
# One thousand kernel-certified retained-pool bands

The cutoff is 15586800/40000020. This improves a fixed multiplicity
exponent, not the unrestricted conjecture.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

/-- A uniformly spaced, rounded partition; it is constant after its last point. -/
def thousandPoolEndpoint (i : ℕ) : ℕ :=
  7793400 + (2206607 * min i 1000)/1000

def thousandPoolB (i : Fin 1000) : ℕ :=
  999999999999999 / thousandPoolEndpoint (i.val+1)

def thousandPoolL (i : Fin 1000) : ℕ := 2*thousandPoolB i-100000000+1

def thousandPoolBudgetNat (i : Fin 1000) : ℕ :=
  poolBandCertificate 10000000000 (thousandPoolEndpoint i.val)
    (thousandPoolEndpoint (i.val+1)) (thousandPoolB i)

noncomputable def thousandPoolBudget (i : Fin 1000) : ℝ :=
  (thousandPoolBudgetNat i : ℝ)/10000000000

lemma thousandPool_band_parameters (i : Fin 1000) :
    1 ≤ thousandPoolEndpoint i.val ∧
    thousandPoolEndpoint i.val ≤ thousandPoolEndpoint (i.val+1) ∧
    thousandPoolEndpoint (i.val+1) ≤ 10000007 ∧
    20000011 ≤ 3*thousandPoolEndpoint i.val ∧
    1 ≤ thousandPoolB i ∧ thousandPoolB i < 200000000 ∧
    1 ≤ thousandPoolL i ∧ 2*thousandPoolB i+1 ≤ thousandPoolL i+100000000 ∧
    thousandPoolL i*thousandPoolEndpoint (i.val+1) <
      100000000*(20000009-thousandPoolEndpoint (i.val+1)) ∧
    thousandPoolB i*thousandPoolEndpoint (i.val+1) < 100000000*10000000 := by
  have hc : ∀ i : Fin 1000,
    1 ≤ thousandPoolEndpoint i.val ∧
    thousandPoolEndpoint i.val ≤ thousandPoolEndpoint (i.val+1) ∧
    thousandPoolEndpoint (i.val+1) ≤ 10000007 ∧
    20000011 ≤ 3*thousandPoolEndpoint i.val ∧
    1 ≤ thousandPoolB i ∧ thousandPoolB i < 200000000 ∧
    1 ≤ thousandPoolL i ∧ 2*thousandPoolB i+1 ≤ thousandPoolL i+100000000 ∧
    thousandPoolL i*thousandPoolEndpoint (i.val+1) <
      100000000*(20000009-thousandPoolEndpoint (i.val+1)) ∧
    thousandPoolB i*thousandPoolEndpoint (i.val+1) < 100000000*10000000 := by
      decide
  exact hc i

lemma thousandPool_band_limit (i : Fin 1000) :
    scaledProductLongLimit (poolBandCoefficient (thousandPoolB i))
      (thousandPoolEndpoint i.val) (thousandPoolEndpoint (i.val+1)) < thousandPoolBudget i := by
  obtain ⟨hu,huv,_,_,hb,_⟩ := thousandPool_band_parameters i
  exact poolBandLimit_lt_certificate 10000000000 _ _ _ (by decide) hu huv hb

lemma thousandPool_budgetNat_sum :
    (∑ i : Fin 1000, thousandPoolBudgetNat i) = 9993098816 := by
  decide

lemma thousandPool_budget_sum :
    (∑ i : Fin 1000, thousandPoolBudget i) = 9993098816/10000000000 := by
  unfold thousandPoolBudget
  rw [← sum_div,← Nat.cast_sum,thousandPool_budgetNat_sum]
  norm_num

lemma eventually_all_thousand_pool_bands :
    ∀ᶠ m : ℕ in atTop, ∀ i : Fin 1000, ∀ X : ℕ,
      independentN 40000020 m ≤ X → X ≤ independentN 40000021 m →
      Real.log (X : ℝ)*(∑ c ∈ widePairPool 10000000 m,
        ((hyperbolicPrimePairPool c (X/c)
          (2^(128*thousandPoolEndpoint i.val*m))
          (2^(128*thousandPoolEndpoint (i.val+1)*m))).card : ℝ)) ≤
            thousandPoolBudget i*(X : ℝ)*poolTotientMass (widePairPool 10000000 m) := by
  rw [Filter.eventually_all]
  intro i
  obtain ⟨hu,huv,hv,hu3,hb,hbt,hl,hlevel,hscale,hrough⟩ := thousandPool_band_parameters i
  exact eventually_pool_band_rejection_bound _ _ _ _ hu huv hv hu3 hb hbt hl hlevel hscale hrough _
    (thousandPool_band_limit i)

end Erdos821.AnalyticSieve
