import FormalConjecturesUtil
import Submission.SafeMergeBatch

/-! Fixed-batch asymptotic estimates. The batch size is fixed before the
order threshold; no uniformity for a linearly growing batch is asserted. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713SafeBatchAsymptotics
open Erdos713DegreePenalty Erdos713DegreePenaltySupports Erdos713MergeDegreePenalty
open Erdos713CommonBlockerPairCount Erdos713SafeMergeBatch
set_option maxHeartbeats 2000000

lemma eventually_lossBound (k : ℕ) {β C ε : ℝ} (hβ : β < 1/4) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (D : ℝ) ≤ C*(n : ℝ)^β →
      ((k*lossBound n D : ℕ) : ℝ) ≤ ε*(n : ℝ)^2 := by
  have h₁ : Tendsto (fun n : ℕ => 96*k*C^4*(n : ℝ)^(4*β-1)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_sub,mul_zero] using
      (((tendsto_rpow_neg_atTop (show 0 < 1-4*β by linarith)).comp
        tendsto_natCast_atTop_atTop).const_mul (96*k*C^4))
  have h₂ : Tendsto (fun n : ℕ => 4*k/(n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_natCast_atTop_atTop.const_div_atTop (4*(k : ℝ))
  have hSq : Tendsto (fun n : ℕ => (n : ℝ)^2) atTop atTop := by
    simpa only [Real.rpow_two] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have h₃ := hSq.const_div_atTop (k : ℝ)
  have hlim : Tendsto (fun n : ℕ => 96*k*C^4*(n : ℝ)^(4*β-1)+4*k/(n : ℝ)+k/(n : ℝ)^2)
      atTop (𝓝 (0 : ℝ)) := by simpa only [add_zero] using (h₁.add h₂).add h₃
  filter_upwards [hlim.eventually_lt_const hε,eventually_gt_atTop (0 : ℕ)] with n hn hn0
  intro D hD
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hDp : (D : ℝ)^4 ≤ C^4*(n : ℝ)^(4*β) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) D) hD 4
    rw [mul_pow,← Real.rpow_mul_natCast hnR.le] at hh
    convert hh using 1
    congr 2
    ring
  have hpow : (n : ℝ)^2*(n : ℝ)^(4*β-1)=(n : ℝ)*(n : ℝ)^(4*β) := by
    calc
      _ = (n : ℝ)^(4*β+1) := by
        rw [← Real.rpow_two,← Real.rpow_add hnR]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_add hnR,Real.rpow_one,mul_comm]
  have hterm₁ : (n : ℝ)^2*(96*k*C^4*(n : ℝ)^(4*β-1))=
      96*k*n*C^4*(n : ℝ)^(4*β) := by
    calc
      _ = 96*k*C^4*((n : ℝ)^2*(n : ℝ)^(4*β-1)) := by ring
      _ = _ := by rw [hpow]; ring
  have hterm₂ : (n : ℝ)^2*(4*k/(n : ℝ))=4*k*n := by field_simp
  have hterm₃ : (n : ℝ)^2*(k/(n : ℝ)^2)=(k : ℝ) := by field_simp
  have hm := mul_le_mul_of_nonneg_left hn.le (sq_nonneg (n : ℝ))
  rw [mul_add,mul_add,hterm₁,hterm₂,hterm₃] at hm
  have hcast : ((k*lossBound n D : ℕ) : ℝ)=96*k*n*(D : ℝ)^4+4*k*n+k := by
    dsimp only [lossBound]
    push_cast
    ring
  rw [hcast]
  have hDp' := mul_le_mul_of_nonneg_left hDp (show 0 ≤ 96*(k : ℝ)*n by positivity)
  nlinarith only [hm,hDp']

/-- For every fixed k, the finite batch comparison gives a uniform sparse
bound for bounded-cost safe pairs after a common spanning loss. -/
theorem eventually_pair_count (k : ℕ) {β C ε : ℝ} (hβ : β < 1/4) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (G F : SimpleGraph (Fin n)) (lam mu t s : ℝ),
      GlobalOptimal (cycleGraph 8) G lam mu → 0 ≤ lam → F ≤ G → edgesR G ≤ edgesR F+t →
      ∀ S : Finset (Fin n × Fin n),
        (∀ p ∈ S, SafePair (cycleGraph 8) F p.1 p.2) →
        (∀ p ∈ S, pairCost F lam p ≤ s) →
        t+(k : ℝ)*s+(k : ℝ)*(k-1)/2 < mu*(2*n*k-(k : ℝ)^2) →
        ∀ D : ℕ, (∀ v, F.degree v ≤ D) → (D : ℝ) ≤ C*(n : ℝ)^β →
          (S.card : ℝ) ≤ ε*(n : ℝ)^2 := by
  filter_upwards [eventually_lossBound k hβ hε] with n hn
  intro G F lam mu t s hg hlam hle hloss S hSafe hCost hcost D hD hDC
  have hC := pair_count hg hlam hle hloss k n D (by simp)
    (fun v => (hD v).trans (by omega)) S hSafe (fun p _ => ⟨hD p.1,hD p.2⟩)
    hCost (by simpa only [Fintype.card_fin] using hcost)
  exact (Nat.cast_le.mpr hC).trans (hn D hDC)

/-- A fixed batch can pay any fixed loss coefficient once its size is large
enough. The constant quadratic collision cost is absorbed only at large order. -/
lemma eventually_batch_slope (k : ℕ) {A b β : ℝ} (_hb : 0 < b)
    (hA : A < (k : ℝ)*b/4) (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ mu : ℝ, 0 ≤ mu →
      b*(n : ℝ)^β ≤ mu*(2*n-1) →
      A*(n : ℝ)^β+(k : ℝ)*(b/4*(n : ℝ)^β)+(k : ℝ)*(k-1)/2 <
        mu*(2*n*k-(k : ℝ)^2) := by
  have hGrow : Tendsto (fun n : ℕ => ((k : ℝ)*b/4-A)*(n : ℝ)^β) atTop atTop :=
    ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).const_mul_atTop (by linarith)
  filter_upwards [eventually_ge_atTop k,hGrow.eventually_gt_atTop ((k : ℝ)*(k-1)/2),
    eventually_gt_atTop (0 : ℕ)] with n hn hGrow hn0
  refine ⟨hn0,?_⟩
  intro mu hmu hSlope
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
  have hprod := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sub_nonneg.mpr hkn)
  have hRatio : (k : ℝ)/2*(2*n-1) ≤ 2*n*k-(k : ℝ)^2 := by
    nlinarith only [hprod,Nat.cast_nonneg (α := ℝ) k]
  have hRat := mul_le_mul_of_nonneg_left hRatio hmu
  have hSl := mul_le_mul_of_nonneg_left hSlope (show 0 ≤ (k : ℝ)/2 by positivity)
  nlinarith only [hRat,hSl,hGrow]

#print axioms eventually_lossBound
#print axioms eventually_pair_count
#print axioms eventually_batch_slope
end Erdos713SafeBatchAsymptotics
