import Submission.MappedSquarefreeDivisorExpansion
import Submission.SquarefreePrimeOutputMean
import Submission.ExactLargeDivisorFirstMoment

/-! Squarefree outputs on genuine prime inputs, uniformly over prefixes
of the actual common direct scales. This is an absolute-support mean,
not a signed Möbius cancellation estimate or a prime-pair lower bound. -/
namespace Erdos972ForwardSquarefreeSupport

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972MappedSquarefreeDivisorExpansion Erdos972SquarefreeDivisorExpansion
open Erdos972SquarefreePrimeOutputMean Erdos972ExactLargeDivisorFirstMoment
open Erdos972PrimeSmoothDivisorEstimate Erdos972PrimeLeastFactorScales
open Erdos972PrimeRoughOutputs Erdos972PrimePowerError Erdos972SelbergLowerTest
open Erdos972PolynomialRowScales Erdos972GrowingTypeIIReduction
open Erdos972ChebyshevRowMean Erdos972ChebyshevPNT

set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] root64

noncomputable def primeSquarefreeSum (α : ℝ) (X : ℕ) : ℝ :=
  ∑ p ∈ Ioc 0 X, primeWeight p*|(moebius (floorMul α p) : ℝ)|

lemma primeSquarefreeSum_nonneg (α : ℝ) (X : ℕ) : 0 ≤ primeSquarefreeSum α X := by
  exact sum_nonneg (fun p _ => mul_nonneg (primeWeight_nonneg p) (abs_nonneg _))

lemma prime_squarefree_finite_error {α : ℝ} (hα : 1 ≤ α) {N D X : ℕ}
    (hD : 0 < D) (hDM : D ≤ floorMul α N) (hXN : X ≤ N) {E : ℝ}
    (hrows : ∀ d ∈ Ioc 0 D,
      |row (Ioc 0 X) primeWeight (floorMul α) (d^2)-Chebyshev.psi X/(d^2 : ℕ)| ≤ E) :
    |primeSquarefreeSum α X-Chebyshev.psi X*squarefreeMeanTruncation D| ≤
      Real.log N*(floorMul α N : ℝ)/D+D*E := by
  apply mapped_squarefree_mean_error (Ioc 0 X) primeWeight (floorMul α)
    hD hDM (Real.log_natCast_nonneg N) (floorMul_strictMono hα).injective.injOn
  · intro p hp
    exact mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hp).1,
      (floorMul_strictMono hα).monotone ((mem_Ioc.mp hp).2.trans hXN)⟩
  · intro p hp
    exact primeWeight_nonneg p
  · intro p hp
    exact primeWeight_le_prefix_log (mem_Ioc.mpr ⟨(mem_Ioc.mp hp).1,
      (mem_Ioc.mp hp).2.trans hXN⟩)
  · exact hrows

noncomputable def forwardSquarefreeBudget (α : ℝ) (u : ℕ) : ℝ :=
  6*α*(1+Real.log u)/(growingCutoff u : ℝ)+
    (growingCutoff u : ℝ)*primeRowError u/(u : ℝ)^6+
      7*|squarefreeMeanTruncation (growingCutoff u)-6/Real.pi^2|

lemma forward_squarefree_row_budget_tendsto :
    Tendsto (fun u : ℕ => (growingCutoff u : ℝ)*primeRowError u/(u : ℝ)^6)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun u => by positivity [primeRowError_nonneg u]))
    (Eventually.of_forall (fun u => ?_)) primeRowError_weighted_tendsto
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (growingCutoff_eligible u).1)
      (primeRowError_nonneg u)) (by positivity)

lemma forwardSquarefreeBudget_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (forwardSquarefreeBudget α) atTop (𝓝 0) := by
  have ht := growingCutoff_log_div_tendsto (6*α) (by positivity) 1
  have hm := (((squarefreeMeanTruncation_tendsto.comp growingCutoff_tendsto).sub_const
    (6/Real.pi^2)).abs).const_mul 7
  have hh := (ht.add forward_squarefree_row_budget_tendsto).add hm
  unfold forwardSquarefreeBudget
  simpa only [pow_one, Function.comp_apply, sub_self, abs_zero, mul_zero, add_zero] using hh

/-- A uniform prefix bound, with error measured against the full scale N.
The row hypotheses here are exactly the available direct prime-input rows. -/
lemma forward_squarefree_prefix_error {α : ℝ} (hα : 1 ≤ α) {u : ℕ}
    (hu : 0 < u) (hW : 0 < growingCutoff u)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ root64 u → ∀ X : ℕ, X ≤ u^6 →
      |row (Ioc 0 X) primeWeight (floorMul α) d-Chebyshev.psi X/(d : ℝ)| ≤ primeRowError u)
    {X : ℕ} (hX : X ≤ u^6) :
    |primeSquarefreeSum α X-Chebyshev.psi X*(6/Real.pi^2)| ≤
      forwardSquarefreeBudget α u*(u : ℝ)^6 := by
  have huN : u ≤ u^6 := Nat.le_self_pow (by decide) u
  have hWN : growingCutoff u ≤ u^6 :=
    ((growingCutoff_eligible u).1.trans (Erdos972GrowingCoprimeCandidates.root64_le_self u)).trans huN
  have hgN := self_le_floorMul hα (u^6)
  have hf := prime_squarefree_finite_error hα hW (hWN.trans hgN) hX (by
    intro d hd
    have hdv : d^2 ≤ root64 u := (Nat.pow_le_pow_left (mem_Ioc.mp hd).2 2).trans
      (by simpa only [pow_two] using (growingCutoff_eligible u).2)
    exact hrows (d^2) (pow_pos (mem_Ioc.mp hd).1 2) hdv X hX)
  have hN : (0 : ℝ) < (u : ℝ)^6 := pow_pos (Nat.cast_pos.mpr hu) _
  have htail : Real.log (u^6 : ℕ)*(floorMul α (u^6) : ℝ)/(growingCutoff u : ℝ) ≤
      (6*α*(1+Real.log u)/(growingCutoff u : ℝ))*(u : ℝ)^6 := by
    have hg : (floorMul α (u^6) : ℝ) ≤ α*(u : ℝ)^6 := by
      exact (floorMul_le_real hα (le_refl (u^6))).trans_eq (by norm_cast)
    have hl : Real.log (u^6 : ℕ) ≤ 6*(1+Real.log u) := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith
    calc
      _ ≤ (6*(1+Real.log u))*(α*(u : ℝ)^6)/(growingCutoff u : ℝ) := by gcongr
      _ = _ := by ring
  have hpsi : Chebyshev.psi X ≤ 7*(u : ℝ)^6 := by
    apply (psi_le_seven_mul (Nat.cast_nonneg X)).trans
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hX) (by norm_num)
  have hcenter : |Chebyshev.psi X*squarefreeMeanTruncation (growingCutoff u)-
      Chebyshev.psi X*(6/Real.pi^2)| ≤
      (7*|squarefreeMeanTruncation (growingCutoff u)-6/Real.pi^2|)*(u : ℝ)^6 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Chebyshev.psi_nonneg _)]
    have hh := mul_le_mul_of_nonneg_right hpsi
      (abs_nonneg (squarefreeMeanTruncation (growingCutoff u)-6/Real.pi^2))
    nlinarith only [hh]
  have hh := (abs_sub_le (primeSquarefreeSum α X)
    (Chebyshev.psi X*squarefreeMeanTruncation (growingCutoff u))
      (Chebyshev.psi X*(6/Real.pi^2))).trans (add_le_add hf hcenter)
  apply hh.trans
  have he : forwardSquarefreeBudget α u*(u : ℝ)^6 =
      (6*α*(1+Real.log u)/(growingCutoff u : ℝ))*(u : ℝ)^6+
        (growingCutoff u : ℝ)*primeRowError u+
        (7*|squarefreeMeanTruncation (growingCutoff u)-6/Real.pi^2|)*(u : ℝ)^6 := by
    unfold forwardSquarefreeBudget
    field_simp
  rw [he]
  linarith only [htail]

/-- All prefixes are controlled at ONE actual good scale, selected after
the error budget threshold. -/
theorem exists_forward_squarefree_prefix_scale {α ε : ℝ} (hα : 1 < α)
    (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧ ∀ X : ℕ, X ≤ u^6 →
      |primeSquarefreeSum α X-Chebyshev.psi X*(6/Real.pi^2)| ≤ ε*(u : ℝ)^6 := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_order.mp (forwardSquarefreeBudget_tendsto (by linarith : 0 < α))).2 ε hε).and
      (growingCutoff_tendsto.eventually_ge_atTop 1))
  obtain ⟨u, hBu, hu, _, hrows⟩ := exists_small_prime_prefix_rows hα hI
    (by norm_num : (0 : ℝ) < 1) (max B T)
  obtain ⟨hb, hW⟩ := hT u ((le_max_right B T).trans hBu.le)
  refine ⟨u, (le_max_left B T).trans_lt hBu, hu, ?_⟩
  intro X hX
  exact (forward_squarefree_prefix_error hα.le hu hW hrows hX).trans
    (mul_le_mul_of_nonneg_right hb.le (by positivity))

/-- The forward squarefree-support mean, with genuine prime inputs. -/
theorem exists_forward_squarefree_mean {α ε : ℝ} (hα : 1 < α)
    (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧
      |primeSquarefreeSum α (u^6)/(u : ℝ)^6-6/Real.pi^2| < ε := by
  have hpow : Tendsto (fun u : ℕ => u^6) atTop atTop := tendsto_pow_atTop (by decide)
  have hp := psi_div_self_tendsto.comp (tendsto_natCast_atTop_atTop.comp hpow)
  have hm := ((hp.mul_const (6/Real.pi^2)).sub_const (6/Real.pi^2)).abs
  simp only [one_mul, sub_self, abs_zero, Function.comp_apply, Nat.cast_pow] at hm
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((tendsto_order.mp hm).2 (ε/2) (by positivity))
  obtain ⟨u, hBu, hu, hf⟩ := exists_forward_squarefree_prefix_scale hα hI
    (show 0 < ε/2 by positivity) (max B T)
  have hmain := hT u ((le_max_right B T).trans hBu.le)
  have hN : (0 : ℝ) < (u : ℝ)^6 := pow_pos (Nat.cast_pos.mpr hu) _
  have herr := (div_le_iff₀ hN).mpr (hf (u^6) le_rfl)
  have he : primeSquarefreeSum α (u^6)/(u : ℝ)^6-6/Real.pi^2 =
      (primeSquarefreeSum α (u^6)-Chebyshev.psi (u^6 : ℕ)*(6/Real.pi^2))/(u : ℝ)^6+
        (Chebyshev.psi (u^6 : ℕ)/(u : ℝ)^6*(6/Real.pi^2)-6/Real.pi^2) := by ring
  refine ⟨u, (le_max_left B T).trans_lt hBu, hu, ?_⟩
  rw [he]
  apply (abs_add_le _ _).trans_lt
  rw [abs_div, abs_of_pos hN]
  push_cast at herr ⊢
  linarith only [herr, hmain]

#print axioms prime_squarefree_finite_error
#print axioms exists_forward_squarefree_prefix_scale
#print axioms exists_forward_squarefree_mean
end Erdos972ForwardSquarefreeSupport
