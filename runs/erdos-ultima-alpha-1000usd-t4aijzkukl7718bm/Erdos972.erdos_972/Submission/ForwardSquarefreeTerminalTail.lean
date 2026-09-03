import Submission.ForwardSquarefreeSupport
import Submission.TerminalPrimeDivisorTail

/-! The exact terminal interval and the squarefree Euler factor are retained
in an actual prime-input Möbius tail bound. No sign cancellation is asserted. -/
namespace Erdos972ForwardSquarefreeTerminalTail

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972ForwardSquarefreeSupport Erdos972TerminalPrimeDivisorTail
open Erdos972ExactLargeDivisorFirstMoment Erdos972PrimePowerError
open Erdos972PrimeRoughOutputs Erdos972PrimeLeastFactorScales
open Erdos972PrimeSmoothDivisorEstimate Erdos972ExponentialSum
open Erdos972SmoothDivisorTail

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def terminalSquarefreePrimeSum (α : ℝ) (D N : ℕ) : ℝ :=
  ∑ p ∈ Ioc 0 N, if D < floorMul α p then
    primeWeight p*|(moebius (floorMul α p) : ℝ)| else 0

lemma terminalSquarefreePrimeSum_nonneg (α : ℝ) (D N : ℕ) :
    0 ≤ terminalSquarefreePrimeSum α D N := by
  apply sum_nonneg
  intro p hp
  split_ifs
  · exact mul_nonneg (primeWeight_nonneg p) (abs_nonneg _)
  · exact le_rfl

/-- The exact lower endpoint includes the ceiling in outputPrefix. -/
lemma terminal_squarefree_prefix_identity {α : ℝ} (hα : 0 < α) (D N : ℕ) :
    terminalSquarefreePrimeSum α D N =
      primeSquarefreeSum α N-primeSquarefreeSum α (min N (outputPrefix α D)) := by
  classical
  have hf : (Ioc 0 N).filter (fun p => floorMul α p ≤ D) =
      Ioc 0 (min N (outputPrefix α D)) := by
    ext p
    simp only [mem_filter, mem_Ioc, le_min_iff, floorMul_le_iff_outputPrefix hα]
    tauto
  unfold terminalSquarefreePrimeSum primeSquarefreeSum
  rw [← hf, sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  by_cases hD : D < floorMul α p
  · simp [hD, not_le.mpr hD]
  · simp [hD, not_lt.mp hD]

lemma terminal_moebius_le_squarefree {t : ℝ} (ht : 0 ≤ t) (α : ℝ) (D N : ℕ) :
    |terminalMoebiusPrimeSum t α D N| ≤ damping t D*terminalSquarefreePrimeSum α D N := by
  unfold terminalMoebiusPrimeSum terminalSquarefreePrimeSum
  rw [mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p hp
  split_ifs with hD
  · rw [abs_mul, abs_mul, abs_of_nonneg (primeWeight_nonneg p),
      abs_of_pos (damping_pos t _)]
    have hd : damping t (floorMul α p) ≤ damping t D := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (monotone_log_natCast hD.le) (neg_nonpos.mpr ht)
    have hh := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (primeWeight_nonneg p) (abs_nonneg (moebius (floorMul α p) : ℝ)))
    nlinarith only [hh]
  · simp only [abs_zero, mul_zero, le_refl]

/-- The same prefix estimate controls every terminal interval. -/
lemma terminal_squarefree_error_of_prefix {α ε : ℝ} (hα : 0 < α) (N : ℕ)
    (hprefix : ∀ X : ℕ, X ≤ N →
      |primeSquarefreeSum α X-Chebyshev.psi X*(6/Real.pi^2)| ≤ ε) (D : ℕ) :
    |terminalSquarefreePrimeSum α D N-
      (6/Real.pi^2)*(Chebyshev.psi N-Chebyshev.psi (min N (outputPrefix α D) : ℕ))| ≤ 2*ε := by
  rw [terminal_squarefree_prefix_identity hα]
  have hN := hprefix N le_rfl
  have hK := hprefix (min N (outputPrefix α D)) (min_le_left _ _)
  have he : primeSquarefreeSum α N-primeSquarefreeSum α (min N (outputPrefix α D))-
      (6/Real.pi^2)*(Chebyshev.psi N-Chebyshev.psi (min N (outputPrefix α D) : ℕ)) =
      (primeSquarefreeSum α N-Chebyshev.psi N*(6/Real.pi^2))-
        (primeSquarefreeSum α (min N (outputPrefix α D))-
          Chebyshev.psi (min N (outputPrefix α D) : ℕ)*(6/Real.pi^2)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith only [hN, hK])

/-- At an actual common scale, all damping parameters and all terminal
cutoffs obey this bound. The main term is the prime mass in the exact
terminal interval, multiplied by the squarefree Euler factor. -/
theorem exists_terminal_moebius_squarefree_scale {α ε : ℝ} (hα : 1 < α)
    (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 0 < u ∧ ∀ D : ℕ, ∀ t : ℝ, 0 ≤ t →
      |terminalMoebiusPrimeSum t α D (u^6)| ≤ damping t D*
        ((6/Real.pi^2)*(Chebyshev.psi (u^6 : ℕ)-
          Chebyshev.psi (min (u^6) (outputPrefix α D) : ℕ))+ε*(u : ℝ)^6) := by
  obtain ⟨u, hBu, hu, hprefix⟩ := exists_forward_squarefree_prefix_scale hα hI
    (show 0 < ε/2 by positivity) B
  refine ⟨u, hBu, hu, ?_⟩
  intro D t ht
  have hs := terminal_squarefree_error_of_prefix (by linarith : 0 < α) (u^6) hprefix D
  have hh := (abs_le.mp hs).2
  apply (terminal_moebius_le_squarefree ht α D (u^6)).trans
  apply mul_le_mul_of_nonneg_left _ (damping_pos t D).le
  linarith only [hh]

/-- Taking absolute values does not produce an o(N) bound even with
GENUINE prime inputs. This does not preclude signed cancellation. -/
theorem not_tendsto_forward_squarefree_zero {α : ℝ} (hα : 1 < α) (hI : Irrational α) :
    ¬ Tendsto (fun N : ℕ => primeSquarefreeSum α N/(N : ℝ)) atTop (𝓝 0) := by
  intro hz
  let c : ℝ := 6/Real.pi^2
  have hc : 0 < c := by dsimp [c]; positivity [Real.pi_pos]
  obtain ⟨B, hB⟩ := eventually_atTop.mp ((tendsto_order.mp hz).2 (c/2) (by positivity))
  obtain ⟨u, hBu, hu, he⟩ := exists_forward_squarefree_mean hα hI
    (show 0 < c/4 by positivity) B
  have hBN : B ≤ u^6 := hBu.le.trans (Nat.le_self_pow (by decide) u)
  have hsmall := hB (u^6) hBN
  have hlarge := (abs_lt.mp he).1
  change -(c/4) < primeSquarefreeSum α (u^6)/(u : ℝ)^6-c at hlarge
  push_cast at hsmall
  linarith only [hsmall, hlarge, hc]

#print axioms terminal_squarefree_prefix_identity
#print axioms terminal_moebius_le_squarefree
#print axioms exists_terminal_moebius_squarefree_scale
#print axioms not_tendsto_forward_squarefree_zero
end Erdos972ForwardSquarefreeTerminalTail
