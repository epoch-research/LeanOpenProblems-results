import Submission.PolynomialCorrelationIncrement
import Submission.HigherPartitionPowerBounds

/-! Non-circular parameters for the conditional higher-degree progression
increment. The modulus threshold is polynomial in the requested length. -/
namespace Erdos3PolynomialIncrementParameters
open Finset Erdos3PolynomialCorrelationIncrement Erdos3HigherPartitionParameters
  Erdos3HigherPartitionPowerBounds Erdos3PolynomialProgressionThresholds
  Erdos3ProgressionIncrementParameters Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

noncomputable def polynomialAccuracy (r : ℝ) : ℕ := Nat.clog 2 (incrementPrecision r)
noncomputable def polynomialCoarseLength (k L : ℕ) (r : ℝ) : ℕ :=
  higherPartitionThreshold k 1 L (polynomialAccuracy r)
noncomputable def polynomialCoarseMesh (k D L : ℕ) (r : ℝ) : ℕ :=
  256*polynomialCoarseLength k L r*windowDenominator D (incrementPrecision r)+1
noncomputable def polynomialTerminalCost (k D L : ℕ) (r : ℝ) : ℕ :=
  (2*polynomialCoarseMesh k D L r+1)^(2*D)*polynomialCoarseLength k L r*257^(2*D)
noncomputable def polynomialIncrementThreshold (k D L : ℕ) (r : ℝ) : ℕ :=
  roundedScale (polynomialTerminalCost k D L r : ℝ) r
noncomputable def polynomialIncrementStride (k D L : ℕ) (r : ℝ) : ℕ :=
  higherPartitionStride k 1 L (polynomialAccuracy r)*(2*polynomialCoarseMesh k D L r+1)^(2*D)

lemma polynomialCoarseLength_pos (k L : ℕ) (r : ℝ) (hL : 0 < L) :
    0 < polynomialCoarseLength k L r := higherPartitionThreshold_pos k 1 L _ hL
lemma polynomialCoarseMesh_pos (k D L : ℕ) (r : ℝ) :
    0 < polynomialCoarseMesh k D L r := Nat.succ_pos _
lemma polynomialAccuracy_error {r : ℝ} (hr : 0 < r) :
    (1/2 : ℝ)^(polynomialAccuracy r) ≤ r/64 :=
  (inverse_power_clog (incrementPrecision_pos r)).trans (roundedScale_ratio 1 hr)

lemma polynomial_bohr_mesh {G : Type*} [AddCommGroup G] [Fintype G]
    (C : Finset (AddChar G ℂ)) {D : ℕ} (hC : C.card ≤ D) (k L : ℕ) (r : ℝ)
    {R : ℝ} (hR : 1/64 ≤ R) :
    4*(polynomialCoarseLength k L r : ℝ)/(polynomialCoarseMesh k D L r : ℝ) ≤
      relativeWidth C (incrementPrecision r) R := by
  let W := windowDenominator D (incrementPrecision r)
  let W' := windowDenominator C.card (incrementPrecision r)
  have hW : (0 : ℝ) < W := by exact_mod_cast windowDenominator_pos D (incrementPrecision_pos r)
  have hW' : (0 : ℝ) < W' := by exact_mod_cast windowDenominator_pos C.card (incrementPrecision_pos r)
  have hWW : (W' : ℝ) ≤ W := by exact_mod_cast windowDenominator_mono hC
  have hn : (0 : ℝ) < polynomialCoarseMesh k D L r := by exact_mod_cast polynomialCoarseMesh_pos k D L r
  have hmesh : 4*(polynomialCoarseLength k L r : ℝ)/(polynomialCoarseMesh k D L r : ℝ) ≤ (1/64 : ℝ)/(W : ℝ) := by
    apply (div_le_div_iff₀ hn hW).mpr
    have he : (polynomialCoarseMesh k D L r : ℝ) = 256*(polynomialCoarseLength k L r : ℝ)*(W : ℝ)+1 := by
      simp only [polynomialCoarseMesh,W,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    rw [he]
    nlinarith only []
  exact (hmesh.trans (div_le_div_of_nonneg_left (by norm_num) hW' hWW)).trans
    (div_le_div_of_nonneg_right hR hW'.le)

lemma polynomial_terminal_bound {d D p k L : ℕ} (hd : d ≤ D) {r : ℝ} (hr : 0 < r)
    (hp : polynomialIncrementThreshold k D L r ≤ p) :
    (((2*polynomialCoarseMesh k D L r+1)^(2*d)*polynomialCoarseLength k L r*257^(2*d) : ℕ) : ℝ)/(p : ℝ) ≤ r/64 := by
  have hcost : (2*polynomialCoarseMesh k D L r+1)^(2*d)*polynomialCoarseLength k L r*257^(2*d) ≤
      polynomialTerminalCost k D L r := by
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.mul_le_mul_left 2 hd))
    · exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 hd)
  have hth : (0 : ℝ) < polynomialIncrementThreshold k D L r := by exact_mod_cast roundedScale_pos (polynomialTerminalCost k D L r : ℝ) r
  calc
    _ ≤ (polynomialTerminalCost k D L r : ℝ)/(p : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcost) (Nat.cast_nonneg p)
    _ ≤ (polynomialTerminalCost k D L r : ℝ)/(polynomialIncrementThreshold k D L r : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hth (by exact_mod_cast hp)
    _ ≤ _ := roundedScale_ratio _ hr

lemma polynomial_partition_budget {d D p k L : ℕ} (hd : d ≤ D) {r : ℝ} (hr : 0 < r)
    (hp : polynomialIncrementThreshold k D L r ≤ p) :
    (1/2 : ℝ)^(polynomialAccuracy r)+2*polynomialPartitionLoss d p
      (polynomialCoarseLength k L r) (polynomialCoarseMesh k D L r)
      (polynomialAccuracy r) (incrementPrecision r) ≤ r/2 := by
  have he := polynomialAccuracy_error hr
  have ht := polynomial_terminal_bound hd hr hp
  have hz := roundedScale_ratio 1 hr
  change 1/(incrementPrecision r : ℝ) ≤ r/64 at hz
  unfold polynomialPartitionLoss
  linarith only [he,ht,hz,hr]

/-- Conditional higher-degree density increment on a proper progression.
The required local polynomial correlation is an explicit hypothesis. -/
theorem polynomial_correlation_increment_explicit
    (p k D L : ℕ) [NeZero p] (hL : 0 < L) {r : ℝ} (hr : 0 < r)
    (hp : polynomialIncrementThreshold k D L r ≤ p)
    (C : Finset (AddChar (ZMod p) ℂ)) (hC : C.card ≤ D) {R : ℝ}
    (hR : 1/64 ≤ R) (hRmax : R ≤ 1/16)
    (hstable : RelativeStable C (incrementPrecision r) R)
    (f : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0)
    (q : ZMod p → ZMod p → Additive Circle)
    (hpoly : ∀ a, IsLocallyPolynomial (bohr C (1/16) : Set (ZMod p)) k (q a))
    (hcorr : r ≤ 𝔼 a, ‖𝔼 x : bohr C R, (f (a+x) : ℂ)*conj (phase (q a x))‖^2) :
    ∃ a : ZMod p, ∃ d : ℕ, 0 < d ∧ d ≤ polynomialIncrementStride k D L r ∧
      (L-1)*d < p ∧ Function.Injective (fun j : Fin L ↦ a+j.val • (d : ZMod p)) ∧
      r/16 ≤ 𝔼 j : Fin L, f (a+j.val • (d : ZMod p)) := by
  obtain ⟨a,d,hd,hdb,hspan,hproper,hmean⟩ := polynomial_correlation_progression_increment
    p k C hR hRmax (incrementPrecision_pos r) hstable f hf hf0 q hpoly hr hcorr
    (polynomialCoarseLength k L r) L (polynomialCoarseMesh k D L r) (polynomialAccuracy r)
    hL (polynomialCoarseMesh_pos k D L r) (le_refl _)
    (polynomial_bohr_mesh C hC k L r hR) (polynomial_partition_budget hC hr hp)
  refine ⟨a,d,hd,?_,hspan,hproper,hmean⟩
  apply hdb.trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.mul_le_mul_left 2 hC))

/-- At fixed degree, rank and gain, the full conditional increment threshold
has polynomial dependence on the target length, with an explicit degree. -/
theorem polynomialIncrementThreshold_poly (k D : ℕ) (r : ℝ) :
    HasPolyBound (fun L ↦ polynomialIncrementThreshold k D L r)
      (higherPartitionDegree k 1*(2*D+1)) := by
  have hK : HasPolyBound (fun L ↦ polynomialCoarseLength k L r) (higherPartitionDegree k 1) :=
    (higher_partition_costs_poly k 1 (polynomialAccuracy r)).1
  have hn : HasPolyBound (fun L ↦ polynomialCoarseMesh k D L r) (higherPartitionDegree k 1) := by
    apply (hK.affine (256*windowDenominator D (incrementPrecision r)) 1).congr
    intro L
    unfold polynomialCoarseMesh
    ring
  have hT := (((hn.affine 2 1).pow (2*D)).mul hK).affine (257^(2*D)) 0
  have hT' : HasPolyBound (fun L ↦ polynomialTerminalCost k D L r)
      (higherPartitionDegree k 1*(2*D+1)) := by
    rw [Nat.mul_add,Nat.mul_one]
    apply hT.congr
    intro L
    unfold polynomialTerminalCost
    ring
  exact hT'.rounded r

#print axioms polynomial_correlation_increment_explicit
#print axioms polynomialIncrementThreshold_poly
end Erdos3PolynomialIncrementParameters
