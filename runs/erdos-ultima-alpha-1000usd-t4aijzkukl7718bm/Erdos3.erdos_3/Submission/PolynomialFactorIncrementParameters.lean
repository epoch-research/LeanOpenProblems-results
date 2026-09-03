import Submission.PolynomialFactorCorrelationIncrement
import Submission.HigherPartitionPowerBounds

/-! Explicit non-circular thresholds for correlation with a Lipschitz polynomial
factor. The requested-length polynomial degree is polynomial in the phase count
and linear in the Bohr rank, for fixed polynomial degree. -/
namespace Erdos3PolynomialFactorIncrementParameters
open Finset Erdos3PolynomialFactorCorrelationIncrement Erdos3EfficientPolynomialPartition
  Erdos3HigherPartitionPowerBounds Erdos3PolynomialProgressionThresholds
  Erdos3ProgressionIncrementParameters Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

noncomputable def factorAccuracy (A : NNReal) (r : ℝ) : ℕ := Nat.clog 2 (roundedScale ((A:ℝ)+2) r)
noncomputable def factorCoarseLength (k m L : ℕ) (A : NNReal) (r : ℝ) : ℕ :=
  efficientThreshold k m L (factorAccuracy A r)
noncomputable def factorCoarseMesh (k m D L : ℕ) (A : NNReal) (r : ℝ) : ℕ :=
  256*factorCoarseLength k m L A r*windowDenominator D (incrementPrecision r)+1
noncomputable def factorTerminalCost (k m D L : ℕ) (A : NNReal) (r : ℝ) : ℕ :=
  (2*factorCoarseMesh k m D L A r+1)^(2*D)*factorCoarseLength k m L A r*257^(2*D)
noncomputable def factorIncrementThreshold (k m D L : ℕ) (A : NNReal) (r : ℝ) : ℕ :=
  roundedScale (factorTerminalCost k m D L A r:ℝ) r
noncomputable def factorIncrementStride (k m D L : ℕ) (A : NNReal) (r : ℝ) : ℕ :=
  efficientStride k m L (factorAccuracy A r)*(2*factorCoarseMesh k m D L A r+1)^(2*D)

lemma factorAccuracy_error (A : NNReal) {r : ℝ} (hr : 0 < r) :
    ((A:ℝ)+2)*(1/2:ℝ)^(factorAccuracy A r) ≤ r/64 := by
  calc
    _ ≤ ((A:ℝ)+2)*(1/(roundedScale ((A:ℝ)+2) r:ℝ)) :=
      mul_le_mul_of_nonneg_left (inverse_power_clog (roundedScale_pos _ _)) (by positivity)
    _ = ((A:ℝ)+2)/(roundedScale ((A:ℝ)+2) r:ℝ) := by ring
    _ ≤ _ := roundedScale_ratio _ hr

lemma factor_bohr_mesh {G : Type*} [AddCommGroup G] [Fintype G]
    (C : Finset (AddChar G ℂ)) {D : ℕ} (hC : C.card ≤ D) (k m L : ℕ) (A : NNReal) (r : ℝ)
    {R : ℝ} (hR : 1/64 ≤ R) :
    4*(factorCoarseLength k m L A r:ℝ)/(factorCoarseMesh k m D L A r:ℝ) ≤
      relativeWidth C (incrementPrecision r) R := by
  let W := windowDenominator D (incrementPrecision r)
  let W' := windowDenominator C.card (incrementPrecision r)
  have hW : (0:ℝ) < W := by exact_mod_cast windowDenominator_pos D (incrementPrecision_pos r)
  have hW' : (0:ℝ) < W' := by exact_mod_cast windowDenominator_pos C.card (incrementPrecision_pos r)
  have hWW : (W':ℝ) ≤ W := by exact_mod_cast windowDenominator_mono hC
  have hn : (0:ℝ) < factorCoarseMesh k m D L A r := by
    exact_mod_cast Nat.succ_pos (256*factorCoarseLength k m L A r*W)
  have hmesh : 4*(factorCoarseLength k m L A r:ℝ)/(factorCoarseMesh k m D L A r:ℝ) ≤ (1/64:ℝ)/(W:ℝ) := by
    apply (div_le_div_iff₀ hn hW).mpr
    have he : (factorCoarseMesh k m D L A r:ℝ) = 256*(factorCoarseLength k m L A r:ℝ)*(W:ℝ)+1 := by
      simp only [factorCoarseMesh,W,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    rw [he]
    nlinarith only []
  exact (hmesh.trans (div_le_div_of_nonneg_left (by norm_num) hW' hWW)).trans
    (div_le_div_of_nonneg_right hR hW'.le)

lemma factor_terminal_bound {d D p k m L : ℕ} (hd : d ≤ D) (A : NNReal) {r : ℝ} (hr : 0 < r)
    (hp : factorIncrementThreshold k m D L A r ≤ p) :
    (((2*factorCoarseMesh k m D L A r+1)^(2*d)*factorCoarseLength k m L A r*257^(2*d):ℕ):ℝ)/(p:ℝ) ≤ r/64 := by
  have hcost : (2*factorCoarseMesh k m D L A r+1)^(2*d)*factorCoarseLength k m L A r*257^(2*d) ≤
      factorTerminalCost k m D L A r := by
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.mul_le_mul_left 2 hd))
    · exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 hd)
  have hth : (0:ℝ) < factorIncrementThreshold k m D L A r := by exact_mod_cast roundedScale_pos _ _
  calc
    _ ≤ (factorTerminalCost k m D L A r:ℝ)/(p:ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcost) (Nat.cast_nonneg p)
    _ ≤ (factorTerminalCost k m D L A r:ℝ)/(factorIncrementThreshold k m D L A r:ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hth (by exact_mod_cast hp)
    _ ≤ _ := roundedScale_ratio _ hr

lemma factor_partition_budget {d D p k m L : ℕ} (hd : d ≤ D) (A : NNReal) {r : ℝ} (hr : 0 < r)
    (hp : factorIncrementThreshold k m D L A r ≤ p) :
    (A:ℝ)*(1/2:ℝ)^(factorAccuracy A r)+2*factorPartitionLoss d p
      (factorCoarseLength k m L A r) (factorCoarseMesh k m D L A r)
      (factorAccuracy A r) (incrementPrecision r) ≤ r/2 := by
  have he := factorAccuracy_error A hr
  have ht := factor_terminal_bound hd A hr hp
  have hz := roundedScale_ratio 1 hr
  change 1/(incrementPrecision r:ℝ) ≤ r/64 at hz
  unfold factorPartitionLoss
  nlinarith only [he,ht,hz,hr]

/-- Conditional polynomial-factor density increment with all parameters fixed
before choosing the Bohr set, phases, and correlating factor. -/
theorem polynomial_factor_increment_explicit {I : Type*} [Fintype I]
    (p k D L : ℕ) [NeZero p] (A : NNReal) (hL : 0 < L) {r : ℝ} (hr : 0 < r)
    (hp : factorIncrementThreshold k (Fintype.card I) D L A r ≤ p)
    (C : Finset (AddChar (ZMod p) ℂ)) (hC : C.card ≤ D) {R : ℝ}
    (hR : 1/64 ≤ R) (hRmax : R ≤ 1/16)
    (hstable : RelativeStable C (incrementPrecision r) R)
    (f : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0)
    (q : ZMod p → I → ZMod p → Additive Circle)
    (hpoly : ∀ a i, IsLocallyPolynomial (bohr C (1/16) : Set (ZMod p)) k (q a i))
    (Φ : ZMod p → (I → ℂ) → ℂ) (hΦlip : ∀ a, LipschitzWith A (Φ a))
    (hΦbound : ∀ a v, (∀ i, ‖v i‖ = 1) → ‖Φ a v‖ ≤ 1)
    (hcorr : r ≤ 𝔼 a, ‖𝔼 x : bohr C R, (f (a+x):ℂ)*conj (Φ a (fun i ↦ phase (q a i x)))‖^2) :
    ∃ a : ZMod p, ∃ d : ℕ, 0 < d ∧ d ≤ factorIncrementStride k (Fintype.card I) D L A r ∧
      (L-1)*d < p ∧ Function.Injective (fun j : Fin L ↦ a+j.val • (d:ZMod p)) ∧
      r/16 ≤ 𝔼 j : Fin L, f (a+j.val • (d:ZMod p)) := by
  obtain ⟨a,d,hd,hdb,hspan,hproper,hmean⟩ := polynomial_factor_progression_increment p k C hR hRmax
    (incrementPrecision_pos r) hstable f hf hf0 q hpoly Φ A hΦlip hΦbound hr hcorr
    (factorCoarseLength k (Fintype.card I) L A r) L (factorCoarseMesh k (Fintype.card I) D L A r)
    (factorAccuracy A r) hL (Nat.succ_pos _) le_rfl (factor_bohr_mesh C hC k _ L A r hR)
    (factor_partition_budget hC A hr hp)
  refine ⟨a,d,hd,hdb.trans ?_,hspan,hproper,hmean⟩
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.mul_le_mul_left 2 hC))

lemma efficientThreshold_poly (k m s : ℕ) :
    HasPolyBound (fun L ↦ efficientThreshold k m L s) (partitionCoefficient k*(m+1)^(5*k)) := by
  let E := partitionCoefficient k*(m+1)^(5*k)
  refine ⟨2^(E*(s+k+1)+E)+1,?_⟩
  intro L
  calc
    _ ≤ 2^(partitionLogBound k m L s)+1 := Nat.add_le_add_right (efficientThreshold_bound k m L s) 1
    _ = 2^(E*(s+k+1)+E*Nat.clog 2 L)+1 := by unfold partitionLogBound; dsimp only [E]; congr 2; ring
    _ ≤ _ := power_clog_bound (E*(s+k+1)) E L

/-- The requested-length degree is polynomial in phase count and linear in rank. -/
theorem factorIncrementThreshold_poly (k m D : ℕ) (A : NNReal) (r : ℝ) :
    HasPolyBound (fun L ↦ factorIncrementThreshold k m D L A r)
      (partitionCoefficient k*(m+1)^(5*k)*(2*D+1)) := by
  let E := partitionCoefficient k*(m+1)^(5*k)
  have hK : HasPolyBound (fun L ↦ factorCoarseLength k m L A r) E := efficientThreshold_poly k m _
  have hn : HasPolyBound (fun L ↦ factorCoarseMesh k m D L A r) E := by
    apply (hK.affine (256*windowDenominator D (incrementPrecision r)) 1).congr
    intro L
    unfold factorCoarseMesh
    ring
  have hT := (((hn.affine 2 1).pow (2*D)).mul hK).affine (257^(2*D)) 0
  have hT' : HasPolyBound (fun L ↦ factorTerminalCost k m D L A r) (E*(2*D+1)) := by
    rw [Nat.mul_add,Nat.mul_one]
    apply hT.congr
    intro L
    unfold factorTerminalCost
    ring
  exact hT'.rounded r

#print axioms polynomial_factor_increment_explicit
#print axioms factorIncrementThreshold_poly
end Erdos3PolynomialFactorIncrementParameters
