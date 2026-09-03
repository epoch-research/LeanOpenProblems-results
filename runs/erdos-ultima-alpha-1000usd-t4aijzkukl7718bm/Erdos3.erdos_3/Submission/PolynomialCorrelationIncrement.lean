import Submission.BohrLocalPolynomialPartition
import Submission.ProgressionCellMean
import Submission.AveragedPartialPartitionIncrement

/-! Density-preserving passage from normalized local polynomial correlation
to a proper progression. The structural correlation hypothesis is conditional;
no higher-order inverse theorem is asserted. -/
namespace Erdos3PolynomialCorrelationIncrement
open Finset Erdos3BohrLocalPolynomialPartition Erdos3HigherPartitionParameters
  Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
  Erdos3ProgressionCellMean Erdos3AveragedPartialPartitionIncrement Erdos3ZModBohrIndices
  Erdos3BohrCoarseProgressionPartition Erdos3FiniteBohr Erdos3RelativeStableBohr
  Erdos3FinitePartitionIncrement
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

noncomputable def polynomialPartitionLoss (rank p K n₀ s z : ℕ) : ℝ :=
  (((2*n₀+1)^(2*rank)*K*257^(2*rank) : ℕ) : ℝ)/(p : ℝ)+1/(z : ℝ)+(1/2 : ℝ)^s

def polynomialPartitionStride (k rank L n₀ s : ℕ) : ℕ :=
  higherPartitionStride k 1 L s*(2*n₀+1)^(2*rank)

/-- A density-preserving passage from local polynomial correlation to a proper
AP. Its error budget includes every coarse-boundary and fine-partition loss;
no phase-grid cell or unproved pointwise-to-average inference is used. -/
theorem polynomial_correlation_progression_increment
    (p k : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ)) {R : ℝ}
    (hR : 1/64 ≤ R) (hRmax : R ≤ 1/16) {z : ℕ} (hz : 0 < z)
    (hstable : RelativeStable C z R)
    (f : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0)
    (q : ZMod p → ZMod p → Additive Circle)
    (hpoly : ∀ a, IsLocallyPolynomial (bohr C (1/16) : Set (ZMod p)) k (q a))
    {r : ℝ} (hr : 0 < r)
    (hcorr : r ≤ 𝔼 a, ‖𝔼 x : bohr C R, (f (a+x) : ℂ)*conj (phase (q a x))‖^2)
    (K L n₀ s : ℕ) (hL : 0 < L) (hn₀ : 0 < n₀)
    (hK : higherPartitionThreshold k 1 L s ≤ K)
    (hmesh : 4*(K : ℝ)/(n₀ : ℝ) ≤ relativeWidth C z R)
    (hbudget : (1/2 : ℝ)^s+2*polynomialPartitionLoss C.card p K n₀ s z ≤ r/2) :
    ∃ a : ZMod p, ∃ d : ℕ, 0 < d ∧ d ≤ polynomialPartitionStride k C.card L n₀ s ∧
      (L-1)*d < p ∧ Function.Injective (fun j : Fin L ↦ a+j.val • (d : ZMod p)) ∧
      r/16 ≤ 𝔼 j : Fin L, f (a+j.val • (d : ZMod p)) := by
  have hK0 : 0 < K := (higherPartitionThreshold_pos k 1 L s hL).trans_le hK
  let B := bohrIndices C R 0 1 p
  have hB : B.Nonempty := bohrIndices_nonempty p C (by linarith)
  letI : Nonempty B := hB.to_subtype
  letI : Nonempty (Fin K) := ⟨⟨0,hK0⟩⟩
  have hpart (a : ZMod p) :
      ∃ c : B → Option (Fin p × Fin K), ∃ w : (Fin p × Fin K) → ℂ,
        (∀ j, ‖w j‖ = 1) ∧ cellMass c none ≤ polynomialPartitionLoss C.card p K n₀ s z ∧
        (∀ x j, c x = some j → ‖phase (q a (x.val.val : ZMod p))-w j‖ ≤ (1/2 : ℝ)^s) ∧
        (∀ j, (cell c (some j)).Nonempty →
          ∃ b d : ℕ, 0 < d ∧ d ≤ polynomialPartitionStride k C.card L n₀ s ∧
            (∀ k < L, ∃ x : B, x.val.val = b+k*d) ∧
            ∀ x : B, c x = some j ↔ ∃ k : Fin L, x.val.val = b+k.val*d) := by
    obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := stable_bohr_polynomial_partition p C k
      (fun _ : Unit ↦ q a) hR hRmax (fun _ ↦ hpoly a) hz hstable
      K L n₀ s hL hn₀ (by simpa only [Fintype.card_unit] using hK) hmesh
    refine ⟨c,w (),hw (),?_,?_,?_⟩
    · simpa only [polynomialPartitionLoss,Fintype.card_unit] using hbad
    · intro x j hx
      exact hflat x j hx ()
    · simpa only [polynomialPartitionStride,Fintype.card_unit] using hgeom
  choose c w hw hbad hflat hgeom using hpart
  let F : ZMod p → B → ℝ := fun a x ↦ f (a+(x.val.val : ZMod p))
  have hF0 : (𝔼 a, 𝔼 x : B, F a x) = 0 := by
    rw [expect_comm]
    have he (x : B) : (𝔼 a, F a x) = 0 :=
      (Fintype.expect_equiv (Equiv.addRight (x.val.val : ZMod p)) _ f (fun _ ↦ rfl)).trans hf0
    simp only [he,Fintype.expect_const]
  have hcorr' : r ≤ 𝔼 a, ‖𝔼 x : B, (F a x : ℂ)*conj (phase (q a (x.val.val : ZMod p)))‖^2 := by
    have he (a : ZMod p) : (𝔼 x : B, (F a x : ℂ)*conj (phase (q a (x.val.val : ZMod p)))) =
        𝔼 x : bohr C R, (f (a+x) : ℂ)*conj (phase (q a x)) :=
      bohrIndices_expect p C R (fun x ↦ (f (a+x) : ℂ)*conj (phase (q a x)))
    simpa only [he] using hcorr
  have hε : 0 ≤ (1/2 : ℝ)^s := pow_nonneg (by norm_num) _
  obtain ⟨a,j,hcell,_,hinc⟩ := averaged_partial_partition_increment c F
    (fun a x ↦ conj (phase (q a (x.val.val : ZMod p)))) (fun a j ↦ conj (w a j))
    (fun a x ↦ hf _) hF0
    (fun a x ↦ by rw [Complex.norm_conj,phase_norm])
    (fun a j ↦ by rw [Complex.norm_conj,hw]) hr hε hbudget
    (expect_le univ_nonempty (fun a _ ↦ hbad a))
    (fun a x j hx ↦ by simpa only [← map_sub,Complex.norm_conj] using hflat a x j hx) hcorr'
  obtain ⟨b,d,hd,hdb,hpoints,hfiber⟩ := hgeom a j hcell
  have hmean : r/16 ≤ 𝔼 k : Fin L, f (a+((b+k.val*d : ℕ) : ZMod p)) := by
    have he := progressionCell_mean B (c a) j b d hd hpoints hfiber (fun v ↦ f (a+(v : ZMod p)))
    exact hinc.trans_eq he
  have hbelow : ∀ k < L, b+k*d < p := by
    intro k hk
    obtain ⟨x,hx⟩ := hpoints k hk
    rw [← hx]
    exact x.val.isLt
  have hproper := shifted_nat_AP_injective p L b d hd hbelow a
  have hspan : (L-1)*d < p := by
    have hh := hbelow (L-1) (by omega)
    omega
  refine ⟨a+(b : ZMod p),d,hd,hdb,hspan,?_,?_⟩
  · simpa only [Nat.cast_add,Nat.cast_mul,nsmul_eq_mul,add_assoc] using hproper
  · simpa only [Nat.cast_add,Nat.cast_mul,nsmul_eq_mul,add_assoc] using hmean


#print axioms polynomial_correlation_progression_increment
end Erdos3PolynomialCorrelationIncrement
