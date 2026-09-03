import Submission.ProgressionCellMean
import Submission.AveragedPartialPartitionIncrement

/-! Positive density increments on proper arithmetic progressions, directly
from averaged normalized local quadratic correlation on a stable Bohr set. -/
namespace Erdos3QuadraticCorrelationProgressionIncrement
open Finset Erdos3ProgressionCellMean Erdos3StableBohrQuadraticPartition
  Erdos3AveragedPartialPartitionIncrement Erdos3ZModBohrIndices
  Erdos3BohrCoarseProgressionPartition Erdos3FiniteBohr Erdos3RelativeStableBohr
  Erdos3LocalQuadraticInverse Erdos3SimultaneousQuadraticRecurrence Erdos3FinitePartitionIncrement
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

noncomputable def partitionError (M L n t : ℕ) : ℝ :=
  2*(M : ℝ)^2*(1/2 : ℝ)^t+2*(L : ℝ)/(n : ℝ)
noncomputable def partitionLoss (rank p K M L n n₀ t z : ℕ) : ℝ :=
  (((2*n₀+1)^(2*rank)*K*257^(2*rank) : ℕ) : ℝ)/(p : ℝ)+1/(z : ℝ)+
    ((recurrenceBound 1 t : ℝ)*(M : ℝ)/(K : ℝ)+((2*n+1)^2 : ℕ)*(L : ℝ)/(M : ℝ))
noncomputable def partitionStride (rank n n₀ t : ℕ) : ℕ :=
  (recurrenceBound 1 t*(2*n+1)^2)*(2*n₀+1)^(2*rank)

/-- A density-preserving passage from local quadratic correlation to a proper
AP. Its error budget includes every coarse-boundary and fine-partition loss;
no phase-grid cell or unproved pointwise-to-average inference is used. -/
theorem quadratic_correlation_progression_increment_with_span
    (p : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ)) {R : ℝ}
    (hR : 1/64 ≤ R) (hRmax : R ≤ 1/16) {z : ℕ} (hz : 0 < z)
    (hstable : RelativeStable C z R)
    (f : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0)
    (q : ZMod p → ZMod p → ℂ) (hq : ∀ a x, ‖q a x‖ = 1)
    (hquad : ∀ a, IsLocallyQuadratic (bohr C (1/16) : Set (ZMod p)) (q a))
    {r : ℝ} (hr : 0 < r)
    (hcorr : r ≤ 𝔼 a, ‖𝔼 x : bohr C R, (f (a+x) : ℂ)*conj (q a x)‖^2)
    (K M L n n₀ t : ℕ) (hK : 0 < K) (hM : 0 < M) (hL : 0 < L) (hn : 0 < n) (hn₀ : 0 < n₀)
    (hmesh : 4*(K : ℝ)/(n₀ : ℝ) ≤ relativeWidth C z R)
    (hbudget : partitionError M L n t+2*partitionLoss C.card p K M L n n₀ t z ≤ r/2) :
    ∃ a : ZMod p, ∃ d : ℕ, 0 < d ∧ d ≤ partitionStride C.card n n₀ t ∧
      (L-1)*d < p ∧ Function.Injective (fun j : Fin L ↦ a+j.val • (d : ZMod p)) ∧
      r/16 ≤ 𝔼 j : Fin L, f (a+j.val • (d : ZMod p)) := by
  let B := bohrIndices C R 0 1 p
  have hB : B.Nonempty := bohrIndices_nonempty p C (by linarith)
  letI : Nonempty B := hB.to_subtype
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  have hpart (a : ZMod p) :
      ∃ c : B → Option (Fin p × (Fin K × Fin M)), ∃ w : (Fin p × (Fin K × Fin M)) → ℂ,
        (∀ j, ‖w j‖ = 1) ∧ cellMass c none ≤ partitionLoss C.card p K M L n n₀ t z ∧
        (∀ x j, c x = some j → ‖q a (x.val.val : ZMod p)-w j‖ ≤ partitionError M L n t) ∧
        (∀ j, (cell c (some j)).Nonempty →
          ∃ b d : ℕ, 0 < d ∧ d ≤ partitionStride C.card n n₀ t ∧
            (∀ k < L, ∃ x : B, x.val.val = b+k*d) ∧
            ∀ x : B, c x = some j ↔ ∃ k : Fin L, x.val.val = b+k.val*d) := by
    obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := stable_bohr_quadratic_partition p C
      (fun _ : Unit ↦ q a) (fun _ x ↦ hq a x) hR hRmax (fun _ ↦ hquad a) hz hstable
      K M L n n₀ t hK hM hL hn hn₀ hmesh
    refine ⟨c,w (),hw (),?_,?_,?_⟩
    · simpa only [partitionLoss,Fintype.card_unit,Nat.mul_one] using hbad
    · intro x j hx
      exact hflat x j hx ()
    · simpa only [partitionStride,Fintype.card_unit,Nat.mul_one] using hgeom
  choose c w hw hbad hflat hgeom using hpart
  let F : ZMod p → B → ℝ := fun a x ↦ f (a+(x.val.val : ZMod p))
  have hF0 : (𝔼 a, 𝔼 x : B, F a x) = 0 := by
    rw [expect_comm]
    have he (x : B) : (𝔼 a, F a x) = 0 :=
      (Fintype.expect_equiv (Equiv.addRight (x.val.val : ZMod p)) _ f (fun _ ↦ rfl)).trans hf0
    simp only [he,Fintype.expect_const]
  have hcorr' : r ≤ 𝔼 a, ‖𝔼 x : B, (F a x : ℂ)*conj (q a (x.val.val : ZMod p))‖^2 := by
    have he (a : ZMod p) : (𝔼 x : B, (F a x : ℂ)*conj (q a (x.val.val : ZMod p))) =
        𝔼 x : bohr C R, (f (a+x) : ℂ)*conj (q a x) :=
      bohrIndices_expect p C R (fun x ↦ (f (a+x) : ℂ)*conj (q a x))
    simpa only [he] using hcorr
  have hε : 0 ≤ partitionError M L n t := by unfold partitionError; positivity
  obtain ⟨a,j,hcell,_,hinc⟩ := averaged_partial_partition_increment c F
    (fun a x ↦ conj (q a (x.val.val : ZMod p))) (fun a j ↦ conj (w a j))
    (fun a x ↦ hf _) hF0
    (fun a x ↦ by rw [Complex.norm_conj,hq])
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

theorem quadratic_correlation_progression_increment
    (p : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ)) {R : ℝ}
    (hR : 1/64 ≤ R) (hRmax : R ≤ 1/16) {z : ℕ} (hz : 0 < z)
    (hstable : RelativeStable C z R)
    (f : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0)
    (q : ZMod p → ZMod p → ℂ) (hq : ∀ a x, ‖q a x‖ = 1)
    (hquad : ∀ a, IsLocallyQuadratic (bohr C (1/16) : Set (ZMod p)) (q a))
    {r : ℝ} (hr : 0 < r)
    (hcorr : r ≤ 𝔼 a, ‖𝔼 x : bohr C R, (f (a+x) : ℂ)*conj (q a x)‖^2)
    (K M L n n₀ t : ℕ) (hK : 0 < K) (hM : 0 < M) (hL : 0 < L) (hn : 0 < n) (hn₀ : 0 < n₀)
    (hmesh : 4*(K : ℝ)/(n₀ : ℝ) ≤ relativeWidth C z R)
    (hbudget : partitionError M L n t+2*partitionLoss C.card p K M L n n₀ t z ≤ r/2) :
    ∃ a : ZMod p, ∃ d : ℕ, 0 < d ∧ d ≤ partitionStride C.card n n₀ t ∧
      Function.Injective (fun j : Fin L ↦ a+j.val • (d : ZMod p)) ∧
      r/16 ≤ 𝔼 j : Fin L, f (a+j.val • (d : ZMod p)) := by
  obtain ⟨a,d,hd,hbound,_,hproper,hmean⟩ := quadratic_correlation_progression_increment_with_span
    p C hR hRmax hz hstable f hf hf0 q hq hquad hr hcorr K M L n n₀ t
    hK hM hL hn hn₀ hmesh hbudget
  exact ⟨a,d,hd,hbound,hproper,hmean⟩

#print axioms quadratic_correlation_progression_increment_with_span
#print axioms quadratic_correlation_progression_increment
end Erdos3QuadraticCorrelationProgressionIncrement
