import Submission.EfficientBohrPolynomialPartition
import Submission.ProgressionCellMean
import Submission.AveragedPartialPartitionIncrement

/-! Bounded Lipschitz functions of several local polynomial phases yield a
progression density increment from averaged correlation. This does not assert
an inverse theorem producing the polynomial factor. -/
namespace Erdos3PolynomialFactorCorrelationIncrement
open Finset Erdos3EfficientBohrPolynomialPartition Erdos3EfficientPolynomialPartition
  Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
  Erdos3ProgressionCellMean Erdos3AveragedPartialPartitionIncrement Erdos3ZModBohrIndices
  Erdos3BohrCoarseProgressionPartition Erdos3FiniteBohr Erdos3RelativeStableBohr
  Erdos3FinitePartitionIncrement
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

noncomputable def factorPartitionLoss (rank p K n₀ s z : ℕ) : ℝ :=
  (((2*n₀+1)^(2*rank)*K*257^(2*rank) : ℕ):ℝ)/(p:ℝ)+1/(z:ℝ)+(1/2:ℝ)^s

def factorPartitionStride (k m rank L n₀ s : ℕ) : ℕ :=
  efficientStride k m L s*(2*n₀+1)^(2*rank)

lemma lipschitz_tuple_error {I : Type*} [Fintype I] {A : NNReal}
    (Φ : (I → ℂ) → ℂ) (hΦ : LipschitzWith A Φ) {v w : I → ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (hclose : ∀ i, ‖v i-w i‖ ≤ ε) : ‖Φ v-Φ w‖ ≤ (A:ℝ)*ε := by
  have hh : ‖v-w‖ ≤ ε := (pi_norm_le_iff_of_nonneg hε).mpr hclose
  exact (hΦ.norm_sub_le v w).trans (mul_le_mul_of_nonneg_left hh A.coe_nonneg)

/-- Averaged correlation with a supplied Lipschitz polynomial factor produces
a positive increment on an actual proper progression. -/
theorem polynomial_factor_progression_increment {I : Type*} [Fintype I]
    (p k : ℕ) [NeZero p] (C : Finset (AddChar (ZMod p) ℂ)) {R : ℝ}
    (hR : 1/64 ≤ R) (hRmax : R ≤ 1/16) {z : ℕ} (hz : 0 < z)
    (hstable : RelativeStable C z R)
    (f : ZMod p → ℝ) (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0)
    (q : ZMod p → I → ZMod p → Additive Circle)
    (hpoly : ∀ a i, IsLocallyPolynomial (bohr C (1/16) : Set (ZMod p)) k (q a i))
    (Φ : ZMod p → (I → ℂ) → ℂ) (A : NNReal)
    (hΦlip : ∀ a, LipschitzWith A (Φ a))
    (hΦbound : ∀ a v, (∀ i, ‖v i‖ = 1) → ‖Φ a v‖ ≤ 1)
    {r : ℝ} (hr : 0 < r)
    (hcorr : r ≤ 𝔼 a, ‖𝔼 x : bohr C R, (f (a+x):ℂ)*conj (Φ a (fun i ↦ phase (q a i x)))‖^2)
    (K L n₀ s : ℕ) (hL : 0 < L) (hn₀ : 0 < n₀)
    (hK : efficientThreshold k (Fintype.card I) L s ≤ K)
    (hmesh : 4*(K:ℝ)/(n₀:ℝ) ≤ relativeWidth C z R)
    (hbudget : (A:ℝ)*(1/2:ℝ)^s+2*factorPartitionLoss C.card p K n₀ s z ≤ r/2) :
    ∃ a : ZMod p, ∃ d : ℕ, 0 < d ∧ d ≤ factorPartitionStride k (Fintype.card I) C.card L n₀ s ∧
      (L-1)*d < p ∧ Function.Injective (fun j : Fin L ↦ a+j.val • (d:ZMod p)) ∧
      r/16 ≤ 𝔼 j : Fin L, f (a+j.val • (d:ZMod p)) := by
  have hK0 : 0 < K := (efficientThreshold_pos k (Fintype.card I) L s hL).trans_le hK
  let B := bohrIndices C R 0 1 p
  have hB : B.Nonempty := bohrIndices_nonempty p C (by linarith)
  letI : Nonempty B := hB.to_subtype
  letI : Nonempty (Fin K) := ⟨⟨0,hK0⟩⟩
  have hpart (a : ZMod p) :
      ∃ c : B → Option (Fin p × Fin K), ∃ w : I → (Fin p × Fin K) → ℂ,
        (∀ i j, ‖w i j‖ = 1) ∧ cellMass c none ≤ factorPartitionLoss C.card p K n₀ s z ∧
        (∀ x j, c x = some j → ∀ i, ‖phase (q a i (x.val.val:ZMod p))-w i j‖ ≤ (1/2:ℝ)^s) ∧
        (∀ j, (cell c (some j)).Nonempty →
          ∃ b d : ℕ, 0 < d ∧ d ≤ factorPartitionStride k (Fintype.card I) C.card L n₀ s ∧
            (∀ n < L, ∃ x : B, x.val.val = b+n*d) ∧
            ∀ x : B, c x = some j ↔ ∃ n : Fin L, x.val.val = b+n.val*d) := by
    exact efficient_stable_bohr_partition p C k (q a) hR hRmax (hpoly a) hz hstable
      K L n₀ s hL hn₀ hK hmesh
  choose c w hw hbad hflat hgeom using hpart
  let F : ZMod p → B → ℝ := fun a x ↦ f (a+(x.val.val:ZMod p))
  let Q : ZMod p → B → ℂ := fun a x ↦ conj (Φ a (fun i ↦ phase (q a i (x.val.val:ZMod p))))
  let W : ZMod p → (Fin p × Fin K) → ℂ := fun a j ↦ conj (Φ a (fun i ↦ w a i j))
  have hF0 : (𝔼 a, 𝔼 x : B, F a x) = 0 := by
    rw [expect_comm]
    have he (x : B) : (𝔼 a, F a x) = 0 :=
      (Fintype.expect_equiv (Equiv.addRight (x.val.val:ZMod p)) _ f (fun _ ↦ rfl)).trans hf0
    simp only [he,Fintype.expect_const]
  have hQ (a : ZMod p) (x : B) : ‖Q a x‖ ≤ 1 := by
    dsimp only [Q]
    rw [Complex.norm_conj]
    exact hΦbound a _ (fun i ↦ phase_norm _)
  have hW (a : ZMod p) (j : Fin p × Fin K) : ‖W a j‖ ≤ 1 := by
    dsimp only [W]
    rw [Complex.norm_conj]
    exact hΦbound a _ (fun i ↦ hw a i j)
  have happrox (a : ZMod p) (x : B) (j : Fin p × Fin K) (hx : c a x = some j) :
      ‖Q a x-W a j‖ ≤ (A:ℝ)*(1/2:ℝ)^s := by
    dsimp only [Q,W]
    rw [← map_sub,Complex.norm_conj]
    exact lipschitz_tuple_error (Φ a) (hΦlip a) (by positivity) (hflat a x j hx)
  have hcorr' : r ≤ 𝔼 a, ‖𝔼 x : B, (F a x:ℂ)*Q a x‖^2 := by
    have he (a : ZMod p) : (𝔼 x : B, (F a x:ℂ)*Q a x) =
        𝔼 x : bohr C R, (f (a+x):ℂ)*conj (Φ a (fun i ↦ phase (q a i x))) :=
      bohrIndices_expect p C R (fun x ↦ (f (a+x):ℂ)*conj (Φ a (fun i ↦ phase (q a i x))))
    simpa only [he] using hcorr
  obtain ⟨a,j,hcell,_,hinc⟩ := averaged_partial_partition_increment c F Q W
    (fun a x ↦ hf _) hF0 hQ hW hr (by positivity) hbudget
    (expect_le univ_nonempty (fun a _ ↦ hbad a)) happrox hcorr'
  obtain ⟨b,d,hd,hdb,hpoints,hfiber⟩ := hgeom a j hcell
  have hmean : r/16 ≤ 𝔼 n : Fin L, f (a+((b+n.val*d:ℕ):ZMod p)) := by
    have he := progressionCell_mean B (c a) j b d hd hpoints hfiber (fun v ↦ f (a+(v:ZMod p)))
    exact hinc.trans_eq he
  have hbelow : ∀ n < L, b+n*d < p := by
    intro n hn
    obtain ⟨x,hx⟩ := hpoints n hn
    rw [← hx]
    exact x.val.isLt
  have hproper := shifted_nat_AP_injective p L b d hd hbelow a
  have hspan : (L-1)*d < p := by
    have hh := hbelow (L-1) (by omega)
    omega
  refine ⟨a+(b:ZMod p),d,hd,hdb,hspan,?_,?_⟩
  · simpa only [Nat.cast_add,Nat.cast_mul,nsmul_eq_mul,add_assoc] using hproper
  · simpa only [Nat.cast_add,Nat.cast_mul,nsmul_eq_mul,add_assoc] using hmean

#print axioms polynomial_factor_progression_increment
end Erdos3PolynomialFactorCorrelationIncrement
