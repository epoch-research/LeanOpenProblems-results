import Submission.StructuredHostExplore
import Submission.CentralEndpointResetExplore
import Submission.JointLogarithmicClippingExplore

/-! A structured host admits two-sided logarithmic resets, with constant
collateral on polynomial horizons. This theorem concerns ONE reset only. -/
namespace Erdos66HostLogarithmicReset
open Filter AdditiveCombinatorics Erdos66StructuredHost Erdos66HostPatternMean
  Erdos66JointBoundaryTripleCounts Erdos66CentralEndpointReset
  Erdos66BoundaryPairCounts Erdos66CentralTripleDeletion Erdos66CentralTripleCounts
  Erdos66JointLogarithmicClipping Erdos66BoundaryLogarithmicClipping
  Erdos66Rounding Erdos66PowerExceptionalProfile Erdos66TripleIntersectionMean
open scoped Classical Topology
set_option maxHeartbeats 2200000

lemma eventually_host_reset_range (A : Set ℕ) (NB : ℕ → ℕ)
    (hboundary : ∀ j n, NB j ≤ n → ((j:ℝ)+1)*((boundary A (hostCutoff j) n).card:ℝ) ≤
      20*Real.log ((n:ℝ)+1))
    (hlower : ∀ᶠ n : ℕ in atTop, 448*Real.log (n:ℝ) ≤ (sumRep A n:ℝ)) :
    ∃ j : ℕ, ∀ᶠ n : ℕ in atTop,
      2*(boundary A (hostCutoff j) n).card+2 ≤ ⌊Real.log (n:ℝ)⌋₊ ∧
      ⌊Real.log (n:ℝ)⌋₊+2*(boundary A (hostCutoff j) n).card+1 ≤ sumRep A n := by
  let j : ℕ := 240
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨j,?_⟩
  filter_upwards [hlower,eventually_ge_atTop (NB j),eventually_ge_atTop 1,
    hlog.eventually_ge_atTop 4] with n hn hN hn1 hlog4
  have hlog0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hb := hboundary j n hN
  have hell := ell_le_three_log hn1 (by linarith : 1 ≤ Real.log (n:ℝ))
  dsimp only [ell] at hell
  have hsmall : 2*((boundary A (hostCutoff j) n).card:ℝ) ≤ Real.log (n:ℝ)/2 := by
    norm_num only [j,Nat.cast_ofNat] at hb
    linarith
  have hlo : 2*(boundary A (hostCutoff j) n).card+2 ≤ ⌊Real.log (n:ℝ)⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  refine ⟨hlo,?_⟩
  have hf := Nat.floor_le hlog0
  have hh : (⌊Real.log (n:ℝ)⌋₊:ℝ)+2*((boundary A (hostCutoff j) n).card:ℝ)+1 ≤ (sumRep A n:ℝ) := by
    linarith
  exact_mod_cast hh

 theorem exists_host_logarithmic_resets : ∃ A : Set ℕ, ∀ g : ℕ, ∃ d N₀ : ℕ, 2 ≤ d ∧
    ∀ n≥N₀, ∀ B : Set ℕ, B ⊆ A → ∃ C : Set ℕ,
      C ⊆ A ∧
      (∀ a, a∉endpoints A (n/d^2) n → (a∈B ↔ a∈C)) ∧
      ⌊Real.log (n:ℝ)⌋₊-1 ≤ sumRep C n ∧ sumRep C n ≤ ⌊Real.log (n:ℝ)⌋₊ ∧
      ∀ z, z ≤ n^g → n≠z → |(sumRep C z:ℝ)-sumRep B z| ≤ 2*(tripleCap (g+1):ℝ) := by
  obtain ⟨A,p,NB,NT,hp,hconv,hbr,hcost,hboundary,htriple,henv⟩ := exists_structured_host
  obtain ⟨j,hj⟩ := eventually_host_reset_range A NB hboundary (henv.mono fun _ h ↦ h.1)
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hj
  refine ⟨A,?_⟩
  intro g
  let d := hostCutoff j
  let K := 2*d^2
  let M := max (NT K (g+1)) (max (K^g) 1)
  let N₀ := max N₁ (d^2*M)
  have hd : 2 ≤ d := hostCutoff_ge_two j
  have hdpos : 0<d^2 := pow_pos (by omega) _
  refine ⟨d,N₀,hd,?_⟩
  intro n hn B hBA
  have hn' : max N₁ (d^2*M) ≤ n := hn
  have hscale : M ≤ n/d^2 := (Nat.le_div_iff_mul_le hdpos).mpr (by nlinarith only [le_max_right N₁ (d^2*M),hn'])
  have hNT : NT K (g+1) ≤ n/d^2 := (le_max_left _ _).trans hscale
  have hKG : K^g ≤ n/d^2 := (le_max_left _ _).trans ((le_max_right _ _).trans hscale)
  have h1 : 1 ≤ n/d^2 := (le_max_right _ _).trans ((le_max_right _ _).trans hscale)
  have hdn : d^2 ≤ n := by simpa using (Nat.le_div_iff_mul_le hdpos).mp h1
  have hcomp : n ≤ K*(n/d^2) := central_quotient_comparable d n (by omega) hdn
  obtain ⟨hlo,hhi⟩ := hN₁ n (by omega)
  obtain ⟨C,hCA,hagree,hlower,hupper,hchange⟩ := exists_central_reset A B d n ⌊Real.log (n:ℝ)⌋₊ hd hBA hlo hhi
  refine ⟨C,hCA,hagree,hlower,hupper,?_⟩
  intro z hz hnz
  have hzh : z ≤ (n/d^2)^(g+1) := hz.trans (polynomial_horizon K (n/d^2) n g hcomp hKG)
  have hcap := htriple K (g+1) (n/d^2) n z hNT hcomp hzh hnz
  have hcap' : ((fiber A (n/d^2) n z).card:ℝ) ≤ tripleCap (g+1) := by exact_mod_cast hcap
  exact (hchange z).trans (mul_le_mul_of_nonneg_left hcap' (by norm_num))

end Erdos66HostLogarithmicReset
