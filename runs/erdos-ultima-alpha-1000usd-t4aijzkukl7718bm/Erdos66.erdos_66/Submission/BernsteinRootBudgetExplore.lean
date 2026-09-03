import Submission.BernsteinColorEnergyExplore
import Submission.FixedTranslateColorRootExplore

/-! Variance-sensitive finite coarse-target costs in the root-count transfer.
Every fine-field target is controlled without a union bound over that field. -/
namespace Erdos66BernsteinRootBudget
open Erdos66UniformColorMoments Erdos66CenteredColorSelection Erdos66OrderedColorEnergy
  Erdos66BernsteinColorEnergy Erdos66FiniteLabelRootTransfer Erdos66FixedTranslateColorRoot
open scoped Classical
set_option maxHeartbeats 3000000
variable {α κ : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

/-- Simultaneous signed and unsigned centered energies. The same coloring is
used throughout, and every target keeps its own centered-entry bound. -/
theorem exists_bernstein_joint_energy (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (S : Finset κ) (K : κ → α → α → ℝ)
    (hsym : ∀ k∈S, ∀ a b, K k a b=K k b a)
    (M : κ → ℝ) (hM : ∀ k∈S, 0<M k)
    (hK : ∀ k∈S, ∀ a b, |centeredKernel (K k) a b|≤M k) :
    ∃ ω : Fin h → α, ∀ k∈S,
      jointCenteredEnergy h f (K k) ω≤
        2*bernsteinEnergy h (2*S.card) (colorVariance (K k)) (M k) := by
  let T := S.product (Finset.univ : Finset (Fin 2))
  let g (j : κ×Fin 2) (i : Fin h) : ℝ := if j.2=0 then f i else 1
  have hT (j : κ×Fin 2) (hj : j∈T) : j.1∈S := (Finset.mem_product.mp hj).1
  have hg (j : κ×Fin 2) (hj : j∈T) (i : Fin h) : (g j i)^2=1 := by
    dsimp [g]
    split_ifs <;> simp [hf]
  have hcard : T.card=2*S.card := by simp [T,Finset.card_product,Nat.mul_comm]
  obtain ⟨ω,hω⟩ := exists_bernstein_centered_energy h T g hg
    (fun j ↦ K j.1) (fun j hj ↦ hsym j.1 (hT j hj))
    (fun j ↦ M j.1) (fun j hj ↦ hM j.1 (hT j hj))
    (fun j hj ↦ hK j.1 (hT j hj))
  refine ⟨ω,fun k hk ↦ ?_⟩
  have h0 := hω (k,0) (by simp [T,hk])
  have h1 := hω (k,1) (by simp [T,hk])
  simp only [g,if_true,hcard] at h0
  simp only [g,show (1:Fin 2)≠0 by decide,if_false,hcard] at h1
  change centeredSignedEnergy h f (K k) ω≤_ at h0
  change centeredSignedEnergy h (fun _ ↦ 1) (K k) ω≤_ at h1
  unfold jointCenteredEnergy
  linarith

variable {p : ℕ} [Fact p.Prime]

/-- The field translate is fixed before the finite coarse list. Only the
coloring depends on that list; the fine targets never enter its budget. -/
theorem exists_pattern_bernstein_root_budget (hp : p≠2) (h : ℕ) (hh : 4*h<p) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      ∀ (S : Finset κ) (K : κ → α → α → ℝ),
        (∀ k∈S, ∀ x y, K k x y=K k y x) →
        ∀ M : κ → ℝ, (∀ k∈S, 0<M k) →
        (∀ k∈S, ∀ x y, |centeredKernel (K k) x y|≤M k) →
        ∃ ω : Fin h → α, ∀ k∈S, ∀ t s : ZMod p,
          (labelRootCount h a (fun i j ↦ K k (ω i) (ω j)) t s-
            (h:ℝ)^2*kernelMean (K k))^2≤
          6*(h:ℝ)*(8*(kernelMean (K k))^2*(h:ℝ)^2+
            2*bernsteinEnergy h (2*S.card) (colorVariance (K k)) (M k)) := by
  obtain ⟨a,ha,hop,hE⟩ := exists_low_energy_pattern hp h hh
  refine ⟨a,ha,hop,fun S K hsym M hM hK ↦ ?_⟩
  obtain ⟨ω,hω⟩ := exists_bernstein_joint_energy h (signPattern h a) (signPattern_sq h a ha)
    S K hsym M hM hK
  refine ⟨ω,fun k hk t s ↦ (coloredRootCount_error_sq hp h a ha hop (K k) ω t s).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ (hω k hk)
  have he := mul_le_mul_of_nonneg_left hE (sq_nonneg (kernelMean (K k)))
  nlinarith only [he]

end Erdos66BernsteinRootBudget
