import Submission.FiniteLabelRootTransferExplore

/-! Coarse color assignments selected after an admissible field translate.
Both the signed fine error and the unsigned main term are controlled by
one finite potential. This is not an infinite-set construction. -/
namespace Erdos66FixedTranslateColorRoot
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66OrderedColorEnergy
  Erdos66CenteredColorSelection Erdos66FiniteLabelRootTransfer
open scoped Classical
set_option maxHeartbeats 2400000

variable {p : ℕ} [Fact p.Prime]
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

lemma labelRootCount_centered (h : ℕ) (a : ZMod p) (K : α → α → ℝ)
    (ω : Fin h → α) (t s : ZMod p) :
    labelRootCount h a (fun i j ↦ centeredKernel K (ω i) (ω j)) t s=
      labelRootCount h a (fun i j ↦ K (ω i) (ω j)) t s-
        kernelMean K*labelRootCount h a (fun _ _ ↦ 1) t s := by
  unfold labelRootCount centeredKernel
  simp only [sub_mul,Finset.sum_sub_distrib,one_mul,Finset.mul_sum]

/-- A deterministic bound, valid for any coloring. The kernel mean multiplies
only the fixed old-pattern energy; both centered errors use the joint energy. -/
theorem coloredRootCount_error_sq (hp : p≠2) (h : ℕ) (a : ZMod p)
    (ha : ∀ i<h, a+(i:ZMod p)≠0) (hop : ∀ q<2*h, 2*a+(q:ZMod p)≠0)
    (K : α → α → ℝ) (ω : Fin h → α) (t s : ZMod p) :
    (labelRootCount h a (fun i j ↦ K (ω i) (ω j)) t s-(h:ℝ)^2*kernelMean K)^2 ≤
      6*(h:ℝ)*((kernelMean K)^2*
        orderedEnergy h (fun i j ↦ signPattern h a i*signPattern h a j)+
        jointCenteredEnergy h (signPattern h a) K ω) := by
  let B := labelRootCount h a (fun _ _ ↦ (1:ℝ)) t s-(h:ℝ)^2
  let C := labelRootCount h a (fun i j ↦ centeredKernel K (ω i) (ω j)) t s
  let M := ∑ i : Fin h, ∑ j : Fin h, centeredKernel K (ω i) (ω j)
  have hbase : B^2 ≤ 2*(h:ℝ)*
      orderedEnergy h (fun i j ↦ signPattern h a i*signPattern h a j) := by
    have he := labelRootCount_error_sq hp h a ha hop (fun _ _ ↦ (1:ℝ)) t s
    simpa only [B,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      pow_two] using he
  have hC : (C-M)^2 ≤ 2*(h:ℝ)*centeredSignedEnergy h (signPattern h a) K ω :=
    labelRootCount_error_sq hp h a ha hop (fun i j ↦ centeredKernel K (ω i) (ω j)) t s
  have hM : M^2 ≤ 2*(h:ℝ)*centeredSignedEnergy h (fun _ ↦ 1) K ω := by
    simpa only [centeredSignedEnergy,one_mul] using matrixSum_sq_le_energy h
      (fun i j ↦ centeredKernel K (ω i) (ω j))
  have he : labelRootCount h a (fun i j ↦ K (ω i) (ω j)) t s-(h:ℝ)^2*kernelMean K=
      kernelMean K*B+(C-M)+M := by
    dsimp only [B,C]
    rw [labelRootCount_centered]
    ring
  rw [he]
  have hthree (x y z : ℝ) : (x+y+z)^2 ≤ 3*(x^2+y^2+z^2) := by
    nlinarith [sq_nonneg (x-y),sq_nonneg (x-z),sq_nonneg (y-z)]
  have hh := hthree (kernelMean K*B) (C-M) M
  have hb := mul_le_mul_of_nonneg_left hbase (sq_nonneg (kernelMean K))
  unfold jointCenteredEnergy
  rw [mul_pow] at hh
  nlinarith only [hh,hb,hC,hM]

/-- For this already fixed translate, one coloring handles a finite kernel
family and every fine target, including its deterministic unsigned main term. -/
theorem exists_fixed_translate_root_budget {κ : Type*} (hp : p≠2) (h : ℕ) (a : ZMod p)
    (ha : ∀ i<h, a+(i:ZMod p)≠0) (hop : ∀ q<2*h, 2*a+(q:ZMod p)≠0)
    (S : Finset κ) (K : κ → α → α → ℝ) (hK : ∀ k∈S, ∀ x y, K k x y=K k y x)
    (w : κ → ℝ) (hw : ∀ k∈S, 0≤w k) :
    ∃ ω : Fin h → α, ∀ k∈S, ∀ t s : ZMod p,
      w k*(labelRootCount h a (fun i j ↦ K k (ω i) (ω j)) t s-
        (h:ℝ)^2*kernelMean (K k))^2 ≤
      6*(h:ℝ)*(w k*(kernelMean (K k))^2*
        orderedEnergy h (fun i j ↦ signPattern h a i*signPattern h a j)+
        ∑ l∈S, w l*(16*(h:ℝ)^2*colorVariance (K l)+
          4*(h:ℝ)*diagonalCenteredSecond (K l))) := by
  obtain ⟨ω,hω⟩ := exists_joint_centered_budget h (signPattern h a) (signPattern_sq h a ha)
    S K hK w hw
  refine ⟨ω,fun k hk t s ↦ ?_⟩
  have hkE : w k*jointCenteredEnergy h (signPattern h a) (K k) ω ≤
      ∑ l∈S, w l*(16*(h:ℝ)^2*colorVariance (K l)+
        4*(h:ℝ)*diagonalCenteredSecond (K l)) :=
    (Finset.single_le_sum (fun l hl ↦ mul_nonneg (hw l hl)
      (jointCenteredEnergy_nonneg h (signPattern h a) (K l) ω)) hk).trans hω
  have he := mul_le_mul_of_nonneg_left (coloredRootCount_error_sq hp h a ha hop (K k) ω t s)
    (hw k hk)
  have hmul := mul_le_mul_of_nonneg_left hkE (show (0:ℝ)≤6*h by positivity)
  nlinarith only [he,hmul]

/-- The translation is selected before all later finite symmetric color
kernels. Their selection affects only the coloring, not the translation. -/
theorem exists_pattern_for_later_kernels {κ : Type*} (hp : p≠2) (h : ℕ) (hh : 4*h<p) :
    ∃ a : ZMod p,
      (∀ i<h, a+(i:ZMod p)≠0) ∧ (∀ q<2*h, 2*a+(q:ZMod p)≠0) ∧
      ∀ (S : Finset κ) (K : κ → α → α → ℝ),
        (∀ k∈S, ∀ x y, K k x y=K k y x) →
        ∀ (w : κ → ℝ), (∀ k∈S, 0≤w k) →
        ∃ ω : Fin h → α, ∀ k∈S, ∀ t s : ZMod p,
          w k*(labelRootCount h a (fun i j ↦ K k (ω i) (ω j)) t s-
            (h:ℝ)^2*kernelMean (K k))^2 ≤
          6*(h:ℝ)*(8*w k*(kernelMean (K k))^2*(h:ℝ)^2+
            ∑ l∈S, w l*(16*(h:ℝ)^2*colorVariance (K l)+
              4*(h:ℝ)*diagonalCenteredSecond (K l))) := by
  obtain ⟨a,ha,hop,hE⟩ := exists_low_energy_pattern hp h hh
  refine ⟨a,ha,hop,fun S K hK w hw ↦ ?_⟩
  obtain ⟨ω,hω⟩ := exists_fixed_translate_root_budget hp h a ha hop S K hK w hw
  refine ⟨ω,fun k hk t s ↦ (hω k hk t s).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ le_rfl
  have he := mul_le_mul_of_nonneg_left hE (mul_nonneg (hw k hk) (sq_nonneg (kernelMean (K k))))
  nlinarith only [he]

end Erdos66FixedTranslateColorRoot
