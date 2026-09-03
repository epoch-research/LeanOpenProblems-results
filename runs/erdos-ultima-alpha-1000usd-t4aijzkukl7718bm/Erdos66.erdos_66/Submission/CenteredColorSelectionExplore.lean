import Submission.OrderedColorEnergyExplore

/-! Joint control of signed and unsigned centered pair kernels, with colors
chosen after the sign pattern. These are finite potential estimates. -/
namespace Erdos66CenteredColorSelection
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66FixedPatternColorEnergy
  Erdos66OrderedColorEnergy
open scoped Classical
set_option maxHeartbeats 2000000

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

noncomputable def colorVariance (K : α → α → ℝ) : ℝ :=
  kernelMean (fun x y ↦ (centeredKernel K x y)^2)

noncomputable def diagonalCenteredSecond (K : α → α → ℝ) : ℝ :=
  mean (fun x : α ↦ (centeredKernel K x x)^2)

noncomputable def centeredSignedEnergy (h : ℕ) (f : Fin h → ℝ)
    (K : α → α → ℝ) (ω : Fin h → α) : ℝ :=
  orderedEnergy h (fun i j ↦ (f i*f j)*centeredKernel K (ω i) (ω j))

noncomputable def jointCenteredEnergy (h : ℕ) (f : Fin h → ℝ)
    (K : α → α → ℝ) (ω : Fin h → α) : ℝ :=
  centeredSignedEnergy h f K ω+centeredSignedEnergy h (fun _ ↦ 1) K ω

lemma centeredSignedEnergy_nonneg (h : ℕ) (f : Fin h → ℝ)
    (K : α → α → ℝ) (ω : Fin h → α) : 0≤centeredSignedEnergy h f K ω := by
  unfold centeredSignedEnergy orderedEnergy
  exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma jointCenteredEnergy_nonneg (h : ℕ) (f : Fin h → ℝ)
    (K : α → α → ℝ) (ω : Fin h → α) : 0≤jointCenteredEnergy h f K ω :=
  add_nonneg (centeredSignedEnergy_nonneg h f K ω)
    (centeredSignedEnergy_nonneg h (fun _ ↦ 1) K ω)

lemma mean_centeredSignedEnergy_le (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (K : α → α → ℝ) (hK : ∀ x y, K x y=K y x) :
    mean (centeredSignedEnergy h f K) ≤
      8*(h:ℝ)^2*colorVariance K+2*(h:ℝ)*diagonalCenteredSecond K := by
  have he := mean_orderedColorEnergy_le h f hf (centeredKernel K)
    (fun x y ↦ by simp only [centeredKernel,hK x y])
  rw [kernelMean_centered] at he
  simp only [zero_pow (by omega : 2≠0),zero_mul,zero_add] at he
  change mean (fun ω : Fin h → α ↦ orderedEnergy h
    (fun i j ↦ (f i*f j)*centeredKernel K (ω i) (ω j))) ≤ _
  simpa only [colorVariance,diagonalCenteredSecond,
    mul_comm,mul_left_comm,mul_assoc] using he

lemma mean_jointCenteredEnergy_le (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (K : α → α → ℝ) (hK : ∀ x y, K x y=K y x) :
    mean (jointCenteredEnergy h f K) ≤
      16*(h:ℝ)^2*colorVariance K+4*(h:ℝ)*diagonalCenteredSecond K := by
  unfold jointCenteredEnergy
  rw [mean_add]
  have h₁ := mean_centeredSignedEnergy_le h f hf K hK
  have h₂ := mean_centeredSignedEnergy_le h (fun _ ↦ 1) (fun _ ↦ by norm_num) K hK
  linarith

/-- The fixed sign pattern may be chosen before the kernel family.
The same coloring controls signed and unsigned errors. -/
theorem exists_joint_centered_budget {κ : Type*} (h : ℕ) (f : Fin h → ℝ)
    (hf : ∀ i, (f i)^2=1) (S : Finset κ) (K : κ → α → α → ℝ)
    (hK : ∀ k∈S, ∀ x y, K k x y=K k y x) (w : κ → ℝ) (hw : ∀ k∈S, 0≤w k) :
    ∃ ω : Fin h → α,
      (∑ k∈S, w k*jointCenteredEnergy h f (K k) ω) ≤
        ∑ k∈S, w k*(16*(h:ℝ)^2*colorVariance (K k)+
          4*(h:ℝ)*diagonalCenteredSecond (K k)) := by
  obtain ⟨ω,hω⟩ := exists_le_mean
    (fun ω : Fin h → α ↦ ∑ k∈S, w k*jointCenteredEnergy h f (K k) ω)
  refine ⟨ω,hω.trans ?_⟩
  rw [mean_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [mean_const_mul]
  exact mul_le_mul_of_nonneg_left (mean_jointCenteredEnergy_le h f hf (K k) (hK k hk)) (hw k hk)

lemma sum_orderedFiber (h : ℕ) (V : Fin h → Fin h → ℝ) :
    (∑ q∈Finset.range (2*h), orderedFiber h V q)=∑ i : Fin h, ∑ j : Fin h, V i j := by
  unfold orderedFiber
  rw [Finset.sum_comm]
  have he (e : Fin h × Fin h) :
      (∑ q∈Finset.range (2*h), if e.1.val+e.2.val=q then V e.1 e.2 else 0)=V e.1 e.2 := by
    have hm : e.1.val+e.2.val∈Finset.range (2*h) := by
      simp only [Finset.mem_range]; have := e.1.isLt; have := e.2.isLt; omega
    simp [hm]
  simp_rw [he]
  exact Fintype.sum_prod_type _

/-- The same label-fiber energy also controls the unsigned total. -/
lemma matrixSum_sq_le_energy (h : ℕ) (V : Fin h → Fin h → ℝ) :
    (∑ i : Fin h, ∑ j : Fin h, V i j)^2 ≤ 2*(h:ℝ)*orderedEnergy h V := by
  rw [←sum_orderedFiber]
  have he := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (2*h))
    (orderedFiber h V) (fun _ ↦ (1:ℝ))
  simpa only [mul_one,one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    Nat.cast_mul,Nat.cast_ofNat,orderedEnergy,mul_comm,one_mul] using he

end Erdos66CenteredColorSelection
