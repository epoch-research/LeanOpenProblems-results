import Submission.FiniteFieldExplore

/-! A shared-label product has a quadratic, not quartic, main term.
Its extra error is the additive energy of the product sign sequence.
This file does not construct compatible integer prefixes. -/
namespace Erdos66SharedParameterKernel
open scoped Classical

noncomputable def labelFiber (h : ℕ) (f : ℕ → ℝ) (w : ℕ) : ℝ :=
  ∑ i∈Finset.range h, ∑ j∈Finset.range h, if i+j=w then f i*f j else 0

noncomputable def labelL1 (h : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ w∈Finset.range (2*h), |labelFiber h f w|

noncomputable def labelEnergy (h : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ w∈Finset.range (2*h), (labelFiber h f w)^2

lemma sum_labelFiber (h : ℕ) (f b : ℕ → ℝ) :
    (∑ w∈Finset.range (2*h), labelFiber h f w*b w) =
      ∑ i∈Finset.range h, ∑ j∈Finset.range h, f i*f j*b (i+j) := by
  unfold labelFiber
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i+j∈Finset.range (2*h) := by
    have := Finset.mem_range.mp hi
    have := Finset.mem_range.mp hj
    simp only [Finset.mem_range]
    omega
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,hij,if_true]

lemma labelL1_nonneg (h : ℕ) (f : ℕ → ℝ) : 0 ≤ labelL1 h f :=
  Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

lemma labelL1_sq_le (h : ℕ) (f : ℕ → ℝ) :
    (labelL1 h f)^2 ≤ (2*h : ℕ)*labelEnergy h f := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (2*h))
    (fun _ : ℕ ↦ (1 : ℝ)) (fun w ↦ |labelFiber h f w|)
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,
    sq_abs,labelL1,labelEnergy] using hh

lemma fiber_pairing_abs_le (h : ℕ) (f b : ℕ → ℝ)
    (hb : ∀ w, |b w| ≤ 1) :
    |∑ w∈Finset.range (2*h), labelFiber h f w*b w| ≤ labelL1 h f := by
  calc
    _ ≤ ∑ w∈Finset.range (2*h), |labelFiber h f w*b w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro w hw
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb w) (abs_nonneg (labelFiber h f w))

noncomputable def sharedKernelCount (h : ℕ) (f g b d : ℕ → ℝ) : ℝ :=
  ∑ i∈Finset.range h, ∑ j∈Finset.range h,
    (1+f i*f j*b (i+j))*(1+g i*g j*d (i+j))

/-- Sharing the label pair retains h² as the main term. Independent label
pairs would instead produce h⁴. -/
lemma sharedKernelCount_identity (h : ℕ) (f g b d : ℕ → ℝ) :
    sharedKernelCount h f g b d = (h : ℝ)^2 +
      (∑ w∈Finset.range (2*h), labelFiber h f w*b w) +
      (∑ w∈Finset.range (2*h), labelFiber h g w*d w) +
      (∑ w∈Finset.range (2*h), labelFiber h (fun i ↦ f i*g i) w*(b w*d w)) := by
  rw [sum_labelFiber,sum_labelFiber,sum_labelFiber]
  unfold sharedKernelCount
  have he (i j : ℕ) :
      (1+f i*f j*b (i+j))*(1+g i*g j*d (i+j)) =
        1+f i*f j*b (i+j)+g i*g j*d (i+j)+
          (f i*g i)*(f j*g j)*(b (i+j)*d (i+j)) := by ring
  simp_rw [he,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  ring

theorem sharedKernelCount_error (h : ℕ) (f g b d : ℕ → ℝ)
    (hb : ∀ w, |b w| ≤ 1) (hd : ∀ w, |d w| ≤ 1) :
    |sharedKernelCount h f g b d-(h : ℝ)^2| ≤
      labelL1 h f+labelL1 h g+labelL1 h (fun i ↦ f i*g i) := by
  rw [sharedKernelCount_identity]
  have hbd (w : ℕ) : |b w*d w| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (hb w) (hd w) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have he := fiber_pairing_abs_le h f b hb
  have hf := fiber_pairing_abs_le h g d hd
  have hg := fiber_pairing_abs_le h (fun i ↦ f i*g i) (fun w ↦ b w*d w) hbd
  have htriangle := (abs_add_le
    ((∑ w∈Finset.range (2*h), labelFiber h f w*b w)+
      (∑ w∈Finset.range (2*h), labelFiber h g w*d w))
    (∑ w∈Finset.range (2*h), labelFiber h (fun i ↦ f i*g i) w*(b w*d w)))
  have htriangle' := abs_add_le
    (∑ w∈Finset.range (2*h), labelFiber h f w*b w)
    (∑ w∈Finset.range (2*h), labelFiber h g w*d w)
  have hh : (h : ℝ)^2+
      (∑ w∈Finset.range (2*h), labelFiber h f w*b w)+
      (∑ w∈Finset.range (2*h), labelFiber h g w*d w)+
      (∑ w∈Finset.range (2*h), labelFiber h (fun i ↦ f i*g i) w*(b w*d w))-(h : ℝ)^2 =
      ((∑ w∈Finset.range (2*h), labelFiber h f w*b w)+
      (∑ w∈Finset.range (2*h), labelFiber h g w*d w))+
      (∑ w∈Finset.range (2*h), labelFiber h (fun i ↦ f i*g i) w*(b w*d w)) := by ring
  rw [hh]
  linarith

/-- Three small energies suffice for a flat shared-label two-factor kernel. -/
theorem sharedKernelCount_error_sq (h : ℕ) (f g b d : ℕ → ℝ)
    (hb : ∀ w, |b w| ≤ 1) (hd : ∀ w, |d w| ≤ 1)
    (C : ℝ) (hf : labelEnergy h f ≤ C*(h : ℝ)^2)
    (hg : labelEnergy h g ≤ C*(h : ℝ)^2)
    (hfg : labelEnergy h (fun i ↦ f i*g i) ≤ C*(h : ℝ)^2) :
    (sharedKernelCount h f g b d-(h : ℝ)^2)^2 ≤ 18*C*(h : ℝ)^3 := by
  have hbound := sharedKernelCount_error h f g b d hb hd
  have hf' := (labelL1_sq_le h f).trans
    (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (2*h)))
  have hg' := (labelL1_sq_le h g).trans
    (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (2*h)))
  have hfg' := (labelL1_sq_le h (fun i ↦ f i*g i)).trans
    (mul_le_mul_of_nonneg_left hfg (Nat.cast_nonneg (2*h)))
  push_cast at hf' hg' hfg'
  have he := sq_le_sq₀ (abs_nonneg _) (add_nonneg
    (add_nonneg (labelL1_nonneg h f) (labelL1_nonneg h g))
    (labelL1_nonneg h (fun i ↦ f i*g i))) |>.mpr hbound
  rw [sq_abs] at he
  nlinarith [sq_nonneg (labelL1 h f-labelL1 h g),
    sq_nonneg (labelL1 h f-labelL1 h (fun i ↦ f i*g i)),
    sq_nonneg (labelL1 h g-labelL1 h (fun i ↦ f i*g i))]

end Erdos66SharedParameterKernel
