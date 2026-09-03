import Submission.MatchingColorMomentsExplore

/-! Coloring after the sign pattern is fixed. At a fixed integer label sum,
unordered off-diagonal pairs form a matching, so their color kernels have an
exact variance formula. This does not assert an infinite profile exists. -/
namespace Erdos66FixedPatternColorEnergy
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66MatchingColorMoments
open scoped Classical
set_option maxHeartbeats 2400000

noncomputable def sumEdges (h q : ℕ) : Finset (Fin h × Fin h) :=
  Finset.univ.filter (fun e ↦ e.1<e.2 ∧ e.1.val+e.2.val=q)

lemma mem_sumEdges (h q : ℕ) (e : Fin h × Fin h) :
    e∈sumEdges h q ↔ e.1<e.2 ∧ e.1.val+e.2.val=q := by simp [sumEdges]

lemma sumEdges_ne (h q : ℕ) (e : Fin h × Fin h) (he : e∈sumEdges h q) : e.1≠e.2 :=
  ne_of_lt (mem_sumEdges h q e |>.mp he).1

lemma sumEdges_matching (h q : ℕ) :
    (sumEdges h q:Set (Fin h × Fin h)).Pairwise
      (fun e d ↦ Disjoint ({e.1,e.2}:Set (Fin h)) ({d.1,d.2}:Set (Fin h))) := by
  intro e he d hd hed
  have he' := (mem_sumEdges h q e).mp he
  have hd' := (mem_sumEdges h q d).mp hd
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    apply hed <;> apply Prod.ext <;> apply Fin.ext <;> omega

noncomputable def edgeFiber (h : ℕ) (f : Fin h → ℝ) (q : ℕ) : ℝ :=
  ∑ e∈sumEdges h q, f e.1*f e.2

noncomputable def edgeEnergy (h : ℕ) (f : Fin h → ℝ) : ℝ :=
  ∑ q∈Finset.range (2*h), (edgeFiber h f q)^2

noncomputable def edgeMass (h : ℕ) : ℝ :=
  ∑ q∈Finset.range (2*h), ((sumEdges h q).card:ℝ)

lemma edgeMass_nonneg (h : ℕ) : 0≤edgeMass h :=
  Finset.sum_nonneg (fun q _ ↦ Nat.cast_nonneg _)

lemma edgeMass_le (h : ℕ) : edgeMass h≤(h:ℝ)^2 := by
  simp only [edgeMass,sumEdges,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _e : Fin h × Fin h, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      have hs : e.1.val+e.2.val∈Finset.range (2*h) := by
        simp only [Finset.mem_range]; have := e.1.isLt; have := e.2.isLt; omega
      by_cases hlt : e.1<e.2 <;> simp [hlt,hs]
    _ = _ := by simp [pow_two]

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

noncomputable def colorFiber (h : ℕ) (f : Fin h → ℝ) (K : α → α → ℝ)
    (ω : Fin h → α) (q : ℕ) : ℝ :=
  ∑ e∈sumEdges h q, (f e.1*f e.2)*K (ω e.1) (ω e.2)

noncomputable def colorEnergy (h : ℕ) (f : Fin h → ℝ) (K : α → α → ℝ)
    (ω : Fin h → α) : ℝ :=
  ∑ q∈Finset.range (2*h), (colorFiber h f K ω q)^2

lemma colorEnergy_nonneg (h : ℕ) (f : Fin h → ℝ) (K : α → α → ℝ)
    (ω : Fin h → α) : 0≤colorEnergy h f K ω :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

lemma mean_colorFiber_sq (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (K : α → α → ℝ) (q : ℕ) :
    mean (fun ω : Fin h → α ↦ (colorFiber h f K ω q)^2)=
      (kernelMean K)^2*(edgeFiber h f q)^2+
        (kernelMean (fun x y ↦ (K x y)^2)-(kernelMean K)^2)*((sumEdges h q).card:ℝ) := by
  have hh := matching_kernel_second_moment (sumEdges h q) (sumEdges_ne h q)
    (sumEdges_matching h q) (fun e ↦ f e.1*f e.2) K
  simpa only [colorFiber,edgeFiber,mul_pow,hf,one_mul,Finset.sum_const,nsmul_eq_mul,
    mul_one] using hh

/-- The original sign pattern is held fixed. Its energy appears explicitly
in the mean, together with the ordinary variance of the coarse color kernel. -/
theorem mean_colorEnergy_identity (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (K : α → α → ℝ) :
    mean (colorEnergy h f K)=
      (kernelMean K)^2*edgeEnergy h f+
        (kernelMean (fun x y ↦ (K x y)^2)-(kernelMean K)^2)*edgeMass h := by
  unfold colorEnergy
  rw [mean_sum]
  simp_rw [mean_colorFiber_sq h f hf K]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  rfl

/-- A convenient bound retaining the old-pattern energy and the kernel's
second moment. The number of available colors does not occur in the bound. -/
theorem mean_colorEnergy_le (h : ℕ) (f : Fin h → ℝ) (hf : ∀ i, (f i)^2=1)
    (K : α → α → ℝ) :
    mean (colorEnergy h f K)≤(kernelMean K)^2*edgeEnergy h f+
      kernelMean (fun x y ↦ (K x y)^2)*(h:ℝ)^2 := by
  rw [mean_colorEnergy_identity h f hf K]
  apply add_le_add le_rfl
  have hν : 0≤kernelMean (fun x y ↦ (K x y)^2) := by
    change 0 ≤ mean _
    have hh := mean_mono (fun _ : α×α ↦ (0:ℝ))
      (fun x : α×α ↦ (K x.1 x.2)^2) (fun x ↦ sq_nonneg _)
    simpa only [mean_const] using hh
  exact mul_le_mul (sub_le_self _ (sq_nonneg _)) (edgeMass_le h) (edgeMass_nonneg h) hν

lemma exists_le_mean {γ : Type*} [Fintype γ] [Nonempty γ] (F : γ → ℝ) :
    ∃ x, F x ≤ mean F := by
  obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image Finset.univ F Finset.univ_nonempty
  refine ⟨x, ?_⟩
  have hh := mean_mono (fun _ : γ ↦ F x) F (fun y ↦ hmin y (Finset.mem_univ y))
  simpa only [mean_const] using hh

/-- One coloring is selected after a fixed sign pattern and a finite weighted
list of kernels. No re-selection of the sign pattern or field translate occurs. -/
theorem exists_fixed_pattern_color_budget {κ : Type*} (h : ℕ) (f : Fin h → ℝ)
    (hf : ∀ i, (f i)^2=1) (S : Finset κ) (K : κ → α → α → ℝ) (w : κ → ℝ)
    (hw : ∀ k∈S, 0≤w k) :
    ∃ ω : Fin h → α,
      (∑ k∈S, w k*colorEnergy h f (K k) ω) ≤
        ∑ k∈S, w k*((kernelMean (K k))^2*edgeEnergy h f+
          kernelMean (fun x y ↦ (K k x y)^2)*(h:ℝ)^2) := by
  obtain ⟨ω,hω⟩ := exists_le_mean (fun ω : Fin h → α ↦ ∑ k∈S, w k*colorEnergy h f (K k) ω)
  refine ⟨ω,hω.trans ?_⟩
  rw [mean_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [mean_const_mul]
  exact mul_le_mul_of_nonneg_left (mean_colorEnergy_le h f hf (K k)) (hw k hk)

end Erdos66FixedPatternColorEnergy
