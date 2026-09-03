import Submission.CompleteBernsteinEnergyExplore

/-! One coloring for every later nonnegative kernel, using the finite list
of ordered matrix masks. The color cost is quadratic up to a logarithm,
with a separate fourth-power range term. -/
namespace Erdos66UniversalBernsteinGraph
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66CenteredColorSelection
  Erdos66CompleteBernsteinEnergy Erdos66CompleteKernelBasis Erdos66KernelSymmetrization
  Erdos66BernsteinBudgetParameters Erdos66LogarithmicActualBudget
  Erdos66CompletePartitionColorTransfer Erdos66UniversalCompleteAccuracy
  Erdos66UniversalCompleteGraph Erdos66UniformGraphColorTransfer
  Erdos66TranslatedGraphPartition Erdos66LogarithmicColorBudget
open scoped Classical
set_option maxHeartbeats 3000000
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype α] [Nonempty α] in
lemma mask_nonneg (q : α×α) (x y : α) : 0≤ mask q x y := by
  unfold mask; split_ifs <;> norm_num

omit [Fintype α] [Nonempty α] in
lemma mask_le_one (q : α×α) (x y : α) : mask q x y≤1 := by
  unfold mask; split_ifs <;> norm_num

omit [Fintype α] [Nonempty α] in
lemma sym_mask_nonneg (q : α×α) (x y : α) : 0≤symKernel (mask q) x y := by
  exact div_nonneg (add_nonneg (mask_nonneg q x y) (mask_nonneg q y x)) (by norm_num)

omit [Fintype α] [Nonempty α] in
lemma sym_mask_le_one (q : α×α) (x y : α) : symKernel (mask q) x y≤1 := by
  unfold symKernel
  linarith only [mask_le_one q x y,mask_le_one q y x]

lemma sym_mask_variance_le (q : α×α) :
    colorVariance (symKernel (mask q))≤1/(Fintype.card (α×α):ℝ) := by
  have he := variance_le_mean_times_range (symKernel (mask q)) 1
    (sym_mask_nonneg q) (sym_mask_le_one q)
  simpa only [one_mul,kernelMean_sym,mask_mean] using he

/-- The request list has size |alpha|^2, independent of all later kernels,
graphs, fine targets, and coarse targets. -/
theorem exists_universal_mask_energy {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ q : α×α,
      colorEnergy ρ (mask q) ω≤
        completeEnergyBound n (Fintype.card (α×α)) (1/(Fintype.card (α×α):ℝ)) 1 := by
  obtain ⟨ω,hω⟩ := exists_complete_bernstein_energy ρ hF (Finset.univ:Finset (α×α))
    (fun q ↦ symKernel (mask q)) (fun q _ ↦ symKernel_symm (mask q))
    (fun _ ↦ 1) (fun _ ↦ 1/(Fintype.card (α×α):ℝ))
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by positivity)
    (fun q _ ↦ centered_bound_of_nonnegative (symKernel (mask q)) 1
      (sym_mask_nonneg q) (sym_mask_le_one q)) (fun q _ ↦ sym_mask_variance_le q)
  refine ⟨ω,fun q ↦ ?_⟩
  simpa only [Finset.card_univ,colorEnergy_sym] using hω q (Finset.mem_univ _)

noncomputable def paletteCost (n q : ℕ) : ℝ :=
  64*(q:ℝ)^2*n*listLog n (q*q)+64*(q:ℝ)^4*(listLog n (q*q))^2+2*(q:ℝ)^4

lemma mask_accuracy_of_energy {n : ℕ} (ρ : Fin n ≃ F) (ω : Fin n → α)
    (q : α×α) (f : F → F) (D : ℕ) (hf : HasBoundedSums f D)
    (ε : ℝ) (hε : 0≤ε)
    (hsize : (D:ℝ)^2*paletteCost n (Fintype.card α)≤ε^2*(n:ℝ)^2)
    (he : colorEnergy ρ (mask q) ω≤
      completeEnergyBound n (Fintype.card (α×α)) (1/(Fintype.card (α×α):ℝ)) 1)
    (t s : F) :
    |graphSum f ρ (fun i j ↦ mask q (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean (mask q)|≤
      ε*(n:ℝ)^2*kernelMean (mask q) := by
  have hc : (Fintype.card α:ℝ)>0 := by exact_mod_cast Fintype.card_pos
  have hraw := (graphSum_error_sq f ρ D hf (mask q) ω t s).trans
    (mul_le_mul_of_nonneg_left he (show (0:ℝ)≤(D:ℝ)^2*n by positivity))
  have hid : ((D:ℝ)^2*n*
      completeEnergyBound n (Fintype.card (α×α)) (1/(Fintype.card (α×α):ℝ)) 1)*
        (Fintype.card α:ℝ)^4=
      (n:ℝ)^2*((D:ℝ)^2*paletteCost n (Fintype.card α)) := by
    unfold completeEnergyBound paletteCost
    rw [Fintype.card_prod,Nat.cast_mul]
    field_simp
  have hs := mul_le_mul_of_nonneg_left hsize (sq_nonneg (n:ℝ))
  rw [←hid] at hs
  have ht := mul_le_mul_of_nonneg_right hraw (show (0:ℝ)≤(Fintype.card α:ℝ)^4 by positivity)
  have hsq : (graphSum f ρ (fun i j ↦ mask q (ω i) (ω j)) t s-
      (n:ℝ)^2*kernelMean (mask q))^2≤(ε*(n:ℝ)^2*kernelMean (mask q))^2 := by
    apply (mul_le_mul_iff_left₀ (show (0:ℝ)<(Fintype.card α:ℝ)^4 by positivity)).mp
    have heq : (ε*(n:ℝ)^2*kernelMean (mask q))^2*(Fintype.card α:ℝ)^4=
        (n:ℝ)^2*(ε^2*(n:ℝ)^2) := by
      rw [mask_mean,Fintype.card_prod,Nat.cast_mul]
      field_simp
    rw [heq]
    exact ht.trans hs
  apply (sq_le_sq₀ (abs_nonneg _) (show 0≤ε*(n:ℝ)^2*kernelMean (mask q) by
    rw [mask_mean]; positivity)).mp
  simpa only [sq_abs] using hsq

omit [Nonempty α] in
lemma graph_mask_combination {n : ℕ} (ρ : Fin n ≃ F) (ω : Fin n → α)
    (f : F → F) (K : α → α → ℝ) (t s : F) :
    graphSum f ρ (fun i j ↦ K (ω i) (ω j)) t s=
      ∑ q : α×α, K q.1 q.2*graphSum f ρ (fun i j ↦ mask q (ω i) (ω j)) t s := by
  unfold graphSum
  have hid (i j : Fin n) : K (ω i) (ω j)*((sumCoeff f (ρ i+ρ j) t s):ℝ)=
      ∑ q : α×α, K q.1 q.2*(mask q (ω i) (ω j)*((sumCoeff f (ρ i+ρ j) t s):ℝ)) := by
    rw [←mask_combination K (ω i) (ω j),Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  simp only [hid]
  rw [Finset.sum_comm]
  have hrow (j : Fin n) :
      (∑ i : Fin n, ∑ q : α×α, K q.1 q.2*
        (mask q (ω i) (ω j)*((sumCoeff f (ρ i+ρ j) t s):ℝ)))=
      ∑ q : α×α, ∑ i : Fin n, K q.1 q.2*
        (mask q (ω i) (ω j)*((sumCoeff f (ρ i+ρ j) t s):ℝ)) := Finset.sum_comm
  simp_rw [hrow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

omit [Nonempty α] in
lemma graph_error_combination {n : ℕ} (ρ : Fin n ≃ F) (ω : Fin n → α)
    (f : F → F) (K : α → α → ℝ) (t s : F) :
    graphSum f ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K=
      ∑ q : α×α, K q.1 q.2*(graphSum f ρ (fun i j ↦ mask q (ω i) (ω j)) t s-
        (n:ℝ)^2*kernelMean (mask q)) := by
  rw [graph_mask_combination]
  simp only [mul_sub,Finset.sum_sub_distrib]
  congr 1
  rw [←mask_mean_combination K,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- One coloring precedes ALL later nonnegative real kernels. The leading
color cost is quadratic times a logarithm; the range term remains explicit. -/
theorem exists_universal_bernstein_graph_accuracy {n : ℕ} (ρ : Fin n ≃ F)
    (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ ε : ℝ, 0≤ε → (D:ℝ)^2*paletteCost n (Fintype.card α)≤ε^2*(n:ℝ)^2 →
      ∀ K : α → α → ℝ, (∀ x y, 0≤K x y) → ∀ t s : F,
        |graphSum f ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K|≤
          ε*(n:ℝ)^2*kernelMean K := by
  obtain ⟨ω,hω⟩ := exists_universal_mask_energy (α := α) ρ hF
  refine ⟨ω,fun f D hf ε hε hsize K hK t s ↦ ?_⟩
  rw [graph_error_combination]
  calc
    _ ≤ ∑ q : α×α, |K q.1 q.2*(graphSum f ρ (fun i j ↦ mask q (ω i) (ω j)) t s-
        (n:ℝ)^2*kernelMean (mask q))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q : α×α, K q.1 q.2*(ε*(n:ℝ)^2*kernelMean (mask q)) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul,abs_of_nonneg (hK q.1 q.2)]
      exact mul_le_mul_of_nonneg_left (mask_accuracy_of_energy ρ ω q f D hf ε hε hsize
        (hω q) t s) (hK q.1 q.2)
    _ = _ := by
      rw [←mask_mean_combination K,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

end Erdos66UniversalBernsteinGraph
