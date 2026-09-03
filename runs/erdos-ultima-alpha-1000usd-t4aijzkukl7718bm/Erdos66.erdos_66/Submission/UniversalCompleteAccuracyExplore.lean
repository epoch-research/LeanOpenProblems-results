import Submission.UniversalCompleteGraphExplore

/-! Explicit relative accuracy for universal complete graph partitions,
including actual infinite coarse families. No finite coarse-target budget
or sparse independently excluded fine support is required. -/
namespace Erdos66UniversalCompleteAccuracy
open Erdos66UniformSelection Erdos66UniformColorMoments Erdos66CenteredColorSelection
  Erdos66UniversalCompleteGraph Erdos66UniversalActualKernel
  Erdos66TranslatedGraphPartition Erdos66InfiniteKernelLocality Erdos66InfiniteMixedKernel
open scoped Classical
set_option maxHeartbeats 2800000
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

omit [DecidableEq α] in
lemma kernel_sum_eq (K : α → α → ℝ) :
    (∑ q : α×α, K q.1 q.2)=(Fintype.card α:ℝ)^2*kernelMean K := by
  have hc : (Fintype.card α:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  unfold kernelMean mean
  rw [Fintype.card_prod,Nat.cast_mul]
  field_simp

lemma centeredMass_eq_variance (K : α → α → ℝ) :
    centeredMass K=(Fintype.card α:ℝ)^2*colorVariance K := by
  exact kernel_sum_eq (fun x y ↦ (centeredKernel K x y)^2)

lemma centeredMass_le_second (K : α → α → ℝ) :
    centeredMass K≤∑ q : α×α, (K q.1 q.2)^2 := by
  rw [centeredMass_eq_variance,kernel_sum_eq (fun x y ↦ (K x y)^2)]
  exact mul_le_mul_of_nonneg_left (kernelVariance_le_second K) (sq_nonneg _)

lemma centeredMass_le_mean_sq (K : α → α → ℝ) (hK : ∀ x y, 0≤K x y) :
    centeredMass K≤(Fintype.card α:ℝ)^4*(kernelMean K)^2 :=
  (centeredMass_le_second K).trans (kernel_second_le_mean_sq K hK)

lemma relative_accuracy_of_bound (n D : ℕ) (hn : 1≤n) (ε X : ℝ) (hε : 0≤ε)
    (K : α → α → ℝ) (hK : ∀ x y, 0≤K x y)
    (hsize : 10*(D:ℝ)^2*(Fintype.card α:ℝ)^4≤ε^2*n)
    (he : (X-(n:ℝ)^2*kernelMean K)^2≤(D:ℝ)^2*n*(8*(n:ℝ)^2+2*n)*centeredMass K) :
    |X-(n:ℝ)^2*kernelMean K|≤ε*(n:ℝ)^2*kernelMean K := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hcoeff : 8*(n:ℝ)^2+2*n≤10*(n:ℝ)^2 := by nlinarith
  have hmass := centeredMass_le_mean_sq K hK
  have hm := mul_le_mul_of_nonneg_left hmass
    (show (0:ℝ)≤(D:ℝ)^2*n*(8*(n:ℝ)^2+2*n) by positivity)
  have hc := mul_le_mul_of_nonneg_left hcoeff
    (show (0:ℝ)≤(D:ℝ)^2*n*(Fintype.card α:ℝ)^4*(kernelMean K)^2 by positivity)
  have hs := mul_le_mul_of_nonneg_right hsize
    (show (0:ℝ)≤(n:ℝ)^3*(kernelMean K)^2 by positivity)
  have hsq : (X-(n:ℝ)^2*kernelMean K)^2≤(ε*(n:ℝ)^2*kernelMean K)^2 := by
    nlinarith only [he,hm,hc,hs]
  have hmu := kernelMean_nonneg K hK
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The coloring precedes the accuracy request as well as all later graph
and kernel data. The explicit hypothesis retains the fourth-power color cost. -/
theorem exists_universal_graph_accuracy {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ ε : ℝ, 0≤ε → 10*(D:ℝ)^2*(Fintype.card α:ℝ)^4≤ε^2*n →
      ∀ K : α → α → ℝ, (∀ x y, 0≤K x y) → ∀ t s : F,
        |graphSum f ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K|≤
          ε*(n:ℝ)^2*kernelMean K := by
  obtain ⟨ω,hω⟩ := exists_universal_graph_kernels (α := α) ρ hF
  have hn : 1≤n := by have hh := (ρ.symm 0).isLt; omega
  exact ⟨ω,fun f D hf ε hε hsize K hK t s ↦
    relative_accuracy_of_bound n D hn ε _ hε K hK hsize (hω f D hf K t s)⟩

/-- All natural coarse targets are included for both infinite families. -/
theorem exists_universal_infinite_accuracy {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ ε : ℝ, 0≤ε → 10*(D:ℝ)^2*(Fintype.card α:ℝ)^4≤ε^2*n →
      ∀ (B C : α → Set ℕ) (q : ℕ) (t s : F),
        |(setPairCount (infiniteGraphSet f ρ B ω) (infiniteGraphSet f ρ C ω) ((t,s),(q:ℤ)):ℝ)-
          (n:ℝ)^2*kernelMean (infiniteMixedKernel B C q)|≤
            ε*(n:ℝ)^2*kernelMean (infiniteMixedKernel B C q) := by
  obtain ⟨ω,hω⟩ := exists_universal_graph_accuracy (α := α) ρ hF
  refine ⟨ω,fun f D hf ε hε hsize B C q t s ↦ ?_⟩
  rw [infinite_graph_mixed_identity]
  exact hω f D hf ε hε hsize (infiniteMixedKernel B C q) (infiniteMixedKernel_nonneg B C q) t s

omit [Fintype α] [Nonempty α] [DecidableEq α] in
lemma mem_infiniteGraphSet (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (B : α → Set ℕ) (ω : Fin n → α) (z : F×F) (q : ℤ) :
    (z,q)∈infiniteGraphSet f ρ B ω ↔ q∈natSupport (B (ω (ρ.symm (z.2-f z.1)))) := by
  simp only [infiniteGraphSet,infiniteAssembly,Set.mem_setOf_eq,mem_graphSlice]
  constructor
  · rintro ⟨i,hi,hq⟩
    have he : ρ.symm (z.2-f z.1)=i := by
      apply ρ.injective
      rw [ρ.apply_symm_apply,hi]
      ring
    rwa [he]
  · intro hq
    refine ⟨ρ.symm (z.2-f z.1),?_,hq⟩
    rw [ρ.apply_symm_apply]
    ring

/-- No fine point is permanently excluded independently of the coarse
family: nonempty coarse colors give full fine projection. This is not
being asserted as asymptotic equidistribution of the natural set. -/
lemma infiniteGraphSet_full_projection (f : F → F) {n : ℕ} (ρ : Fin n ≃ F)
    (B : α → Set ℕ) (hB : ∀ a, (B a).Nonempty) (ω : Fin n → α) :
    Prod.fst '' infiniteGraphSet f ρ B ω=Set.univ := by
  ext z
  simp only [Set.mem_univ,iff_true]
  obtain ⟨q,hq⟩ := hB (ω (ρ.symm (z.2-f z.1)))
  refine ⟨(z,(q:ℤ)),?_,rfl⟩
  rw [mem_infiniteGraphSet]
  simpa only [natSupport,Set.mem_setOf_eq,Int.natCast_nonneg,Int.toNat_natCast,true_and] using hq

end Erdos66UniversalCompleteAccuracy
