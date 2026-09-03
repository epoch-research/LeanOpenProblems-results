import Submission.BinaryZeroSpanExplore

/-! A binary coordinate family has a vector supporting a large subspace.
This is the linear-algebraic ingredient of a natural digit-sum peak. -/
namespace Erdos66BinarySupportedSubspace
open Module Erdos66BinaryZeroSpan
open scoped Classical
set_option maxHeartbeats 1400000
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- There is a vector c and a subspace of codimension at most n/3 whose
coordinates vanish wherever c's coordinates vanish. -/
theorem exists_supported_subspace {n : ℕ} (ℓ : Fin n → Module.Dual F V) :
    ∃ c : V, ∃ W : Submodule F V,
      finrank F V-n/3≤finrank F W ∧ c∈W ∧
      ∀ x∈W, ∀ i, ℓ i c=0 → ℓ i x=0 := by
  let S : Finset (Module.Dual F V) := Finset.univ.image ℓ
  obtain ⟨f,hf⟩ := exists_small_zero_span S
  let c := (Module.evalEquiv F V).symm f
  have heval (φ : Module.Dual F V) : f φ=φ c := by
    have hh := congrArg (fun ψ : Module.Dual F (Module.Dual F V) ↦ ψ φ)
      ((Module.evalEquiv F V).apply_symm_apply f)
    simpa only [Module.evalEquiv_apply,Module.Dual.eval_apply] using hh.symm
  let Z := zeroSpan S f
  let W := Z.dualCoannihilator
  have hcS : S.card≤n := by
    exact (Finset.card_image_le).trans_eq (by simp)
  have hdimZ : finrank F Z≤n/3 := by
    change 3*finrank F Z≤S.card at hf
    omega
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq Z
  have hker : Z≤f.ker := by
    apply Submodule.span_le.mpr
    intro φ hφ
    change φ∈S.filter (fun ψ : Module.Dual F V ↦ f ψ=0) at hφ
    change f φ=0
    exact (Finset.mem_filter.mp hφ).2
  have hc : c∈W := by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    rw [←heval]
    exact hker hφ
  refine ⟨c,W,by dsimp only [W]; omega,hc,fun x hx i hic ↦ ?_⟩
  have hi : ℓ i∈Z := by
    apply Submodule.subset_span
    change ℓ i∈S.filter (fun ψ : Module.Dual F V ↦ f ψ=0)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,?_⟩
    rw [heval,hic]
  exact (Submodule.mem_dualCoannihilator x).mp hx (ℓ i) hi

theorem code_supported_subspace {n : ℕ} (C : Submodule F (Fin n → F)) :
    ∃ c : C, ∃ W : Submodule F C,
      finrank F C-n/3≤finrank F W ∧ c∈W ∧
      ∀ x∈W, ∀ i, c.val i=0 → x.val i=0 := by
  exact exists_supported_subspace (fun i ↦ (LinearMap.proj i).comp C.subtype)

end Erdos66BinarySupportedSubspace
