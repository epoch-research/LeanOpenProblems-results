import Submission.UniversalMixedHeightExplore
import Submission.MixedProfileQuantizationExplore
import Submission.MonotoneProfileOperatorExplore

/-! One finite causal rounding rule simultaneously controls mixed counts for
ALL pairs of bounded monotone profiles. This is still a same-modulus theorem. -/
namespace Erdos66JointMonotoneProfileOperator
open AdditiveCombinatorics Erdos66UniversalMixedHeight Erdos66MixedProfileQuantization
  Erdos66MixedStepBridge Erdos66MonotoneProfileOperator Erdos66BoundedProfileQuantization
  Erdos66StepConvolutionBridge Erdos66MonotoneIntervalFibers
  Erdos66IntegerPaletteAssembly Erdos66NatPairAlgebra
open scoped Classical
set_option maxHeartbeats 3200000

theorem exists_joint_bounded_monotone_rounding_operator (c δ W : ℝ)
    (hc : 0<c) (hδ : 0<δ) (hW : 1 ≤ W) (N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ 1<M ∧ ∃ Φ : (ℕ → ℝ) → Finset ℕ,
      (∀ f, Φ f ⊆ Finset.range M) ∧
      (∀ f g L, (∀ x<L, f x=g x) → ∀ x<L, x∈Φ f ↔ x∈Φ g) ∧
      (∀ f g L, (∀ x<L, f x=g x) → ∀ n<L,
        sumRep (Φ f:Set ℕ) n=sumRep (Φ g:Set ℕ) n) ∧
      ∀ f g : ℕ → ℝ,
        (∀ x<M, 1 ≤ f x ∧ f x ≤ W) → (∀ x y, x ≤ y → y<M → f y ≤ f x) →
        (∀ x<M, 1 ≤ g x ∧ g x ≤ W) → (∀ x y, x ≤ y → y<M → g y ≤ g x) →
        ∀ n : ℕ, |(pairs (Φ f) (Φ g) n:ℝ)/Real.log M-c*normMixedConv M f g n| ≤ δ := by
  let e := min 1 (δ/(100*(c+1)*(W+1)^2))
  have he : 0<e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := min_le_left _ _
  have hbudget : 100*e*(c+1)*(W+1)^2 ≤ δ := by
    have hh := (le_div_iff₀ (by positivity : 0<100*(c+1)*(W+1)^2)).mp
      (min_le_right 1 (δ/(100*(c+1)*(W+1)^2)))
    dsimp [e]
    nlinarith only [hh]
  let J := ⌈(W-1)/e⌉₊
  obtain ⟨M,hMN,hM1,hM,C,hC⟩ := exists_universal_mixed_height_realizer
    (Finset.univ : Finset (Fin (J+1))) (gridWeight e)
    (fun i hi ↦ gridWeight_ge_one e he.le i) c (δ/2) hc (by positivity) N₀
  letI := hM
  let Φ := realize M e J C
  have hp : ∀ f g L, (∀ x<L, f x=g x) → ∀ x<L, x∈Φ f ↔ x∈Φ g :=
    realize_prefix M e J C
  have hdecomp : ∀ f : ℕ → ℝ, (∀ x<M, 1 ≤ f x ∧ f x ≤ W) →
      (∀ x y, x ≤ y → y<M → f y ≤ f x) →
      ∃ a b : Fin (J+1) → ℕ,
        (∀ i∈(Finset.univ : Finset (Fin (J+1))), b i ≤ M) ∧
        (∀ i∈(Finset.univ : Finset (Fin (J+1))), ∀ j∈(Finset.univ : Finset (Fin (J+1))),
          i ≠ j → b i ≤ a j ∨ b j ≤ a i) ∧
        Φ f=assembled M Finset.univ C a b ∧
        ∀ x<M, 0 ≤ f x ∧ f x ≤ W ∧
          f x ≤ stepFunction Finset.univ (gridWeight e) a b x ∧
          stepFunction Finset.univ (gridWeight e) a b x ≤ (1+e)*f x := by
    intro f hf hanti
    let idx : ℕ → ℕ := fun x ↦ (binIndex e J (f x)).val
    have hianti : ∀ x y, x ≤ y → y<M → idx y ≤ idx x := by
      intro x y hxy hy
      exact Fin.le_iff_val_le_val.mp (binIndex_mono e he J (hanti x y hxy hy))
    obtain ⟨a,b,hab,hmem,hdisj⟩ := exists_interval_fibers M (J+1) idx hianti
    refine ⟨a,b,fun i hi ↦ (hab i).2,fun i hi j hj hij ↦ hdisj i j hij,
      realize_eq_assembled M e J C f a b hmem,?_⟩
    intro x hx
    have hfx := hf x hx
    have hbin := bin_weight_bracket e W (f x) he hfx.1 hfx.2
    rw [stepFunction_bin M e J f a b hmem x hx]
    exact ⟨by linarith,hfx.2,hbin⟩
  refine ⟨M,hMN,hM1,Φ,fun f ↦ Finset.filter_subset _ _,hp,?_,?_⟩
  · intro f g L hfg n hn
    apply Erdos66Compactness.sumRep_congr_below
    intro x hx
    exact hp f g L hfg x (by omega)
  · intro f g hf hanti_f hg hanti_g n
    obtain ⟨a,b,hb,hdisj₁,hf_eq,hF⟩ := hdecomp f hf hanti_f
    obtain ⟨d,k,hk,hdisj₂,hg_eq,hG⟩ := hdecomp g hg hanti_g
    have hround := hC a b d k hb hk hdisj₁ hdisj₂ n
    rw [←hf_eq,←hg_eq,mixedProfile_eq_normMixedConv M Finset.univ (gridWeight e) a b d k hb hk n] at hround
    let F := stepFunction Finset.univ (gridWeight e) a b
    let G := stepFunction Finset.univ (gridWeight e) d k
    have hdiff := normMixedConv_quantization_error M f g F G W (1+e)
      (by linarith) (by linarith) hF hG n
    have hscalar := mul_le_mul_of_nonneg_left hdiff hc.le
    have herr : |c*normMixedConv M F G n-c*normMixedConv M f g n| ≤ δ/2 := by
      rw [←mul_sub,abs_mul,abs_of_pos hc]
      have hcost := bin_convolution_budget c δ W e hc hδ hW he.le he1 hbudget
      nlinarith only [hscalar,hcost]
    have htri := abs_sub_le ((pairs (Φ f) (Φ g) n:ℝ)/Real.log M)
      (c*normMixedConv M F G n) (c*normMixedConv M f g n)
    change |(pairs (Φ f) (Φ g) n:ℝ)/Real.log M-c*normMixedConv M F G n| ≤ δ/2 at hround
    linarith

end Erdos66JointMonotoneProfileOperator
