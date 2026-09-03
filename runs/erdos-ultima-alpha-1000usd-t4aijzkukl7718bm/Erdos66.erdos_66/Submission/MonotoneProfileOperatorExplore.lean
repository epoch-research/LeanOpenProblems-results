import Submission.UniversalHeightPaletteExplore
import Submission.BoundedProfileQuantizationExplore

/-! A single finite, pointwise-causal rounding operator for all bounded
monotone profiles. The height range is fixed before the modulus is chosen. -/
namespace Erdos66MonotoneProfileOperator
open AdditiveCombinatorics Erdos66UniversalHeightPalette Erdos66BoundedProfileQuantization
  Erdos66StepConvolutionBridge Erdos66MonotoneIntervalFibers
  Erdos66IntegerPaletteAssembly Erdos66IntegerPaletteSlices
open scoped Classical
set_option maxHeartbeats 3200000

noncomputable def realize (M : ℕ) (e : ℝ) (J : ℕ)
    (C : Fin (J+1) → Finset (ZMod M)) (f : ℕ → ℝ) : Finset ℕ :=
  (Finset.range M).filter (fun x ↦ (x:ZMod M)∈C (binIndex e J (f x)))

lemma realize_prefix (M : ℕ) (e : ℝ) (J : ℕ)
    (C : Fin (J+1) → Finset (ZMod M)) (f g : ℕ → ℝ) (L : ℕ)
    (hfg : ∀ x<L, f x=g x) : ∀ x<L, x∈realize M e J C f ↔ x∈realize M e J C g := by
  intro x hx
  simp only [realize,Finset.mem_filter,Finset.mem_range,hfg x hx]

lemma realize_eq_assembled (M : ℕ) [NeZero M] (e : ℝ) (J : ℕ)
    (C : Fin (J+1) → Finset (ZMod M)) (f : ℕ → ℝ) (a b : Fin (J+1) → ℕ)
    (hmem : ∀ j x, a j ≤ x ∧ x<b j ↔ x<M ∧ (binIndex e J (f x)).val=j.val) :
    realize M e J C f = assembled M Finset.univ C a b := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxM,hxC⟩ := Finset.mem_filter.mp hx
    have hxM' := Finset.mem_range.mp hxM
    let j := binIndex e J (f x)
    have hj := (hmem j x).mpr ⟨hxM',rfl⟩
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,
      (mem_slice M (C j) (a j) (b j) x).mpr ⟨hxM',hj.1,hj.2,hxC⟩⟩
  · intro hx
    obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hxM,hxa,hxb,hxC⟩ := (mem_slice M (C j) (a j) (b j) x).mp hx
    have he : binIndex e J (f x)=j := Fin.ext ((hmem j x).mp ⟨hxa,hxb⟩).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxM,by rwa [he]⟩

lemma stepFunction_bin (M : ℕ) (e : ℝ) (J : ℕ) (f : ℕ → ℝ)
    (a b : Fin (J+1) → ℕ)
    (hmem : ∀ j x, a j ≤ x ∧ x<b j ↔ x<M ∧ (binIndex e J (f x)).val=j.val)
    (x : ℕ) (hx : x<M) :
    stepFunction Finset.univ (gridWeight e) a b x=gridWeight e (binIndex e J (f x)) := by
  have he (j : Fin (J+1)) : (a j ≤ x ∧ x<b j) ↔ j=binIndex e J (f x) := by
    rw [hmem]
    constructor
    · intro hh
      exact Fin.ext hh.2.symm
    · intro hh
      subst j
      exact ⟨hx,rfl⟩
  simp only [stepFunction,he,Finset.sum_ite_eq',Finset.mem_univ,if_true]

lemma bin_convolution_budget (c δ W e : ℝ) (hc : 0<c) (hδ : 0<δ) (hW : 1 ≤ W)
    (he : 0 ≤ e) (he1 : e ≤ 1)
    (hbudget : 100*e*(c+1)*(W+1)^2 ≤ δ) :
    c*((1+e)^2-1)*W^2 ≤ δ/2 := by
  have hfactor : (1+e)^2-1 ≤ 3*e := by nlinarith
  have hWsq : W^2 ≤ (W+1)^2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hfactor (mul_nonneg hc.le (sq_nonneg W))
  have h2 := mul_le_mul_of_nonneg_left hWsq (show 0 ≤ 3*e*c by positivity)
  have h3 := mul_le_mul_of_nonneg_left (show c ≤ c+1 by linarith)
    (show 0 ≤ 3*e*(W+1)^2 by positivity)
  nlinarith only [h1,h2,h3,hbudget,hδ]

/-- One map, selected before any profile, rounds EVERY bounded antitone
profile with an all-target normalized convolution error. The map preserves
agreement of profile prefixes exactly, including their representation counts. -/
theorem exists_bounded_monotone_rounding_operator (c δ W : ℝ)
    (hc : 0<c) (hδ : 0<δ) (hW : 1 ≤ W) (N₀ : ℕ) :
    ∃ M : ℕ, N₀<M ∧ 1<M ∧ ∃ Φ : (ℕ → ℝ) → Finset ℕ,
      (∀ f, Φ f ⊆ Finset.range M) ∧
      (∀ f g L, (∀ x<L, f x=g x) → ∀ x<L, x∈Φ f ↔ x∈Φ g) ∧
      (∀ f g L, (∀ x<L, f x=g x) → ∀ n<L,
        sumRep (Φ f:Set ℕ) n=sumRep (Φ g:Set ℕ) n) ∧
      ∀ f : ℕ → ℝ, (∀ x<M, 1 ≤ f x ∧ f x ≤ W) →
        (∀ x y, x ≤ y → y<M → f y ≤ f x) →
        ∀ n : ℕ, |(sumRep (Φ f:Set ℕ) n:ℝ)/Real.log M-c*normConv M f n| ≤ δ := by
  let e := min 1 (δ/(100*(c+1)*(W+1)^2))
  have he : 0<e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := min_le_left _ _
  have hbudget : 100*e*(c+1)*(W+1)^2 ≤ δ := by
    have hh := (le_div_iff₀ (by positivity : 0<100*(c+1)*(W+1)^2)).mp
      (min_le_right 1 (δ/(100*(c+1)*(W+1)^2)))
    dsimp [e]
    nlinarith only [hh]
  let J := ⌈(W-1)/e⌉₊
  obtain ⟨M,hMN,hM1,hM,C,hC⟩ := exists_universal_height_realizer
    (Finset.univ : Finset (Fin (J+1))) (gridWeight e)
    (fun i hi ↦ gridWeight_ge_one e he.le i) c (δ/2) hc (by positivity) N₀
  letI := hM
  let Φ := realize M e J C
  have hp : ∀ f g L, (∀ x<L, f x=g x) → ∀ x<L, x∈Φ f ↔ x∈Φ g :=
    realize_prefix M e J C
  refine ⟨M,hMN,hM1,Φ,fun f ↦ Finset.filter_subset _ _,hp,?_,?_⟩
  · intro f g L hfg n hn
    apply Erdos66Compactness.sumRep_congr_below
    intro x hx
    exact hp f g L hfg x (by omega)
  · intro f hf hanti n
    let idx : ℕ → ℕ := fun x ↦ (binIndex e J (f x)).val
    have hianti : ∀ x y, x ≤ y → y<M → idx y ≤ idx x := by
      intro x y hxy hy
      exact Fin.le_iff_val_le_val.mp (binIndex_mono e he J (hanti x y hxy hy))
    obtain ⟨a,b,hab,hmem,hdisj⟩ := exists_interval_fibers M (J+1) idx hianti
    have hb : ∀ i∈(Finset.univ : Finset (Fin (J+1))), b i ≤ M := fun i hi ↦ (hab i).2
    have hround := hC a b hb (fun i hi j hj hij ↦ hdisj i j hij) n
    have hrealize := realize_eq_assembled M e J C f a b hmem
    change Φ f=assembled M Finset.univ C a b at hrealize
    rw [←hrealize,weightedProfile_eq_normConv M Finset.univ (gridWeight e) a b hb n] at hround
    let g := stepFunction Finset.univ (gridWeight e) a b
    have hg : ∀ x<M, 0 ≤ f x ∧ f x ≤ W ∧ f x ≤ g x ∧ g x ≤ (1+e)*f x := by
      intro x hx
      have hfx := hf x hx
      have hbin := bin_weight_bracket e W (f x) he hfx.1 hfx.2
      have hstep := stepFunction_bin M e J f a b hmem x hx
      change g x=gridWeight e (binIndex e J (f x)) at hstep
      rw [hstep]
      exact ⟨by linarith,hfx.2,hbin⟩
    have hdiff := normConv_quantization_error M f g W (1+e) (by linarith) (by linarith) hg n
    have hscalar := mul_le_mul_of_nonneg_left hdiff hc.le
    have herr : |c*normConv M g n-c*normConv M f n| ≤ δ/2 := by
      rw [←mul_sub,abs_mul,abs_of_pos hc]
      have hcost := bin_convolution_budget c δ W e hc hδ hW he.le he1 hbudget
      nlinarith only [hscalar,hcost]
    have htri := abs_sub_le ((sumRep (Φ f:Set ℕ) n:ℝ)/Real.log M)
      (c*normConv M g n) (c*normConv M f n)
    change |(sumRep (Φ f:Set ℕ) n:ℝ)/Real.log M-c*normConv M g n| ≤ δ/2 at hround
    linarith

end Erdos66MonotoneProfileOperator
