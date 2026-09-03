import Submission.AdaptiveStrongRegularity

/-! Strong regularity retaining explicit provenance of every test and a
cumulative stage cost. A stage is used only once, and adds at most its weak
regularity block size, which permits summably allocated localization errors. -/
namespace Erdos3BudgetedStrongRegularity
open Finset Erdos3AdaptiveStrongRegularity Erdos3ProjectedWeakRegularity
  Erdos3BoundedFeatureClasses Erdos3ClippedWeakRegularity Erdos3ConvexLeastSquares
open scoped BigOperators Classical
set_option maxHeartbeats 7000000

abbrev TaggedTest (X : Type*) := ℕ × (X → ℝ)

noncomputable def taggedFeatures {X : Type*} (ρ : ℕ → NNReal) (t : List (TaggedTest X)) :
    List (Feature X) := t.map (fun p ↦ (ρ p.1,p.2))

noncomputable def tagCost {X : Type*} (c : ℕ → ℝ) (t : List (TaggedTest X)) : ℝ :=
  (t.map (fun p ↦ c p.1)).sum

noncomputable def prefixCost (B : ℕ → ℕ) (c : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ range m, (B j : ℝ)*c j

lemma prefixCost_mono (B : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) :
    Monotone (prefixCost B c) := by
  intro m n hmn
  exact sum_le_sum_of_subset_of_nonneg (range_mono hmn)
    (fun j _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (hc j))

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Coarse tests have strict prior-stage labels. Their total cost is bounded
by the sum of stage block-size times per-test cost, not by a guessed bound on
how many tests could have come from each stage. -/
theorem budgeted_strong_regularity (T : ℕ → Set (X → ℝ))
    (Good : ℕ → (X → ℝ) → Prop) (ρ : ℕ → NNReal)
    (hρ : ∀ m, 0 < (ρ m : ℝ))
    (hT : ∀ m ψ, ψ ∈ T m → ∀ x, |ψ x| ≤ 1)
    (hdetect : ∀ m, ∀ r : X → ℝ, (∀ x, |r x| ≤ 1) → ¬ Good m r →
      ∃ ψ ∈ T m, (ρ m : ℝ) ≤ 𝔼 x : X, r x*ψ x)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j)
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : (𝔼 x : X, f x)/ε^2 < (N : ℝ)) :
    ∃ m : ℕ, ∃ t : List (TaggedTest X), ∃ g g' : X → ℝ,
      m ≤ complexityBudget (blockSize f ρ) N ∧ t.length ≤ m ∧
      (∀ p ∈ t, p.1 < m ∧ p.2 ∈ T p.1) ∧
      tagCost c t ≤ prefixCost (blockSize f ρ) c m ∧
      IsFeatureMinimizer f (taggedFeatures ρ t) g ∧
      (∀ x, 0 ≤ g' x ∧ g' x ≤ 1) ∧
      Good m (fun x ↦ f x-g' x) ∧ squaredError g g' ≤ ε^2 := by
  let M : ℕ → ℕ := complexityBudget (blockSize f ρ)
  let State (n : ℕ) := {p : List (TaggedTest X) × (X → ℝ) //
    IsFeatureMinimizer f (taggedFeatures ρ p.1) p.2 ∧ p.1.length ≤ M n ∧
      (∀ a ∈ p.1, a.1 < M n ∧ a.2 ∈ T a.1) ∧
      tagCost c p.1 ≤ prefixCost (blockSize f ρ) c (M n)}
  obtain ⟨g₀,hg₀,hmin₀⟩ := exists_feature_minimizer f ([] : List (Feature X))
  let s₀ : State 0 := ⟨([],g₀),⟨hg₀,hmin₀⟩,le_refl 0,by simp,by simp [tagCost,prefixCost,M,complexityBudget]⟩
  have hnext (n : ℕ) (s : State n) : ∃ s' : State (n+1),
      Good (M n) (fun x ↦ f x-s'.val.2 x) ∧
      squaredError s.val.2 s'.val.2 ≤ squaredError f s.val.2-squaredError f s'.val.2 := by
    obtain ⟨u,g,hlen,hu,hmin,hgood,hclose⟩ := projected_weak_refinement
      (T (M n)) (Good (M n)) f hf (ρ (M n)) (hρ (M n))
      (hT (M n)) (hdetect (M n)) (taggedFeatures ρ s.val.1) s.val.2 s.property.1
    let t' := u.map (fun ψ ↦ (M n,ψ))++s.val.1
    have hfeat : taggedFeatures ρ t' =
        extendFeatures (ρ (M n)) u (taggedFeatures ρ s.val.1) := by
      simp only [t',taggedFeatures,extendFeatures,List.map_append,List.map_map,Function.comp_def]
    have hMM : M n ≤ M (n+1) := complexityBudget_mono _ (Nat.le_succ n)
    have hMMlt : M n < M (n+1) := by
      change M n < M n+blockSize f ρ (M n)
      unfold blockSize
      omega
    have hlen' : t'.length ≤ M (n+1) := by
      change _ ≤ M n+blockSize f ρ (M n)
      simp only [t',List.length_append,List.length_map]
      have hs := s.property.2.1
      change u.length ≤ blockSize f ρ (M n) at hlen
      omega
    have hcert : ∀ p ∈ t', p.1 < M (n+1) ∧ p.2 ∈ T p.1 := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨ψ,hψ,rfl⟩ := List.mem_map.mp hp
        exact ⟨hMMlt,hu ψ hψ⟩
      · have hp' := s.property.2.2.1 p hp
        exact ⟨hp'.1.trans_le hMM,hp'.2⟩
    have hcost : tagCost c t' ≤ prefixCost (blockSize f ρ) c (M (n+1)) := by
      have he : tagCost c t' = (u.length : ℝ)*c (M n)+tagCost c s.val.1 := by
        simp [tagCost,t',List.map_map,Function.comp_def]
      rw [he]
      have hlenR : (u.length : ℝ) ≤ blockSize f ρ (M n) := by exact_mod_cast hlen
      calc
        _ ≤ (blockSize f ρ (M n) : ℝ)*c (M n)+prefixCost (blockSize f ρ) c (M n) :=
          add_le_add (mul_le_mul_of_nonneg_right hlenR (hc _)) s.property.2.2.2
        _ = prefixCost (blockSize f ρ) c (M n+1) := by simp only [prefixCost,sum_range_succ]; ring
        _ ≤ _ := prefixCost_mono _ c hc (Nat.succ_le_of_lt hMMlt)
    refine ⟨⟨(t',g),?_,hlen',hcert,hcost⟩,hgood,hclose⟩
    rw [hfeat]
    exact hmin
  choose next hnextGood hnextClose using hnext
  let state : (n : ℕ) → State n := fun n ↦ Nat.rec s₀ (fun n s ↦ next n s) n
  let g : ℕ → X → ℝ := fun n ↦ (state n).val.2
  have hstep (n : ℕ) : squaredError (g n) (g (n+1)) ≤ squaredError f (g n)-squaredError f (g (n+1)) :=
    hnextClose n (state n)
  have hinit : squaredError f (g 0) ≤ squaredError f 0 := hmin₀ 0 (featureClass_zero [])
  obtain ⟨i,hi,hsmall⟩ := exists_small_nested_step f g hf hinit hε hN (fun n _ ↦ hstep n)
  refine ⟨M i,(state i).val.1,g i,g (i+1),complexityBudget_mono _ hi.le,
    (state i).property.2.1,(state i).property.2.2.1,(state i).property.2.2.2,
    (state i).property.1,(state (i+1)).property.1.1.1,hnextGood i (state i),hsmall⟩

#print axioms budgeted_strong_regularity
end Erdos3BudgetedStrongRegularity
