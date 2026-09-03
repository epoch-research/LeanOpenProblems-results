import Submission.ConvexLeastSquares

/-! Compact convex classes of [0,1]-valued functions whose changes are
controlled by weighted test coordinates. Adding a test enlarges the class and
admits the usual clipped update, while least-squares projections remain bounded. -/
namespace Erdos3BoundedFeatureClasses
open Finset Erdos3ClippedWeakRegularity Erdos3ConvexLeastSquares
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {X : Type*} [Fintype X] [Nonempty X]

noncomputable def boundedClass (d : X → X → ℝ) : Set (X → ℝ) :=
  {g | (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ ∀ x y, |g x-g y| ≤ d x y}

lemma boundedClass_compact (d : X → X → ℝ) : IsCompact (boundedClass d) := by
  have hcube : IsCompact {g : X → ℝ | ∀ x, g x ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite (fun _ ↦ isCompact_Icc)
  have hclosed : IsClosed {g : X → ℝ | ∀ x y, |g x-g y| ≤ d x y} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    exact isClosed_le (by fun_prop) continuous_const
  exact hcube.inter_right hclosed

lemma boundedClass_convex (d : X → X → ℝ) : Convex ℝ (boundedClass d) := by
  intro g hg h hh a b ha hb hab
  constructor
  · intro x
    change 0 ≤ a*g x+b*h x ∧ a*g x+b*h x ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg ha (hg.1 x).1) (mul_nonneg hb (hh.1 x).1)
    · calc
        _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left (hg.1 x).2 ha)
          (mul_le_mul_of_nonneg_left (hh.1 x).2 hb)
        _ = 1 := by simpa only [mul_one] using hab
  · intro x y
    change |(a*g x+b*h x)-(a*g y+b*h y)| ≤ d x y
    calc
      _ = |a*(g x-g y)+b*(h x-h y)| := by congr 1; ring
      _ ≤ |a| * |g x-g y|+|b| * |h x-h y| := by
        simpa only [abs_mul] using abs_add_le (a*(g x-g y)) (b*(h x-h y))
      _ ≤ a*d x y+b*d x y := by
        rw [abs_of_nonneg ha,abs_of_nonneg hb]
        exact add_le_add (mul_le_mul_of_nonneg_left (hg.2 x y) ha)
          (mul_le_mul_of_nonneg_left (hh.2 x y) hb)
      _ = d x y := by rw [← add_mul,hab,one_mul]

lemma boundedClass_zero (d : X → X → ℝ) (hd : ∀ x y, 0 ≤ d x y) :
    (0 : X → ℝ) ∈ boundedClass d := by
  constructor
  · intro x; norm_num
  · intro x y; simpa using hd x y

lemma boundedClass_mono {d e : X → X → ℝ} (hde : ∀ x y, d x y ≤ e x y) :
    boundedClass d ⊆ boundedClass e := by
  intro g hg
  exact ⟨hg.1,fun x y ↦ (hg.2 x y).trans (hde x y)⟩

lemma clipped_update_mem {d : X → X → ℝ} {g : X → ℝ} (hg : g ∈ boundedClass d)
    (ψ : X → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (fun x ↦ clip01 (g x+ρ*ψ x)) ∈ boundedClass (fun x y ↦ d x y+ρ*|ψ x-ψ y|) := by
  refine ⟨fun x ↦ clip01_bounds _,?_⟩
  intro x y
  calc
    _ ≤ |(g x+ρ*ψ x)-(g y+ρ*ψ y)| := clip01_abs_sub _ _
    _ = |(g x-g y)+ρ*(ψ x-ψ y)| := by congr 1; ring
    _ ≤ |g x-g y|+ρ*|ψ x-ψ y| := by
      simpa only [abs_mul,abs_of_nonneg hρ] using abs_add_le (g x-g y) (ρ*(ψ x-ψ y))
    _ ≤ _ := add_le_add (hg.2 x y) le_rfl

abbrev Feature (X : Type*) := NNReal × (X → ℝ)

noncomputable def featureDistance (l : List (Feature X)) (x y : X) : ℝ :=
  (l.map (fun p ↦ (p.1 : ℝ)*|p.2 x-p.2 y|)).sum

noncomputable def featureClass (l : List (Feature X)) : Set (X → ℝ) := boundedClass (featureDistance l)

lemma featureDistance_nonneg (l : List (Feature X)) (x y : X) : 0 ≤ featureDistance l x y := by
  unfold featureDistance
  apply List.sum_nonneg
  intro a ha
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
  positivity

lemma featureClass_zero (l : List (Feature X)) : (0 : X → ℝ) ∈ featureClass l :=
  boundedClass_zero _ (featureDistance_nonneg l)

lemma featureClass_compact (l : List (Feature X)) : IsCompact (featureClass l) := boundedClass_compact _
lemma featureClass_convex (l : List (Feature X)) : Convex ℝ (featureClass l) := boundedClass_convex _

lemma featureClass_cons (l : List (Feature X)) (p : Feature X) : featureClass l ⊆ featureClass (p::l) := by
  apply boundedClass_mono
  intro x y
  change featureDistance l x y ≤ (p.1 : ℝ)*|p.2 x-p.2 y|+featureDistance l x y
  have hp : 0 ≤ (p.1 : ℝ)*|p.2 x-p.2 y| := by positivity
  linarith

lemma featureClass_append (l l' : List (Feature X)) : featureClass l ⊆ featureClass (l'++l) := by
  induction l' with
  | nil => exact Set.Subset.rfl
  | cons p l' ih => exact ih.trans (featureClass_cons (l'++l) p)

lemma clipped_update_feature {l : List (Feature X)} {g : X → ℝ} (hg : g ∈ featureClass l)
    (ψ : X → ℝ) (ρ : NNReal) :
    (fun x ↦ clip01 (g x+(ρ : ℝ)*ψ x)) ∈ featureClass ((ρ,ψ)::l) := by
  have h := clipped_update_mem hg ψ ρ.coe_nonneg
  convert h using 1
  ext q
  simp only [featureClass,boundedClass,featureDistance,List.map_cons,List.sum_cons,add_comm]

lemma exists_feature_minimizer (f : X → ℝ) (l : List (Feature X)) :
    ∃ g ∈ featureClass l, ∀ h ∈ featureClass l, squaredError f g ≤ squaredError f h :=
  exists_least_squares f (featureClass_compact l) ⟨0,featureClass_zero l⟩

/-- Add one detecting test, then project onto the enlarged convex feature class.
The projection improves at least as much as the clipped candidate. -/
theorem projected_test_step (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (l : List (Feature X)) (g : X → ℝ) (hg : g ∈ featureClass l)
    (ψ : X → ℝ) (hψ : ∀ x, |ψ x| ≤ 1) (ρ : NNReal)
    (hcorr : (ρ : ℝ) ≤ 𝔼 x : X, (f x-g x)*ψ x) :
    ∃ g' ∈ featureClass ((ρ,ψ)::l),
      (∀ h ∈ featureClass ((ρ,ψ)::l), squaredError f g' ≤ squaredError f h) ∧
      squaredError f g' ≤ squaredError f g-(ρ : ℝ)^2 ∧
      squaredError g g' ≤ squaredError f g-squaredError f g' := by
  obtain ⟨g',hg',hmin⟩ := exists_feature_minimizer f ((ρ,ψ)::l)
  have hc := hmin _ (clipped_update_feature hg ψ ρ)
  refine ⟨g',hg',hmin,hc.trans (clip_step_decrease f g ψ hf hψ ρ.coe_nonneg hcorr),?_⟩
  exact nested_minimizers_close f g g' (featureClass_cons l (ρ,ψ))
    (featureClass_convex _) hg hg' hmin

#print axioms featureClass_compact
#print axioms projected_test_step
end Erdos3BoundedFeatureClasses
