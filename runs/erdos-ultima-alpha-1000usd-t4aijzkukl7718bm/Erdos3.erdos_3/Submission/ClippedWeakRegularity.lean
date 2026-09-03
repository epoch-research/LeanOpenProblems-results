import FormalConjecturesUtil

/-! A finite weak-regularity energy argument with clipping. Bounded correlation
detectors produce bounded approximants, with the number of steps controlled by
the original mean density divided by the squared correlation gain. -/
namespace Erdos3ClippedWeakRegularity
open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

noncomputable def clip01 (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clip01_bounds (x : ℝ) : 0 ≤ clip01 x ∧ clip01 x ≤ 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

lemma clip01_sq_dist {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (x : ℝ) :
    (a-clip01 x)^2 ≤ (a-x)^2 := by
  by_cases hx : x ≤ 0
  · have he : clip01 x = 0 := by
      rw [clip01,min_eq_right (by linarith),max_eq_left hx]
    rw [he,sub_zero]
    nlinarith
  · by_cases hx1 : 1 ≤ x
    · have he : clip01 x = 1 := by
        rw [clip01,min_eq_left hx1,max_eq_right (by norm_num)]
      rw [he]
      nlinarith
    · have he : clip01 x = x := by
        rw [clip01,min_eq_right (le_of_not_ge hx1),max_eq_right (le_of_not_ge hx)]
      rw [he]

lemma clip01_abs_sub (x y : ℝ) : |clip01 x-clip01 y| ≤ |x-y| := by
  have hm := abs_min_sub_min_le_max (1 : ℝ) x 1 y
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (x-y))] at hm
  have hx := abs_max_sub_max_le_max (0 : ℝ) (min 1 x) 0 (min 1 y)
  simp only [sub_self,abs_zero,max_eq_right (abs_nonneg (min 1 x-min 1 y))] at hx
  exact hx.trans hm

variable {X : Type*} [Fintype X] [Nonempty X]

noncomputable def squaredError (f g : X → ℝ) : ℝ := 𝔼 x : X, (f x-g x)^2

lemma squaredError_nonneg (f g : X → ℝ) : 0 ≤ squaredError f g := expect_nonneg (fun _ _ ↦ sq_nonneg _)

lemma squaredError_zero_le_mean (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    squaredError f 0 ≤ 𝔼 x : X, f x := by
  apply expect_le_expect
  intro x _
  simp only [Pi.zero_apply,sub_zero]
  nlinarith [(hf x).1,(hf x).2]

lemma clip_step_decrease (f g ψ : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hψ : ∀ x, |ψ x| ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcorr : ρ ≤ 𝔼 x : X, (f x-g x)*ψ x) :
    squaredError f (fun x ↦ clip01 (g x+ρ*ψ x)) ≤ squaredError f g-ρ^2 := by
  have hnorm : (𝔼 x : X, (ψ x)^2) ≤ 1 := by
    calc
      _ ≤ 𝔼 _x : X, (1 : ℝ) := expect_le_expect (fun x _ ↦ by
        have hx := abs_le.mp (hψ x)
        nlinarith [hx.1,hx.2])
      _ = _ := Fintype.expect_const _
  have he (x : X) : (f x-(g x+ρ*ψ x))^2 =
      (f x-g x)^2-2*ρ*((f x-g x)*ψ x)+ρ^2*(ψ x)^2 := by ring
  calc
    _ ≤ 𝔼 x : X, (f x-(g x+ρ*ψ x))^2 :=
      expect_le_expect (fun x _ ↦ clip01_sq_dist (hf x).1 (hf x).2 _)
    _ = squaredError f g-2*ρ*(𝔼 x : X, (f x-g x)*ψ x)+ρ^2*(𝔼 x : X, (ψ x)^2) := by
      simp only [he,expect_add_distrib,expect_sub_distrib,← mul_expect,squaredError]
    _ ≤ squaredError f g-ρ^2 := by
      have hc := mul_le_mul_of_nonneg_left hcorr (by positivity : 0 ≤ 2*ρ)
      have hn := mul_le_mul_of_nonneg_left hnorm (sq_nonneg ρ)
      nlinarith only [hc,hn]

noncomputable def clippedSum (ρ : ℝ) : List (X → ℝ) → X → ℝ
  | [] => 0
  | ψ::l => fun x ↦ clip01 (clippedSum ρ l x+ρ*ψ x)

lemma clippedSum_bounds (ρ : ℝ) (l : List (X → ℝ)) (x : X) :
    0 ≤ clippedSum ρ l x ∧ clippedSum ρ l x ≤ 1 := by
  cases l with
  | nil => simp [clippedSum]
  | cons ψ l => exact clip01_bounds _

lemma residual_bound (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (ρ : ℝ) (l : List (X → ℝ)) (x : X) : |f x-clippedSum ρ l x| ≤ 1 := by
  have hg := clippedSum_bounds ρ l x
  exact abs_le.mpr ⟨by linarith [(hf x).1],by linarith [(hf x).2]⟩

/-- At each stage either the residual is acceptable or the squared error has
paid for every selected detector. No boundedness of the un-clipped sum is used. -/
lemma regularize_or_energy (T : Set (X → ℝ)) (Good : (X → ℝ) → Prop)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hT : ∀ ψ ∈ T, ∀ x, |ψ x| ≤ 1)
    (hdetect : ∀ r : X → ℝ, (∀ x, |r x| ≤ 1) → ¬ Good r →
      ∃ ψ ∈ T, ρ ≤ 𝔼 x : X, r x*ψ x) (N : ℕ) :
    (∃ l : List (X → ℝ), l.length ≤ N ∧ (∀ ψ ∈ l, ψ ∈ T) ∧
      Good (fun x ↦ f x-clippedSum ρ l x)) ∨
    (∃ l : List (X → ℝ), l.length = N ∧ (∀ ψ ∈ l, ψ ∈ T) ∧
      squaredError f (clippedSum ρ l)+(N : ℝ)*ρ^2 ≤ squaredError f 0) := by
  induction N with
  | zero =>
    right
    refine ⟨[],rfl,by simp,?_⟩
    simp only [clippedSum,Nat.cast_zero,zero_mul,add_zero,le_refl]
  | succ N ih =>
    rcases ih with ⟨l,hlen,hl,hgood⟩ | ⟨l,hlen,hl,henergy⟩
    · exact Or.inl ⟨l,by omega,hl,hgood⟩
    · by_cases hg : Good (fun x ↦ f x-clippedSum ρ l x)
      · exact Or.inl ⟨l,by omega,hl,hg⟩
      · obtain ⟨ψ,hψ,hcorr⟩ := hdetect _ (residual_bound f hf ρ l) hg
        right
        refine ⟨ψ::l,by simp [hlen],?_,?_⟩
        · intro φ hφ
          rcases List.mem_cons.mp hφ with hφ | hφ
          · exact hφ ▸ hψ
          · exact hl φ hφ
        · have hd := clip_step_decrease f (clippedSum ρ l) ψ hf (hT ψ hψ) hρ hcorr
          change squaredError f (fun x ↦ clip01 (clippedSum ρ l x+ρ*ψ x))+(N+1 : ℕ)*ρ^2 ≤ _
          rw [Nat.cast_add,Nat.cast_one]
          linarith

/-- Quantitative weak regularity from an explicit correlation detector. The
number of tests is bounded by mean(f)/rho^2, with one rounding step. -/
theorem clipped_weak_regularity (T : Set (X → ℝ)) (Good : (X → ℝ) → Prop)
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hT : ∀ ψ ∈ T, ∀ x, |ψ x| ≤ 1)
    (hdetect : ∀ r : X → ℝ, (∀ x, |r x| ≤ 1) → ¬ Good r →
      ∃ ψ ∈ T, ρ ≤ 𝔼 x : X, r x*ψ x) :
    ∃ l : List (X → ℝ), l.length ≤ ⌈(𝔼 x : X, f x)/ρ^2⌉₊+1 ∧
      (∀ ψ ∈ l, ψ ∈ T) ∧ Good (fun x ↦ f x-clippedSum ρ l x) := by
  let N := ⌈(𝔼 x : X, f x)/ρ^2⌉₊+1
  rcases regularize_or_energy T Good f hf hρ.le hT hdetect N with h | ⟨l,_,_,he⟩
  · exact h
  · have hN : (𝔼 x : X, f x)/ρ^2 < (N : ℝ) := by
      apply (Nat.le_ceil _).trans_lt
      dsimp only [N]
      rw [Nat.cast_add,Nat.cast_one]
      linarith
    have hh := (div_lt_iff₀ (sq_pos_of_pos hρ)).mp hN
    have h0 := squaredError_nonneg f (clippedSum ρ l)
    have hf0 := squaredError_zero_le_mean f hf
    exfalso
    linarith

#print axioms clip_step_decrease
#print axioms clipped_weak_regularity
end Erdos3ClippedWeakRegularity
