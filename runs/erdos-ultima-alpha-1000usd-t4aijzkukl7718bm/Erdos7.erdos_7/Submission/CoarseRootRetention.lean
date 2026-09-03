import FormalConjecturesUtil

/-! An auxiliary two-branch root estimate. This is not a disproof of Erdos7.
The hypotheses expose the common first ternary digit of two real count
families; the remaining tails need only have mean at most one third. -/
namespace Erdos7CoarseRootRetention
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def retention (a b d : ℝ) : ℝ :=
  max 0 (max 0 (1-a/4) * max 0 (1-b/6) - d/24)

noncomputable def base (y : ℝ) (b : Bool) : ℝ :=
  if b then 1+y else 2-y

lemma base_bounds (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) (b : Bool) :
    base y b ∈ Set.Icc (1:ℝ) 2 := by
  cases b <;> simp only [base, Bool.false_eq_true, if_false, if_true] <;>
    constructor <;> linarith [hy.1, hy.2]

/-- A pointwise affine minorant. Counts and tails are real, not integer. -/
lemma retention_minorant (a b u v d : ℝ)
    (ha : a ∈ Set.Icc (1:ℝ) 2) (hb : b ∈ Set.Icc (1:ℝ) 2)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (24-6*a-4*b+a*b-5*u-3*v-d)/24 ≤ retention (a+u) (b+v) d := by
  let A := 1-a/4
  let B := 1-b/6
  let U := max 0 (1-(a+u)/4)
  let V := max 0 (1-(b+v)/6)
  have hA : 0 ≤ A := by dsimp [A]; linarith [ha.2]
  have hB : 0 ≤ B := by dsimp [B]; linarith [hb.2]
  have hU : 0 ≤ U := le_max_left _ _
  have hV : 0 ≤ V := le_max_left _ _
  have hUA : U ≤ A := max_le hA (by dsimp [A]; linarith)
  have hVB : V ≤ B := max_le hB (by dsimp [B]; linarith)
  have hdu : A-U ≤ u/4 := by
    have := le_max_right 0 (1-(a+u)/4)
    dsimp [A, U]; linarith
  have hdv : B-V ≤ v/6 := by
    have := le_max_right 0 (1-(b+v)/6)
    dsimp [B, V]; linarith
  have hh := mul_nonneg (sub_nonneg.mpr hUA) (sub_nonneg.mpr hVB)
  have hh₁ := mul_le_mul_of_nonneg_left hdu hB
  have hh₂ := mul_le_mul_of_nonneg_left hdv hA
  have hp : A*B-B*u/4-A*v/6 ≤ U*V := by nlinarith
  have hbu := mul_nonneg (sub_nonneg.mpr hb.1) hu
  have hav := mul_nonneg (sub_nonneg.mpr ha.1) hv
  have hr : U*V-d/24 ≤ retention (a+u) (b+v) d := le_max_right _ _
  dsimp [A, B] at hp
  nlinarith

/-- The common coarse branch forces a stronger bilinear mean bound than
independent marginal estimates. The proof interpolates the two endpoints
of the allowable branch-mass interval. -/
lemma coarse_polynomial (t y z : ℝ) (ht : t ∈ Set.Icc (1/3:ℝ) (2/3))
    (hy : y ∈ Set.Icc (0:ℝ) 1) (hz : z ∈ Set.Icc (0:ℝ) 1) :
    17/3 ≤ 10/3+7*t+(4-9*t)*y+(2-5*t)*z+y*z := by
  have hy0 := hy.1
  have hz0 := hz.1
  have h₀ : 0 ≤ y+z/3+y*z := by positivity
  have h₁ : 0 ≤ (1-y)+(1-z)/3+(1-y)*(1-z) := by
    have hy' : 0 ≤ 1-y := by linarith [hy.2]
    have hz' : 0 ≤ 1-z := by linarith [hz.2]
    positivity
  have ha : 0 ≤ 2-3*t := by linarith [ht.2]
  have hb : 0 ≤ 3*t-1 := by linarith [ht.1]
  have hh := add_nonneg (mul_nonneg ha h₀) (mul_nonneg hb h₁)
  nlinarith

lemma branch_mean {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (q : Ω → Bool)
    (hm : (∑ x, μ x) = 1) (y : ℝ) :
    (∑ x, μ x*base y (q x)) =
      2-(∑ x, if q x then μ x else 0)+
      (2*(∑ x, if q x then μ x else 0)-1)*y := by
  have hp (x : Ω) : μ x*base y (q x) =
      (2-y)*μ x+(2*y-1)*(if q x then μ x else 0) := by
    cases h : q x <;> simp [base] <;> ring
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hm]
  ring

lemma branch_product_mean {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (q : Ω → Bool)
    (hm : (∑ x, μ x) = 1) (y z : ℝ) :
    (∑ x, μ x*(base y (q x)*base z (q x))) =
      4-3*(∑ x, if q x then μ x else 0)+
      (3*(∑ x, if q x then μ x else 0)-2)*(y+z)+y*z := by
  have hp (x : Ω) : μ x*(base y (q x)*base z (q x)) =
      (2-y)*(2-z)*μ x+(-3+3*y+3*z)*(if q x then μ x else 0) := by
    cases h : q x <;> simp [base] <;> ring
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hm]
  ring

/-- Shared first-digit structure gives retained mass at least17/72.
This theorem is conditional on the displayed coarse decomposition. It does
not assert its extraction from an arbitrary arithmetic covering system. -/
theorem retained_mass_lower_bound {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (q : Ω → Bool)
    (ht : (∑ x, if q x then μ x else 0) ∈ Set.Icc (1/3:ℝ) (2/3))
    (y z : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) (hz : z ∈ Set.Icc (0:ℝ) 1)
    (u v d : Ω → ℝ) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hmu : (∑ x, μ x*u x) ≤ 1/3) (hmv : (∑ x, μ x*v x) ≤ 1/3)
    (hmd : (∑ x, μ x*d x) ≤ 2) :
    (17/72:ℝ) ≤ ∑ x, μ x*retention (base y (q x)+u x) (base z (q x)+v x) (d x) := by
  have hp := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (retention_minorant (base y (q x)) (base z (q x)) (u x) (v x) (d x)
        (base_bounds y hy (q x)) (base_bounds z hz (q x)) (hu x) (hv x)) (hμ x))
  have he : (∑ x, μ x*((24-6*base y (q x)-4*base z (q x)+
      base y (q x)*base z (q x)-5*u x-3*v x-d x)/24)) =
      (24-6*(∑ x, μ x*base y (q x))-4*(∑ x, μ x*base z (q x))+
      (∑ x, μ x*(base y (q x)*base z (q x)))-5*(∑ x, μ x*u x)-
      3*(∑ x, μ x*v x)-(∑ x, μ x*d x))/24 := by
    calc
      _ = ∑ x, (μ x - (1/4:ℝ)*(μ x*base y (q x)) -
          (1/6:ℝ)*(μ x*base z (q x)) +
          (1/24:ℝ)*(μ x*(base y (q x)*base z (q x))) -
          (5/24:ℝ)*(μ x*u x) - (1/8:ℝ)*(μ x*v x) - (1/24:ℝ)*(μ x*d x)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, hm]
        ring
  rw [he, branch_mean μ q hm y, branch_mean μ q hm z,
    branch_product_mean μ q hm y z] at hp
  have hh := coarse_polynomial _ y z ht hy hz
  nlinarith

/-- A smaller removal count can only increase the retained mass. -/
lemma retention_antitone (a a' b b' d d' : ℝ)
    (ha : a ≤ a') (hb : b ≤ b') (hd : d ≤ d') :
    retention a' b' d' ≤ retention a b d := by
  apply max_le_max le_rfl
  have hA : max 0 (1-a'/4) ≤ max 0 (1-a/4) := max_le_max le_rfl (by linarith)
  have hB : max 0 (1-b'/6) ≤ max 0 (1-b/6) := max_le_max le_rfl (by linarith)
  have hh := mul_le_mul hA hB (le_max_left _ _) (le_max_left _ _)
  linarith

/-- A first-digit family may put some weight on the removed branch. The
missing weight can be assigned to a surviving branch for a majorant. -/
lemma exists_base_majorant (f : Bool → ℝ) (hf : ∀ b, 0 ≤ f b)
    (hs : f false+f true ≤ 1) :
    ∃ y ∈ Set.Icc (0:ℝ) 1, ∀ b, 1+f b ≤ base y b := by
  refine ⟨f true, ⟨hf true, by linarith [hf false]⟩, ?_⟩
  intro b
  cases b <;> simp only [base, Bool.false_eq_true, if_false, if_true] <;> linarith

/-- The estimate also applies to incomplete or averaged families that are
only dominated by a common coarse decomposition. -/
theorem dominated_retained_mass_lower_bound {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hm : (∑ x, μ x) = 1)
    (q : Ω → Bool)
    (ht : (∑ x, if q x then μ x else 0) ∈ Set.Icc (1/3:ℝ) (2/3))
    (f g : Bool → ℝ) (hf : ∀ b, 0 ≤ f b) (hg : ∀ b, 0 ≤ g b)
    (hsf : f false+f true ≤ 1) (hsg : g false+g true ≤ 1)
    (a b u v d : Ω → ℝ) (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (ha : ∀ x, a x ≤ 1+f (q x)+u x) (hb : ∀ x, b x ≤ 1+g (q x)+v x)
    (hmu : (∑ x, μ x*u x) ≤ 1/3) (hmv : (∑ x, μ x*v x) ≤ 1/3)
    (hmd : (∑ x, μ x*d x) ≤ 2) :
    (17/72:ℝ) ≤ ∑ x, μ x*retention (a x) (b x) (d x) := by
  obtain ⟨y,hy,hyf⟩ := exists_base_majorant f hf hsf
  obtain ⟨z,hz,hzg⟩ := exists_base_majorant g hg hsg
  apply (retained_mass_lower_bound μ hμ hm q ht y z hy hz u v d hu hv hmu hmv hmd).trans
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hμ x)
  exact retention_antitone _ _ _ _ _ _
    (by linarith [ha x, hyf (q x)])
    (by linarith [hb x, hzg (q x)]) le_rfl

#print axioms retained_mass_lower_bound
#print axioms dominated_retained_mass_lower_bound
end Erdos7CoarseRootRetention
