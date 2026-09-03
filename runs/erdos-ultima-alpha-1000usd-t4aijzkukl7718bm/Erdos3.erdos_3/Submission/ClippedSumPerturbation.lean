import Submission.ClippedWeakRegularity

/-! Quantitative stability of the bounded clipped regularity approximant under
perturbing its tests, in both pointwise and normalized mean-square form. -/
namespace Erdos3ClippedSumPerturbation
open Finset Erdos3ClippedWeakRegularity
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

lemma list_sum_map_eq_sum_get {J : Type*} (l : List J) (f : J → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  calc
    _ = ((List.ofFn l.get).map f).sum := by rw [List.ofFn_get]
    _ = _ := by rw [List.map_ofFn,List.sum_ofFn]; rfl

lemma list_cauchy_schwarz {J : Type*} (l : List J) (f : J → ℝ) :
    (l.map f).sum^2 ≤ (l.length : ℝ)*(l.map (fun j ↦ (f j)^2)).sum := by
  rw [list_sum_map_eq_sum_get,list_sum_map_eq_sum_get]
  have h := sum_mul_sq_le_sq_mul_sq univ
    (fun _i : Fin l.length ↦ (1 : ℝ)) (fun i ↦ f (l.get i))
  simpa only [one_mul,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using h

lemma expect_list_sum {J X : Type*} [Fintype X] (l : List J) (f : J → X → ℝ) :
    (𝔼 x : X, (l.map (fun j ↦ f j x)).sum) = (l.map (fun j ↦ 𝔼 x : X, f j x)).sum := by
  induction l with
  | nil => simp
  | cons j l ih => simp only [List.map_cons,List.sum_cons,expect_add_distrib,ih]

lemma clippedSum_map_abs_sub {J X Y : Type*} (l : List J) (ρ : ℝ)
    (f : J → X → ℝ) (g : J → Y → ℝ) (x : X) (y : Y) :
    |clippedSum ρ (l.map f) x-clippedSum ρ (l.map g) y| ≤
      |ρ| *(l.map (fun j ↦ |f j x-g j y|)).sum := by
  induction l with
  | nil => simp [clippedSum]
  | cons j l ih =>
    simp only [List.map_cons,clippedSum,List.sum_cons]
    calc
      _ ≤ |(clippedSum ρ (l.map f) x+ρ*f j x)-
          (clippedSum ρ (l.map g) y+ρ*g j y)| := clip01_abs_sub _ _
      _ = |(clippedSum ρ (l.map f) x-clippedSum ρ (l.map g) y)+ρ*(f j x-g j y)| := by congr 1; ring
      _ ≤ |clippedSum ρ (l.map f) x-clippedSum ρ (l.map g) y|+|ρ| *|f j x-g j y| := by
        simpa only [abs_mul] using abs_add_le
          (clippedSum ρ (l.map f) x-clippedSum ρ (l.map g) y) (ρ*(f j x-g j y))
      _ ≤ _ := by linarith

lemma clippedSum_map_sq_sub {J X Y : Type*} (l : List J) (ρ : ℝ)
    (f : J → X → ℝ) (g : J → Y → ℝ) (x : X) (y : Y) :
    (clippedSum ρ (l.map f) x-clippedSum ρ (l.map g) y)^2 ≤
      ρ^2*(l.length : ℝ)*(l.map (fun j ↦ (f j x-g j y)^2)).sum := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (clippedSum_map_abs_sub l ρ f g x y) 2
  simp only [sq_abs,mul_pow] at h
  have hc := list_cauchy_schwarz l (fun j ↦ |f j x-g j y|)
  simp only [sq_abs] at hc
  exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hc (sq_nonneg ρ))

/-- If each test has mean squared error at most epsilon, the clipped output has
mean squared error at most rho^2 * (number of tests)^2 * epsilon. -/
theorem clippedSum_mean_sq_sub {J X : Type*} [Fintype X]
    (l : List J) (ρ : ℝ) (f g : J → X → ℝ) {ε : ℝ}
    (hfg : ∀ j ∈ l, (𝔼 x : X, (f j x-g j x)^2) ≤ ε) :
    (𝔼 x : X, (clippedSum ρ (l.map f) x-clippedSum ρ (l.map g) x)^2) ≤
      ρ^2*(l.length : ℝ)^2*ε := by
  calc
    _ ≤ 𝔼 x : X, ρ^2*(l.length : ℝ)*(l.map (fun j ↦ (f j x-g j x)^2)).sum :=
      expect_le_expect (fun x _ ↦ clippedSum_map_sq_sub l ρ f g x x)
    _ = ρ^2*(l.length : ℝ)*(l.map (fun j ↦ 𝔼 x : X, (f j x-g j x)^2)).sum := by
      rw [← mul_expect,expect_list_sum]
    _ ≤ ρ^2*(l.length : ℝ)*((l.length : ℝ)*ε) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [list_sum_map_eq_sum_get]
      calc
        _ ≤ ∑ _i : Fin l.length, ε := sum_le_sum (fun i _ ↦ hfg _ (List.get_mem _ _))
        _ = _ := by simp
    _ = _ := by ring

/-- A clipped combination of A-Lipschitz tests is |rho| * length * A Lipschitz.
The bound does not require the tests themselves to be bounded. -/
theorem clippedSum_map_lipschitz {J X : Type*} [PseudoMetricSpace X]
    (l : List J) (ρ : ℝ) (f : J → X → ℝ) (A : NNReal)
    (hf : ∀ j ∈ l, LipschitzWith A (f j)) :
    LipschitzWith (⟨|ρ|,abs_nonneg ρ⟩*(l.length : NNReal)*A)
      (clippedSum ρ (l.map f)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  apply (clippedSum_map_abs_sub l ρ f f x y).trans
  have he : (l.map (fun j ↦ |f j x-f j y|)).sum ≤
      (l.length : ℝ)*(A : ℝ)*dist x y := by
    rw [list_sum_map_eq_sum_get]
    calc
      _ ≤ ∑ _i : Fin l.length, (A : ℝ)*dist x y := by
        apply sum_le_sum
        intro i _
        exact (hf _ (List.get_mem _ _)).dist_le_mul x y
      _ = _ := by simp [mul_assoc]
  simpa only [NNReal.coe_mul,NNReal.coe_mk,NNReal.coe_natCast,mul_assoc] using
    mul_le_mul_of_nonneg_left he (abs_nonneg ρ)

#print axioms clippedSum_mean_sq_sub
#print axioms clippedSum_map_lipschitz
end Erdos3ClippedSumPerturbation
