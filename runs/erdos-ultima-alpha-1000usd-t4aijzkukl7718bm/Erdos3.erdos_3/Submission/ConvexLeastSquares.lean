import Submission.ClippedWeakRegularity

/-! Bounded least-squares approximation over convex classes. Nested classes
provide Pythagorean control of coarse/fine approximants, unlike arbitrary
successive clipped weak-regularity outputs. -/
namespace Erdos3ConvexLeastSquares
open Finset Erdos3ClippedWeakRegularity
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {X : Type*} [Fintype X] [Nonempty X]

noncomputable def realPairing (f g : X → ℝ) : ℝ := 𝔼 x : X, f x*g x

lemma squaredError_symm (f g : X → ℝ) : squaredError f g = squaredError g f := by
  apply expect_congr rfl
  intro x _
  ring

lemma squaredError_affine (f g h : X → ℝ) (t : ℝ) :
    squaredError f (fun x ↦ g x+t*(h x-g x)) = squaredError f g-
      2*t*realPairing (fun x ↦ f x-g x) (fun x ↦ h x-g x)+t^2*squaredError g h := by
  have he (x : X) : (f x-(g x+t*(h x-g x)))^2 =
      (f x-g x)^2-2*t*((f x-g x)*(h x-g x))+t^2*(g x-h x)^2 := by ring
  simp only [squaredError,he,expect_add_distrib,expect_sub_distrib,← mul_expect,realPairing]

lemma quadratic_variational {A B : ℝ} (hB : 0 ≤ B)
    (hmin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ -2*t*A+t^2*B) : A ≤ 0 := by
  by_contra h
  have hA : 0 < A := lt_of_not_ge h
  let t := min 1 (A/(B+1))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hA (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htB : t*(B+1) ≤ A := (le_div_iff₀ (by linarith : 0 < B+1)).mp (min_le_right _ _)
  have hm := hmin t ht.le ht1
  have hh := mul_le_mul_of_nonneg_left htB ht.le
  have hp := mul_pos ht hA
  nlinarith only [hm,hh,hp,sq_nonneg t]

/-- The variational inequality at a minimizer follows by testing the line
segment toward every other member of the convex class. -/
theorem minimizer_variational (f g : X → ℝ) {K : Set (X → ℝ)}
    (hK : Convex ℝ K) (hg : g ∈ K)
    (hmin : ∀ h ∈ K, squaredError f g ≤ squaredError f h) {h : X → ℝ} (hh : h ∈ K) :
    realPairing (fun x ↦ f x-g x) (fun x ↦ h x-g x) ≤ 0 := by
  apply quadratic_variational (squaredError_nonneg g h)
  intro t ht ht1
  have hm := hmin (g+t • (h-g)) (hK.add_smul_sub_mem hg hh ⟨ht,ht1⟩)
  change squaredError f g ≤ squaredError f (fun x ↦ g x+t*(h x-g x)) at hm
  rw [squaredError_affine] at hm
  linarith

/-- Pythagorean inequality for a convex least-squares minimizer. -/
theorem minimizer_pythagorean (f g : X → ℝ) {K : Set (X → ℝ)}
    (hK : Convex ℝ K) (hg : g ∈ K)
    (hmin : ∀ h ∈ K, squaredError f g ≤ squaredError f h) {h : X → ℝ} (hh : h ∈ K) :
    squaredError g h ≤ squaredError f h-squaredError f g := by
  have hv := minimizer_variational f g hK hg hmin hh
  have he := squaredError_affine f g h 1
  have hf : (fun x ↦ g x+1*(h x-g x)) = h := by funext x; ring
  rw [hf] at he
  norm_num at he
  linarith

lemma squaredError_continuous (f : X → ℝ) : Continuous (squaredError f) := by
  unfold squaredError
  simp only [Finset.expect_eq_sum_div_card]
  fun_prop

/-- Existence is applied to compact approximation classes, not to an assumed
unrestricted inverse theorem. -/
theorem exists_least_squares (f : X → ℝ) {K : Set (X → ℝ)}
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ g ∈ K, ∀ h ∈ K, squaredError f g ≤ squaredError f h := by
  obtain ⟨g,hg,hmin⟩ := hK.exists_isMinOn hne (squaredError_continuous f).continuousOn
  exact ⟨g,hg,hmin⟩

/-- The finer minimizer is close to every coarser approximant whenever the
least-squares energy drop is small. -/
theorem nested_minimizers_close (f g h : X → ℝ) {K L : Set (X → ℝ)}
    (hKL : K ⊆ L) (hL : Convex ℝ L) (hg : g ∈ K) (hh : h ∈ L)
    (hmin : ∀ q ∈ L, squaredError f h ≤ squaredError f q) :
    squaredError g h ≤ squaredError f g-squaredError f h := by
  rw [squaredError_symm g h]
  exact minimizer_pythagorean f h hL hh hmin (hKL hg)

/-- At most mean(f)/epsilon^2 many coarse/fine stages can all have large L2
changes. The fine accuracy within each stage may be chosen independently. -/
theorem exists_small_nested_step (f : X → ℝ) (g : ℕ → X → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hinit : squaredError f (g 0) ≤ squaredError f 0)
    {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (hN : (𝔼 x : X, f x)/(ε^2) < (N : ℝ))
    (hstep : ∀ i < N, squaredError (g i) (g (i+1)) ≤
      squaredError f (g i)-squaredError f (g (i+1))) :
    ∃ i < N, squaredError (g i) (g (i+1)) ≤ ε^2 := by
  by_contra! hno
  have he : ∀ j ≤ N, squaredError f (g j)+(j : ℝ)*ε^2 ≤ squaredError f (g 0) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hi := ih (by omega)
      have hs := hstep j (by omega)
      have hn := hno j (by omega)
      rw [Nat.cast_add,Nat.cast_one]
      linarith
  have hfinal := he N le_rfl
  have h0 := squaredError_nonneg f (g N)
  have hi := hinit.trans (squaredError_zero_le_mean f hf)
  have hn := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hN
  linarith

#print axioms minimizer_pythagorean
#print axioms exists_least_squares
#print axioms exists_small_nested_step
end Erdos3ConvexLeastSquares
