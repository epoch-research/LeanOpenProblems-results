import Submission.CircleCoverReduction
import Submission.CartesianGridMetric

/-! A geometric covering bound for arbitrary Cartesian grids, and a conditional
route to Erdős 213 from rational-distance grids of unbounded side cardinality.
No existence theorem for such grids is asserted. -/
namespace Erdos213.CartesianGridCover
open EuclideanGeometry InversionReduction CircleCoverReduction MvPolynomial
noncomputable section
set_option maxHeartbeats 3000000

private def circlePoly (a b c d : ℝ) : MvPolynomial (Fin 2) ℝ :=
  C a*(X 0^2+X 1^2)+C b*X 0+C c*X 1+C d

private lemma eval_circlePoly (a b c d : ℝ) (x : Fin 2 → ℝ) :
    eval x (circlePoly a b c d)=a*(x 0^2+x 1^2)+b*x 0+c*x 1+d := by
  simp [circlePoly]

private lemma circlePoly_ne_zero {a b c d : ℝ}
    (h : a≠0 ∨ b≠0 ∨ c≠0) : circlePoly a b c d≠0 := by
  intro hz
  have h0 := congrArg (eval (![0,0] : Fin 2 → ℝ)) hz
  have h1 := congrArg (eval (![1,0] : Fin 2 → ℝ)) hz
  have h2 := congrArg (eval (![-1,0] : Fin 2 → ℝ)) hz
  have h3 := congrArg (eval (![0,1] : Fin 2 → ℝ)) hz
  simp only [eval_circlePoly,map_zero,Matrix.cons_val_zero,Matrix.cons_val_one,
    zero_pow (by decide : (2 : ℕ)≠0),one_pow,neg_one_sq] at h0 h1 h2 h3
  rcases h with ha | hb | hc
  · apply ha; linarith
  · apply hb; linarith
  · apply hc; linarith

private lemma degree_circlePoly (a b c d : ℝ) (i : Fin 2) :
    degreeOf i (circlePoly a b c d)≤2 := by
  have hX (j : Fin 2) : degreeOf i (X j : MvPolynomial (Fin 2) ℝ)≤1 := by
    rw [degreeOf_X]
    split_ifs <;> omega
  have hp (j : Fin 2) : degreeOf i ((X j : MvPolynomial (Fin 2) ℝ)^2)≤2 :=
    (degreeOf_pow_le _ _ _).trans (by have := hX j; omega)
  unfold circlePoly
  apply (degreeOf_add_le _ _ _).trans
  apply max_le
  · apply (degreeOf_add_le _ _ _).trans
    apply max_le
    · apply (degreeOf_add_le _ _ _).trans
      apply max_le
      · apply (degreeOf_C_mul_le _ _ _).trans
        exact (degreeOf_add_le _ _ _).trans (max_le (hp 0) (hp 1))
      · exact (degreeOf_C_mul_le _ _ _).trans ((hX 0).trans (by omega))
    · exact (degreeOf_C_mul_le _ _ _).trans ((hX 1).trans (by omega))
  · simp only [degreeOf_C]; omega

def pair (a b : ℝ) : ℝ² := !₂[a,b]

def planeGrid (A B : Finset ℝ) : Finset ℝ² :=
  (A ×ˢ B).image (fun ab => pair ab.1 ab.2)

lemma mem_planeGrid {A B : Finset ℝ} {a b : ℝ} (ha : a∈A) (hb : b∈B) :
    pair a b∈planeGrid A B :=
  Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩

/-- A union of k generalized circles cannot cover a Cartesian product having
more than 2k coordinates in each direction. The proof uses polynomial
interpolation on a grid, including the cases of line factors and an empty
cover. -/
theorem not_covered {A B : Finset ℝ} {k : ℕ}
    (hA : 2*k<A.card) (hB : 2*k<B.card) :
    ¬CoveredBy (planeGrid A B : Set ℝ²) k := by
  classical
  rintro ⟨F,hFk,hgen,hcover⟩
  have hh (i : F) := hgen i.val i.property
  choose a b c d hn he using hh
  let f : F → MvPolynomial (Fin 2) ℝ := fun i => circlePoly (a i) (b i) (c i) (d i)
  let P : MvPolynomial (Fin 2) ℝ := ∏ i : F, f i
  have hP : P≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => circlePoly_ne_zero (hn i))
  have hd (j : Fin 2) : P.degreeOf j≤2*F.card := by
    calc
      P.degreeOf j ≤ ∑ i : F, (f i).degreeOf j := degreeOf_prod_le _ _ _
      _ ≤ ∑ i : F, 2 := Finset.sum_le_sum (fun i _ => degree_circlePoly _ _ _ _ _)
      _ = 2*F.card := by simp [Nat.mul_comm]
  apply hP
  apply eq_zero_of_eval_zero_at_prod_finset P (![A,B] : Fin 2 → Finset ℝ)
  · intro j
    have hd' := (hd j).trans (Nat.mul_le_mul_left 2 hFk)
    fin_cases j
    · simpa using hd'.trans_lt hA
    · simpa using hd'.trans_lt hB
  · intro x hx
    have hp : pair (x 0) (x 1)∈planeGrid A B :=
      mem_planeGrid (by simpa using hx 0) (by simpa using hx 1)
    obtain ⟨T,hT,hpT⟩ := hcover _ hp
    rw [show P=∏ i : F, f i from rfl,eval_prod]
    apply Finset.prod_eq_zero_iff.mpr
    refine ⟨⟨T,hT⟩,Finset.mem_univ _,?_⟩
    rw [show f ⟨T,hT⟩=circlePoly (a ⟨T,hT⟩) (b ⟨T,hT⟩) (c ⟨T,hT⟩) (d ⟨T,hT⟩) from rfl,
      eval_circlePoly]
    simpa [radiusSq,pair] using he ⟨T,hT⟩ _ hpT

lemma plane_distance_eq_complex (a b a' b' : ℚ) :
    dist (pair a b) (pair a' b')=
      dist (CartesianGridMetric.point a b) (CartesianGridMetric.point a' b') := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [InversionReduction.distance_sq,CartesianGridMetric.distance_sq]
  simp only [pair,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  push_cast
  ring

def rationalGrid (A B : Finset ℚ) : Finset ℝ² :=
  planeGrid (A.image (Rat.cast : ℚ → ℝ)) (B.image (Rat.cast : ℚ → ℝ))

lemma rational_distances {A B : Finset ℚ}
    (h : CartesianGridMetric.Grid (A : Set ℚ) (B : Set ℚ)) :
    (rationalGrid A B : Set ℝ²).Pairwise
      (fun p q => dist p q∈Set.range (Rat.cast : ℚ → ℝ)) := by
  classical
  rintro p hp q hq _
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨⟨c,d⟩,hcd,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  obtain ⟨hc,hd⟩ := Finset.mem_product.mp hcd
  obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c',hc',rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨d',hd',rfl⟩ := Finset.mem_image.mp hd
  rw [plane_distance_eq_complex,CartesianGridMetric.distance_rational_iff]
  exact h a' ha' c' hc' b' hb' d' hd'

/-- A large rational-distance Cartesian grid would suffice. The existence
of grids satisfying these assumptions remains an independent arithmetic
problem. -/
theorem erdos213For_of_grid {A B : Finset ℚ} {n : ℕ}
    (h : CartesianGridMetric.Grid (A : Set ℚ) (B : Set ℚ))
    (hA : 2*(n+n^3)<A.card) (hB : 2*(n+n^3)<B.card) : Erdos213For n := by
  apply erdos213For_of_not_covered_rational (Finset.finite_toSet _) (rational_distances h)
  apply not_covered
  · simpa only [Finset.card_image_of_injective _ (Rat.cast_injective (α := ℝ))] using hA
  · simpa only [Finset.card_image_of_injective _ (Rat.cast_injective (α := ℝ))] using hB

/-- Conditional only: unbounded rational-distance grids would settle the
original conjecture. No such unbounded family is constructed here. -/
theorem conjecture_of_unbounded_grids
    (h : ∀ m : ℕ, ∃ A B : Finset ℚ, m<A.card ∧ m<B.card ∧
      CartesianGridMetric.Grid (A : Set ℚ) (B : Set ℚ)) :
    ∀ n : ℕ, n≥4 → Erdos213For n := by
  intro n _
  obtain ⟨A,B,hA,hB,hG⟩ := h (2*(n+n^3))
  exact erdos213For_of_grid hG hA hB

#print axioms not_covered
#print axioms plane_distance_eq_complex
#print axioms rational_distances
#print axioms erdos213For_of_grid
#print axioms conjecture_of_unbounded_grids
end
end Erdos213.CartesianGridCover
