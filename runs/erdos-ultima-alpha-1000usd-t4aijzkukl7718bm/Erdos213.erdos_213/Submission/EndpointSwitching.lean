import Submission.SquareClassProjection
import Mathlib.Tactic

/-! Exact cancellation of arbitrary real endpoint weights. These necessary
conditions do not assert that the weights or their squares are rational. -/
namespace Erdos213.EndpointSwitching

variable {ι : Type*}

/-- Rational squared original edges can be made rational lengths by positive
real factors attached to their endpoints. The factors here are the squares
of the factors multiplying lengths. -/
def RealWeightedRational (N : ι → ι → ℚ) : Prop :=
  ∃ s : ι → ℝ, (∀ i, 0 < s i) ∧
    ∀ i j, i ≠ j → ∃ r : ℚ, (r : ℝ)^2 = s i*s j*(N i j : ℝ)

lemma four_edge_square (N : ι → ι → ℚ) (h : RealWeightedRational N)
    {a b c d : ι} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hda : d ≠ a)
    (hNbc : N b c ≠ 0) (hNda : N d a ≠ 0) :
    IsSquare (N a b * N c d / (N b c * N d a)) := by
  obtain ⟨s, hs, hr⟩ := h
  obtain ⟨u, hu⟩ := hr a b hab
  obtain ⟨v, hv⟩ := hr b c hbc
  obtain ⟨w, hw⟩ := hr c d hcd
  obtain ⟨t, ht⟩ := hr d a hda
  have hb : (N b c : ℝ) ≠ 0 := by exact_mod_cast hNbc
  have hd : (N d a : ℝ) ≠ 0 := by exact_mod_cast hNda
  have ha0 := ne_of_gt (hs a)
  have hb0 := ne_of_gt (hs b)
  have hc0 := ne_of_gt (hs c)
  have hd0 := ne_of_gt (hs d)
  have he : (((u*w/(v*t) : ℚ) : ℝ))^2 =
      ((N a b*N c d/(N b c*N d a) : ℚ) : ℝ) := by
    push_cast
    rw [div_pow, mul_pow, mul_pow, hu, hv, hw, ht]
    field_simp
  refine ⟨u*w/(v*t), ?_⟩
  apply Rat.cast_injective (α := ℝ)
  push_cast
  push_cast at he
  simpa only [pow_two] using he.symm

/-- The triangle-product square class is invariant across all triangles
through a fixed vertex. An explicit rational witness cancels all the real
endpoint weights. -/
lemma triangle_product_square (N : ι → ι → ℚ)
    (h : RealWeightedRational N)
    {a b c i j : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hai : a ≠ i) (haj : a ≠ j) (hij : i ≠ j)
    (hN : ∀ u v, u ≠ v → N u v ≠ 0) :
    IsSquare (N a i*N a j*N i j*(N a b*N a c*N b c)) := by
  obtain ⟨s, hs, hr⟩ := h
  obtain ⟨u, hu⟩ := hr a i hai
  obtain ⟨v, hv⟩ := hr a j haj
  obtain ⟨w, hw⟩ := hr i j hij
  obtain ⟨r, hrr⟩ := hr a b hab
  obtain ⟨t, ht⟩ := hr a c hac
  obtain ⟨e, he⟩ := hr b c hbc
  -- This witness uses only rational quantities. The real weights cancel.
  refine ⟨u*v*e*(N i j*N a b*N a c)/(w*r*t), ?_⟩
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [← pow_two, div_pow]
  simp only [mul_pow]
  rw [hu, hv, hw, hrr, ht, he]
  have hn1 : (N a b : ℝ) ≠ 0 := by exact_mod_cast hN a b hab
  have hn2 : (N a c : ℝ) ≠ 0 := by exact_mod_cast hN a c hac
  have hn3 : (N i j : ℝ) ≠ 0 := by exact_mod_cast hN i j hij
  have hsa := ne_of_gt (hs a)
  have hsb := ne_of_gt (hs b)
  have hsc := ne_of_gt (hs c)
  have hsi := ne_of_gt (hs i)
  have hsj := ne_of_gt (hs j)
  field_simp

section Inversion
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- Inversion and a positive real dilation give real endpoint weights. Neither
the center nor the scale has to be rational. -/
lemma weights_of_inverted_lengths (p : ι → P) (o : P)
    (ho : ∀ i, p i ≠ o) (A : ℝ) (hA : 0 < A)
    (hd : ∀ i j, i ≠ j → A*
      dist (EuclideanGeometry.inversion o 1 (p i)) (EuclideanGeometry.inversion o 1 (p j))
      ∈ Set.range ((↑) : ℚ → ℝ)) :
    ∃ l : ι → ℝ, (∀ i, 0 < l i) ∧
      ∀ i j, i ≠ j → l i*l j*dist (p i) (p j) ∈ Set.range ((↑) : ℚ → ℝ) := by
  let l := fun i => Real.sqrt A/dist (p i) o
  have hdist (i) : 0 < dist (p i) o := dist_pos.mpr (ho i)
  refine ⟨l,fun i => div_pos (Real.sqrt_pos.mpr hA) (hdist i),?_⟩
  intro i j hij
  have he : l i*l j*dist (p i) (p j) = A*
      dist (EuclideanGeometry.inversion o 1 (p i)) (EuclideanGeometry.inversion o 1 (p j)) := by
    rw [EuclideanGeometry.dist_inversion_inversion (ho i) (ho j)]
    dsimp [l]
    rw [one_pow]
    have hi := ne_of_gt (hdist i)
    have hj := ne_of_gt (hdist j)
    field_simp
    linear_combination dist (p i) (p j) * (Real.sq_sqrt hA.le)
  rw [he]
  exact hd i j hij
end Inversion

/-- Irrational squares of endpoint factors genuinely add possibilities:
three edges of squared length two can be reweighted over R, but cannot
be reweighted by positive rational squared endpoint factors. -/
theorem irrational_endpoint_control :
    RealWeightedRational (fun (_ _ : Fin 3) => (2 : ℚ)) ∧
    ¬ ∃ s : Fin 3 → ℚ, (∀ i, 0 < s i) ∧
      ∀ i j, i ≠ j → IsSquare (s i*s j*2) := by
  constructor
  · refine ⟨fun _ => Real.sqrt 2/2,fun _ => by positivity,?_⟩
    intro i j hij
    refine ⟨1,?_⟩
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    norm_num only [Rat.cast_one,Rat.cast_ofNat]
    nlinarith only [hs]
  · rintro ⟨s,hs,h⟩
    have hp := ((h 0 1 (by decide)).mul (h 0 2 (by decide))).mul (h 1 2 (by decide))
    have h0 := ne_of_gt (hs 0)
    have h1 := ne_of_gt (hs 1)
    have h2 := ne_of_gt (hs 2)
    have hf : IsSquare (2 : ℚ) := by
      convert hp.div (IsSquare.sq (2*s 0*s 1*s 2)) using 1
      field_simp
    norm_num at hf

#print axioms four_edge_square
#print axioms triangle_product_square
#print axioms weights_of_inverted_lengths
#print axioms irrational_endpoint_control
end Erdos213.EndpointSwitching
