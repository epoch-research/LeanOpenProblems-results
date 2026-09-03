import FormalConjecturesUtil

/-! A common-chord lift of independent convex summands. The lift agrees
exactly with an affine-envelope maximum on the diagonal. This is an auxiliary
convexity theorem, not a covering-system obstruction. -/
namespace Erdos7CommonChordEnvelope
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable def chord (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  f a + (f b-f a)/(b-a)*(x-a)

lemma chord_mul (f : ℝ → ℝ) (a b x : ℝ) (hab : a < b) :
    (b-a)*chord f a b x = (b-x)*f a+(x-a)*f b := by
  unfold chord
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  <;> ring

@[simp] lemma chord_left (f : ℝ → ℝ) (a b : ℝ) : chord f a b a = f a := by
  simp [chord]

@[simp] lemma chord_right (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) :
    chord f a b b = f b := by
  have h := chord_mul f a b b hab
  have hp : 0 < b-a := sub_pos.mpr hab
  nlinarith

lemma le_chord (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (a b x : ℝ) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    f x ≤ chord f a b x := by
  rcases hx.1.eq_or_lt with h | h
  · subst x; simp
  rcases hx.2.eq_or_lt with h' | h'
  · subst x; simp [chord_right f a b hab]
  have hc := hf.secant_mono_aux1 (Set.mem_univ a) (Set.mem_univ b) h h'
  have he := chord_mul f a b x hab
  have hp : 0 < b-a := sub_pos.mpr hab
  nlinarith

lemma chord_le_outside (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (a b x : ℝ) (hab : a < b) (hx : x ≤ a ∨ b ≤ x) :
    chord f a b x ≤ f x := by
  have he := chord_mul f a b x hab
  have hp : 0 < b-a := sub_pos.mpr hab
  rcases hx with hx | hx
  · rcases hx.eq_or_lt with rfl | hx
    · simp
    have hc := hf.secant_mono_aux1 (Set.mem_univ x) (Set.mem_univ b) hx hab
    nlinarith
  · rcases hx.eq_or_lt with rfl | hx
    · simp [chord_right f a b hab]
    have hc := hf.secant_mono_aux1 (Set.mem_univ a) (Set.mem_univ x) hab hx
    nlinarith

lemma convex_chord (f : ℝ → ℝ) (a b : ℝ) :
    ConvexOn ℝ Set.univ (chord f a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy u v hu hv huv
  simp only [smul_eq_mul, chord]
  have hh : (u+v)*(f a-(f b-f a)/(b-a)*a) = f a-(f b-f a)/(b-a)*a := by
    rw [huv,one_mul]
  nlinarith

lemma monotone_chord (f : ℝ → ℝ) (hf : Monotone f) (a b : ℝ) (hab : a < b) :
    Monotone (chord f a b) := by
  intro x y hxy
  have hs : 0 ≤ (f b-f a)/(b-a) := div_nonneg (sub_nonneg.mpr (hf hab.le)) (by linarith)
  unfold chord
  nlinarith [mul_le_mul_of_nonneg_left (sub_le_sub_right hxy a) hs]

/-- Chords of all summands are above their summands on the SAME interval,
and below them outside it; hence their maxima add without diagonal loss. -/
theorem common_chord_identity {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, ConvexOn ℝ Set.univ (f i)) (a b x : ℝ) (hab : a < b) :
    (∑ i ∈ S, max (f i x) (chord (f i) a b x)) =
      max (∑ i ∈ S, f i x) (∑ i ∈ S, chord (f i) a b x) := by
  by_cases hx : x ∈ Set.Icc a b
  · have hp (i : ι) (hi : i ∈ S) := le_chord (f i) (hf i hi) a b x hab hx
    rw [max_eq_right (Finset.sum_le_sum hp)]
    exact Finset.sum_congr rfl (fun i hi => max_eq_right (hp i hi))
  · have ho : x ≤ a ∨ b ≤ x := by simp only [Set.mem_Icc] at hx; grind
    have hp (i : ι) (hi : i ∈ S) := chord_le_outside (f i) (hf i hi) a b x hab ho
    rw [max_eq_left (Finset.sum_le_sum hp)]
    exact Finset.sum_congr rfl (fun i hi => max_eq_left (hp i hi))

/-- Lift an affine row touching the diagonal sum at two points. Every
summand can still be evaluated at its OWN independently selected argument. -/
theorem affine_contact_split {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, ConvexOn ℝ Set.univ (f i))
    (hmf : ∀ i ∈ S, Monotone (f i)) (c A B a b : ℝ) (hab : a < b)
    (ha : c+(∑ i ∈ S, f i a) = A*a+B)
    (hb : c+(∑ i ∈ S, f i b) = A*b+B) :
    ∃ g : ι → ℝ → ℝ,
      (∀ i ∈ S, ConvexOn ℝ Set.univ (g i) ∧ Monotone (g i)) ∧
      (∀ i ∈ S, ∀ x, f i x ≤ g i x) ∧
      (∀ x, c+(∑ i ∈ S, g i x) = max (c+∑ i ∈ S, f i x) (A*x+B)) ∧
      (∀ x : ι → ℝ, c+(∑ i ∈ S, f i (x i)) ≤ c+∑ i ∈ S, g i (x i)) := by
  let g (i : ι) (x : ℝ) := max (f i x) (chord (f i) a b x)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨(hf i hi).sup (convex_chord (f i) a b),
      (hmf i hi).max (monotone_chord (f i) (hmf i hi) a b hab)⟩
  · intro i hi x
    exact le_max_left _ _
  · intro x
    have he : c+(∑ i ∈ S, chord (f i) a b x) = A*x+B := by
      have hs := Finset.sum_congr rfl (fun i (_ : i ∈ S) => chord_mul (f i) a b x hab)
      simp only [← Finset.mul_sum,Finset.sum_add_distrib] at hs
      rw [show (∑ i ∈ S, f i a) = A*a+B-c by linarith,
        show (∑ i ∈ S, f i b) = A*b+B-c by linarith] at hs
      have hh : (b-a)*(c+(∑ i ∈ S, chord (f i) a b x)-(A*x+B)) = 0 := by
        linear_combination hs
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt (sub_pos.mpr hab)))
    change c+(∑ i ∈ S, max (f i x) (chord (f i) a b x)) = _
    rw [common_chord_identity S f hf a b x hab,add_max,he]
  · intro x
    have hh := Finset.sum_le_sum (s := S) (fun i _ => le_max_left (f i (x i)) (chord (f i) a b (x i)))
    change c+(∑ i ∈ S, f i (x i)) ≤ c+∑ i ∈ S, max (f i (x i)) (chord (f i) a b (x i))
    linarith

#print axioms common_chord_identity
#print axioms affine_contact_split
end Erdos7CommonChordEnvelope
