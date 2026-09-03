import FormalConjecturesUtil

/-!
Exact geometry of a conic bundle on the equal-sums-of-cubes surface.
These results do not establish a positive-density construction or its negation.
-/

namespace Erdos1206

private lemma rational_cube_difference_one {t x : ℚ}
    (h : t ^ 3 + x ^ 3 = (x + 1) ^ 3) : t = 1 := by
  have ht0 : t ≠ 0 := by
    intro ht
    subst t
    nlinarith [sq_nonneg (2 * x + 1)]
  have hx : x = 0 ∨ x + 1 = 0 := by
    by_contra! hx
    exact (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree)
      t x (x + 1) ht0 hx.1 hx.2 h
  have ht3 : t ^ 3 = 1 ^ 3 := by
    rcases hx with hx | hx
    · subst x
      norm_num at h ⊢
      exact h
    · have : x = -1 := by linarith
      subst x
      norm_num at h ⊢
      linarith
  exact (Odd.pow_inj (by decide : Odd 3)).mp ht3

/-- The first conic discriminant is a rational square only in the degenerate fiber. -/
lemma cubeConic_discriminant_left_square_iff (t : ℚ) :
    IsSquare (3 * (4 * t ^ 3 - 1)) ↔ t = 1 := by
  constructor
  · rintro ⟨y, hy⟩
    apply rational_cube_difference_one (x := (y - 3) / 6)
    nlinarith [hy]
  · rintro rfl
    exact ⟨3, by norm_num⟩

/-- The second discriminant likewise has only the two degenerate square cases. -/
lemma cubeConic_discriminant_right_square_iff (t : ℚ) :
    IsSquare (3 * t * (4 - t ^ 3)) ↔ t = 0 ∨ t = 1 := by
  constructor
  · rintro ⟨y, hy⟩
    by_cases ht : t = 0
    · exact Or.inl ht
    · right
      have hsq : IsSquare (3 * (4 * (1 / t) ^ 3 - 1)) := by
        refine ⟨y / t ^ 2, ?_⟩
        field_simp
        nlinarith [hy]
      have ht' := (cubeConic_discriminant_left_square_iff (1 / t)).mp hsq
      field_simp at ht'
      linarith
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨3, by norm_num⟩

/-- The conic after writing `a = c + t*u` and `d = b + u`. -/
def cubeCollisionConic (t b c u : ℚ) : ℚ :=
  3 * t * c ^ 2 - 3 * b ^ 2 + 3 * u * (t ^ 2 * c - b) + (t ^ 3 - 1) * u ^ 2

lemma cubeCollisionConic_identity (t b c u : ℚ) :
    (c + t * u) ^ 3 + b ^ 3 - c ^ 3 - (b + u) ^ 3 =
      u * cubeCollisionConic t b c u := by
  dsimp [cubeCollisionConic]
  ring

lemma cubeCollisionConic_iff {t b c u : ℚ} (hu : u ≠ 0) :
    (c + t * u) ^ 3 + b ^ 3 = c ^ 3 + (b + u) ^ 3 ↔
      cubeCollisionConic t b c u = 0 := by
  have h := cubeCollisionConic_identity t b c u
  constructor
  · intro he
    have hz : u * cubeCollisionConic t b c u = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hu
  · intro he
    rw [he, mul_zero] at h
    linarith

/-- On a nondegenerate rational conic, setting either of the first pair of
cube coordinates to zero cannot give a rational point with `u ≠ 0`. -/
lemma cubeConic_left_boundary_ne_zero {t b u : ℚ} (ht : t ≠ 1) (hu : u ≠ 0) :
    -3 * b ^ 2 - 3 * b * u + (t ^ 3 - 1) * u ^ 2 ≠ 0 := by
  intro h
  apply ht
  have hx : t ^ 3 + (b / u) ^ 3 = (b / u + 1) ^ 3 := by
    field_simp
    nlinarith [congrArg (fun z : ℚ => z * u) h]
  exact rational_cube_difference_one hx

#print axioms cubeConic_discriminant_left_square_iff
#print axioms cubeConic_discriminant_right_square_iff
#print axioms cubeCollisionConic_iff

end Erdos1206
