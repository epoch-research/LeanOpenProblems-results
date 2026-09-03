import Submission.QuarticHuaBox

/-! Signed quartic moments cannot have a fixed box-growth exponent at every
order, even when only strictly positive targets are included. This diagnoses
an obstruction to a moment proof strategy; it says nothing comparable about
the all-positive representation count in the conjecture. -/
namespace Erdos322Research.QuarticSignedMomentObstruction

open QuarticHuaBox
set_option Elab.async false

/-- The signed fiber at the positive target one. -/
def unitFiber (B : ℕ) : Finset (Quad B) :=
  Finset.univ.filter (fun a => signedValue a = 1)

/-- Positive-target moments of the three-plus, one-minus quartic sum. -/
def positiveMoment (B q : ℕ) : ℕ :=
  ∑ t ∈ ((Finset.univ : Finset (Quad B)).image signedValue).filter (fun t => 0 < t),
    ((Finset.univ : Finset (Quad B)).filter (fun a => signedValue a = t)).card ^ q

private def diagonalPoint {B : ℕ} (hB : 2 ≤ B) (x : Fin B) : Quad B :=
  ((x, ⟨1, by omega⟩), (⟨0, by omega⟩, x))

private lemma diagonalPoint_value {B : ℕ} (hB : 2 ≤ B) (x : Fin B) :
    signedValue (diagonalPoint hB x) = 1 := by
  simp [signedValue, pairValue, diagonalPoint]

/-- Cancellation gives a distinct solution for every choice of `x`, at the
fixed positive target one. In particular, deleting target zero is not enough
to repair an all-order signed-moment argument. -/
theorem unitFiber_lower (B : ℕ) (hB : 2 ≤ B) : B ≤ (unitFiber B).card := by
  have h := Finset.card_le_card_of_injOn (diagonalPoint hB)
    (s := Finset.univ) (t := unitFiber B)
    (by
      intro x _
      simp only [Finset.mem_coe, unitFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      exact diagonalPoint_value hB x)
    (by
      intro x _ y _ hxy
      exact congrArg (fun a : Quad B => a.1.1) hxy)
  simpa using h

/-- The `q`th positive-target signed moment is at least `B^q`. -/
theorem positiveMoment_lower (B q : ℕ) (hB : 2 ≤ B) :
    B ^ q ≤ positiveMoment B q := by
  have hmem : (1 : ℤ) ∈
      ((Finset.univ : Finset (Quad B)).image signedValue).filter (fun t => 0 < t) := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨diagonalPoint hB ⟨0, by omega⟩,
        Finset.mem_univ _, diagonalPoint_value hB _⟩
    · norm_num
  have hs := Finset.single_le_sum
    (f := fun t : ℤ => ((Finset.univ : Finset (Quad B)).filter
      (fun a => signedValue a = t)).card ^ q)
    (fun t _ => Nat.zero_le _) hmem
  exact (Nat.pow_le_pow_left (unitFiber_lower B hB) q).trans hs

/-- No exponent fixed independently of the moment order can bound all the
positive-target signed moments, even with constants depending on the order. -/
theorem no_fixed_degree_all_moments (D : ℕ) :
    ¬ (∀ q : ℕ, 1 ≤ q → ∃ C > (0 : ℝ), ∀ B : ℕ, 2 ≤ B →
      (positiveMoment B q : ℝ) ≤ C * (B : ℝ) ^ D) := by
  intro h
  obtain ⟨C, _, hC⟩ := h (D + 1) (by omega)
  obtain ⟨B, hB⟩ := exists_nat_gt (max (2 : ℝ) C)
  have hB2 : 2 ≤ B := by
    have h2 : (2 : ℝ) < B := lt_of_le_of_lt (le_max_left _ _) hB
    exact_mod_cast h2.le
  have hCB : C < (B : ℝ) := lt_of_le_of_lt (le_max_right _ _) hB
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlo : (B : ℝ) ^ (D + 1) ≤ (positiveMoment B (D + 1) : ℝ) := by
    exact_mod_cast positiveMoment_lower B (D + 1) hB2
  have hstrict : C * (B : ℝ) ^ D < (B : ℝ) ^ (D + 1) := by
    rw [pow_succ, mul_comm ((B : ℝ) ^ D)]
    exact mul_lt_mul_of_pos_right hCB (pow_pos hBp _)
  exact (not_lt_of_ge (hlo.trans (hC B hB2))) hstrict

end Erdos322Research.QuarticSignedMomentObstruction
