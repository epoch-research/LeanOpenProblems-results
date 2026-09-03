import Submission.ExactCoverLinear
import Submission.Work

/-! Constant-factor conversion of arbitrary covers to exact covers is impossible.
This is a disproof only of that proposed bridge, not of the quadratic conjecture. -/
namespace Erdos970.DisjointCover
open Finset

lemma no_linear_cover_bound : ¬ (∃ C > (0 : ℝ),
    ∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ), (∀ p ∈ P, p.Prime) →
      (∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) → (m : ℝ) ≤ C * P.card) := by
  rintro ⟨C, hC, hbound⟩
  apply Erdos970.not_linear_bound
  refine ⟨C + 2, by linarith, ?_⟩
  intro k hk
  let m : ℕ := ⌊C * k⌋₊ + 1
  have hm : C * k < (m : ℝ) := by
    simp only [m, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one (C * (k : ℝ))
  have hboundm : IsJacobsthalBound k m := by
    by_contra hbad
    obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
    have hp := hbound P r m hP hcover
    have hc : (P.card : ℝ) ≤ k := by exact_mod_cast hPk
    have hmul := mul_le_mul_of_nonneg_left hc hC.le
    linarith
  have hj : (jacobsthalFunction k : ℝ) ≤ m := by
    exact_mod_cast ((jacobsthalFunction_le_iff k m).mpr hboundm)
  have hfloor : (⌊C * k⌋₊ : ℝ) ≤ C * k := Nat.floor_le (by positivity)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmm : (m : ℝ) = (⌊C * k⌋₊ : ℝ) + 1 := by simp [m]
  nlinarith

/-- No fixed multiplicative budget increase suffices for exactification, even
when every prime and residue in the replacement may be changed. -/
theorem no_constant_factor_exactification : ¬ (∃ A > (0 : ℝ),
    ∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ), (∀ p ∈ P, p.Prime) →
      (∀ i < m, ∃ p ∈ P, i ≡ r p [MOD p]) →
      ∃ (Q : Finset ℕ) (s : ℕ → ℕ), (∀ q ∈ Q, q.Prime) ∧
        (Q.card : ℝ) ≤ A * P.card ∧ ExactCover Q s m) := by
  rintro ⟨A, hA, hconvert⟩
  obtain ⟨C, hC, hlinear⟩ := prime_exact_cover_linear
  apply no_linear_cover_bound
  refine ⟨C * A, mul_pos hC hA, ?_⟩
  intro P r m hP hcover
  obtain ⟨Q, s, hQ, hcard, hQs⟩ := hconvert P r m hP hcover
  calc
    (m : ℝ) ≤ C * Q.card := hlinear Q s m hQ hQs
    _ ≤ C * (A * P.card) := mul_le_mul_of_nonneg_left hcard hC.le
    _ = (C * A) * P.card := by ring

#print axioms no_linear_cover_bound
#print axioms no_constant_factor_exactification
end Erdos970.DisjointCover
