import Submission.DoubleCoverLinear
import Submission.ExactificationUnboundedCost

/-! A constant-factor conversion of arbitrary prime-class covers into covers
of multiplicity at most two is impossible, even with arbitrary new primes and
residues. This does not disprove the quadratic Jacobsthal conjecture. -/
namespace Erdos970.DoubleCover

/-- The proposed constant-factor multiplicity-reduction bridge is false. -/
theorem no_constant_factor_double_conversion : ¬ (∃ A > (0 : ℝ),
    ∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ), (∀ p ∈ P, p.Prime) →
      (∀ x < m, ∃ p ∈ P, x ≡ r p [MOD p]) →
      ∃ (Q : Finset ℕ) (s : ℕ → ℕ), (∀ q ∈ Q, q.Prime) ∧
        (Q.card : ℝ) ≤ A * P.card ∧
        (∀ x < m, ∃ q ∈ Q, x ≡ s q [MOD q]) ∧
        (∀ x < m, (Q.filter (fun q => x ≡ s q [MOD q])).card ≤ 2)) := by
  rintro ⟨A, hA, hconvert⟩
  obtain ⟨C, hC, hlinear⟩ := prime_double_cover_linear
  apply DisjointCover.no_linear_cover_bound
  refine ⟨C * A, mul_pos hC hA, ?_⟩
  intro P r m hP hcover
  obtain ⟨Q, s, hQ, hcard, hcoverQ, hdoubleQ⟩ := hconvert P r m hP hcover
  calc
    (m : ℝ) ≤ C * Q.card := hlinear Q s m hQ hcoverQ hdoubleQ
    _ ≤ C * (A * P.card) := mul_le_mul_of_nonneg_left hcard hC.le
    _ = (C * A) * P.card := by ring

#print axioms no_constant_factor_double_conversion
end Erdos970.DoubleCover
