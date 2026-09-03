import Submission.MorleyQuarticDescent
import Submission.MorleyIsoscelesReduction

/-! Complete elementary exclusion for one isosceles Morley norm class.
This is an auxiliary theorem, not a settlement of Erdős 213. -/
namespace Erdos213.MorleyIsoscelesReduction

/-- The only rational square values occur at the five degenerate parameters. -/
theorem high_norm_square_iff (t : ℚ) :
    IsSquare (highNorm t) ↔ t=0 ∨ t=1 ∨ t=-1 ∨ t=1/3 ∨ t=-1/3 := by
  constructor
  · intro h
    by_cases ht : t=0
    · exact Or.inl ht
    right
    obtain ⟨r,hr⟩ := h
    have hw : (9*r/(16*t^2))^2=
        (quotientParameter t)^4-3*(quotientParameter t)^2+3 := by
      calc
        (9*r/(16*t^2))^2=(9/(16*t^2))^2*highNorm t := by rw [hr]; ring
        _=(quotientParameter t)^4-3*(quotientParameter t)^2+3 := quotient_identity t ht
    exact (quotient_square_one_iff t ht).mp (MorleyQuarticDescent.rational_quartic hw)
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact ⟨1/9, by norm_num [highNorm]⟩
    · exact ⟨16/9, by norm_num [highNorm]⟩
    · exact ⟨16/9, by norm_num [highNorm]⟩
    · exact ⟨16/81, by norm_num [highNorm]⟩
    · exact ⟨16/81, by norm_num [highNorm]⟩

theorem high_norm_not_square {t : ℚ} (ht : Nondegenerate t) :
    ¬ IsSquare (highNorm t) := by
  intro h
  rcases (high_norm_square_iff t).mp h with h0 | h1 | hn1 | hthird | hnthird
  · exact ht.1 h0
  · exact ht.2.1 h1
  · exact ht.2.2.1 hn1
  · exact ht.2.2.2.1 hthird
  · exact ht.2.2.2.2 hnthird

#print axioms high_norm_square_iff
#print axioms high_norm_not_square
end Erdos213.MorleyIsoscelesReduction
