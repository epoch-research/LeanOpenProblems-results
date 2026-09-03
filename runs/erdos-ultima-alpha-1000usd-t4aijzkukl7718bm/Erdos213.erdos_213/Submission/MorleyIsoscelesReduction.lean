import FormalConjecturesUtil

/-! An algebraic reduction for one isosceles Morley norm class.
The rational-point classification of Y²=X³+1 is NOT assumed or proved here.
In particular these lemmas alone do not exclude any rational parameter and
do not settle the unrestricted Erdős conjecture. -/
namespace Erdos213.MorleyIsoscelesReduction
set_option maxHeartbeats 2000000

def highNorm (t : ℚ) : ℚ :=
  t^8-4*t^6+178/27*t^4-4/9*t^2+1/81

def quotientParameter (t : ℚ) : ℚ := (3*t^2+1)/(4*t)

def Nondegenerate (t : ℚ) : Prop :=
  t ≠ 0 ∧ t ≠ 1 ∧ t ≠ -1 ∧ t ≠ 1/3 ∧ t ≠ -1/3

lemma quotient_identity (t : ℚ) (ht : t ≠ 0) :
    (9/(16*t^2))^2*highNorm t =
      (quotientParameter t)^4-3*(quotientParameter t)^2+3 := by
  dsimp [highNorm,quotientParameter]
  field_simp
  ring

lemma quartic_to_mordell {v w : ℚ} (h : w^2=v^4-3*v^2+3) :
    (v*w)^2=(v^2-1)^3+1 := by
  linear_combination v^2*h

lemma quotient_ne_zero (t : ℚ) (ht : t ≠ 0) : quotientParameter t ≠ 0 := by
  apply div_ne_zero
  · nlinarith [sq_nonneg t]
  · exact mul_ne_zero (by norm_num) ht

lemma quotient_square_one_iff (t : ℚ) (ht : t ≠ 0) :
    (quotientParameter t)^2=1 ↔ t=1 ∨ t=-1 ∨ t=1/3 ∨ t=-1/3 := by
  constructor
  · intro h
    have he : quotientParameter t=1 ∨ quotientParameter t=-1 := by
      have h' : (quotientParameter t)^2=(1 : ℚ)^2 := by simpa using h
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h'
    have hd : (4 : ℚ)*t ≠ 0 := mul_ne_zero (by norm_num) ht
    rcases he with he | he
    · change (3*t^2+1)/(4*t)=1 at he
      have hh := (div_eq_iff hd).mp he
      have hf : (t-1)*(3*t-1)=0 := by nlinarith [hh]
      rcases mul_eq_zero.mp hf with hf | hf
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · change (3*t^2+1)/(4*t)=-1 at he
      have hh := (div_eq_iff hd).mp he
      have hf : (t+1)*(3*t+1)=0 := by nlinarith [hh]
      rcases mul_eq_zero.mp hf with hf | hf
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
  · rintro (rfl | rfl | rfl | rfl) <;> norm_num [quotientParameter]

lemma high_norm_mordell (t : ℚ) (ht : t ≠ 0) (h : IsSquare (highNorm t)) :
    ∃ x y : ℚ, x=(quotientParameter t)^2-1 ∧ y^2=x^3+1 := by
  obtain ⟨r,hr⟩ := h
  let v := quotientParameter t
  let w := 9*r/(16*t^2)
  have hw : w^2=v^4-3*v^2+3 := by
    calc
      w^2 = (9/(16*t^2))^2*highNorm t := by rw [hr]; dsimp [w]; ring
      _ = v^4-3*v^2+3 := quotient_identity t ht
  exact ⟨v^2-1,v*w,rfl,quartic_to_mordell hw⟩

/-- A nondegenerate square value would require a Mordell point whose abscissa
is none of the three standard rational torsion abscissas. No classification
of all Mordell points is smuggled into this statement. -/
lemma high_norm_nonstandard_mordell (t : ℚ) (ht : Nondegenerate t)
    (h : IsSquare (highNorm t)) :
    ∃ x y : ℚ, y^2=x^3+1 ∧ x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 2 := by
  obtain ⟨x,y,hx,he⟩ := high_norm_mordell t ht.1 h
  refine ⟨x,y,he,?_,?_,?_⟩
  · intro hh
    have hv : quotientParameter t=0 := by nlinarith [hx,hh]
    exact quotient_ne_zero t ht.1 hv
  · intro hh
    have hv : (quotientParameter t)^2=1 := by linarith [hx]
    rcases (quotient_square_one_iff t ht.1).mp hv with h1 | h2 | h3 | h4
    · exact ht.2.1 h1
    · exact ht.2.2.1 h2
    · exact ht.2.2.2.1 h3
    · exact ht.2.2.2.2 h4
  · intro hh
    have hn : ¬ IsSquare (3 : ℚ) := by norm_num [Rat.isSquare_natCast_iff]
    apply hn
    refine ⟨quotientParameter t,?_⟩
    nlinarith [hx,hh]

#print axioms quotient_identity
#print axioms quartic_to_mordell
#print axioms quotient_square_one_iff
#print axioms high_norm_mordell
#print axioms high_norm_nonstandard_mordell
end Erdos213.MorleyIsoscelesReduction
