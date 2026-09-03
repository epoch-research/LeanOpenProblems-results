import Submission.TetrahedralOrbit
import Submission.MedianDiscriminant

/-! A complete arithmetic coordinate reduction for the tetrahedral template.
No admissible non-diagonal parameter, or solution of Erdős 213, is asserted. -/
namespace Erdos213.TetrahedralNormalForm
open TetrahedralOrbit MedianDiscriminant

def Admissible (a b c : ℚ) : Prop := ∀ k, IsSquare (values a b c k)

def radius (s : ℚ) : ℚ := s^2-s+1

def face (T A B : ℚ) : ℚ := (T-A/2)^2+B^2/4

def cross (T A B : ℚ) : ℚ := 4*(T+A/4)^2+3*B^2/4

def Centered (s T : ℚ) : Prop :=
  IsSquare (face T (alpha₃ s) (alpha₁ s-alpha₂ s)) ∧
  IsSquare (face T (alpha₂ s) (alpha₁ s-alpha₃ s)) ∧
  IsSquare (face T (alpha₁ s) (alpha₂ s-alpha₃ s)) ∧
  IsSquare (cross T (alpha₃ s) (alpha₁ s-alpha₂ s)) ∧
  IsSquare (cross T (alpha₂ s) (alpha₁ s-alpha₃ s)) ∧
  IsSquare (cross T (alpha₁ s) (alpha₂ s-alpha₃ s))

lemma values_homogeneous (q a b c : ℚ) (k : Fin 7) :
    values (q*a) (q*b) (q*c) k = q^2*values a b c k := by
  fin_cases k
  · change ((q*a)^2+(q*b)^2)/2=q^2*((a^2+b^2)/2); ring
  · change ((q*a)^2+(q*c)^2)/2=q^2*((a^2+c^2)/2); ring
  · change ((q*b)^2+(q*c)^2)/2=q^2*((b^2+c^2)/2); ring
  · change (q*a)^2+(q*b)^2+(q*c)^2-(q*a)*(q*b)-(q*a)*(q*c)-(q*b)*(q*c)=
      q^2*(a^2+b^2+c^2-a*b-a*c-b*c); ring
  · change (q*a)^2+(q*b)^2+(q*c)^2-(q*a)*(q*b)+(q*a)*(q*c)+(q*b)*(q*c)=
      q^2*(a^2+b^2+c^2-a*b+a*c+b*c); ring
  · change (q*a)^2+(q*b)^2+(q*c)^2+(q*a)*(q*b)-(q*a)*(q*c)+(q*b)*(q*c)=
      q^2*(a^2+b^2+c^2+a*b-a*c+b*c); ring
  · change (q*a)^2+(q*b)^2+(q*c)^2+(q*a)*(q*b)+(q*a)*(q*c)-(q*b)*(q*c)=
      q^2*(a^2+b^2+c^2+a*b+a*c-b*c); ring

lemma admissible_scale (a b c q : ℚ) (hq : q ≠ 0) :
    Admissible (q*a) (q*b) (q*c) ↔ Admissible a b c := by
  constructor
  · intro h k
    have hh := (h k).div (IsSquare.sq q)
    rw [values_homogeneous] at hh
    simpa [hq] using hh
  · intro h k
    rw [values_homogeneous]
    exact (IsSquare.sq q).mul (h k)

lemma centered_values (s T : ℚ) :
    values (T+alpha₁ s) (T+alpha₂ s) (T+alpha₃ s) =
      ![face T (alpha₃ s) (alpha₁ s-alpha₂ s),
        face T (alpha₂ s) (alpha₁ s-alpha₃ s),
        face T (alpha₁ s) (alpha₂ s-alpha₃ s),
        (radius s)^2,
        cross T (alpha₃ s) (alpha₁ s-alpha₂ s),
        cross T (alpha₂ s) (alpha₁ s-alpha₃ s),
        cross T (alpha₁ s) (alpha₂ s-alpha₃ s)] := by
  funext k
  fin_cases k <;>
    norm_num [values,face,cross,radius,alpha₁,alpha₂,alpha₃] <;> ring

lemma centered_iff_admissible (s T : ℚ) :
    Centered s T ↔ Admissible (T+alpha₁ s) (T+alpha₂ s) (T+alpha₃ s) := by
  unfold Admissible
  rw [centered_values]
  constructor
  · rintro ⟨h0,h1,h2,h4,h5,h6⟩ k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact IsSquare.sq _
    · exact h4
    · exact h5
    · exact h6
  · intro h
    exact ⟨h 0,h 1,h 2,h 4,h 5,h 6⟩

/-- Every non-diagonal parameter with nonzero third coordinate is a nonzero
similarity of a centered parameter. The six displayed squares are sufficient
as well as necessary. This theorem does not assert their solvability. -/
lemma admissible_centered_iff (a b c : ℚ) (hc : c ≠ 0)
    (hne : a ≠ c ∨ b ≠ c) :
    Admissible a b c ↔ ∃ s T q : ℚ, q ≠ 0 ∧
      a = q*(T+alpha₁ s) ∧ b = q*(T+alpha₂ s) ∧ c = q*(T+alpha₃ s) ∧
      Centered s T := by
  constructor
  · intro h
    have hd : IsSquare (delta (a/c) (b/c)) := by
      have hh := (h 3).div (IsSquare.sq c)
      convert hh using 1
      change delta (a/c) (b/c) = (a^2+b^2+c^2-a*b-a*c-b*c)/c^2
      unfold delta
      field_simp
      ring
    obtain ⟨s,q,hA,hB⟩ := (delta_parametrization (a/c) (b/c)).mp hd
    have hq : q ≠ 0 := by
      intro he
      subst q
      simp only [sideA,sideC,zero_mul,add_zero] at hA hB
      have ha : a=c := (div_eq_one_iff_eq hc).mp hA
      have hb : b=c := (div_eq_one_iff_eq hc).mp hB
      rcases hne with hne | hne
      · exact hne ha
      · exact hne hb
    let T := coordinate s q
    have hs := side_coordinates s q hq
    have ha : a=(c*q)*(T+alpha₁ s) := by
      have hx := (div_eq_iff hc).mp hA
      rw [hs.1] at hx
      dsimp [T]
      nlinarith only [hx]
    have hb : b=(c*q)*(T+alpha₂ s) := by
      have hx := (div_eq_iff hc).mp hB
      rw [hs.2.1] at hx
      dsimp [T]
      nlinarith only [hx]
    have hh : c=(c*q)*(T+alpha₃ s) := by
      dsimp [T]
      linear_combination c*hs.2.2
    refine ⟨s,T,c*q,mul_ne_zero hc hq,ha,hb,hh,?_⟩
    apply (centered_iff_admissible s T).mpr
    apply (admissible_scale _ _ _ (c*q) (mul_ne_zero hc hq)).mp
    simpa only [← ha,← hb,← hh] using h
  · rintro ⟨s,T,q,hq,rfl,rfl,rfl,h⟩
    exact (admissible_scale _ _ _ q hq).mpr ((centered_iff_admissible s T).mp h)

lemma centered_sum (s T : ℚ) :
    (T+alpha₁ s)+(T+alpha₂ s)+(T+alpha₃ s) = 3*T := by
  linear_combination alpha_sum s

lemma face_cross_relation (s T : ℚ) :
    cross T (alpha₃ s) (alpha₁ s-alpha₂ s) -
      4*face T (alpha₃ s) (alpha₁ s-alpha₂ s) =
        6*(alpha₃ s)*T-(radius s)^2/3 := by
  unfold face cross alpha₁ alpha₂ alpha₃ radius
  ring

#print axioms centered_values
#print axioms admissible_centered_iff
#print axioms face_cross_relation
end Erdos213.TetrahedralNormalForm
