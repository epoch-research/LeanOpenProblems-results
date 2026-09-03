import Submission.QuinticPairedMomentCertificate
import Submission.QuinticPairedMomentArithmetic

/-! Rigidity for the common-quadratic-core quintic moment equations when the
four linear coefficients occur in opposite pairs. This is a construction
obstruction only, not a bound for unrestricted representations. -/
namespace Erdos322Research.QuinticPairedMoments
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1000000

open QuinticPairedMomentCertificate QuinticPairedMomentArithmetic

def momentEven {R : Type*} [CommRing R] (a b c d u v : R) : R :=
  (a^5+b^5+c^5+d^5)*((a+b)*u^4+(c+d)*v^4)-
    4*((a^3+b^3)*u^2+(c^3+d^3)*v^2)^2

/-- Positive real centres must pair if both opposite linear slopes are nonzero. -/
theorem real_centres_pair {a b c d u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (h₁ : (a^4-b^4)*u+(c^4-d^4)*v=0)
    (h₃ : (a^2-b^2)*u^3+(c^2-d^2)*v^3=0)
    (hE : momentEven a b c d u v=0) : a=b ∧ c=d := by
  have hab : a=b := by
    by_contra hne
    have hS : a+b ≠ 0 := ne_of_gt (by positivity)
    let B := (a-b)/(a+b)
    let C := (c+d)/(a+b)
    let D := (c-d)/(a+b)
    let T := v/u
    have hB : B ≠ 0 := div_ne_zero (sub_ne_zero.mpr hne) hS
    have hC : 0 < C := div_pos (by positivity) (by positivity)
    have hT : T ≠ 0 := div_ne_zero hv hu
    have h3 : B+C*D*T^3=0 := by
      dsimp [B,C,D,T]
      field_simp
      linear_combination h₃
    have h1 : B*(1+B^2)+C*D*(C^2+D^2)*T=0 := by
      dsimp [B,C,D,T]
      field_simp
      linear_combination 2*h₁
    have h2 : C^2+D^2-T^2*(1+B^2)=0 := by
      have hh : B*(C^2+D^2-T^2*(1+B^2))=0 := by
        linear_combination (C^2+D^2)*h3-T^2*h1
      exact (mul_eq_zero.mp hh).resolve_left hB
    have hsq : B^2-C^2*D^2*T^6=0 := by
      linear_combination (B-C*D*T^3)*h3
    have he : evenResidual B C D T=0 := by
      unfold evenResidual
      dsimp [B,C,D,T]
      field_simp
      unfold momentEven at hE
      linear_combination 16*hE
    exact normalized_even_moment_impossible hC hT hsq h2 he
  have hcd : c=d := by
    rw [hab,sub_self,zero_mul,zero_add] at h₃
    have hh : c^2-d^2=0 :=
      (mul_eq_zero.mp h₃).resolve_right (pow_ne_zero _ hv)
    nlinarith
  exact ⟨hab,hcd⟩

private theorem single_slope_impossible {a b c d A v : ℚ}
    (hc : 0 < c) (hd : 0 < d) (hv : v ≠ 0)
    (hf : a^5+b^5+c^5+d^5=A^5)
    (h₃ : (c^2-d^2)*v^3=0) (hE : momentEven a b c d 0 v=0) : False := by
  have hcd : c=d := by
    have hh : c^2-d^2=0 := (mul_eq_zero.mp h₃).resolve_right (pow_ne_zero _ hv)
    nlinarith
  subst d
  have he : 2*c*v^4*(A^5-8*c^5)=0 := by
    unfold momentEven at hE
    linear_combination hE-2*c*v^4*hf
  have hh : A^5=8*c^5 := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_left (by positivity))
  exact no_eight_fifth hc.ne' hh

/-- In the positive rational common-core moment equations, paired opposite
linear coefficients must all vanish, for every rational leading vector. -/
theorem rational_paired_slopes_zero {a b c d A u v : ℚ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hf : a^5+b^5+c^5+d^5=A^5)
    (h₁ : (a^4-b^4)*u+(c^4-d^4)*v=0)
    (h₃ : (a^2-b^2)*u^3+(c^2-d^2)*v^3=0)
    (hE : momentEven a b c d u v=0) : u=0 ∧ v=0 := by
  by_cases hu : u=0
  · subst u
    refine ⟨rfl,?_⟩
    by_contra hv
    exact single_slope_impossible hc hd hv hf (by simpa using h₃) hE
  · by_cases hv : v=0
    · subst v
      exfalso
      apply single_slope_impossible (a := c) (b := d) ha hb hu
        (by convert hf using 1; ring)
        (by simpa using h₃)
      unfold momentEven at hE ⊢
      linear_combination hE
    · have hreal : (a : ℝ)=(b : ℝ) ∧ (c : ℝ)=(d : ℝ) := by
        apply real_centres_pair (u := (u : ℝ)) (v := (v : ℝ)) (by exact_mod_cast ha) (by exact_mod_cast hb)
          (by exact_mod_cast hc) (by exact_mod_cast hd)
          (by exact_mod_cast hu) (by exact_mod_cast hv)
          (by exact_mod_cast h₁) (by exact_mod_cast h₃)
        unfold momentEven at hE ⊢
        exact_mod_cast hE
      have hab : a=b := by exact_mod_cast hreal.1
      have hcd : c=d := by exact_mod_cast hreal.2
      subst b
      subst d
      exfalso
      apply paired_centres_impossible (A := A) (u := u) (v := v) ha hc hu
        (by linear_combination hf)
      unfold momentEven at hE
      linear_combination hE/4

end
end Erdos322Research.QuinticPairedMoments
