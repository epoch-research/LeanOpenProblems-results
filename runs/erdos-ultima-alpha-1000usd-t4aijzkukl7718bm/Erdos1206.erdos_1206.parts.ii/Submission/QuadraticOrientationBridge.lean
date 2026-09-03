import Submission.QuadraticResidualBridge

/-!
The coordinate-change bridge from normalized quadratic triple families to
three explicit plane obstructions. These are auxiliary classification results.
-/
namespace Erdos1206.QuadraticOrientationBridge
open Polynomial FermatCubicConics FermatCubicSubspaces QuadraticResidualBridge
open QuadraticTriplePlaneObstructions

private lemma three_surjective (a b c : Vec →ₗ[ℚ] ℚ)
    (h : ∀ x, a x=0 → b x=0 → c x=0 → x=0) (A B C : ℚ) :
    ∃ x, a x=A ∧ b x=B ∧ c x=C := by
  let π : Vec →ₗ[ℚ] Vec := LinearMap.pi (fun i : Fin 3 => ![a,b,c] i)
  have hi : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
    intro x hx
    apply h x
    · exact congrArg (fun v : Vec => v 0) hx
    · exact congrArg (fun v : Vec => v 1) hx
    · exact congrArg (fun v : Vec => v 2) hx
  obtain ⟨x,hx⟩ := LinearMap.surjective_of_injective hi ![A,B,C]
  refine ⟨x,?_,?_,?_⟩
  · exact congrArg (fun v : Vec => v 0) hx
  · exact congrArg (fun v : Vec => v 1) hx
  · exact congrArg (fun v : Vec => v 2) hx

private lemma diff_scaling {A B C D E F r s t : ℚ}
    (h₁ : A-C=r*(B-D)) (h₂ : A-E=s*(B-F)) (h₃ : C-F=t*(D-E)) :
    diffQ₁ r s t B D F=(t+1)^2*(r*(A^2+A*C+C^2)+(B^2+B*D+D^2)) ∧
    diffQ₂ r s t B D F=(t+1)^2*(s*(A^2+A*E+E^2)+(B^2+B*F+F^2)) := by
  have he : (r-s)*B+(s+1)*F+(t-r)*D=(t+1)*E := by
    linear_combination -h₁+h₂-h₃
  have ha : (t+1)*E+s*((t+1)*B)-s*((t+1)*F)=(t+1)*A := by
    linear_combination -(t+1)*h₂
  have hc : (t+1)*F+t*((t+1)*D)-t*((t+1)*E)=(t+1)*C := by
    linear_combination -(t+1)*h₃
  dsimp only [diffQ₁,diffQ₂]
  simp only [he,ha,hc]
  constructor <;> ring

/-- Inconsistent orientations are impossible for a nondegenerate quadratic
triple with negative nontrivial direction ratios. -/
theorem inconsistent_difference_false {a b c d e f : Vec} {r s t : ℚ}
    (h₁ : ∀ x, linear a x-linear c x=r*(linear b x-linear d x))
    (h₂ : ∀ x, linear a x-linear e x=s*(linear b x-linear f x))
    (h₃ : ∀ x, linear c x-linear f x=t*(linear d x-linear e x))
    (he₁ : quad a^3+quad b^3=quad c^3+quad d^3)
    (he₂ : quad a^3+quad b^3=quad e^3+quad f^3)
    (hd : quad b ≠ quad d) (hf : quad b ≠ quad f)
    (hj : JointlyInjective (linear a) (linear b) (linear e) (linear f))
    (hr : r < 0) (hs : s ≠ 0) (ht : t < 0) (hr₁ : r ≠ -1) (ht₁ : t ≠ -1) : False := by
  obtain ⟨l,hl⟩ := residuals_proportional h₁ h₂ he₁ he₂ hd hf hj
  have hkernel : ∀ x, linear b x=0 → linear d x=0 → linear f x=0 → x=0 := by
    intro x hb hd hf
    have hh₁ := h₁ x
    have hh₂ := h₂ x
    have hh₃ := h₃ x
    rw [hb,hd] at hh₁
    rw [hb,hf] at hh₂
    rw [hd,hf] at hh₃
    have ht0 : t+1 ≠ 0 := by intro he; apply ht₁; linarith
    have hz : (t+1)*linear a x=0 := by
      linear_combination hh₁+hh₃+t*hh₂
    have ha := (mul_eq_zero.mp hz).resolve_left ht0
    apply hj x ha hb (by linear_combination -hh₂+ha) hf
  apply inconsistent_difference_not_proportional hr hs ht hr₁ ht₁
  refine ⟨l,fun B D F => ?_⟩
  obtain ⟨x,hb,hd,hf⟩ := three_surjective (linear b) (linear d) (linear f) hkernel B D F
  obtain ⟨hq₁,hq₂⟩ := diff_scaling (h₁ x) (h₂ x) (h₃ x)
  rw [hb,hd,hf] at hq₁ hq₂
  rw [hq₁,hq₂]
  have hh := hl x
  dsimp only [differenceResidual] at hh
  rw [hb,hd,hf] at hh
  linear_combination (t+1)^2*hh


private lemma sum_scaling {A B C D E F r s k : ℚ}
    (h₁ : A-C=r*(B-D)) (h₂ : A-E=s*(B-F)) (h₃ : C+D=k*(E+F)) :
    sumQ₁ r s k B D F=(1-k)^2*(r*(A^2+A*C+C^2)+(B^2+B*D+D^2)) ∧
    sumQ₂ r s k B D F=(1-k)^2*(s*(A^2+A*E+E^2)+(B^2+B*F+F^2)) := by
  have ha : (r-k*s)*B-(r+1)*D+k*(s+1)*F=(1-k)*A := by
    linear_combination -h₁+k*h₂-h₃
  have hc : (1-k)*A-r*((1-k)*B-(1-k)*D)=(1-k)*C := by
    linear_combination (1-k)*h₁
  have he : (1-k)*A-s*((1-k)*B-(1-k)*F)=(1-k)*E := by
    linear_combination (1-k)*h₂
  dsimp only [sumQ₁,sumQ₂]
  simp only [ha,hc,he]
  constructor <;> ring

/-- Exactly one sum relation and two normalized difference relations are
incompatible with a nondegenerate quadratic triple. -/
theorem one_sum_false {a b c d e f : Vec} {r s k : ℚ}
    (h₁ : ∀ x, linear a x-linear c x=r*(linear b x-linear d x))
    (h₂ : ∀ x, linear a x-linear e x=s*(linear b x-linear f x))
    (h₃ : ∀ x, linear c x+linear d x=k*(linear e x+linear f x))
    (he₁ : quad a^3+quad b^3=quad c^3+quad d^3)
    (he₂ : quad a^3+quad b^3=quad e^3+quad f^3)
    (hd : quad b ≠ quad d) (hf : quad b ≠ quad f)
    (hj : JointlyInjective (linear a) (linear b) (linear e) (linear f))
    (hs : s ≠ 0) (hr₁ : r ≠ -1) (hk : 0 < k) (hk₁ : k ≠ 1) : False := by
  obtain ⟨l,hl⟩ := residuals_proportional h₁ h₂ he₁ he₂ hd hf hj
  have hkernel : ∀ x, linear b x=0 → linear d x=0 → linear f x=0 → x=0 := by
    intro x hb hd hf
    have hh₁ := h₁ x
    have hh₂ := h₂ x
    have hh₃ := h₃ x
    rw [hb,hd] at hh₁
    rw [hb,hf] at hh₂
    rw [hd,hf] at hh₃
    have hk0 : 1-k ≠ 0 := sub_ne_zero.mpr hk₁.symm
    have hz : (1-k)*linear a x=0 := by
      linear_combination hh₁-k*hh₂+hh₃
    have ha := (mul_eq_zero.mp hz).resolve_left hk0
    apply hj x ha hb (by linear_combination -hh₂+ha) hf
  apply one_sum_not_proportional hs hr₁ hk hk₁
  refine ⟨l,fun B D F => ?_⟩
  obtain ⟨x,hb,hd,hf⟩ := three_surjective (linear b) (linear d) (linear f) hkernel B D F
  obtain ⟨hq₁,hq₂⟩ := sum_scaling (h₁ x) (h₂ x) (h₃ x)
  rw [hb,hd,hf] at hq₁ hq₂
  rw [hq₁,hq₂]
  have hh := hl x
  dsimp only [differenceResidual] at hh
  rw [hb,hd,hf] at hh
  linear_combination (1-k)^2*hh

private lemma consistent_scaling {A B C D E F r s t : ℚ}
    (h₁ : A-C=r*(B-D)) (h₂ : A-E=s*(B-F)) (h₃ : C-E=t*(D-F)) :
    consistentQ₁ r s t A D F=(s-r)^2*(r*(A^2+A*C+C^2)+(B^2+B*D+D^2)) ∧
    consistentQ₂ r s t A D F=(s-r)^2*(s*(A^2+A*E+E^2)+(B^2+B*F+F^2)) := by
  have hb : (t-r)*D+(s-t)*F=(s-r)*B := by
    linear_combination -h₁+h₂-h₃
  have hc : (s-r)*A-r*((s-r)*B-(s-r)*D)=(s-r)*C := by
    linear_combination (s-r)*h₁
  have he : (s-r)*A-s*((s-r)*B-(s-r)*F)=(s-r)*E := by
    linear_combination (s-r)*h₂
  dsimp only [consistentQ₁,consistentQ₂]
  simp only [hb,hc,he]
  constructor <;> ring

/-- Consistently oriented difference relations in a nondegenerate quadratic
triple must have the same direction ratio at the first point. -/
theorem consistent_ratios_equal {a b c d e f : Vec} {r s t : ℚ}
    (h₁ : ∀ x, linear a x-linear c x=r*(linear b x-linear d x))
    (h₂ : ∀ x, linear a x-linear e x=s*(linear b x-linear f x))
    (h₃ : ∀ x, linear c x-linear e x=t*(linear d x-linear f x))
    (he₁ : quad a^3+quad b^3=quad c^3+quad d^3)
    (he₂ : quad a^3+quad b^3=quad e^3+quad f^3)
    (hd : quad b ≠ quad d) (hf : quad b ≠ quad f)
    (hj : JointlyInjective (linear a) (linear b) (linear e) (linear f))
    (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) : s=r := by
  by_contra hrs
  obtain ⟨l,hl⟩ := residuals_proportional h₁ h₂ he₁ he₂ hd hf hj
  have hkernel : ∀ x, linear a x=0 → linear d x=0 → linear f x=0 → x=0 := by
    intro x ha hd hf
    have hh₁ := h₁ x
    have hh₂ := h₂ x
    have hh₃ := h₃ x
    rw [ha,hd] at hh₁
    rw [ha,hf] at hh₂
    rw [hd,hf] at hh₃
    have hsr : s-r ≠ 0 := sub_ne_zero.mpr hrs
    have hz : (s-r)*linear b x=0 := by
      linear_combination hh₁-hh₂+hh₃
    have hb := (mul_eq_zero.mp hz).resolve_left hsr
    apply hj x ha hb (by rw [hb] at hh₂; linarith) hf
  apply consistent_unequal_not_proportional hr hs ht hrs
  refine ⟨l,fun A D F => ?_⟩
  obtain ⟨x,ha,hd,hf⟩ := three_surjective (linear a) (linear d) (linear f) hkernel A D F
  obtain ⟨hq₁,hq₂⟩ := consistent_scaling (h₁ x) (h₂ x) (h₃ x)
  rw [ha,hd,hf] at hq₁ hq₂
  rw [hq₁,hq₂]
  have hh := hl x
  dsimp only [differenceResidual] at hh
  rw [ha,hd,hf] at hh
  linear_combination (s-r)^2*hh

#print axioms inconsistent_difference_false
#print axioms one_sum_false
#print axioms consistent_ratios_equal
end Erdos1206.QuadraticOrientationBridge
