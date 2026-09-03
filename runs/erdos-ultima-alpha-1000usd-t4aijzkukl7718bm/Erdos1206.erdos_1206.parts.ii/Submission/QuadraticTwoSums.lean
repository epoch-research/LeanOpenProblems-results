import Submission.RationalCubePairRelations
import Submission.PolynomialTriplePairSums

/-! Two sum relations force degeneracy of a nontrivial quadratic triple. -/
namespace Erdos1206.QuadraticTwoSums
open Polynomial FermatCubicConics FermatCubicSubspaces RationalCubePairRelations
open PolynomialTriplePairSums

lemma linearize_has_kernel (q : ℚ[X]) : ∃ x : Vec, x ≠ 0 ∧ linearize q x=0 := by
  by_cases hq : q.coeff 2=0
  · refine ⟨![1,0,0],by decide,?_⟩
    simp [linearize,hq]
  · refine ⟨![q.coeff 1,-q.coeff 2,0],?_,?_⟩
    · intro hh
      have hz := congrArg (fun x : Vec => x 1) hh
      change -q.coeff 2=0 at hz
      exact hq (neg_eq_zero.mp hz)
    · dsimp [linearize]
      ring

lemma common_factor_not_jointlyInjective {a b c d : Vec} {q : ℚ[X]} {u v w z : ℚ}
    (ha : quad a=C u*q) (hb : quad b=C v*q) (hc : quad c=C w*q) (hd : quad d=C z*q) :
    ¬ JointlyInjective (linear a) (linear b) (linear c) (linear d) := by
  intro hj
  obtain ⟨x,hx,hq⟩ := linearize_has_kernel q
  have hz (g : Vec) (r : ℚ) (he : quad g=C r*q) : linear g x=0 := by
    rw [← linearize_quad,he,linearize_Cmul,hq,mul_zero]
  exact hx (hj x (hz a u ha) (hz b v hb) (hz c w hc) (hz d z hd))

/-- Two normalized sum relations are impossible if the three pairs are
nontrivial, have unequal coordinates, and one four-coordinate image is
jointly injective. -/
theorem two_sums_false {a b c d e f : Vec}
    (he₁ : quad a^3+quad b^3=quad c^3+quad d^3)
    (he₂ : quad a^3+quad b^3=quad e^3+quad f^3)
    (hn : quad a^3+quad b^3 ≠ 0)
    (hab : quad a ≠ quad b) (hcd : quad c ≠ quad d) (hef : quad e ≠ quad f)
    (hce : quad c ≠ quad e) (hcf : quad c ≠ quad f)
    (hj : JointlyInjective (linear a) (linear b) (linear c) (linear d))
    (hs₁ : SumRelation a b c d) (hs₂ : SumRelation a b e f) : False := by
  obtain ⟨r,hr,hr₁,hs₁⟩ := hs₁.symm
  obtain ⟨s,hs,hs₁',hs₂⟩ := hs₂.symm
  have hp₁ := sum_relation_polynomial hs₁
  have hp₂ := sum_relation_polynomial hs₂
  have hne : r ≠ s := by
    intro hrs
    have hsum : quad c+quad d=quad e+quad f := by rw [hp₁,hp₂,hrs]
    have hcubes : quad c^3+quad d^3=quad e^3+quad f^3 := he₁.symm.trans he₂
    have hn' : quad c^3+quad d^3 ≠ 0 := by rw [← he₁]; exact hn
    exact (same_sum_repeated hcubes hn' hsum).elim hce hcf
  have hpowinj := (by decide : Odd (3 : ℕ)).pow_injective (R := ℚ)
  have hr3 : r^3 ≠ 1 := by intro hz; exact hr₁ (hpowinj (by simpa using hz))
  have hs3 : s^3 ≠ 1 := by intro hz; exact hs₁' (hpowinj (by simpa using hz))
  have hrs3 : r^3 ≠ s^3 := fun hz => hne (hpowinj hz)
  obtain ⟨q,u,v,w,z,u',v',_,ha,hb,hc,hd,_,_⟩ := proportional_pair_sums_common_factor
    (ne_of_gt hr) (ne_of_gt hs) hr3 hs3 hrs3 (sum_ne_zero hn)
    (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hcd) (sub_ne_zero.mpr hef)
    hp₁ hp₂ he₁.symm he₂.symm
  exact common_factor_not_jointlyInjective ha hb hc hd hj

#print axioms common_factor_not_jointlyInjective
#print axioms two_sums_false
end Erdos1206.QuadraticTwoSums
