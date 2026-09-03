import Submission.QuadraticFamilyAvoidance
import Submission.CubeArithmeticProgressions

/-! A finite list of rational quadratic four-cube families cannot cover all
strict positive integral collisions. This is not a disproof of the Sidon-set
conjecture: a cover of collisions is an auxiliary strategy, not its statement. -/
namespace Erdos1206.QuadraticFamilyNoncoverage
open FermatCubicConics QuadraticFamilyAvoidance

lemma arbitrarily_near_unit_gap (H : ℕ) :
    ∃ a b c d : ℕ, 0 < a ∧ a < b ∧ b < c ∧ c < d ∧
      a^3+d^3=b^3+c^3 ∧ H*(b-a) < (H+1)*(d-c) := by
  let z := 12*H+1
  refine ⟨CubeArithmeticProgressions.A 1 z,CubeArithmeticProgressions.B 1 z,
    CubeArithmeticProgressions.C 1 z,CubeArithmeticProgressions.D 1 z,?_⟩
  obtain ⟨ha,hab,hbc,hcd⟩ := CubeArithmeticProgressions.ordered (q := 1) (z := z) (by decide)
  refine ⟨ha,hab,hbc,hcd,CubeArithmeticProgressions.identity 1 z,?_⟩
  have h₁ : CubeArithmeticProgressions.B 1 z-CubeArithmeticProgressions.A 1 z=
      z^2+9*z+21 := by
    dsimp [CubeArithmeticProgressions.A,CubeArithmeticProgressions.B]
    omega
  have h₂ : CubeArithmeticProgressions.D 1 z-CubeArithmeticProgressions.C 1 z=
      z^2+3*z+3 := by
    dsimp [CubeArithmeticProgressions.C,CubeArithmeticProgressions.D]
    omega
  rw [h₁,h₂]
  dsimp [z]
  nlinarith [sq_nonneg (H:ℤ)]

/-- There is a single collision outside every linearized plane in any given
finite list of quadratic identities, hence also outside all of their scaled
polynomial specializations. -/
theorem finite_families_do_not_cover {ι : Type*} [Finite ι] (a b c d : ι → Vec)
    (hc : ∀ i, quad (a i)^3+quad (d i)^3=quad (b i)^3+quad (c i)^3) :
    ∃ u v w z : ℕ, 0 < u ∧ u < v ∧ v < w ∧ w < z ∧
      u^3+z^3=v^3+w^3 ∧ ∀ i x,
      ¬ (linear (a i) x=(u:ℚ) ∧ linear (b i) x=(v:ℚ) ∧
        linear (c i) x=(w:ℚ) ∧ linear (d i) x=(z:ℚ)) := by
  obtain ⟨H,hH,hbound⟩ := finite_uniform_gap_bound a b c d hc
  obtain ⟨u,v,w,z,hu,huv,hvw,hwz,he,hgap⟩ := arbitrarily_near_unit_gap H
  refine ⟨u,v,w,z,hu,huv,hvw,hwz,he,fun i x hx => ?_⟩
  obtain ⟨ha,hb,hc',hd⟩ := hx
  have hinst : OrderedInstance (a i) (b i) (c i) (d i) x := by
    simp only [OrderedInstance,ha,hb,hc',hd]
    exact ⟨by exact_mod_cast hu,by exact_mod_cast huv,by exact_mod_cast hvw.le,
      by exact_mod_cast hwz,by exact_mod_cast he⟩
  have hbnd := (hbound i x hinst).1
  rw [ha,hb,hc',hd,← Nat.cast_sub hwz.le,← Nat.cast_sub huv.le] at hbnd
  have hh : (H+1)*(z-w) ≤ H*(v-u) := by exact_mod_cast hbnd
  omega

#print axioms arbitrarily_near_unit_gap
#print axioms finite_families_do_not_cover
end Erdos1206.QuadraticFamilyNoncoverage
