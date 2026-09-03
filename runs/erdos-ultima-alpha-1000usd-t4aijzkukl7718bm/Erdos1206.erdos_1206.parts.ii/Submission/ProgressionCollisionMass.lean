import Submission.RoughNearUnitPrimitiveMass

/-!
Divergent primitive collision mass with all four roots in one common invertible
residue class. The common class may vary with the collision. This is an
arithmetic counting result, not a proof or disproof of the density conjecture.
-/
namespace Erdos1206.ProgressionCollisionMass
open RoughNearUnitPrimitiveMass RoughNearUnitConicFamily
open PrimitiveCollisionMass (Collision)
open scoped Classical
set_option maxHeartbeats 2000000

/-- The normalized coordinates all have the same residue, and it is a unit. -/
def CongruentUnit (Q : ℕ) (e : Collision) : Prop :=
  Nat.Coprime e.val.1 Q ∧ Nat.ModEq Q e.val.1 e.val.2.1 ∧
    Nat.ModEq Q e.val.1 e.val.2.2.1 ∧ Nat.ModEq Q e.val.1 e.val.2.2.2

private lemma cancel_eighteen_congruence {Q g a : ℕ} {v : ℤ}
    (hv : v=(18*g:ℤ)*a) (hc : (18*(Q:ℤ)) ∣ v-18) :
    Nat.ModEq Q (g*a) 1 := by
  obtain ⟨z,hz⟩ := hc
  have hdiv : (Q:ℤ) ∣ (g:ℤ)*a-1 := by
    refine ⟨z,?_⟩
    rw [hv] at hz
    nlinarith only [hz]
  exact Nat.modEq_iff_dvd.mpr (by
    simpa only [Nat.cast_mul,Nat.cast_one,neg_sub] using dvd_neg.mpr hdiv)

lemma family_congruent_unit (Q H : ℕ) (hQ : 0 < Q) (x : Index Q) :
    CongruentUnit Q (collision Q H hQ x) := by
  obtain ⟨hg,hA,hB,hC,hD,hcop⟩ := scale_spec Q H hQ x
  obtain ⟨hcA,hcB,hcC,hcD⟩ := raw_congruences Q H x
  have ha := cancel_eighteen_congruence hA hcA
  have hb := cancel_eighteen_congruence hB hcB
  have hc := cancel_eighteen_congruence hC hcC
  have hd := cancel_eighteen_congruence hD hcD
  have hgc : Nat.Coprime (scale Q H hQ x) Q := by
    have hprod : Nat.Coprime (scale Q H hQ x*(collision Q H hQ x).val.1) Q := by
      rw [Nat.coprime_iff_gcd_eq_one,ha.gcd_eq]
      simp
    exact (Nat.coprime_mul_iff_left.mp hprod).1
  refine ⟨hcop.1,?_,?_,?_⟩
  · exact Nat.ModEq.cancel_left_of_coprime hgc.symm (ha.trans hb.symm)
  · exact Nat.ModEq.cancel_left_of_coprime hgc.symm (ha.trans hc.symm)
  · exact Nat.ModEq.cancel_left_of_coprime hgc.symm (ha.trans hd.symm)

abbrev Family (Q : ℕ) := {e : Collision // CongruentUnit Q e}

theorem reciprocal_mass_not_summable (Q : ℕ) (hQ : 0 < Q) :
    ¬ Summable (fun e : Family Q => (1 : ℝ)/e.val.val.2.2.2) := by
  let f : Index Q → Family Q := fun x =>
    ⟨collision Q 0 hQ x,family_congruent_unit Q 0 hQ x⟩
  have hf : Function.Injective f := by
    intro x y he
    have hh : (f x).val=(f y).val := congrArg (fun e : Family Q => e.val) he
    exact collision_injective Q 0 hQ hh
  intro hs
  have hcomp := hs.comp_injective hf
  exact index_mass_not_summable Q 0 hQ hcomp

theorem exists_large_reciprocal_sum (Q : ℕ) (hQ : 0 < Q) (C : ℝ) :
    ∃ F : Finset (Family Q), C < ∑ e ∈ F, (1 : ℝ)/e.val.val.2.2.2 := by
  by_contra! h
  exact reciprocal_mass_not_summable Q hQ
    (summable_of_sum_le (fun _ => by positivity) h)

#print axioms family_congruent_unit
#print axioms reciprocal_mass_not_summable
#print axioms exists_large_reciprocal_sum
end Erdos1206.ProgressionCollisionMass
