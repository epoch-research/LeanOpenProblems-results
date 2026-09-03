import Submission.NewmanFixedResidual

/-! Consequences of fixed-residual finiteness for bounded residual degree.
The missing uniform bound is left explicit. -/
namespace Erdos406BoundedResidual
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoQuadratic
  Erdos406FixedResidualTools Erdos406FixedResidual
  Erdos406Cyclotomic Erdos406ReciprocalCandidate

lemma finite_mod_two_bounded_degree (D : ℕ) :
    {R : (ZMod 2)[X] | R.natDegree ≤ D}.Finite := by
  let f : (ZMod 2)[X] → (Fin (D+1) → ZMod 2) := fun R i => R.coeff i
  apply (Set.toFinite (f '' {R : (ZMod 2)[X] | R.natDegree ≤ D})).of_finite_image
  intro P hP Q hQ h
  change P.natDegree ≤ D at hP
  change Q.natDegree ≤ D at hQ
  ext i
  by_cases hi : i ≤ D
  · exact congrFun h ⟨i,by omega⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < i),
      coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < i)]

/-- Bounded residual degree suffices, even if the linear multiplicity and
therefore the total digit-polynomial degree are initially unbounded. -/
theorem finite_candidates_bounded_residual (D : ℕ) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1] ∧
      ∃ R : (ZMod 2)[X], R.coeff 0 = 1 ∧ R.natDegree ≤ D ∧ ∃ a : ℕ,
        (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
          (X+1)^a*R}.Finite := by
  let Rs : Set (ZMod 2)[X] := {R | R.coeff 0 = 1 ∧ R.natDegree ≤ D}
  have hfR : Rs.Finite := (finite_mod_two_bounded_degree D).subset (by
    intro R hR
    exact hR.2)
  apply (hfR.biUnion (fun R hR => finite_candidates_fixed_residual R hR.1)).subset
  rintro n ⟨hn,hg,R,hR,hD,a,hm⟩
  exact Set.mem_iUnion.mpr ⟨R,Set.mem_iUnion.mpr ⟨⟨hR,hD⟩,⟨hn,hg,a,hm⟩⟩⟩

/-- A uniform residual-degree bound is sufficient for the original
conjecture. The bound is a hypothesis, not an established assertion. -/
theorem finite_of_uniform_residual_degree (D : ℕ)
    (hbound : ∀ n : ℕ, n.isPowerOfTwo → Nat.digits 3 n ⊆ [0,1] →
      ∃ R : (ZMod 2)[X], R.coeff 0 = 1 ∧ R.natDegree ≤ D ∧ ∃ a : ℕ,
        (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
          (X+1)^a*R) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  exact (finite_candidates_bounded_residual D).subset (by
    rintro n ⟨hn,hg⟩
    exact ⟨hn,hg,hbound n hn hg⟩)

/-- If there are infinitely many candidates, then no bounded-degree
residual family covers them, even allowing arbitrary linear multiplicity. -/
theorem infinite_forces_unbounded_residual_degree
    (hinf : ¬ {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite) (D : ℕ) :
    ∃ n : ℕ, n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1] ∧
      ∀ R : (ZMod 2)[X], R.coeff 0 = 1 →
        (∃ a : ℕ, (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
          (X+1)^a*R) → D < R.natDegree := by
  by_contra hh
  push_neg at hh
  apply hinf
  apply finite_of_uniform_residual_degree D
  intro n hn hg
  obtain ⟨R,hR,hm,hD⟩ := hh n hn hg
  exact ⟨R,hR,hD,hm⟩

#print axioms finite_candidates_bounded_residual
#print axioms finite_of_uniform_residual_degree
#print axioms infinite_forces_unbounded_residual_degree
end Erdos406BoundedResidual
