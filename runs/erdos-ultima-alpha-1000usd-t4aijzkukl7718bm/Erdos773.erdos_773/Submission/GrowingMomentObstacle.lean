import Submission.SignedBlockMoments
import Submission.SmallSignJets

/-!
Polynomial-length collisions with an arbitrarily large number of matching
binary digit moments. This obstructs a proposed sufficient condition, not the
square-Sidon conjecture and not all specifically chosen moment classes.
-/
namespace Erdos773.GrowingMomentObstacle
open Polynomial Finset
noncomputable section
set_option maxHeartbeats 1000000

/-- The first k binary digit moments can agree in a nontrivial four-distinct-root
square collision of word length at most 64*k^3. In particular, the earlier
exponential-length construction is not a length lower bound. -/
theorem matching_moment_collision_cubic (k : ℕ) (hk : 1 ≤ k) :
    ∃ L : ℕ, 4 * (k + 1) ≤ L ∧ L ≤ 64 * k ^ 3 ∧
      ∃ P Q R S : ℤ[X],
        (∀ T ∈ ({P,Q,R,S} : Finset ℤ[X]),
          T ∈ binaryPolynomials ∧ ∀ i, L ≤ i → T.coeff i = 0) ∧
        0 < P.eval 2 ∧ P.eval 2 < R.eval 2 ∧ R.eval 2 < S.eval 2 ∧ S.eval 2 < Q.eval 2 ∧
        (P.eval 2) ^ 2 + (Q.eval 2) ^ 2 = (R.eval 2) ^ 2 + (S.eval 2) ^ 2 ∧
        (∀ j < k, polynomialDigitMoment L P j = polynomialDigitMoment L Q j ∧
          polynomialDigitMoment L P j = polynomialDigitMoment L R j ∧
          polynomialDigitMoment L P j = polynomialDigitMoment L S j) ∧
        ¬ IsSidon ({(P.eval 2)^2, (Q.eval 2)^2, (R.eval 2)^2, (S.eval 2)^2} : Set ℤ) := by
  obtain ⟨V, hV, hdeg, hl, hc, hj⟩ := SmallSignJets.exists_signed_jet_cubic k hk
  have hkle : k ≤ V.natDegree := by
    have hh := natDegree_le_of_dvd hj hV
    simpa only [natDegree_pow, ← C_1, natDegree_X_sub_C, Nat.mul_one] using hh
  have hsum : (X - 1 : ℤ[X]) ^ k ∣
      ∑ i ∈ range (V.natDegree + 1), C (V.coeff i) * X ^ i := by
    rw [← V.as_sum_range_C_mul_X_pow]
    exact hj
  obtain ⟨P,Q,R,S,hw,hp,hpr,hrs,hsq,he,hm⟩ :=
    SignedBlockMoments.collision_from_signed_polynomial V.natDegree k V.coeff
      (fun i hi => hc i) (by simpa only [coeff_natDegree] using hl) hsum
  refine ⟨4*(V.natDegree+1), by omega, by omega,
    P,Q,R,S,hw,hp,hpr,hrs,hsq,he,hm,?_⟩
  intro hs
  have hh := hs _ (by simp) _ (by simp) _ (by simp) _ (by simp) he
  rcases hh with hh | hh
  · nlinarith [sq_nonneg (R.eval 2 - P.eval 2)]
  · nlinarith [sq_nonneg (S.eval 2 - P.eval 2)]

/-- The first k binary digit moments can agree in a nontrivial four-distinct-root
square collision of word length at most 64*k^2*(log2 k + 1). In particular, the earlier
exponential-length construction is not a length lower bound. -/
theorem matching_moment_collision_quadratic_log (k : ℕ) (hk : 1 ≤ k) :
    ∃ L : ℕ, 4 * (k + 1) ≤ L ∧ L ≤ 64 * k ^ 2 * (k.log2 + 1) ∧
      ∃ P Q R S : ℤ[X],
        (∀ T ∈ ({P,Q,R,S} : Finset ℤ[X]),
          T ∈ binaryPolynomials ∧ ∀ i, L ≤ i → T.coeff i = 0) ∧
        0 < P.eval 2 ∧ P.eval 2 < R.eval 2 ∧ R.eval 2 < S.eval 2 ∧ S.eval 2 < Q.eval 2 ∧
        (P.eval 2) ^ 2 + (Q.eval 2) ^ 2 = (R.eval 2) ^ 2 + (S.eval 2) ^ 2 ∧
        (∀ j < k, polynomialDigitMoment L P j = polynomialDigitMoment L Q j ∧
          polynomialDigitMoment L P j = polynomialDigitMoment L R j ∧
          polynomialDigitMoment L P j = polynomialDigitMoment L S j) ∧
        ¬ IsSidon ({(P.eval 2)^2, (Q.eval 2)^2, (R.eval 2)^2, (S.eval 2)^2} : Set ℤ) := by
  obtain ⟨V, hV, hdeg, hl, hc, hj⟩ := SmallSignJets.exists_signed_jet_quadratic_log k hk
  have hkle : k ≤ V.natDegree := by
    have hh := natDegree_le_of_dvd hj hV
    simpa only [natDegree_pow, ← C_1, natDegree_X_sub_C, Nat.mul_one] using hh
  have hsum : (X - 1 : ℤ[X]) ^ k ∣
      ∑ i ∈ range (V.natDegree + 1), C (V.coeff i) * X ^ i := by
    rw [← V.as_sum_range_C_mul_X_pow]
    exact hj
  obtain ⟨P,Q,R,S,hw,hp,hpr,hrs,hsq,he,hm⟩ :=
    SignedBlockMoments.collision_from_signed_polynomial V.natDegree k V.coeff
      (fun i hi => hc i) (by simpa only [coeff_natDegree] using hl) hsum
  refine ⟨4*(V.natDegree+1), by omega, by nlinarith only [hdeg],
    P,Q,R,S,hw,hp,hpr,hrs,hsq,he,hm,?_⟩
  intro hs
  have hh := hs _ (by simp) _ (by simp) _ (by simp) _ (by simp) he
  rcases hh with hh | hh
  · nlinarith [sq_nonneg (R.eval 2 - P.eval 2)]
  · nlinarith [sq_nonneg (S.eval 2 - P.eval 2)]

#print axioms matching_moment_collision_quadratic_log

#print axioms matching_moment_collision_cubic
end
end Erdos773.GrowingMomentObstacle
