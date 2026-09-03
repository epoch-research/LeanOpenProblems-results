import Submission.NewmanFrobeniusMultiplicityBound
import Submission.NewmanAllPatternDilations
import Submission.NewmanBoundedResidual

/-! Finiteness with a fixed residual shape, allowing arbitrary linear
multiplicity and arbitrary pure Frobenius multiplicity. Unbounded variation
of the residual shape is not controlled by this theorem. -/
namespace Erdos406FixedFrobeniusResidual
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406ModTwoFrobenius Erdos406FixedResidualTools
  Erdos406FixedResidual Erdos406BinaryBlocks Erdos406FrobeniusBound
  Erdos406AllDilations Erdos406BoundedResidual
  Erdos406Cyclotomic Erdos406ReciprocalCandidate

lemma residual_positive_degree (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (hne : R ≠ 1) :
    0 < R.natDegree := by
  by_contra hh
  have he := eq_C_of_natDegree_eq_zero (show R.natDegree = 0 by omega)
  apply hne
  simpa [hR] using he

lemma binary_monic_of_constant_one (P : ℤ[X]) (hP : Binary P) (h0 : P.coeff 0 = 1) :
    P.Monic := by
  have hnz : P ≠ 0 := by intro hh; simp [hh] at h0
  rcases hP P.natDegree with h | h
  · exact (leadingCoeff_ne_zero.mpr hnz h).elim
  · exact h

noncomputable def corePoly (R : (ZMod 2)[X]) (b : ℕ) : ℤ[X] := liftTwo ((X+1)^b*R)

def coreValues (R : (ZMod 2)[X]) (B : ℕ) : Set ℕ :=
  {n | ∃ b : ℕ, b < B ∧ ∃ L k : ℕ, (corePoly R b).eval ((3 : ℤ)^L) = (2 : ℤ)^k ∧ n = 2^k}

lemma finite_core_values (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (hne : R ≠ 1) (B : ℕ) :
    (coreValues R B).Finite := by
  have hP (b : ℕ) : Binary (corePoly R b) := binary_liftTwo _
  have h0 (b : ℕ) : (corePoly R b).coeff 0 = 1 := by
    apply liftTwo_constant_one
    simpa using residual_constant_one R hR b 1
  have hdeg (b : ℕ) : 0 < (corePoly R b).natDegree := by
    have hm : (corePoly R b).map (Int.castRingHom (ZMod 2)) = (X+1)^b*R := map_liftTwo _
    rw [residual_degree _ (hP b) R hR b hm]
    have hh := residual_positive_degree R hR hne
    omega
  have hf (b : ℕ) := finite_pattern_dilations (corePoly R b) (hP b)
    (binary_monic_of_constant_one _ (hP b) (h0 b)) (h0 b) (hdeg b)
  apply ((Set.finite_lt_nat B).biUnion (fun b _ =>
    (hf b).image (fun L => ((corePoly R b).eval ((3 : ℤ)^L)).natAbs))).subset
  rintro n ⟨b,hb,L,k,he,rfl⟩
  refine Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨hb,?_⟩⟩
  refine ⟨L,⟨k,he⟩,?_⟩
  change ((corePoly R b).eval ((3 : ℤ)^L)).natAbs = 2^k
  rw [he]
  simp

/-- The residual R is fixed, but neither a nor t is bounded in advance.
This is strictly stronger than fixed-residual finiteness without Frobenius
multiplicity, and still does not cover arbitrary residual shapes. -/
theorem finite_candidates_fixed_frobenius_residual (R : (ZMod 2)[X])
    (hR : R.coeff 0 = 1) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1] ∧ ∃ a t : ℕ,
      (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
        (X+1)^a*R^(2^t)}.Finite := by
  by_cases hne : R = 1
  · apply (finite_candidates_fixed_residual 1 (by simp)).subset
    rintro n ⟨hn,hg,a,t,hm⟩
    refine ⟨hn,hg,a,?_⟩
    simpa [hne] using hm
  let s := R.natDegree+2
  let B := 2^(2*R.natDegree+2)
  have hpow0 (t : ℕ) : (R^(2^t)).coeff 0 = 1 := by
    simpa using residual_constant_one R hR 0 (2^t)
  have hfsmall := (Set.finite_lt_nat s).biUnion (fun t _ =>
    finite_candidates_fixed_residual (R^(2^t)) (hpow0 t))
  have hfvalues := finite_core_values R hR hne B
  apply (hfsmall.union (hfvalues.union (hfvalues.image (fun n : ℕ => 4*n)))).subset
  rintro n ⟨⟨k,rfl⟩,hg,a,t,hm⟩
  by_cases ht : t < s
  · left
    exact Set.mem_iUnion.mpr ⟨t,Set.mem_iUnion.mpr ⟨ht,⟨⟨k,rfl⟩,hg,a,hm⟩⟩⟩
  right
  have he : (digitPoly (Nat.digits 3 (2^k))).eval ((3 : ℤ)^1) = (2 : ℤ)^k := by
    rw [pow_one,digitPoly_eval_three]
    norm_cast
  obtain ⟨Q,j,hQ,_,hmQ,heQ,hshape⟩ := frobenius_deflation t _ (binary_digitPoly _ hg)
    R hR a 1 k (by decide) hm he
  have heQ' : Q.eval ((3 : ℤ)^(2^t)) = (2 : ℤ)^j := by simpa using heQ
  have hb : a/2^t < B := linear_multiplicity_bound_at_high_base Q hQ R hR (a/2^t) t j
    (by dsimp [s] at ht; omega) hmQ heQ'
  have hQeq : Q = corePoly R (a/2^t) :=
    binary_map_two_injective _ _ hQ (binary_liftTwo _) (hmQ.trans (map_liftTwo _).symm)
  have hval : 2^j ∈ coreValues R B :=
    ⟨a/2^t,hb,2^t,j,by rwa [← hQeq],rfl⟩
  rcases hshape with hp | ⟨_,hp⟩
  · left
    have hh := congrArg (eval (3 : ℤ)) hp
    rw [digitPoly_eval_three,expand_eval,heQ'] at hh
    have hnat : (2 : ℕ)^k = 2^j := by exact_mod_cast hh
    rwa [hnat]
  · right
    have hh := congrArg (eval (3 : ℤ)) hp
    rw [digitPoly_eval_three,eval_mul,eval_add,eval_X,eval_one,expand_eval,heQ'] at hh
    have hnat : (2 : ℕ)^k = 4*2^j := by norm_num at hh; exact_mod_cast hh
    exact ⟨2^j,hval,hnat.symm⟩

/-- Bounded residual degree remains sufficient even after allowing
arbitrary pure Frobenius powers of every residual polynomial. -/
theorem finite_candidates_bounded_frobenius_residual (D : ℕ) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1] ∧
      ∃ R : (ZMod 2)[X], R.coeff 0 = 1 ∧ R.natDegree ≤ D ∧ ∃ a t : ℕ,
        (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
          (X+1)^a*R^(2^t)}.Finite := by
  let Rs : Set (ZMod 2)[X] := {R | R.coeff 0 = 1 ∧ R.natDegree ≤ D}
  have hfR : Rs.Finite := (finite_mod_two_bounded_degree D).subset (by
    intro R hR
    exact hR.2)
  apply (hfR.biUnion (fun R hR => finite_candidates_fixed_frobenius_residual R hR.1)).subset
  rintro n ⟨hn,hg,R,hR,hD,a,t,hm⟩
  exact Set.mem_iUnion.mpr ⟨R,Set.mem_iUnion.mpr ⟨⟨hR,hD⟩,⟨hn,hg,a,t,hm⟩⟩⟩

#print axioms finite_core_values
#print axioms finite_candidates_fixed_frobenius_residual
#print axioms finite_candidates_bounded_frobenius_residual
end Erdos406FixedFrobeniusResidual
