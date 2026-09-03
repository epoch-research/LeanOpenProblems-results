import Submission.NewmanModTwoCubic

/-! Exact Frobenius deflation for arbitrary residual reductions over F₂.
This is a structural result with an explicit reduction hypothesis, not an
exponent bound or a proof of the Erdős finiteness conjecture. -/
namespace Erdos406ModTwoFrobenius
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406ModTwoCubic Erdos406Cyclotomic
  Erdos406ReciprocalCandidate

lemma liftTwo_constant_one (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) :
    (liftTwo R).coeff 0 = 1 := by
  rw [coeff_liftTwo,hR]
  decide

lemma binary_constant_one_of_map (P : ℤ[X]) (hP : Binary P)
    (hm : (P.map (Int.castRingHom (ZMod 2))).coeff 0 = 1) : P.coeff 0 = 1 := by
  rw [coeff_map] at hm
  rcases hP 0 with h | h
  · simp [h] at hm
  · exact h

lemma residual_constant_one (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (a b : ℕ) :
    ((X+1)^a*R^b).coeff 0 = 1 := by
  have hr : R.eval 0 = 1 := by rwa [← coeff_zero_eq_eval_zero]
  simp [coeff_zero_eq_eval_zero,hr]

/-- One deflation step. A linear factor can be removed only at the original
base three, not at any higher power-of-three base. -/
theorem frobenius_step (P : ℤ[X]) (hP : Binary P) (R : (ZMod 2)[X])
    (hR : R.coeff 0 = 1) (a L k : ℕ) (hL : 0 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R^2)
    (he : P.eval ((3 : ℤ)^L) = (2 : ℤ)^k) :
    ∃ Q : ℤ[X], ∃ j : ℕ, Binary Q ∧ Q.coeff 0 = 1 ∧
      Q.map (Int.castRingHom (ZMod 2)) = (X+1)^(a/2)*R ∧
      Q.eval ((3 : ℤ)^(2*L)) = (2 : ℤ)^j ∧
      (P = expand ℤ 2 Q ∨ (L = 1 ∧ P = (X+1)*expand ℤ 2 Q)) := by
  let Q : ℤ[X] := liftTwo ((X+1)^(a/2)*R)
  have hQ : Binary Q := binary_liftTwo _
  have hmQ : Q.map (Int.castRingHom (ZMod 2)) = (X+1)^(a/2)*R := map_liftTwo _
  have hQ0 : Q.coeff 0 = 1 := by
    apply liftTwo_constant_one
    simpa only [pow_one] using residual_constant_one R hR (a/2) 1
  have hmE : (expand ℤ 2 Q).map (Int.castRingHom (ZMod 2)) = (X+1)^(2*(a/2))*R^2 := by
    rw [map_expand,hmQ,expand_two_eq_square,mul_pow,← pow_mul,Nat.mul_comm (a/2) 2]
  have hshape : P = expand ℤ 2 Q ∨ (L = 1 ∧ P = (X+1)*expand ℤ 2 Q) := by
    by_cases ha : a%2 = 0
    · left
      apply binary_map_two_injective _ _ hP (binary_expand_two Q hQ)
      rw [hm,hmE,show 2*(a/2) = a by omega]
    · have hp : P = (X+1)*expand ℤ 2 Q := by
        apply binary_map_two_injective _ _ hP (binary_interlace Q hQ)
        rw [hm,Polynomial.map_mul,Polynomial.map_add,map_X,Polynomial.map_one,hmE]
        conv_lhs => rw [show a = 2*(a/2)+1 by omega,pow_succ']
        ring
      have hd : 3^L+1 ∣ 2^k := by
        have hv : ((3 : ℤ)^L+1) ∣ (2 : ℤ)^k := by
          rw [← he,hp,eval_mul,eval_add,eval_X,eval_one]
          exact dvd_mul_right _ _
        exact_mod_cast hv
      exact Or.inr ⟨Erdos406Structure.three_pow_add_one_dvd_two_pow hL hd,hp⟩
  have hdiv : Q.eval ((3 : ℤ)^(2*L)) ∣ (2 : ℤ)^k := by
    rcases hshape with hp | ⟨_,hp⟩
    · rw [hp,expand_eval,← pow_mul,Nat.mul_comm L 2] at he
      rw [he]
    · rw [hp,eval_mul,expand_eval,← pow_mul,Nat.mul_comm L 2] at he
      exact ⟨(X+1 : ℤ[X]).eval ((3 : ℤ)^L),by rw [← he]; ring⟩
  obtain ⟨j,hj⟩ := positive_int_dvd_two_power _
    (binary_eval_pos Q hQ hQ0 _ (by positivity)) k hdiv
  exact ⟨Q,j,hQ,hQ0,hmQ,hj,hshape⟩

/-- In arbitrary degree, all but possibly the lowest linear bit disappear
under a Frobenius deflation of a pure-power-valued binary polynomial.
The exponent j of the deflated evaluation is NOT asserted to be smaller. -/
theorem frobenius_deflation (t : ℕ) (P : ℤ[X]) (hP : Binary P)
    (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (a L k : ℕ) (hL : 0 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R^(2^t))
    (he : P.eval ((3 : ℤ)^L) = (2 : ℤ)^k) :
    ∃ Q : ℤ[X], ∃ j : ℕ, Binary Q ∧ Q.coeff 0 = 1 ∧
      Q.map (Int.castRingHom (ZMod 2)) = (X+1)^(a/(2^t))*R ∧
      Q.eval ((3 : ℤ)^(2^t*L)) = (2 : ℤ)^j ∧
      (P = expand ℤ (2^t) Q ∨ (L = 1 ∧ P = (X+1)*expand ℤ (2^t) Q)) := by
  induction t generalizing P a L k with
  | zero =>
    have h0 : P.coeff 0 = 1 := by
      apply binary_constant_one_of_map P hP
      rw [hm,residual_constant_one R hR a (2^0)]
    refine ⟨P,k,hP,h0,?_,?_,Or.inl ?_⟩
    · simpa using hm
    · simpa using he
    · simp
  | succ t ih =>
    have hr : (R^(2^t)).coeff 0 = 1 := by
      simpa using residual_constant_one R hR 0 (2^t)
    have hm' : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*(R^(2^t))^2 := by
      simpa only [← pow_mul,← pow_succ] using hm
    obtain ⟨A,b,hA,_,hmA,heA,hshape⟩ := frobenius_step P hP (R^(2^t)) hr a L k hL hm' he
    obtain ⟨Q,j,hQ,hQ0,hmQ,heQ,hshapeA⟩ := ih A hA (a/2) (2*L) b (by omega) hmA heA
    have hAQ : A = expand ℤ (2^t) Q := by
      rcases hshapeA with hh | ⟨hh,_⟩
      · exact hh
      · omega
    have hdiv : (a/2)/(2^t) = a/(2^(t+1)) := by
      rw [Nat.div_div_eq_div_mul,pow_succ']
    have hpow : 2^t*(2*L) = 2^(t+1)*L := by rw [pow_succ]; ring
    rw [hdiv] at hmQ
    rw [hpow] at heQ
    refine ⟨Q,j,hQ,hQ0,hmQ,heQ,?_⟩
    rcases hshape with hp | ⟨hL1,hp⟩
    · left
      rw [hp,hAQ,expand_expand,← pow_succ']
    · right
      refine ⟨hL1,?_⟩
      rw [hp,hAQ,expand_expand,← pow_succ']

/-- At every higher power-of-three base there is no exceptional X+1 factor. -/
theorem frobenius_deflation_high_base (t : ℕ) (P : ℤ[X]) (hP : Binary P)
    (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (a L k : ℕ) (hL : 1 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R^(2^t))
    (he : P.eval ((3 : ℤ)^L) = (2 : ℤ)^k) :
    ∃ Q : ℤ[X], ∃ j : ℕ, Binary Q ∧ Q.coeff 0 = 1 ∧
      Q.map (Int.castRingHom (ZMod 2)) = (X+1)^(a/(2^t))*R ∧
      Q.eval ((3 : ℤ)^(2^t*L)) = (2 : ℤ)^j ∧ P = expand ℤ (2^t) Q := by
  obtain ⟨Q,j,hQ,h0,hmQ,heQ,hshape⟩ := frobenius_deflation t P hP R hR a L k
    (by omega) hm he
  refine ⟨Q,j,hQ,h0,hmQ,heQ,?_⟩
  rcases hshape with hp | ⟨hh,_⟩
  · exact hp
  · omega

/-- Direct structural consequence for the original candidates. This allows
unbounded degrees for the residual polynomial R and does not bound n. -/
theorem candidate_frobenius_deflation (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1]) (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (a t : ℕ)
    (hm : (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
      (X+1)^a*R^(2^t)) :
    ∃ Q : ℤ[X], ∃ j : ℕ, Binary Q ∧ Q.coeff 0 = 1 ∧
      Q.map (Int.castRingHom (ZMod 2)) = (X+1)^(a/(2^t))*R ∧
      Q.eval ((3 : ℤ)^(2^t)) = (2 : ℤ)^j ∧
      (digitPoly (Nat.digits 3 n) = expand ℤ (2^t) Q ∨
        digitPoly (Nat.digits 3 n) = (X+1)*expand ℤ (2^t) Q) := by
  obtain ⟨k,rfl⟩ := hn
  have he : (digitPoly (Nat.digits 3 (2^k))).eval ((3 : ℤ)^1) = (2 : ℤ)^k := by
    rw [pow_one,digitPoly_eval_three]
    norm_cast
  simpa using frobenius_deflation t _ (binary_digitPoly _ hg) R hR a 1 k (by decide) hm he

#print axioms frobenius_step
#print axioms frobenius_deflation
#print axioms frobenius_deflation_high_base
#print axioms candidate_frobenius_deflation
end Erdos406ModTwoFrobenius
