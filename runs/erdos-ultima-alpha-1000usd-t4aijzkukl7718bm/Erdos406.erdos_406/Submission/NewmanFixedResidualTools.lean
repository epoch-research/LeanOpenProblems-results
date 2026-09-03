import Submission.NewmanModTwoFrobenius

/-! Polynomial tools for finiteness with a fixed residual reduction over F₂.
These lemmas do not impose a bound on the residual polynomial. -/
namespace Erdos406FixedResidualTools
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic

lemma natDegree_liftTwo (R : (ZMod 2)[X]) : (liftTwo R).natDegree = R.natDegree := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_liftTwo,coeff_eq_zero_of_natDegree_lt hi]
    simp
  · simpa only [map_liftTwo] using
      (natDegree_map_le (f := Int.castRingHom (ZMod 2)) (p := liftTwo R))

lemma binary_eq_lift_map (P : ℤ[X]) (hP : Binary P) :
    P = liftTwo (P.map (Int.castRingHom (ZMod 2))) :=
  binary_map_two_injective _ _ hP (binary_liftTwo _) (map_liftTwo _).symm

lemma binary_natDegree_map (P : ℤ[X]) (hP : Binary P) :
    (P.map (Int.castRingHom (ZMod 2))).natDegree = P.natDegree := by
  conv_rhs => rw [binary_eq_lift_map P hP,natDegree_liftTwo]

lemma residual_ne_zero (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) : R ≠ 0 := by
  intro hh
  simp [hh] at hR

lemma residual_degree (P : ℤ[X]) (hP : Binary P) (R : (ZMod 2)[X])
    (hR : R.coeff 0 = 1) (a : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R) :
    P.natDegree = a+R.natDegree := by
  have hx : (X+1 : (ZMod 2)[X]) ≠ 0 := by simpa using X_add_C_ne_zero (1 : ZMod 2)
  rw [← binary_natDegree_map P hP,hm,natDegree_mul
    (pow_ne_zero _ hx) (residual_ne_zero R hR),natDegree_pow]
  have hxd : (X+1 : (ZMod 2)[X]).natDegree = 1 := by
    simpa using natDegree_X_add_C (1 : ZMod 2)
  rw [hxd,mul_one]

lemma binary_separated_binomial (Q : ℤ[X]) (hQ : Binary Q) (N : ℕ)
    (hN : Q.natDegree < N) : Binary ((X^N+1)*Q) := by
  intro i
  rw [add_mul,one_mul,coeff_add,coeff_X_pow_mul']
  by_cases hi : N ≤ i
  · rw [if_pos hi,coeff_eq_zero_of_natDegree_lt (hN.trans_le hi),add_zero]
    exact hQ _
  · rw [if_neg hi,zero_add]
    exact hQ _

lemma separated_binomial_lift (P : ℤ[X]) (hP : Binary P) (S : (ZMod 2)[X])
    (N : ℕ) (hN : S.natDegree < N)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X^N+1)*S) :
    P = (X^N+1)*liftTwo S := by
  apply binary_map_two_injective _ _ hP
    (binary_separated_binomial _ (binary_liftTwo S) N (by rwa [natDegree_liftTwo]))
  simp only [Polynomial.map_mul,Polynomial.map_add,Polynomial.map_pow,map_X,
    Polynomial.map_one,map_liftTwo,hm]

lemma shifted_binary_difference_bound (P : ℤ[X]) (hP : Binary P) (T i : ℕ) :
    |((X^T-1)*P).coeff i| ≤ 1 := by
  rw [sub_mul,one_mul,coeff_sub,coeff_X_pow_mul']
  split_ifs with hi
  · rcases hP (i-T) with hh | hh <;> rcases hP i with hh' | hh' <;>
      simp [hh,hh']
  · rcases hP i with hh | hh <;> simp [hh]

lemma small_coeff_zero_of_map_zero (F : ℤ[X]) (i : ℕ)
    (hb : |F.coeff i| ≤ 1)
    (hz : (F.map (Int.castRingHom (ZMod 2))).coeff i = 0) : F.coeff i = 0 := by
  rw [coeff_map] at hz
  have hd : (2 : ℤ) ∣ F.coeff i :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (F.coeff i) 2).mp hz
  obtain ⟨j,hj⟩ := hd
  have hh := abs_le.mp hb
  omega

lemma middle_coeff_zero (P : ℤ[X]) (hP : Binary P) (S : (ZMod 2)[X])
    (T N K i : ℕ) (hS : S.natDegree < K) (hi : K ≤ i) (hiN : i < N)
    (hm : (((X^T-1)*P).map (Int.castRingHom (ZMod 2))) = (X^N+1)*S) :
    ((X^T-1)*P).coeff i = 0 := by
  apply small_coeff_zero_of_map_zero _ _ (shifted_binary_difference_bound P hP T i)
  rw [hm,add_mul,one_mul,coeff_add,coeff_X_pow_mul',if_neg (by omega),zero_add]
  exact coeff_eq_zero_of_natDegree_lt (hS.trans_le hi)

noncomputable def endValue (F : ℤ[X]) (start K : ℕ) : ℤ :=
  ∑ i ∈ Finset.range K, F.coeff (start+i)*3^i

noncomputable def endBound (K : ℕ) : ℤ := ∑ i ∈ Finset.range K, 3^i

lemma endValue_bound (F : ℤ[X]) (start K : ℕ)
    (hF : ∀ i, |F.coeff i| ≤ 1) : |endValue F start K| ≤ endBound K := by
  calc
    _ ≤ ∑ i ∈ Finset.range K, |F.coeff (start+i)*3^i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ endBound K := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (show (0 : ℤ) ≤ 3^i by positivity)]
      simpa using mul_le_mul_of_nonneg_right (hF (start+i))
        (show (0 : ℤ) ≤ 3^i by positivity)

lemma endBound_lt (K : ℕ) : endBound K < (3 : ℤ)^K := by
  have hh := geom_sum_mul (3 : ℤ) K
  change endBound K*(3-1) = 3^K-1 at hh
  have hp : (0 : ℤ) < 3^K := by positivity
  linarith

lemma endBound_nonneg (K : ℕ) : 0 ≤ endBound K := by
  exact Finset.sum_nonneg (fun _ _ => by positivity)

lemma eval_eq_endValues (F : ℤ[X]) (N K : ℕ) (hKN : K ≤ N)
    (hdeg : F.natDegree < N+K) (hz : ∀ i, K ≤ i → i < N → F.coeff i = 0) :
    F.eval 3 = endValue F 0 K+3^N*endValue F N K := by
  rw [eval_eq_sum_range' hdeg,Finset.sum_range_add]
  have hlo : (∑ i ∈ Finset.range N, F.coeff i*3^i) = endValue F 0 K := by
    rw [show N = K+(N-K) from (Nat.add_sub_of_le hKN).symm,
      Finset.sum_range_add]
    have hzero : (∑ i ∈ Finset.range (N-K), F.coeff (K+i)*3^(K+i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hz (K+i) (by omega) (by have := Finset.mem_range.mp hi; omega),zero_mul]
    rw [hzero,add_zero]
    simp [endValue]
  rw [hlo]
  congr 1
  simp only [endValue,Finset.mul_sum,pow_add]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma binary_eval_lower_bound (P : ℤ[X]) (hP : Binary P) (hnz : P ≠ 0)
    (N : ℕ) (hN : N ≤ P.natDegree) : (3 : ℤ)^N ≤ P.eval 3 := by
  have hlc : P.coeff P.natDegree = 1 := by
    rcases hP P.natDegree with hh | hh
    · exact (leadingCoeff_ne_zero.mpr hnz hh).elim
    · exact hh
  calc
    (3 : ℤ)^N ≤ 3^P.natDegree := pow_le_pow_right₀ (by decide) hN
    _ = P.coeff P.natDegree*3^P.natDegree := by rw [hlc,one_mul]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree+1), P.coeff i*3^i := by
      apply Finset.single_le_sum (f := fun i => P.coeff i*(3 : ℤ)^i)
      · intro i _
        rcases hP i with hh | hh <;> rw [hh] <;> positivity
      · exact Finset.mem_range.mpr (by omega)
    _ = P.eval 3 := (eval_eq_sum_range 3).symm

#print axioms eval_eq_endValues
#print axioms binary_eval_lower_bound
end Erdos406FixedResidualTools
