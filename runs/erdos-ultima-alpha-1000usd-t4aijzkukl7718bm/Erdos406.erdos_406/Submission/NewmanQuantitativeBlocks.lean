import Submission.NewmanFrobeniusMultiplicityBound

/-! Quantitative block exclusions at every positive ternary power input.
These preserve the exact binary overlap condition and do not replace it
by a coefficient-height or root-only estimate. -/
namespace Erdos406QuantitativeBlocks
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406FixedResidualTools Erdos406FixedResidual
  Erdos406CubicHighBase Erdos406BinaryBlocks Erdos406FrobeniusBound

/-- The same overlap correction controls evaluation at every input, not
only at one. -/
lemma pattern_eq_geometric_correction {A : Type*} [CommRing A] (U V W : A[X])
    (T M : ℕ) (hM : 0 < M) :
    pattern U V W T M = ((X^T-1)*V+W)*geo T M+(U+V-W) := by
  have hprev : X^((M-1)*T) = (geo T (M-1) : A[X])*(X^T-1)+1 := by
    rw [geo_mul]
    ring
  have hgeo : (geo T M : A[X]) = 1+X^T*geo T (M-1) := by
    conv_lhs => rw [show M = M-1+1 by omega]
    exact geo_succ_first T (M-1)
  rw [pattern,hprev,hgeo]
  ring

lemma nonnegative_eval_mono (P : ℤ[X]) (hP : ∀ i, 0 ≤ P.coeff i)
    (x y : ℤ) (hx : 0 ≤ x) (hxy : x ≤ y) : P.eval x ≤ P.eval y := by
  rw [eval_eq_sum_range x,eval_eq_sum_range y]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy i) (hP i)

lemma xor_correction_eval_bound (U V W : ℤ[X]) (hU : Binary U) (hV : Binary V) (hW : Binary W)
    (hm : W.map (Int.castRingHom (ZMod 2)) =
      U.map (Int.castRingHom (ZMod 2))+V.map (Int.castRingHom (ZMod 2)))
    (T : ℕ) (hDU : U.natDegree < T) (hDV : V.natDegree < T) (hDW : W.natDegree < T)
    (x : ℤ) (hx : 3 ≤ x) :
    (U+V-W = 0 ∨ 0 < (U+V-W).eval x) ∧ (U+V-W).eval x < x^T := by
  let J := U+V-W
  have hj (i : ℕ) : J.coeff i = 0 ∨ J.coeff i = 2 :=
    xor_coeff_correction U V W hU hV hW hm i
  have hnn (i : ℕ) : 0 ≤ J.coeff i := by rcases hj i with h | h <;> omega
  have hdeg : J.natDegree < T :=
    (natDegree_sub_le (U+V) W).trans_lt
      (max_lt ((natDegree_add_le U V).trans_lt (max_lt hDU hDV)) hDW)
  constructor
  · rcases (xor_correction_bound U V W hU hV hW hm T hDU hDV hDW).1 with hz | hpos
    · exact Or.inl hz
    · right
      have hh := nonnegative_eval_mono J hnn 1 x (by decide) (by omega)
      change 0 < J.eval x
      change 0 < J.eval 1 at hpos
      omega
  · change J.eval x < x^T
    have hb : J.eval x ≤ (x-1)*(∑ i ∈ Finset.range T, x^i) := by
      rw [eval_eq_sum_range' hdeg,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hcoeff : J.coeff i ≤ x-1 := by rcases hj i with h | h <;> omega
      exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
    rw [mul_comm,geom_sum_mul] at hb
    omega

lemma geo_power_two_eval_divisibility (L T v : ℕ) (hT : 0 < T) :
    (2 : ℤ)^v ∣ (geo T (2^v) : ℤ[X]).eval ((3 : ℤ)^L) := by
  induction v generalizing T with
  | zero => simp
  | succ v ih =>
    have hEven : (2 : ℤ) ∣ ((3 : ℤ)^L)^T+1 := by
      exact even_iff_two_dvd.mp
        (((show Odd (3 : ℤ) by decide).pow (n := L)).pow (n := T)).add_one
    rw [pow_succ' (2 : ℕ),geo_double T _ hT,eval_mul,eval_add,eval_pow,eval_X,eval_one,
      pow_succ' (2 : ℤ)]
    exact mul_dvd_mul hEven (ih (2*T) (by omega))

/-- A sufficiently long binary block pattern cannot have pure-power value
at 3^L. The length threshold depends only on the block width and L. -/
theorem binary_block_no_large_length (P : ℤ[X]) (hP : Binary P) (S : (ZMod 2)[X])
    (T v L k : ℕ) (hT : 0 < T) (hL : 0 < L) (hv : 2*L*T ≤ v)
    (hdeg : v ≤ P.natDegree) (hS : S.natDegree < 2*T)
    (hm : (X^T-1)*P.map (Int.castRingHom (ZMod 2)) = (X^(2^v*T)-1)*S) :
    P.eval ((3 : ℤ)^L) ≠ (2 : ℤ)^k := by
  intro he
  have hv2 : 2 ≤ v := by nlinarith
  obtain ⟨U,V,W,hU,hV,hW,hDU,hDV,hDW,hmW,hp⟩ :=
    binary_block_representation P hP S T (2^v) hT (by positivity) hS hm
  have hx : (3 : ℤ) ≤ 3^L := by
    simpa using pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 3) hL
  obtain ⟨hJ,hJbound⟩ := xor_correction_eval_bound U V W hU hV hW hmW T hDU hDV hDW _ hx
  rcases hJ with hJ | hJ
  · exact zero_correction_not_power_value U V W T v L k hT hv2 hL hJ (by rwa [← hp])
  have hnz : P ≠ 0 := by
    intro hz
    rw [hz,natDegree_zero] at hdeg
    omega
  have hk : v ≤ k := by
    have hb : (2 : ℤ)^v ≤ 2^k := calc
      _ ≤ (3^L)^v := pow_le_pow_left₀ (by decide) (by omega) v
      _ ≤ P.eval ((3 : ℤ)^L) := binary_eval_lower_bound_at P hP hnz v hdeg _ (by omega)
      _ = _ := he
    by_contra hh
    have hlt : (2 : ℤ)^k < 2^v := pow_lt_pow_right₀ (by decide) (by omega)
    omega
  have hgeo := geo_power_two_eval_divisibility L T v hT
  have hdP : (2 : ℤ)^v ∣ P.eval ((3 : ℤ)^L) := by rw [he]; exact pow_dvd_pow 2 hk
  rw [hp,pattern_eq_geometric_correction _ _ _ T (2^v) (by positivity),eval_add,eval_mul] at hdP
  have hdJ : (2 : ℤ)^v ∣ (U+V-W).eval ((3 : ℤ)^L) := by
    convert dvd_sub hdP (dvd_mul_of_dvd_right hgeo (((X^T-1)*V+W).eval ((3 : ℤ)^L))) using 1
    ring
  have hle := Int.le_of_dvd hJ hdJ
  have hsmall : ((3 : ℤ)^L)^T ≤ (2 : ℤ)^v := calc
    ((3 : ℤ)^L)^T = 3^(L*T) := by rw [← pow_mul]
    _ ≤ (4 : ℤ)^(L*T) := pow_le_pow_left₀ (by decide) (by decide) _
    _ = (2 : ℤ)^(2*L*T) := by
      rw [mul_assoc,pow_mul (2 : ℤ) 2 (L*T)]
      norm_num
    _ ≤ (2 : ℤ)^v := pow_le_pow_right₀ (by decide) hv
  omega

#print axioms pattern_eq_geometric_correction
#print axioms xor_correction_eval_bound
#print axioms binary_block_no_large_length
end Erdos406QuantitativeBlocks
