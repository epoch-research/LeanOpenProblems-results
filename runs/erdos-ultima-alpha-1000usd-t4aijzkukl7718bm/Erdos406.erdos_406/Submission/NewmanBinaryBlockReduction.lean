import Submission.NewmanBinaryBlockTools
import Submission.NewmanCubicHighBase

/-! Recovering integer binary block patterns from a mod-two geometric
identity, and excluding zero-overlap long geometric patterns. -/
namespace Erdos406BinaryBlocks
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406FixedResidualTools Erdos406FixedResidual
  Erdos406CubicHighBase

/-- The two end blocks and the repeated middle block are binary. The middle
is their coefficientwise exclusive-or, not their integer sum in general. -/
theorem binary_block_representation (P : ℤ[X]) (hP : Binary P) (S : (ZMod 2)[X])
    (T M : ℕ) (hT : 0 < T) (hM : 0 < M) (hS : S.natDegree < 2*T)
    (hm : (X^T-1)*P.map (Int.castRingHom (ZMod 2)) = (X^(M*T)-1)*S) :
    ∃ U V W : ℤ[X], Binary U ∧ Binary V ∧ Binary W ∧
      U.natDegree < T ∧ V.natDegree < T ∧ W.natDegree < T ∧
      W.map (Int.castRingHom (ZMod 2)) =
        U.map (Int.castRingHom (ZMod 2))+V.map (Int.castRingHom (ZMod 2)) ∧
      P = pattern U V W T M := by
  let Z := liftTwo S
  let U := cut Z 0 T
  let V := cut Z T T
  let W := liftTwo (U.map (Int.castRingHom (ZMod 2))+V.map (Int.castRingHom (ZMod 2)))
  have hU : Binary U := binary_cut Z (binary_liftTwo S) 0 T
  have hV : Binary V := binary_cut Z (binary_liftTwo S) T T
  have hW : Binary W := binary_liftTwo _
  have hDU : U.natDegree < T := cut_degree Z 0 T hT
  have hDV : V.natDegree < T := cut_degree Z T T hT
  have hmW : W.map (Int.castRingHom (ZMod 2)) =
      U.map (Int.castRingHom (ZMod 2))+V.map (Int.castRingHom (ZMod 2)) := map_liftTwo _
  have hDW : W.natDegree < T := by
    dsimp [W]
    rw [natDegree_liftTwo]
    apply (natDegree_add_le _ _).trans_lt
    exact max_lt (natDegree_map_le.trans_lt hDU) (natDegree_map_le.trans_lt hDV)
  have hZ : Z = U+X^T*V := cut_decomposition Z T (by dsimp [Z]; rwa [natDegree_liftTwo])
  have hmZ : U.map (Int.castRingHom (ZMod 2))+X^T*V.map (Int.castRingHom (ZMod 2)) = S := by
    have hh := congrArg (Polynomial.map (Int.castRingHom (ZMod 2))) hZ
    change (liftTwo S).map _ = (U+X^T*V).map _ at hh
    rw [map_liftTwo,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,map_X] at hh
    exact hh.symm
  have hmPattern : (pattern U V W T M).map (Int.castRingHom (ZMod 2)) = S*geo T M := by
    rw [map_pattern,hmW,pattern_eq_geometric _ _ T M hM,hmZ]
  have hp : P = pattern U V W T M := by
    apply binary_map_two_injective _ _ hP (binary_pattern U V W hU hV hW T M hDU hDW)
    have hx : (X^T-1 : (ZMod 2)[X]) ≠ 0 := by simpa using X_pow_sub_C_ne_zero hT (1 : ZMod 2)
    apply mul_left_cancel₀ hx
    rw [hm,hmPattern]
    calc
      _ = S*(geo T M*(X^T-1)) := by rw [geo_mul]; ring
      _ = _ := by ring
  exact ⟨U,V,W,hU,hV,hW,hDU,hDV,hDW,hmW,hp⟩

lemma geo_double (T M : ℕ) (hT : 0 < T) :
    (geo T (2*M) : ℤ[X]) = (X^T+1)*geo (2*T) M := by
  have hx : (X^T-1 : ℤ[X]) ≠ 0 := by simpa using X_pow_sub_C_ne_zero hT (1 : ℤ)
  apply mul_right_cancel₀ hx
  calc
    _ = X^((2*M)*T)-1 := geo_mul T (2*M)
    _ = X^(M*(2*T))-1 := by congr 2; ring
    _ = geo (2*T) M*(X^(2*T)-1) := (geo_mul (2*T) M).symm
    _ = _ := by rw [show 2*T = T*2 by omega,pow_mul]; ring

lemma geo_two_power_binomial_divisor (T v : ℕ) (hT : 0 < T) (hv : 2 ≤ v) :
    (X^(2*T)+1 : ℤ[X]) ∣ geo T (2^v) := by
  have hv2 : 2^v = 2*(2*(2^(v-2))) := by
    rw [← pow_succ',← pow_succ',Nat.sub_add_cancel hv]
  rw [hv2,geo_double T _ hT,geo_double (2*T) _ (by omega)]
  refine ⟨(X^T+1)*geo (2*(2*T)) (2^(v-2)),?_⟩
  ring

lemma zero_correction_not_power_value (U V W : ℤ[X]) (T v L k : ℕ)
    (hT : 0 < T) (hv : 2 ≤ v) (hL : 0 < L) (hJ : U+V-W = 0) :
    (pattern U V W T (2^v)).eval ((3 : ℤ)^L) ≠ (2 : ℤ)^k := by
  intro he
  have hW : W = U+V := by linear_combination -hJ
  have hp : pattern U V W T (2^v) = (U+X^T*V)*geo T (2^v) := by
    rw [hW,pattern_eq_geometric _ _ T (2^v) (by positivity)]
  have hd : (X^(2*T)+1 : ℤ[X]) ∣ pattern U V W T (2^v) := by
    rw [hp]
    exact dvd_mul_of_dvd_right (geo_two_power_binomial_divisor T v hT hv) _
  have hh := binomial_dvd_at_power_three _ L (2*T) k hL (by omega) hd he
  nlinarith

lemma binary_eval_lower_bound_at (P : ℤ[X]) (hP : Binary P) (hnz : P ≠ 0)
    (N : ℕ) (hN : N ≤ P.natDegree) (x : ℤ) (hx : 1 ≤ x) : x^N ≤ P.eval x := by
  have hlc : P.coeff P.natDegree = 1 := by
    rcases hP P.natDegree with hh | hh
    · exact (leadingCoeff_ne_zero.mpr hnz hh).elim
    · exact hh
  calc
    x^N ≤ x^P.natDegree := pow_le_pow_right₀ hx hN
    _ = P.coeff P.natDegree*x^P.natDegree := by rw [hlc,one_mul]
    _ ≤ ∑ i ∈ Finset.range (P.natDegree+1), P.coeff i*x^i := by
      apply Finset.single_le_sum (f := fun i => P.coeff i*x^i)
      · intro i _
        rcases hP i with hh | hh <;> rw [hh] <;> positivity
      · exact Finset.mem_range.mpr (by omega)
    _ = P.eval x := (eval_eq_sum_range x).symm

lemma near_dyadic_boundary_at (P : ℤ[X]) (hP : Binary P) (R : (ZMod 2)[X])
    (hR : R.coeff 0 = 1) (a L k : ℕ) (ha : 2 ≤ a) (hL : 0 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R)
    (he : P.eval ((3 : ℤ)^L) = (2 : ℤ)^k) :
    ∃ r : ℕ, a < 2^r ∧ 2^r ≤ a+R.natDegree := by
  let s := a.log2
  let u := a-2^s
  have hpow : 2^s ≤ a := Nat.log2_self_le (by omega)
  have htop : a < 2^(s+1) := (Nat.log2_lt (by omega : a ≠ 0)).mp (by dsimp [s]; omega)
  have hau : a = 2^s+u := by dsimp [u]; omega
  refine ⟨s+1,htop,?_⟩
  by_contra hb
  have hgap : u+R.natDegree < 2^s := by
    rw [pow_succ] at hb
    omega
  have hmap : P.map (Int.castRingHom (ZMod 2)) =
      (X^(2^s)+1)*((X+1)^u*R) := by
    rw [hm,hau,pow_add,binomial_frobenius,mul_assoc]
  have hshape := separated_binomial_lift P hP ((X+1)^u*R) (2^s)
    (by rwa [binomial_residual_degree R hR u]) hmap
  have hd : (X^(2^s)+1 : ℤ[X]) ∣ P := ⟨liftTwo ((X+1)^u*R),hshape⟩
  have hh := binomial_dvd_at_power_three P L (2^s) k hL (by positivity) hd he
  rw [pow_succ] at htop
  nlinarith

#print axioms binary_block_representation
#print axioms zero_correction_not_power_value
#print axioms near_dyadic_boundary_at
end Erdos406BinaryBlocks
