import Submission.NewmanQuantitativeBlocks

/-! Explicit bounds relating linear multiplicity to residual degree for
binary pure-power-valued polynomials. These are uniform inequalities, but
leave the residual degree unbounded and therefore do not settle Erdős406. -/
namespace Erdos406ExplicitResidualBounds
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406FixedResidualTools Erdos406FixedResidual
  Erdos406CubicHighBase Erdos406BinaryBlocks Erdos406FrobeniusBound
  Erdos406QuantitativeBlocks Erdos406Cyclotomic Erdos406ReciprocalCandidate

lemma residual_block_data (P : ℤ[X]) (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1)
    (a s r : ℕ) (hD : R.natDegree ≤ 2^s) (hlo : a < 2^r)
    (hhi : 2^r ≤ a+R.natDegree) (hs : s ≤ r)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R) :
    ∃ S : (ZMod 2)[X], S.natDegree < 2*2^s ∧
      (X^(2^s)-1)*P.map (Int.castRingHom (ZMod 2)) = (X^(2^(r-s)*2^s)-1)*S := by
  let S : (ZMod 2)[X] := (X+1)^(a+2^s-2^r)*R
  have hM : 2^r = 2^(r-s)*2^s := by rw [← pow_add,Nat.sub_add_cancel hs]
  refine ⟨S,?_,?_⟩
  · dsimp [S]
    rw [binomial_residual_degree R hR]
    omega
  · have hh := shifted_residual_map P R a s r (by omega) hm
    rw [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_pow,map_X,Polynomial.map_one] at hh
    have hchar : (X^(2^r)-1 : (ZMod 2)[X]) = X^(2^r)+1 := by
      have hc2 : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
      linear_combination -hc2
    rw [← hM,hchar]
    exact hh

/-- A completely explicit bound at every positive ternary power base.
The block width 2^s may be any dyadic width at least the residual degree. -/
theorem linear_multiplicity_bound_with_width (P : ℤ[X]) (hP : Binary P)
    (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (a L s k : ℕ) (hL : 0 < L)
    (hD : R.natDegree ≤ 2^s)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R)
    (he : P.eval ((3 : ℤ)^L) = (2 : ℤ)^k) :
    a < 2^(s+2*L*2^s) := by
  let c := 2*L*2^s
  have hc : 2 ≤ c := by
    have hp : 1 ≤ (2 : ℕ)^s := Nat.one_le_pow _ _ (by decide)
    dsimp [c]
    nlinarith
  by_contra ha
  have ha' : 2^(s+c) ≤ a := by simpa [c] using (Nat.le_of_not_gt ha)
  have hsc : s+c < 2^(s+c) := Nat.lt_two_pow_self
  obtain ⟨r,hlo,hhi⟩ := near_dyadic_boundary_at P hP R hR a L k (by omega) hL hm he
  have hlarge : s+c < r := by
    by_contra hh
    have hp : 2^r ≤ (2 : ℕ)^(s+c) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨S,hS,hmap⟩ := residual_block_data P R hR a s r hD hlo hhi (by omega) hm
  have hdeg : r-s ≤ P.natDegree := by
    rw [residual_degree P hP R hR a hm]
    have hp : r < 2^r := Nat.lt_two_pow_self
    omega
  exact binary_block_no_large_length P hP S (2^s) (r-s) L k (by positivity) hL
    (by dsimp [c] at hlarge; omega) hdeg hS hmap he

/-- Optimizing the earlier high-base bound is possible because its proof
works with any dyadic block width, rather than only 2^(deg R). -/
theorem linear_multiplicity_high_base_with_width (P : ℤ[X]) (hP : Binary P)
    (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (a t s k : ℕ)
    (hD : R.natDegree ≤ 2^s) (ht : s+2 ≤ t)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R)
    (he : P.eval ((3 : ℤ)^(2^t)) = (2 : ℤ)^k) :
    a < 2^(2*s+2) := by
  let c := s+2
  have hc : 2 ≤ c := by dsimp [c]; omega
  have hbound : 2^(2*s+2) = 2^(s+c) := by dsimp [c]; congr 1; omega
  rw [hbound]
  by_contra ha
  have hsc : s+c < 2^(s+c) := Nat.lt_two_pow_self
  obtain ⟨r,hlo,hhi⟩ := near_dyadic_boundary_at P hP R hR a (2^t) k (by omega)
    (by positivity) hm he
  have hlarge : s+c < r := by
    by_contra hh
    have hp : 2^r ≤ (2 : ℕ)^(s+c) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨S,hS,hmap⟩ := residual_block_data P R hR a s r hD hlo hhi (by omega) hm
  have hsize : 2*2^s < 2^c := by
    have hp : 2^c = 4*2^s := by dsimp [c]; rw [pow_add]; norm_num; ring
    have hpos : (0 : ℕ) < 2^s := by positivity
    omega
  have hdeg : c ≤ P.natDegree := by
    rw [residual_degree P hP R hR a hm]
    omega
  exact binary_block_no_high_base P hP S (2^s) (r-s) c t k (by positivity) hc
    (by omega) ht hsize hdeg hS hmap he

lemma log2_succ_width (D : ℕ) (hD : 0 < D) :
    D ≤ 2^(D.log2+1) ∧ 2^(D.log2+1) ≤ 2*D ∧ D.log2+1 ≤ D := by
  have hlo : 2^D.log2 ≤ D := Nat.log2_self_le (by omega)
  have hhi : D < 2^(D.log2+1) := (Nat.log2_lt (by omega : D ≠ 0)).mp (by omega)
  have hs : D.log2 < D := (Nat.log2_lt (by omega : D ≠ 0)).mpr Nat.lt_two_pow_self
  refine ⟨by omega,?_,by omega⟩
  rw [pow_succ]
  omega

/-- This bound is simultaneous over all residual shapes of positive degree:
linear multiplicity is at most exponential in L times residual degree. -/
theorem linear_multiplicity_exponential_bound (P : ℤ[X]) (hP : Binary P)
    (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (hD : 0 < R.natDegree)
    (a L k : ℕ) (hL : 0 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R)
    (he : P.eval ((3 : ℤ)^L) = (2 : ℤ)^k) :
    a < 2^(5*L*R.natDegree) := by
  obtain ⟨hwidth,hsize,hs⟩ := log2_succ_width R.natDegree hD
  have hb := linear_multiplicity_bound_with_width P hP R hR a L (R.natDegree.log2+1) k
    hL hwidth hm he
  apply hb.trans_le
  apply Nat.pow_le_pow_right (by decide)
  have hh := Nat.mul_le_mul_left (2*L) hsize
  nlinarith

/-- At high Frobenius bases the bound is quadratic in residual degree,
not exponential. The threshold for t is only logarithmic in that degree. -/
theorem linear_multiplicity_quadratic_bound (P : ℤ[X]) (hP : Binary P)
    (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (hD : 0 < R.natDegree)
    (a t k : ℕ) (ht : R.natDegree.log2+3 ≤ t)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R)
    (he : P.eval ((3 : ℤ)^(2^t)) = (2 : ℤ)^k) :
    a < 16*R.natDegree^2 := by
  obtain ⟨hwidth,hsize,_⟩ := log2_succ_width R.natDegree hD
  have hb := linear_multiplicity_high_base_with_width P hP R hR a t (R.natDegree.log2+1) k
    hwidth (by omega) hm he
  have hp : (2 : ℕ)^(2*(R.natDegree.log2+1)+2) = 4*(2^(R.natDegree.log2+1))^2 := by
    rw [pow_add,Nat.mul_comm 2 (R.natDegree.log2+1),pow_mul]
    norm_num
    ring
  rw [hp] at hb
  nlinarith

/-- Direct quantitative restriction for the original natural-number
candidates. No upper bound on the residual degree is supplied. -/
theorem candidate_linear_multiplicity_bound (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1]) (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1)
    (hD : 0 < R.natDegree) (a : ℕ)
    (hm : (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) = (X+1)^a*R) :
    a < 2^(5*R.natDegree) := by
  obtain ⟨k,rfl⟩ := hn
  have he : (digitPoly (Nat.digits 3 (2^k))).eval ((3 : ℤ)^1) = (2 : ℤ)^k := by
    rw [pow_one,digitPoly_eval_three]
    norm_cast
  simpa using linear_multiplicity_exponential_bound _ (binary_digitPoly _ hg) R hR hD a 1 k
    (by decide) hm he

#print axioms linear_multiplicity_bound_with_width
#print axioms linear_multiplicity_high_base_with_width
#print axioms linear_multiplicity_exponential_bound
#print axioms linear_multiplicity_quadratic_bound
#print axioms candidate_linear_multiplicity_bound
end Erdos406ExplicitResidualBounds
