import Submission.NewmanBinaryBlockReduction

/-! A uniform linear-multiplicity bound at high Frobenius bases, for each
fixed residual polynomial. This does not bound the residual degree itself. -/
namespace Erdos406FrobeniusBound
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406FixedResidualTools Erdos406FixedResidual
  Erdos406CubicHighBase Erdos406BinaryBlocks Erdos406AffineTower

lemma binary_block_no_high_base (P : ℤ[X]) (hP : Binary P) (S : (ZMod 2)[X])
    (T v c t k : ℕ) (hT : 0 < T) (hc : 2 ≤ c) (hv : c ≤ v) (ht : c ≤ t)
    (hsize : 2*T < 2^c) (hdeg : c ≤ P.natDegree) (hS : S.natDegree < 2*T)
    (hm : (X^T-1)*P.map (Int.castRingHom (ZMod 2)) = (X^(2^v*T)-1)*S) :
    P.eval ((3 : ℤ)^(2^t)) ≠ (2 : ℤ)^k := by
  intro he
  obtain ⟨U,V,W,hU,hV,hW,hDU,hDV,hDW,hmW,hp⟩ :=
    binary_block_representation P hP S T (2^v) hT (by positivity) hS hm
  obtain ⟨hJ,hJbound⟩ := xor_correction_bound U V W hU hV hW hmW T hDU hDV hDW
  rcases hJ with hJ | hJ
  · exact zero_correction_not_power_value U V W T v (2^t) k hT (by omega)
      (by positivity) hJ (by rwa [← hp])
  have hnz : P ≠ 0 := by
    intro hz
    rw [hz,natDegree_zero] at hdeg
    omega
  have hx : (2 : ℤ) ≤ 3^(2^t) := by
    have hpos : 1 ≤ (2 : ℕ)^t := Nat.one_le_pow _ _ (by decide)
    have hh : (3 : ℤ)^1 ≤ 3^(2^t) := pow_le_pow_right₀ (by decide) hpos
    norm_num at hh
    omega
  have hk : c ≤ k := by
    have hb : (2 : ℤ)^c ≤ 2^k := calc
      _ ≤ (3^(2^t))^c := pow_le_pow_left₀ (by decide) hx c
      _ ≤ P.eval ((3 : ℤ)^(2^t)) := binary_eval_lower_bound_at P hP hnz c hdeg _ (by omega)
      _ = _ := he
    by_contra hh
    have hlt : (2 : ℤ)^k < 2^c := pow_lt_pow_right₀ (by decide) (by omega)
    omega
  have hdEval : (2 : ℤ)^c ∣ P.eval ((3 : ℤ)^(2^t)) := by
    rw [he]
    exact pow_dvd_pow 2 hk
  have hdInput : (2 : ℤ)^c ∣ 3^(2^t)-1 :=
    (pow_dvd_pow 2 (by omega : c ≤ t+1)).trans (three_tower_congruence t)
  have hdDiff : (2 : ℤ)^c ∣ P.eval ((3 : ℤ)^(2^t))-P.eval 1 :=
    hdInput.trans (sub_dvd_eval_sub ((3 : ℤ)^(2^t)) 1 P)
  have hdOne : (2 : ℤ)^c ∣ P.eval 1 := by
    convert dvd_sub hdEval hdDiff using 1
    ring
  rw [hp,pattern_eval_one U V W T (2^v) (by positivity)] at hdOne
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hdOne
  have hdM : (2 : ℤ)^c ∣ 2^v*W.eval 1 := dvd_mul_of_dvd_left (pow_dvd_pow 2 hv) _
  have hdJ : (2 : ℤ)^c ∣ (U+V-W).eval 1 := by
    convert dvd_sub hdOne hdM using 1
    ring
  have hle := Int.le_of_dvd hJ hdJ
  have hsmall : (2 : ℤ)*T < 2^c := by exact_mod_cast hsize
  omega

/-- Once the Frobenius base exponent t is at least deg(R)+2, every
possible linear multiplicity a is less than 2^(2*deg(R)+2).
The bound is uniform in t, but NOT uniform in R. -/
theorem linear_multiplicity_bound_at_high_base (P : ℤ[X]) (hP : Binary P)
    (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (a t k : ℕ)
    (ht : R.natDegree+2 ≤ t)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R)
    (he : P.eval ((3 : ℤ)^(2^t)) = (2 : ℤ)^k) :
    a < 2^(2*R.natDegree+2) := by
  let s := R.natDegree
  let c := s+2
  have hc : 2 ≤ c := by dsimp [c]; omega
  have ht' : c ≤ t := ht
  have hD : R.natDegree ≤ 2^s := Nat.le_of_lt Nat.lt_two_pow_self
  have hbound : 2^(2*R.natDegree+2) = 2^(s+c) := by
    dsimp [s,c]
    congr 1
    omega
  rw [hbound]
  by_contra ha
  have hsc : s+c < 2^(s+c) := Nat.lt_two_pow_self
  have ha2 : 2 ≤ a := by omega
  obtain ⟨r,hlo,hhi⟩ := near_dyadic_boundary_at P hP R hR a (2^t) k ha2
    (by positivity) hm he
  have hlarge : s+c < r := by
    by_contra hh
    have hp : 2^r ≤ (2 : ℕ)^(s+c) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hM : 2^r = 2^(r-s)*2^s := by
    rw [← pow_add,Nat.sub_add_cancel (by omega : s ≤ r)]
  let S : (ZMod 2)[X] := (X+1)^(a+2^s-2^r)*R
  have hS : S.natDegree < 2*2^s := by
    dsimp [S]
    rw [binomial_residual_degree R hR]
    omega
  have hmap : (X^(2^s)-1)*P.map (Int.castRingHom (ZMod 2)) =
      (X^(2^(r-s)*2^s)-1)*S := by
    have hh := shifted_residual_map P R a s r (by omega) hm
    rw [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_pow,map_X,Polynomial.map_one] at hh
    have hchar : (X^(2^r)-1 : (ZMod 2)[X]) = X^(2^r)+1 := by
      have hc2 : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
      linear_combination -hc2
    rw [← hM,hchar]
    exact hh
  have hsize : 2*2^s < 2^c := by
    have hp : 2^c = 4*2^s := by
      dsimp [c]
      rw [pow_add]
      norm_num
      ring
    have hpos : (0 : ℕ) < 2^s := by positivity
    omega
  have hdeg : c ≤ P.natDegree := by
    rw [residual_degree P hP R hR a hm]
    omega
  exact binary_block_no_high_base P hP S (2^s) (r-s) c t k (by positivity) hc
    (by omega) ht' hsize hdeg hS hmap he

#print axioms binary_block_no_high_base
#print axioms linear_multiplicity_bound_at_high_base
end Erdos406FrobeniusBound
