import Submission.PolynomialSquareValues
import Submission.NewmanPowerClassRigidity

/-! Fixed-pattern consequences of the elementary Runge argument. These
control uniform zero insertion in a fixed binary pattern, not all patterns
at once, and do not settle Erdős406. -/
namespace Erdos406PatternDilations
open Polynomial Erdos406Runge Erdos406ReciprocalFlip Erdos406PowerClass

lemma even_power_exponent_at_ternary_base (P : ℤ[X]) (h0 : P.coeff 0 = 1)
    (L k : ℕ) (hL : 0 < L) (hv : P.eval ((3 : ℤ)^L) = (2 : ℤ)^k) :
    Even k := by
  let f := Int.castRingHom (ZMod 3)
  have hz : f ((3 : ℤ)^L) = 0 := by
    rw [map_pow]
    have h3 : f (3 : ℤ) = 0 := by decide
    rw [h3, zero_pow (by omega)]
  have he := congrArg f hv
  rw [← eval₂_at_apply f ((3 : ℤ)^L), hz] at he
  have hpow : (2 : ZMod 3)^k = 1 := by
    simpa [h0, f] using he.symm
  by_contra hh
  obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hh
  have hk : k = 2*r+1 := by omega
  rw [hk, pow_add, pow_mul, show (2 : ZMod 3)^2 = 1 by decide] at hpow
  norm_num at hpow
  exact (by decide : (2 : ZMod 3) ≠ 1) hpow

lemma normalized_binary_not_square (P : ℤ[X]) (hP : Binary P)
    (h0 : P.coeff 0 = 1) (hD : 0 < P.natDegree) : ¬ IsSquare P := by
  rintro ⟨Q, he⟩
  have hh := binary_square_eq_one P Q hP h0 (by simpa only [pow_two] using he)
  simp [hh] at hD

/-- A fixed normalized binary polynomial of positive even degree has only
finitely many square values at natural integer arguments. -/
theorem finite_square_values_binary (P : ℤ[X]) (hP : Binary P) (hm : P.Monic)
    (h0 : P.coeff 0 = 1) (hD : 0 < P.natDegree) (hE : Even P.natDegree) :
    {n : ℕ | IsSquare (P.eval (n : ℤ))}.Finite := by
  obtain ⟨d, hd⟩ := hE
  exact finite_square_values P hm d (by omega) (by omega)
    (normalized_binary_not_square P hP h0 hD)

/-- Fixed monic even-degree nonsquare polynomials have only finitely many
pure-power-of-two evaluations at ternary power arguments. -/
theorem finite_power_dilations_even_degree (P : ℤ[X]) (hm : P.Monic)
    (h0 : P.coeff 0 = 1) (hD : 0 < P.natDegree) (hE : Even P.natDegree)
    (hns : ¬ IsSquare P) :
    {L : ℕ | ∃ k : ℕ, P.eval ((3 : ℤ)^L) = (2 : ℤ)^k}.Finite := by
  obtain ⟨d, hd⟩ := hE
  have hf := finite_square_values P hm d (by omega) (by omega) hns
  have hpow : {L : ℕ | IsSquare (P.eval ((3 : ℤ)^L))}.Finite := by
    have hh := hf.preimage (fun a ha b hb h => Nat.pow_right_injective (by decide : 2 ≤ 3) h)
    simpa only [Set.preimage_setOf_eq, Nat.cast_pow, Nat.cast_ofNat] using hh
  apply ((Set.finite_singleton 0).union hpow).subset
  intro L hL
  by_cases hz : L = 0
  · exact Or.inl hz
  obtain ⟨k, hk⟩ := hL
  obtain ⟨r, hr⟩ := even_power_exponent_at_ternary_base P h0 L k (by omega) hk
  right
  refine ⟨(2 : ℤ)^r, ?_⟩
  rw [hk, hr, pow_add]

/-- If the fixed binary pattern has even degree, only finitely many uniform
zero insertions can give power-of-two values at three. -/
theorem finite_dilations_even_degree (P : ℤ[X]) (hP : Binary P) (hm : P.Monic)
    (h0 : P.coeff 0 = 1) (hD : 0 < P.natDegree) (hE : Even P.natDegree) :
    {L : ℕ | ∃ k : ℕ, P.eval ((3 : ℤ)^L) = (2 : ℤ)^k}.Finite :=
  finite_power_dilations_even_degree P hm h0 hD hE
    (normalized_binary_not_square P hP h0 hD)

lemma binary_expand (P : ℤ[X]) (hP : Binary P) (r : ℕ) (hr : 0 < r) :
    Binary (expand ℤ r P) := by
  intro i
  rw [coeff_expand hr]
  split_ifs
  · exact hP _
  · exact Or.inl rfl

/-- For an arbitrary fixed positive-degree normalized binary pattern, the
subfamily with even spacing also has only finitely many pure-power values. -/
theorem finite_even_dilations (P : ℤ[X]) (hP : Binary P) (hm : P.Monic)
    (h0 : P.coeff 0 = 1) (hD : 0 < P.natDegree) :
    {L : ℕ | ∃ k : ℕ, P.eval ((3 : ℤ)^(2*L)) = (2 : ℤ)^k}.Finite := by
  let F := expand ℤ 2 P
  have hF : Binary F := binary_expand P hP 2 (by decide)
  have hFm : F.Monic := Monic.expand (by decide : 0 < 2) hm
  have hF0 : F.coeff 0 = 1 := by simp [F, coeff_expand (by decide : 0 < 2), h0]
  have hFD : F.natDegree = 2*P.natDegree := by simp [F, natDegree_expand, Nat.mul_comm]
  have he (L : ℕ) : F.eval ((3 : ℤ)^L) = P.eval ((3 : ℤ)^(2*L)) := by
    simp only [F, expand_eq_comp_X_pow, eval_comp, eval_pow, eval_X]
    rw [← pow_mul, Nat.mul_comm L 2]
  have hf := finite_dilations_even_degree F hF hFm hF0 (by omega)
    ⟨P.natDegree, by omega⟩
  simpa only [he] using hf

#print axioms finite_power_dilations_even_degree
#print axioms finite_square_values_binary
#print axioms finite_dilations_even_degree
#print axioms finite_even_dilations
end Erdos406PatternDilations
