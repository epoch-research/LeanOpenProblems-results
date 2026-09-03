import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

namespace Erdos213

lemma not_rat_sum_two_squares_three (x y : ℚ) : x^2+y^2 ≠ 3 := by
  intro h
  let N : ℕ := x.den*y.den
  let a : ℤ := x.num*y.den
  let b : ℤ := y.num*x.den
  have hN : N ≠ 0 := Nat.mul_ne_zero x.den_ne_zero y.den_ne_zero
  have ha : (a : ℚ) = x*N := by
    dsimp [a,N]
    push_cast
    linear_combination -(y.den : ℚ)*x.mul_den_eq_num
  have hb : (b : ℚ) = y*N := by
    dsimp [b,N]
    push_cast
    linear_combination -(x.den : ℚ)*y.mul_den_eq_num
  have heq : (a : ℚ)^2+(b : ℚ)^2 = 3*(N : ℚ)^2 := by
    rw [ha,hb]
    linear_combination (N : ℚ)^2*h
  have hei : a^2+b^2 = 3*(N : ℤ)^2 := by exact_mod_cast heq
  have hen : 3*N^2 = a.natAbs^2+b.natAbs^2 := by
    apply Int.ofNat_inj.mp
    push_cast
    rw [sq_abs,sq_abs]
    exact hei.symm
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hp : 3 ∈ (3*N^2).primeFactors := Nat.mem_primeFactors.mpr
    ⟨by decide,dvd_mul_right 3 (N^2),Nat.mul_ne_zero (by decide) (pow_ne_zero _ hN)⟩
  have hev := Nat.eq_sq_add_sq_iff.mp ⟨a.natAbs,b.natAbs,hen⟩ 3 hp (by decide)
  rw [padicValNat.mul (by decide) (pow_ne_zero _ hN),
    padicValNat.self (by decide),padicValNat.pow 2 hN] at hev
  obtain ⟨k,hk⟩ := hev
  omega

lemma rat_sum_two_squares_three_mul {x y z : ℚ} (h : x^2+y^2 = 3*z^2) : z = 0 := by
  by_contra hz
  apply not_rat_sum_two_squares_three (x/z) (y/z)
  field_simp
  nlinarith [h]

lemma isSquare_pair_three_mul {a b z : ℚ} (ha : IsSquare a) (hb : IsSquare b)
    (h : a+b = 3*z^2) : z = 0 := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  apply rat_sum_two_squares_three_mul (x := x) (y := y)
  nlinarith [hx,hy,h]

#print axioms not_rat_sum_two_squares_three
#print axioms isSquare_pair_three_mul
end Erdos213
