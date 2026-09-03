import FormalConjecturesUtil

/-! Exact mixed-modulus identities for integer lifts of modular parabolas.
The formulas expose the extra quotient term introduced by changing modulus;
they do not assert an asymptotic representation bound. -/
namespace Erdos66NearbyPrimeCarry

/-- A transposed digit lift: the high digit is the curve variable. -/
def curveLift (p u x : ℕ) : ℕ := p*x+(u*x^2)%p

lemma curveLift_injective_on (p u : ℕ) (hp : 0 < p) :
    Function.Injective (curveLift p u) := by
  intro x y h
  have hh := congrArg (fun n ↦ n/p) h
  simpa only [curveLift,Nat.mul_add_div hp,Nat.mod_div_self,Nat.add_zero] using hh

lemma mixed_lift_carry_identity (p q u v x y n : ℕ) (hpq : p ≤ q) :
    curveLift p u x + curveLift q v y=n ↔
      q*(x+y)+((u*x^2)%p+(v*y^2)%q)=n+(q-p)*x := by
  have hd : q-p+p=q := Nat.sub_add_cancel hpq
  unfold curveLift
  constructor <;> intro h <;> nlinarith

/-- When q is close to p, the sum of the high digits has few possible values.
This is only a carry reduction; the remaining fibers are not quadratic over
one common field. -/
lemma high_digit_sum_bounds (p q u v x y n : ℕ)
    (hp : 0 < p) (hpq : p ≤ q) (hx : x < p)
    (hsum : curveLift p u x + curveLift q v y=n) :
    n/q-1 ≤ x+y ∧ x+y ≤ n/q+(q-p) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have he := (mixed_lift_carry_identity p q u v x y n hpq).mp hsum
  have hr := Nat.mod_lt (u*x^2) hp
  have hs := Nat.mod_lt (v*y^2) hq
  have hn : n < q*(x+y+2) := by nlinarith
  have hdiv : n/q < x+y+2 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
  have hdx : (q-p)*x ≤ (q-p)*q := Nat.mul_le_mul_left _ (by omega)
  have hu : (x+y)*q ≤ n+(q-p)*q := by
    nlinarith [Nat.zero_le ((u*x^2)%p),Nat.zero_le ((v*y^2)%q)]
  have hupper : x+y ≤ (n+(q-p)*q)/q := (Nat.le_div_iff_mul_le hq).mpr hu
  rw [Nat.add_mul_div_right _ _ hq] at hupper
  exact ⟨by omega,hupper⟩

lemma high_digit_sum_mem (p q u v x y n : ℕ)
    (hp : 0 < p) (hpq : p ≤ q) (hx : x < p)
    (hsum : curveLift p u x + curveLift q v y=n) :
    x+y ∈ Finset.Icc (n/q-1) (n/q+(q-p)) := by
  exact Finset.mem_Icc.mpr (high_digit_sum_bounds p q u v x y n hp hpq hx hsum)

lemma high_digit_sum_choices (p q n : ℕ) :
    (Finset.Icc (n/q-1) (n/q+(q-p))).card ≤ q-p+2 := by
  rw [Nat.card_Icc]
  omega

/-- Changing modulus introduces a quotient depending on the curve variable.
For equal moduli the perturbation vanishes and the usual quadratic equation
is recovered. For unequal moduli it cannot simply be dropped. -/
lemma mixed_lift_quotient_equation (p q u v x y n : ℕ) [NeZero p]
    (hpq : p ≤ q) (hsum : curveLift p u x + curveLift q v y=n) :
    (u : ZMod p)*x^2+(v : ZMod p)*y^2+((q-p : ℕ) : ZMod p)*y =
      (n : ZMod p)+((q-p : ℕ) : ZMod p)*((v*y^2/q : ℕ) : ZMod p) := by
  have he := congrArg (fun k : ℕ ↦ (k : ZMod p)) hsum
  simp only [curveLift,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    ZMod.natCast_self,zero_mul,zero_add,ZMod.natCast_mod] at he
  have hd := congrArg (fun k : ℕ ↦ (k : ZMod p)) (Nat.mod_add_div (v*y^2) q)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow] at hd
  have hqp : (q : ZMod p) = ((q-p : ℕ) : ZMod p) := by
    have hh := congrArg (fun k : ℕ ↦ (k : ZMod p)) (Nat.sub_add_cancel hpq)
    simpa only [Nat.cast_add,ZMod.natCast_self,add_zero] using hh.symm
  rw [hqp] at he hd
  linear_combination he-hd

end Erdos66NearbyPrimeCarry
