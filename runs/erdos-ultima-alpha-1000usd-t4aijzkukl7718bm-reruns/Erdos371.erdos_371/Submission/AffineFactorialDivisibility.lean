import FormalConjecturesUtil

/-! Prime-occurrence divisibility for affine products. These statements do not
bound the number of favorable largest-prime-factor comparisons: a single
output can contain prime occurrences from several inputs. -/

namespace Erdos371AffineFactorialDivisibility

open Finset

/-- Any divisor of `A!` coprime to the slope divides an affine product of
length `A`. No primality of the slope or the intercept is needed here. -/
theorem factorial_divisor_dvd_progression {d p A : ℕ}
    (hd : d ∣ A.factorial) (hp : p.Coprime d) (b : ℕ) :
    d ∣ ∏ k ∈ range A, (p*k+b) := by
  have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos hd (Nat.factorial_pos A)).ne'
  letI : NeZero d := ⟨hd0⟩
  let c := ((p : ZMod d)⁻¹ * (b : ZMod d)).val
  have hc : (p : ZMod d) * (c : ZMod d) = b := by
    dsimp [c]
    rw [ZMod.natCast_zmod_val, ← mul_assoc, ZMod.coe_mul_inv_eq_one p hp, one_mul]
  have hz : ((c.ascFactorial A : ℕ) : ZMod d) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (hd.trans (Nat.factorial_dvd_ascFactorial c A))
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_prod]
  calc
    (∏ k ∈ range A, ((p*k+b : ℕ) : ZMod d)) =
        ∏ k ∈ range A, (p : ZMod d) * ((c : ZMod d) + k) := by
      apply prod_congr rfl
      intro k _
      push_cast
      rw [mul_add, hc]
      ring
    _ = (p : ZMod d)^A * ((c.ascFactorial A : ℕ) : ZMod d) := by
      rw [prod_mul_distrib, prod_const, card_range, Nat.ascFactorial_eq_prod_range,
        Nat.cast_prod]
      simp only [Nat.cast_add]
    _ = 0 := by rw [hz, mul_zero]

/-- The prime-to-`p` part of the factorial. -/
def freeFactorial (p A : ℕ) : ℕ := A.factorial / p^(A.factorial.factorization p)

lemma freeFactorial_dvd (p A : ℕ) : freeFactorial p A ∣ A.factorial :=
  Nat.ordCompl_dvd A.factorial p

lemma freeFactorial_pos (p A : ℕ) : 0 < freeFactorial p A :=
  Nat.ordCompl_pos p (Nat.factorial_ne_zero A)

lemma freeFactorial_coprime {p : ℕ} (hp : p.Prime) (A : ℕ) :
    p.Coprime (freeFactorial p A) :=
  Nat.coprime_ordCompl hp (Nat.factorial_ne_zero A)

theorem freeFactorial_dvd_progression {p : ℕ} (hp : p.Prime) (b A : ℕ) :
    freeFactorial p A ∣ ∏ k ∈ range A, (p*k+b) :=
  factorial_divisor_dvd_progression (freeFactorial_dvd p A)
    (freeFactorial_coprime hp A) b

lemma prod_Icc_eq_range {M : Type*} [CommMonoid M] (f : ℕ → M) (A : ℕ) :
    (∏ a ∈ Icc 1 A, f a) = ∏ k ∈ range A, f (k+1) := by
  induction A with
  | zero => simp
  | succ A ih => rw [prod_Icc_succ_top (by omega), prod_range_succ, ih]

/-- Both affine signs have the same prime-occurrence divisibility lower bound. -/
theorem freeFactorial_dvd_affine_products {p : ℕ} (hp : p.Prime) (A : ℕ) :
    freeFactorial p A ∣ (∏ a ∈ Icc 1 A, (p*a-1)) ∧
    freeFactorial p A ∣ (∏ a ∈ Icc 1 A, (p*a+1)) := by
  constructor
  · rw [prod_Icc_eq_range]
    convert freeFactorial_dvd_progression hp (p-1) A using 1
    apply prod_congr rfl
    intro k _
    rw [Nat.mul_add, Nat.mul_one]
    have hp2 := hp.two_le
    omega
  · rw [prod_Icc_eq_range]
    convert freeFactorial_dvd_progression hp (p+1) A using 1

/-- Each prime distinct from the slope has at least as many occurrences in
the affine product as in the factorial. This is about occurrences, not inputs. -/
theorem affine_valuation_lower {p q : ℕ} (hp : p.Prime) (hq : q ≠ p) (A : ℕ) :
    A.factorial.factorization q ≤
      ∑ a ∈ Icc 1 A, (p*a-1).factorization q ∧
    A.factorial.factorization q ≤
      ∑ a ∈ Icc 1 A, (p*a+1).factorization q := by
  have hminus (a : ℕ) (ha : a ∈ Icc 1 A) : p*a-1 ≠ 0 := by
    have ha1 := (mem_Icc.mp ha).1
    have hp2 := hp.two_le
    have hpa : 2 ≤ p*a := by nlinarith
    omega
  have hplus (a : ℕ) (ha : a ∈ Icc 1 A) : p*a+1 ≠ 0 := by omega
  have hm0 : (∏ a ∈ Icc 1 A, (p*a-1)) ≠ 0 := prod_ne_zero_iff.mpr hminus
  have hp0 : (∏ a ∈ Icc 1 A, (p*a+1)) ≠ 0 := prod_ne_zero_iff.mpr hplus
  have hdiv := freeFactorial_dvd_affine_products hp A
  have hm := (Nat.factorization_le_iff_dvd (freeFactorial_pos p A).ne' hm0).mpr hdiv.1
  have hh := (Nat.factorization_le_iff_dvd (freeFactorial_pos p A).ne' hp0).mpr hdiv.2
  have hf : (freeFactorial p A).factorization q = A.factorial.factorization q := by
    rw [freeFactorial, Nat.factorization_ordCompl, Finsupp.erase_ne hq]
  have hm' := hm q
  have hh' := hh q
  rw [hf, Nat.factorization_prod_apply hminus] at hm'
  rw [hf, Nat.factorization_prod_apply hplus] at hh'
  exact ⟨hm', hh'⟩

end Erdos371AffineFactorialDivisibility

#print axioms Erdos371AffineFactorialDivisibility.factorial_divisor_dvd_progression
#print axioms Erdos371AffineFactorialDivisibility.affine_valuation_lower
