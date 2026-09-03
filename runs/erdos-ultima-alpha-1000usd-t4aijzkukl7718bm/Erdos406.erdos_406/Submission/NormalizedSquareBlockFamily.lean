import Submission.SixthPowerQuadraticBlockObstruction

/-! A monic, constant-one polynomial producing infinitely many ternary-good
squares after block separation. The roots are not powers of two. This is a
diagnostic for proposed square-value rigidity, not a disproof of Erdős 406. -/
namespace Erdos406NormalizedSquareBlocks
open Polynomial Erdos406Work Erdos406SixthQuadratic

noncomputable def rootPolynomial : ℕ[X] := X^4 + 2*X^3 + 2*X + 1

def root (q : ℕ) : ℕ := q^4 + 2*q^3 + 2*q + 1

def squareBlocks : List ℕ := [1,4,4,4,10,4,4,4,1]

lemma rootPolynomial_monic : rootPolynomial.Monic := by
  unfold rootPolynomial
  monicity <;> norm_num

lemma rootPolynomial_constant : rootPolynomial.coeff 0 = 1 := by
  norm_num [rootPolynomial,coeff_add,coeff_mul]

lemma rootPolynomial_eval (q : ℕ) : rootPolynomial.eval q = root q := by
  simp [rootPolynomial,root]

lemma square_blocks_identity (q : ℕ) :
    Nat.ofDigits q squareBlocks = (root q)^2 := by
  simp only [squareBlocks,Nat.ofDigits_cons,Nat.ofDigits_nil]
  unfold root
  ring

lemma square_blocks_good : ∀ d ∈ squareBlocks, Nat.digits 3 d ⊆ [0,1] := by
  decide +kernel

/-- This is a whole-number digit statement for every spacing L≥3. -/
theorem separated_square_good (L : ℕ) (hL : 3 ≤ L) :
    Nat.digits 3 ((root (3^L))^2) ⊆ [0,1] := by
  rw [← square_blocks_identity]
  apply (good_ofDigits_blocks_iff squareBlocks L ?_).mpr square_blocks_good
  intro d hd
  have hp : 27 ≤ 3^L := by
    change 3^3 ≤ 3^L
    exact Nat.pow_le_pow_right (by decide) hL
  simp only [squareBlocks,List.mem_cons,List.not_mem_nil,or_false] at hd
  omega

lemma odd_root_mod_eight (q : ℕ) (hq : q%2 = 1) : root q%8 = 6 := by
  have hc : ∀ a : Fin 8, (a : ℕ)%2 = 1 → root (a : ℕ)%8 = 6 := by
    decide +kernel
  have hmod : q%8%2 = 1 := by
    simpa only [Nat.mod_mod_of_dvd q (by decide : 2 ∣ 8)] using hq
  have hh := hc ⟨q%8,Nat.mod_lt _ (by decide)⟩ hmod
  simpa only [root,Nat.add_mod,Nat.mul_mod,Nat.pow_mod,Nat.mod_mod] using hh

lemma root_not_power_of_two (q : ℕ) (hq : q%2 = 1) : ¬ (root q).isPowerOfTwo := by
  rintro ⟨k,hk⟩
  have hm := odd_root_mod_eight q hq
  rw [hk] at hm
  by_cases hsmall : k < 3
  · interval_cases k <;> norm_num at hm
  · have hd : 8 ∣ (2 : ℕ)^k := Nat.pow_dvd_pow 2 (by omega : 3 ≤ k)
    rw [Nat.mod_eq_zero_of_dvd hd] at hm
    omega

lemma square_not_power_of_two (q : ℕ) (hq : q%2 = 1) :
    ¬ ((root q)^2).isPowerOfTwo := by
  rintro ⟨k,hk⟩
  have hd : root q ∣ (2 : ℕ)^k := by
    rw [← hk]
    exact dvd_pow_self _ (by decide)
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact root_not_power_of_two q hq ⟨j,hj⟩

lemma separated_root_bad (L : ℕ) (hL : 1 ≤ L) :
    ¬ Nat.digits 3 (root (3^L)) ⊆ [0,1] := by
  intro hg
  have hd := ternary_digit_bound hg L
  have hq : 1 < 3^L := one_lt_pow₀ (by decide) (by omega)
  have hdiv : root (3^L) / 3^L = (3^L)^3+2*(3^L)^2+2 := by
    have he : root (3^L) = 1+3^L*((3^L)^3+2*(3^L)^2+2) := by
      unfold root
      ring
    rw [he,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt hq,zero_add]
  have hm : 3^L%3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self _ (by omega))
  rw [hdiv] at hd
  norm_num [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,hm] at hd

/-- Monicity and constant coefficient one do not prevent an unbounded
family of good squares with bad roots. The pure-power hypothesis is absent
and, as proved here, is false for every member of this family. -/
theorem arbitrarily_large_normalized_good_squares (B : ℕ) :
    ∃ L : ℕ, 3 ≤ L ∧ B < (root (3^L))^2 ∧
      Nat.digits 3 ((root (3^L))^2) ⊆ [0,1] ∧
      ¬ Nat.digits 3 (root (3^L)) ⊆ [0,1] ∧
      ¬ ((root (3^L))^2).isPowerOfTwo := by
  refine ⟨B+3,by omega,?_,separated_square_good _ (by omega),
    separated_root_bad _ (by omega),square_not_power_of_two _ ?_⟩
  · have hh : B+3 < 3^(B+3) := Nat.lt_pow_self (by decide)
    have hr : 3^(B+3) < root (3^(B+3)) := by unfold root; omega
    have hp : 1 ≤ root (3^(B+3)) := by unfold root; omega
    nlinarith
  · norm_num [Nat.pow_mod]

#print axioms separated_square_good
#print axioms square_not_power_of_two
#print axioms arbitrarily_large_normalized_good_squares
end Erdos406NormalizedSquareBlocks
