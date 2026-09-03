import Submission.LambertTwicePrimeSquare
import Submission.RowRemainderBounds

/-!
An exact fractional-part formula for the row indexed by an odd prime at
index `2*p-2`. This is an auxiliary estimate, not a settlement of Erdős 68.
-/

namespace PrimeRowRemainder

open RowRemainderBounds

lemma central_eq_catalan (p : ℕ) (hp : 0 < p) :
    p.centralBinom = 2 * (2*p-1) * catalan (p-1) := by
  have h := Nat.succ_mul_centralBinom_succ (p-1)
  have hc := succ_mul_catalan_eq_centralBinom (p-1)
  rw [Nat.sub_add_cancel hp] at h hc
  have he : 2*(p-1)+1 = 2*p-1 := by omega
  rw [he, ← hc] at h
  nlinarith

lemma catalan_add_one_dvd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ catalan (p-1) + 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hm := (LambertTwicePrimeSquare.central_choose_mod_square p hp).of_dvd
    (show p ∣ p^2 by exact dvd_pow_self _ (by decide))
  have hz : (p.centralBinom : ZMod p) = 2 := by
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  have he := central_eq_catalan p hp.pos
  have hpR : ((2*p-1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub (by have := hp.pos; omega), Nat.cast_mul, Nat.cast_ofNat,
      ZMod.natCast_self, Nat.cast_one]
    ring
  have heR : (p.centralBinom : ZMod p) = -2 * (catalan (p-1) : ZMod p) := by
    rw [he, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, hpR]
    ring
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hh
    have heq := (Nat.dvd_prime Nat.prime_two).mp hd
    rcases heq with heq | heq
    · exact hp.ne_one heq
    · exact hp2 heq
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  apply (mul_eq_zero.mp (show (2 : ZMod p) * ((catalan (p-1) : ZMod p)+1) = 0 by
    linear_combination heR - hz)).resolve_left htwo

lemma pow_four_lt_factorial (n : ℕ) (hn : 4 ≤ n) :
    4^(n-1) < n * (n.factorial-1) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hf : 1 ≤ n.factorial := Nat.factorial_pos n
    have hf' : 1 ≤ (n+1)*n.factorial := Nat.mul_pos (by omega) (Nat.factorial_pos n)
    have hs : n+1-1 = (n-1)+1 := by omega
    rw [hs, pow_succ, Nat.factorial_succ]
    have hh : 4 * (n * (n.factorial-1)) ≤
        (n+1) * ((n+1)*n.factorial-1) := by
      have hsq : 4*n ≤ (n+1)^2 := by nlinarith
      have hprod := Nat.mul_le_mul_right n.factorial hsq
      have hfsub := Nat.sub_add_cancel hf
      have hfsub' := Nat.sub_add_cancel hf'
      nlinarith
    omega

lemma central_lt_factorial (p : ℕ) (hp : 3 ≤ p) :
    (p-1).centralBinom < p * (p.factorial-1) := by
  by_cases h3 : p = 3
  · subst p
    decide
  have h := Nat.choose_le_two_pow (2*(p-1)) (p-1)
  have hh : 2^(2*(p-1)) = 4^(p-1) := by rw [pow_mul]; rfl
  exact (h.trans_eq hh).trans_lt (pow_four_lt_factorial p (by omega))

lemma factorial_ratio_eq (p : ℕ) (hp : 0 < p) :
    ((2*p-2).factorial : ℝ) / (p.factorial : ℝ)^2 =
      (catalan (p-1) : ℝ) / p := by
  have hc := succ_mul_catalan_eq_centralBinom (p-1)
  rw [Nat.sub_add_cancel hp] at hc
  have hb := Nat.choose_mul_factorial_mul_factorial
    (show p-1 ≤ 2*(p-1) by omega)
  rw [show 2*(p-1)-(p-1) = p-1 by omega] at hb
  have he : 2*p-2 = 2*(p-1) := by omega
  have hf : p.factorial = p*(p-1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hp, Nat.factorial_succ]
    rw [Nat.sub_add_cancel hp]
  have hbR : ((2*(p-1)).factorial : ℝ) =
      ((p-1).centralBinom : ℝ) * (p-1).factorial * (p-1).factorial := by
    exact_mod_cast hb.symm
  have hcR : ((p-1).centralBinom : ℝ) = p * (catalan (p-1) : ℝ) := by
    exact_mod_cast hc.symm
  rw [he, hbR, hcR, hf, Nat.cast_mul]
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hfR : ((p-1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- At the indicated prime-indexed subsequence, this individual row is
strictly below one but greater than `1-1/p`. -/
theorem row_formula (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    rowRemainder (2*p-2) p = 1 - 1/(p : ℝ) +
      ((2*p-2).factorial : ℝ) / ((p.factorial : ℝ)^2 * (p.factorial-1)) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpR : (0 : ℝ) < p := by positivity
  have hfR : (0 : ℝ) < p.factorial := by positivity
  have hf2 : (2 : ℝ) ≤ p.factorial := by
    exact_mod_cast (show 2 ≤ p.factorial by simpa using Nat.factorial_le hp.two_le)
  have hdR : (0 : ℝ) < p.factorial-1 := by linarith
  obtain ⟨a, ha⟩ := catalan_add_one_dvd p hp hp2
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha0
  have hc : (catalan (p-1) : ℝ) = (p : ℝ)*(q+1)-1 := by
    have h : (catalan (p-1) : ℝ)+1 = (p : ℝ)*(q+1) := by exact_mod_cast ha
    linarith
  let eps : ℝ := ((2*p-2).factorial : ℝ) /
    ((p.factorial : ℝ)^2 * (p.factorial-1))
  have heps : eps = (catalan (p-1) : ℝ) / ((p : ℝ)*(p.factorial-1)) := by
    dsimp [eps]
    rw [← div_div, factorial_ratio_eq p hp.pos, div_div]
  have heps0 : 0 < eps := by dsimp [eps]; positivity
  have heps1 : eps < 1/(p : ℝ) := by
    have h := central_lt_factorial p hp3
    have he := succ_mul_catalan_eq_centralBinom (p-1)
    rw [Nat.sub_add_cancel hp.pos] at he
    rw [← he] at h
    have hsmall : catalan (p-1) < p.factorial-1 := Nat.lt_of_mul_lt_mul_left h
    have hsmallR : (catalan (p-1) : ℝ) < (p.factorial : ℝ)-1 := by
      have hh : (catalan (p-1) : ℝ)+1 < (p.factorial : ℝ) := by
        exact_mod_cast (show catalan (p-1)+1 < p.factorial by omega)
      linarith
    rw [heps]
    apply (div_lt_div_iff₀ (mul_pos hpR hdR) hpR).mpr
    nlinarith
  have hfrac0 : 0 ≤ 1 - 1/(p : ℝ) + eps := by
    have : 1/(p : ℝ) ≤ 1 := (div_le_one hpR).mpr (by exact_mod_cast hp.pos)
    linarith
  have hfrac1 : 1 - 1/(p : ℝ) + eps < 1 := by linarith
  let I := (2*p-2).factorial / p.factorial
  have hI : (I : ℝ) = ((2*p-2).factorial : ℝ) / (p.factorial : ℝ) := by
    exact Nat.cast_div (Nat.factorial_dvd_factorial (by omega)) hfR.ne'
  have hsecond : ((2*p-2).factorial : ℝ) / (p.factorial : ℝ)^2 =
      (q : ℝ) + 1 - 1/(p : ℝ) := by
    rw [factorial_ratio_eq p hp.pos, hc]
    field_simp
  have hgeom : ((2*p-2).factorial : ℝ) / (p.factorial-1) =
      (I : ℝ) + ((2*p-2).factorial : ℝ) / (p.factorial : ℝ)^2 + eps := by
    rw [hI]
    dsimp [eps]
    field_simp
    ring
  have htotal : ((2*p-2).factorial : ℝ) / (p.factorial-1) =
      ((I+q : ℕ) : ℝ) + (1 - 1/(p : ℝ) + eps) := by
    rw [hgeom, hsecond, Nat.cast_add]
    ring
  unfold rowRemainder
  rw [htotal, Int.fract_natCast_add, Int.fract_eq_self.mpr ⟨hfrac0, hfrac1⟩]

theorem row_gt_one_sub_inv (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    1 - 1/(p : ℝ) < rowRemainder (2*p-2) p := by
  rw [row_formula p hp hp2]
  have hf : (2 : ℝ) ≤ p.factorial := by
    exact_mod_cast (show 2 ≤ p.factorial by simpa using Nat.factorial_le hp.two_le)
  have hd : (0 : ℝ) < p.factorial-1 := by linarith
  have he : 0 < ((2*p-2).factorial : ℝ) /
      ((p.factorial : ℝ)^2 * (p.factorial-1)) := by positivity
  linarith

open Erdos68Development

lemma rowRemainder_lt_tail (n k : ℕ) (hn : 2 ≤ n) (hk : k ∈ Finset.Ico 2 (n+1)) :
    rowRemainder n k < rowTail n := by
  have hs : rowRemainder n k ≤ ∑ j ∈ Finset.Ico 2 (n+1), rowRemainder n j :=
    Finset.single_le_sum (f := rowRemainder n) (fun j _ => Int.fract_nonneg _) hk
  rw [rowRemainder_sum n hn] at hs
  have he := (partial_sum_error (n-1)).1
  have he' := mul_pos (show (0 : ℝ) < n.factorial by positivity) he
  unfold rowTail
  nlinarith

theorem tail_gt_one_sub_inv (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    1 - 1/(p : ℝ) < rowTail (2*p-2) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  exact (row_gt_one_sub_inv p hp hp2).trans
    (rowRemainder_lt_tail (2*p-2) p (by omega) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩))

/-- There are arbitrarily late row tails above every real number below one.
This is compatible with rationality, which permits positive integer tails. -/
theorem frequently_tail_gt (c : ℝ) (hc : c < 1) (N : ℕ) :
    ∃ n ≥ N, c < rowTail n := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1-c))
  obtain ⟨p, hpm, hp⟩ := Nat.exists_infinite_primes (max (max m N) 3)
  have hp3 : 3 ≤ p := by omega
  have hpR : (0 : ℝ) < p := by positivity
  have hmp : (m : ℝ) ≤ p := by exact_mod_cast (show m ≤ p by omega)
  have hi : 1/(p : ℝ) < 1-c := by
    apply (div_lt_iff₀ hpR).mpr
    have hh := (div_lt_iff₀ (by linarith : (0 : ℝ) < 1-c)).mp (hm.trans_le hmp)
    nlinarith
  refine ⟨2*p-2, by omega, ?_⟩
  have ht := tail_gt_one_sub_inv p hp (by omega)
  linarith

#print axioms row_formula
#print axioms row_gt_one_sub_inv
#print axioms tail_gt_one_sub_inv
#print axioms frequently_tail_gt

end PrimeRowRemainder
