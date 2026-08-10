import FormalConjectures.Util.ProblemImports

open Int

/--
A122589: Expansion of $1/(1 - 11x + 45x^2 - 84x^3 + 70x^4 - 21x^5 + x^6)$.
The sequence is defined by the linear recurrence relation:
$a(n) = 11 a(n-1) - 45 a(n-2) + 84 a(n-3) - 70 a(n-4) + 21 a(n-5) - a(n-6)$ for $n \ge 6$.
The initial values are $a(0)=1, a(1)=11, a(2)=76, a(3)=425, a(4)=2109, a(5)=9709$.
-/
def a (n : ℕ) : ℕ :=
  let rec a_int : ℕ → ℤ := fun n =>
    match n with
    | 0 => 1
    | 1 => 11
    | 2 => 76
    | 3 => 425
    | 4 => 2109
    | 5 => 9709
    | k + 6 =>
      11 * a_int (k + 5)
      - 45 * a_int (k + 4)
      + 84 * a_int (k + 3)
      - 70 * a_int (k + 2)
      + 21 * a_int (k + 1)
      - a_int k
  (a_int n).toNat

open Polynomial

noncomputable section

private abbrev P : ℝ[X] :=
  X^6 - (11:ℝ[X])*X^5 + (45:ℝ[X])*X^4 - (84:ℝ[X])*X^3 + (70:ℝ[X])*X^2 - (21:ℝ[X])*X + (1:ℝ[X])
private abbrev Q : ℝ[X] :=
  X^6 + X^5 - (5:ℝ[X])*X^4 - (4:ℝ[X])*X^3 + (6:ℝ[X])*X^2 + (3:ℝ[X])*X - (1:ℝ[X])
private def r (k : ℕ) : ℝ := 4 * Real.cos (Real.pi * (k.succ : ℝ) / 13) ^ 2

private lemma P_monic : P.Monic := by
  unfold P
  monicity!

private lemma P_natDegree : P.natDegree = 6 := by
  unfold P
  compute_degree!

private lemma P_ne_zero : P ≠ 0 := P_monic.ne_zero

private lemma P_comp_Q : P = Q.comp (X - (2:ℝ[X])) := by
  unfold P Q
  simp only [add_comp, sub_comp, mul_comp, pow_comp, X_comp, ofNat_comp, one_comp]
  ring

private lemma cheb_expand : Polynomial.Chebyshev.C ℝ (13:ℤ) = X^13 - (13:ℝ[X])*X^11 + (65:ℝ[X])*X^9 - (156:ℝ[X])*X^7 + (182:ℝ[X])*X^5 - (91:ℝ[X])*X^3 + (13:ℝ[X])*X := by
  change Polynomial.Chebyshev.C ℝ (11 + 2 : ℤ) = _
  rw [Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (12:ℤ)=10+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (11:ℤ)=9+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (10:ℤ)=8+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (9:ℤ)=7+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (8:ℤ)=6+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (7:ℤ)=5+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (6:ℤ)=4+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (5:ℤ)=3+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (4:ℤ)=2+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (3:ℤ)=1+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  rw [show (2:ℤ)=0+2 by norm_num, Polynomial.Chebyshev.C_add_two]; norm_num
  ring_nf

private lemma cheb_factor : Polynomial.Chebyshev.C ℝ (13:ℤ) - (2:ℝ[X]) = (X - (2:ℝ[X])) * Q^2 := by
  unfold Q
  rw [cheb_expand]
  ring_nf

private lemma r_sub_two (k : ℕ) : r k - 2 = 2 * Real.cos (2 * (Real.pi * (k.succ : ℝ) / 13)) := by
  unfold r
  rw [Real.cos_two_mul]
  ring

private lemma Q_root (k : ℕ) (hk : k < 6) : Q.eval (r k - 2) = 0 := by
  have hcos : Real.cos ((13:ℤ) * (2 * (Real.pi * (k.succ : ℝ) / 13))) = 1 := by
    have harg : ((13:ℤ) : ℝ) * (2 * (Real.pi * (k.succ : ℝ) / 13)) = (k.succ : ℝ) * (2 * Real.pi) := by
      norm_num
      ring
    rw [harg]
    exact Real.cos_nat_mul_two_pi k.succ
  have heval : (Polynomial.Chebyshev.C ℝ (13:ℤ)).eval (r k - 2) = 2 := by
    rw [r_sub_two, Polynomial.Chebyshev.C_two_mul_real_cos, hcos]
    ring
  have hfac := congr_arg (fun p : ℝ[X] => p.eval (r k - 2)) cheb_factor
  simp only [eval_sub, eval_ofNat, eval_mul, eval_pow, eval_X] at hfac
  rw [heval] at hfac
  norm_num at hfac
  have hneq : r k - 2 - 2 ≠ 0 := by
    rw [r_sub_two]
    have hpos : 0 < 2 * (Real.pi * (k.succ : ℝ) / 13) := by
      positivity
    have hle : 2 * (Real.pi * (k.succ : ℝ) / 13) ≤ Real.pi := by
      have hk1 : (k.succ : ℝ) ≤ 6 := by exact_mod_cast Nat.succ_le_of_lt hk
      nlinarith [Real.pi_pos]
    have hltcos : Real.cos (2 * (Real.pi * (k.succ : ℝ) / 13)) < 1 := by
      simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := 2 * (Real.pi * (k.succ : ℝ) / 13)) (le_refl 0) hle hpos
    nlinarith
  have hq := hfac.resolve_left hneq
  unfold Q
  norm_num
  exact hq

end

noncomputable section
open Polynomial

private lemma P_root (k : ℕ) (hk : k < 6) : P.eval (r k) = 0 := by
  rw [P_comp_Q]
  simpa using Q_root k hk

private lemma r_alt (k : ℕ) : r k = 2 + 2 * Real.cos (2 * (Real.pi * (k.succ : ℝ) / 13)) := by
  unfold r
  rw [Real.cos_two_mul]
  ring

private lemma r_injOn : Set.InjOn r (↑(Finset.range 6) : Set ℕ) := by
  intro i hi j hj hrij
  simp only [Finset.mem_coe, Finset.mem_range] at hi hj
  have hiang_nonneg : 0 ≤ 2 * (Real.pi * (i.succ : ℝ) / 13) := by positivity
  have hjang_nonneg : 0 ≤ 2 * (Real.pi * (j.succ : ℝ) / 13) := by positivity
  have hiang_le : 2 * (Real.pi * (i.succ : ℝ) / 13) ≤ Real.pi := by
    have hi1 : (i.succ : ℝ) ≤ 6 := by exact_mod_cast Nat.succ_le_of_lt hi
    nlinarith [Real.pi_pos]
  have hjang_le : 2 * (Real.pi * (j.succ : ℝ) / 13) ≤ Real.pi := by
    have hj1 : (j.succ : ℝ) ≤ 6 := by exact_mod_cast Nat.succ_le_of_lt hj
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (2 * (Real.pi * (i.succ : ℝ) / 13)) = Real.cos (2 * (Real.pi * (j.succ : ℝ) / 13)) := by
    have hi_alt := r_alt i
    have hj_alt := r_alt j
    nlinarith
  have hang : 2 * (Real.pi * (i.succ : ℝ) / 13) = 2 * (Real.pi * (j.succ : ℝ) / 13) :=
    Real.injOn_cos ⟨hiang_nonneg, hiang_le⟩ ⟨hjang_nonneg, hjang_le⟩ hcos
  have hs : (i.succ : ℝ) = (j.succ : ℝ) := by
    nlinarith [Real.pi_pos]
  exact Nat.succ.inj (Nat.cast_injective hs)

private lemma P_roots_image : P.roots = ((Finset.range 6).image r).val := by
  classical
  refine Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero (p := P) (S := (Finset.range 6).image r) ?_ ?_ P_ne_zero
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    exact P_root k (by simpa using hk)
  · have hcard : ((Finset.range 6).image r).card = 6 := by
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro x hx y hy hxy
        exact r_injOn (by simpa using hx) (by simpa using hy) hxy
    rw [hcard]
    unfold P
    compute_degree!

private lemma P_eq_prod_X_sub : P = Finset.prod (Finset.range 6) (fun k => (X - C (r k) : ℝ[X])) := by
  classical
  have hroots := P_roots_image
  have hcardImage : ((Finset.range 6).image r).card = 6 := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro x hx y hy hxy
      exact r_injOn (by simpa using hx) (by simpa using hy) hxy
  have hcard : P.roots.card = P.natDegree := by
    rw [hroots, P_natDegree]
    change ((Finset.range 6).image r).card = 6
    exact hcardImage
  have hsplits : P.Splits := Polynomial.splits_iff_card_roots.mpr hcard
  calc
    P = (P.roots.map fun a => X - C a).prod := hsplits.eq_prod_roots_of_monic P_monic
    _ = (((Finset.range 6).image r).val.map fun a => X - C a).prod := by rw [hroots]
    _ = Finset.prod ((Finset.range 6).image r) (fun x => (X - C x : ℝ[X])) := rfl
    _ = Finset.prod (Finset.range 6) (fun k => (X - C (r k) : ℝ[X])) := by
      rw [Finset.prod_image]
      intro x hx y hy hxy
      exact r_injOn (by simpa using hx) (by simpa using hy) hxy

end

noncomputable section
open Polynomial

private lemma reverse_X_sub_C (a : ℝ) : (X - C a : ℝ[X]).reverse = (1 - C a * X : ℝ[X]) := by
  rw [Polynomial.reverse]
  simp

private lemma reverse_prod_X_sub :
    (Finset.prod (Finset.range 6) (fun k => (X - C (r k) : ℝ[X]))).reverse =
      Finset.prod (Finset.range 6) (fun k => (1 - C (r k) * X : ℝ[X])) := by
  classical
  refine Finset.induction_on (Finset.range 6) ?_ ?_
  · simpa using (Polynomial.reverse_C (R := ℝ) (1 : ℝ))
  · intro a s has ih
    rw [Finset.prod_insert has, Finset.prod_insert has, Polynomial.reverse_mul_of_domain, ih, reverse_X_sub_C]

private lemma reverse_P_eq_target : P.reverse =
    ((1:ℝ[X]) - (11:ℝ[X]) * X + (45:ℝ[X]) * X^2 - (84:ℝ[X]) * X^3 + (70:ℝ[X]) * X^4 - (21:ℝ[X]) * X^5 + X^6) := by
  ext n
  rw [Polynomial.coeff_reverse, P_natDegree]
  by_cases hn : n ≤ 6
  · interval_cases n <;> simp [P, Polynomial.coeff_X, Polynomial.coeff_one]
  · have hgt : 6 < n := Nat.lt_of_not_ge hn
    rw [Polynomial.revAt_eq_self_of_lt hgt]
    have hleft : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [P_natDegree] using hgt)
    have hright : (((1:ℝ[X]) - (11:ℝ[X]) * X + (45:ℝ[X]) * X^2 - (84:ℝ[X]) * X^3 + (70:ℝ[X]) * X^4 - (21:ℝ[X]) * X^5 + X^6).coeff n) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      compute_degree!
    rw [hleft, hright]

/--
The conjecture suggested by the study of polynomials associated with the regular 13-gon
is that the denominator of the generating function for A122589 factors based on
the cosines of the angles of a regular 13-gon.
Specifically, let $P(x)$ be the denominator of the generating function. Then
$$P(x) = 1 - 11x + 45x^2 - 84x^3 + 70x^4 - 21x^5 + x^6 = \prod_{k=1}^6 \left(1 - 4 \cos^2\left(\frac{\pi k}{13}\right) x\right)$$
-/
theorem oeis_a122589_conjecture_0 :
    (C (1 : ℝ) - C (11 : ℝ) * X + C (45 : ℝ) * X^2 - C (84 : ℝ) * X^3 + C (70 : ℝ) * X^4 - C (21 : ℝ) * X^5 + C (1 : ℝ) * X^6)
    = Finset.prod (Finset.range 6)
        (fun k : ℕ => C (1 : ℝ) - C (4 * Real.cos (Real.pi * (k.succ : ℝ) / 13) ^ 2) * X) := by
  have h := congr_arg Polynomial.reverse P_eq_prod_X_sub
  rw [reverse_prod_X_sub] at h
  rw [reverse_P_eq_target] at h
  -- convert target constants to numerals/r
  change ((1:ℝ[X]) - (11:ℝ[X]) * X + (45:ℝ[X]) * X^2 - (84:ℝ[X]) * X^3 + (70:ℝ[X]) * X^4 - (21:ℝ[X]) * X^5 + (1:ℝ[X]) * X^6) =
    Finset.prod (Finset.range 6) (fun k : ℕ => (1:ℝ[X]) - C (r k) * X)
  simpa [r] using h

end

instance : Coe ℕ ℝ where
  coe := Nat.cast
