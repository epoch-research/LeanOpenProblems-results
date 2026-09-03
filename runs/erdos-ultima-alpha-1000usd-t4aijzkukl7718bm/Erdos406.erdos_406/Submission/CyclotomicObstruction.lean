import Submission.ValuationStructure

/-! Cyclotomic factors of polynomials taking a pure power-of-two value at
three. These factor restrictions do not imply the missing-digit conjecture. -/

namespace Erdos406Cyclotomic
open Polynomial

lemma cyclotomic_eval_three_dvd_two_pow {m k : ℕ}
    (hd : ((cyclotomic m ℤ).eval 3).natAbs ∣ 2 ^ k) : m ≤ 2 := by
  by_contra hm
  have hm2 : 2 < m := by omega
  have hlarge : 2 < ((cyclotomic m ℤ).eval 3).natAbs := by
    exact sub_one_lt_natAbs_cyclotomic_eval (by omega : 1 < m) (by decide : (3 : ℕ) ≠ 1)
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hd
  have hj0 : j ≠ 0 := by intro hz; simp [hz] at hj; omega
  have hd2 : (2 : ℤ) ∣ (cyclotomic m ℤ).eval 3 := by
    apply Int.natAbs_dvd_natAbs.mp
    change 2 ∣ ((cyclotomic m ℤ).eval 3).natAbs
    rw [hj]
    exact dvd_pow_self 2 hj0
  have hdiff : (2 : ℤ) ∣ (cyclotomic m ℤ).eval 3 - (cyclotomic m ℤ).eval 1 :=
    sub_dvd_eval_sub 3 1 _
  have heven : (2 : ℤ) ∣ (cyclotomic m ℤ).eval 1 := by
    convert dvd_sub hd2 hdiff using 1
    ring
  have hpp : ∃ p s : ℕ, p.Prime ∧ p ^ s = m := by
    by_contra hh
    push_neg at hh
    have h1 : (cyclotomic m ℤ).eval 1 = 1 :=
      eval_one_cyclotomic_not_prime_pow (fun {p} hp s => hh p s hp)
    rw [h1] at heven
    norm_num at heven
  obtain ⟨p, s, hp, hpow⟩ := hpp
  have hs : 0 < s := by
    by_contra hh
    have hz : s = 0 := by omega
    simp [hz] at hpow
    omega
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← hpow, eval_one_cyclotomic_prime_pow] at heven
  have hp2 : p = 2 := (hp.dvd_iff_eq (by decide : 2 ≠ 1)).mp (Int.natCast_dvd_natCast.mp heven)
  subst p
  have hval : ((cyclotomic m ℤ).eval 3).natAbs = 3 ^ (2 ^ t) + 1 := by
    rw [← hpow, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    norm_num [Finset.sum_range_succ, eval_add, eval_pow, eval_X, eval_one]
    rw [show (1 : ℤ) + 3 ^ (2 ^ t) = ((3 ^ (2 ^ t) + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.natAbs_natCast _
  rw [hval] at hd
  have hexp := Erdos406Structure.three_pow_add_one_dvd_two_pow
    (by positivity : 0 < 2 ^ t) hd
  rw [pow_succ, hexp] at hpow
  omega

/-- Every nonconstant cyclotomic divisor of a polynomial with P(3)=2^k
is X-1 or X+1. This does not classify the noncyclotomic factors. -/
lemma cyclotomic_factor_index {P : ℤ[X]} {k m : ℕ}
    (he : P.eval 3 = (2 : ℤ) ^ k) (hm : 0 < m) (hd : cyclotomic m ℤ ∣ P) :
    m = 1 ∨ m = 2 := by
  have hdv := eval_dvd (x := (3 : ℤ)) hd
  rw [he] at hdv
  have hnat := Int.natAbs_dvd_natAbs.mpr hdv
  have hh := cyclotomic_eval_three_dvd_two_pow (by simpa using hnat)
  omega

lemma cyclotomic_factor_index_of_eval_one_ne_zero {P : ℤ[X]} {k m : ℕ}
    (he : P.eval 3 = (2 : ℤ) ^ k) (h1 : P.eval 1 ≠ 0)
    (hm : 0 < m) (hd : cyclotomic m ℤ ∣ P) : m = 2 := by
  rcases cyclotomic_factor_index he hm hd with rfl | h
  · have hz : (0 : ℤ) ∣ P.eval 1 := by
      simpa only [cyclotomic_one, eval_sub, eval_X, eval_one, sub_self] using
        eval_dvd (x := (1 : ℤ)) hd
    exact False.elim (h1 (zero_dvd_iff.mp hz))
  · exact h

noncomputable def digitPoly (w : List ℕ) : ℤ[X] := Nat.ofDigits X w

lemma eval_digitPoly (w : List ℕ) (a : ℤ) : (digitPoly w).eval a = Nat.ofDigits a w := by
  induction w with
  | nil => simp [digitPoly, Nat.ofDigits]
  | cons d w ih => simpa [digitPoly, Nat.ofDigits] using congrArg (fun z => (d : ℤ) + a * z) ih

lemma digitPoly_eval_three (n : ℕ) : (digitPoly (Nat.digits 3 n)).eval 3 = n := by
  rw [eval_digitPoly]
  simpa only [Nat.ofDigits_digits, Nat.cast_ofNat] using
    (Nat.coe_ofDigits ℤ 3 (Nat.digits 3 n)).symm

lemma digitPoly_eval_one_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (digitPoly (Nat.digits 3 n)).eval 1 ≠ 0 := by
  intro h
  rw [eval_digitPoly] at h
  have hh : ((Nat.ofDigits 1 (Nat.digits 3 n) : ℕ) : ℤ) = 0 :=
    (Nat.coe_ofDigits ℤ 1 (Nat.digits 3 n)).trans (by simpa using h)
  have hz : Nat.ofDigits 1 (Nat.digits 3 n) = 0 := by exact_mod_cast hh
  have hne : Nat.digits 3 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hh := Nat.digits_zero_of_eq_zero (by decide : (1 : ℕ) ≠ 0) hz
    ((Nat.digits 3 n).getLast hne) (List.getLast_mem hne)
  exact Nat.getLast_digit_ne_zero 3 hn hh

lemma good_digitPoly_coeff_one {w : List ℕ} (hw : w ⊆ [0, 1]) :
    (digitPoly w).coeff 1 ≤ 1 := by
  cases w with
  | nil => simp [digitPoly, Nat.ofDigits]
  | cons a w =>
    cases w with
    | nil => simp [digitPoly, Nat.ofDigits]
    | cons b w =>
      have hb := hw (by simp : b ∈ a :: b :: w)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl <;> simp [digitPoly, Nat.ofDigits, coeff_X_mul]

/-- The restriction applies directly to the digit polynomial of every power
of two. Goodness is not needed for this individual factor restriction. -/
theorem digitPoly_cyclotomic_factor {n m : ℕ} (hn : n.isPowerOfTwo)
    (hm : 0 < m) (hd : cyclotomic m ℤ ∣ digitPoly (Nat.digits 3 n)) : m = 2 := by
  obtain ⟨k, rfl⟩ := hn
  apply cyclotomic_factor_index_of_eval_one_ne_zero (k := k) _
    (digitPoly_eval_one_ne_zero (by positivity)) hm hd
  rw [digitPoly_eval_three]
  norm_cast

lemma prod_cyclotomics_twos (L : List ℕ) (h : ∀ m ∈ L, m = 2) :
    (L.map (fun m => cyclotomic m ℤ)).prod = (X + 1) ^ L.length := by
  induction L with
  | nil => simp
  | cons m L ih =>
    rw [List.map_cons, List.prod_cons, h m (by simp), cyclotomic_two,
      ih (fun m hm => h m (by simp [hm])), List.length_cons, pow_succ']

/-- If a hypothetical good power has no factors other than cyclotomic ones,
it is 1 or 4. The hypothesis that all factors are cyclotomic is essential:
the digit polynomial of 256 already has a noncyclotomic factor. -/
theorem good_power_product_cyclotomics {n : ℕ} (hn : n.isPowerOfTwo)
    (hd : Nat.digits 3 n ⊆ [0, 1]) (L : List ℕ) (hL : ∀ m ∈ L, 0 < m)
    (hfac : digitPoly (Nat.digits 3 n) = (L.map (fun m => cyclotomic m ℤ)).prod) :
    n = 1 ∨ n = 4 := by
  have htwo : ∀ m ∈ L, m = 2 := by
    intro m hm
    apply digitPoly_cyclotomic_factor hn (hL m hm)
    rw [hfac]
    exact List.dvd_prod (List.mem_map_of_mem hm)
  rw [prod_cyclotomics_twos L htwo] at hfac
  have hc := good_digitPoly_coeff_one hd
  rw [hfac, coeff_X_add_one_pow, Nat.choose_one_right] at hc
  have hlen : L.length ≤ 1 := by exact_mod_cast hc
  have he := congrArg (eval (3 : ℤ)) hfac
  rw [digitPoly_eval_three] at he
  rcases (show L.length = 0 ∨ L.length = 1 by omega) with h0 | h1
  · simp [h0] at he
    exact Or.inl (by exact_mod_cast he)
  · simp [h1] at he
    exact Or.inr (by exact_mod_cast he)

lemma digitPoly_256_factorization :
    digitPoly (Nat.digits 3 256) =
      (X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 + 1 : ℤ[X]) := by
  have hd : Nat.digits 3 256 = [1, 1, 1, 0, 0, 1] := by
    norm_num [Nat.digits_of_two_le_of_pos]
  rw [hd]
  simp only [digitPoly, Nat.ofDigits]
  ring

lemma quartic_eval_three :
    (X ^ 4 - X ^ 3 + X ^ 2 + 1 : ℤ[X]).eval 3 = 2 ^ 6 := by norm_num

lemma quartic_not_cyclotomic (m : ℕ) :
    (X ^ 4 - X ^ 3 + X ^ 2 + 1 : ℤ[X]) ≠ cyclotomic m ℤ := by
  intro he
  have hd : ((cyclotomic m ℤ).eval 3).natAbs ∣ 2 ^ 6 := by
    rw [← he, quartic_eval_three]
    norm_num
  have hm := cyclotomic_eval_three_dvd_two_pow hd
  have hv := congrArg (eval (3 : ℤ)) he
  rw [quartic_eval_three] at hv
  interval_cases m <;> norm_num [cyclotomic_zero, cyclotomic_one, cyclotomic_two] at hv

/-- The all-cyclotomic hypothesis cannot be inferred merely from the original
conditions: the known example 256 is already a counterexample. -/
theorem good_power_need_not_be_product_cyclotomics :
    ¬ (∀ n : ℕ, n.isPowerOfTwo → Nat.digits 3 n ⊆ [0, 1] →
      ∃ L : List ℕ, (∀ m ∈ L, 0 < m) ∧
        digitPoly (Nat.digits 3 n) = (L.map (fun m => cyclotomic m ℤ)).prod) := by
  intro h
  have hp : (256 : ℕ).isPowerOfTwo := ⟨8, by norm_num⟩
  have hg : Nat.digits 3 256 ⊆ [0, 1] := by norm_num [Nat.digits_of_two_le_of_pos]
  obtain ⟨L, hL, hfac⟩ := h 256 hp hg
  have hh := good_power_product_cyclotomics hp hg L hL hfac
  omega

#print axioms quartic_not_cyclotomic
#print axioms good_power_need_not_be_product_cyclotomics
#print axioms digitPoly_cyclotomic_factor
#print axioms good_power_product_cyclotomics
#print axioms cyclotomic_eval_three_dvd_two_pow
#print axioms cyclotomic_factor_index_of_eval_one_ne_zero
end Erdos406Cyclotomic
