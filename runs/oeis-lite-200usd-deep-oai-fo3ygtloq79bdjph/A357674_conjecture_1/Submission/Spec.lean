import FormalConjectures.Util.ProblemImports
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.moduleDocstring false



open Nat Finset BigOperators







def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3






def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)


theorem A357674_one : A357674 1 = 3 ^ 7 := by
  norm_num [A357674, Finset.sum_range_succ]



theorem A357674_conjecture_1_p3 : A357674 3 ≡ A357674 1 [MOD 3 ^ 5] := by
  norm_num [A357674, A357674_one, Finset.sum_range_succ, Nat.ModEq, Nat.choose]


theorem A357674_conjecture_1_p5 : A357674 5 ≡ A357674 1 [MOD 5 ^ 5] := by
  norm_num [A357674, A357674_one, Finset.sum_range_succ, Nat.ModEq, Nat.choose]



theorem A357674_prime_ge_five_of_ne_three (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3)
    (hne3 : p ≠ 3) : 5 ≤ p := by
  by_contra h
  have hp_le4 : p ≤ 4 := by omega
  interval_cases p
  · contradiction
  · norm_num at hp


theorem A357674_prime_ge_seven_of_ne_five (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5)
    (hne5 : p ≠ 5) : 7 ≤ p := by
  by_contra h
  have hp_le6 : p ≤ 6 := by omega
  interval_cases p <;> try contradiction <;> norm_num at hp





theorem A357674_S1_eq_choose (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n + 1), (n + k - 1).choose k) = (3 * n).choose (2 * n) := by
  cases n with
  | zero => norm_num
  | succ n =>
      have h := Nat.sum_range_add_choose (2 * (n + 1)) n
      calc
        (∑ k ∈ Finset.range (2 * (n + 1) + 1), (n + 1 + k - 1).choose k)
            = ∑ k ∈ Finset.range (2 * (n + 1) + 1), (k + n).choose n := by
              refine sum_congr rfl ?_
              intro k hk
              rw [show n + 1 + k - 1 = k + n by omega]
              exact Nat.choose_symm_add
        _ = (3 * (n + 1)).choose (n + 1) := by
              convert h using 2
              ring
        _ = (3 * (n + 1)).choose (2 * (n + 1)) := by
              apply Nat.choose_symm_of_eq_add
              omega





theorem A357674_S1_eq_three_mul_T (p : ℕ) (hp0 : 0 < p) :
    (∑ k ∈ Finset.range (2 * p + 1), (p + k - 1).choose k) =
      3 * ((3 * p - 1).choose (p - 1)) := by
  rw [A357674_S1_eq_choose]
  have hsym : (3 * p - 1).choose (2 * p) = (3 * p - 1).choose (p - 1) := by
    apply Nat.choose_symm_of_eq_add
    omega
  have hmul := Nat.choose_mul_succ_eq (3 * p - 1) (2 * p)
  rw [hsym] at hmul
  have hsub : 3 * p - 1 + 1 - 2 * p = p := by omega
  have hsucc : 3 * p - 1 + 1 = 3 * p := by omega
  rw [hsub, hsucc] at hmul
  have hmul2 : (3 * ((3 * p - 1).choose (p - 1))) * p = ((3 * p).choose (2 * p)) * p := by
    calc
      (3 * ((3 * p - 1).choose (p - 1))) * p
          = ((3 * p - 1).choose (p - 1)) * (3 * p) := by ring
      _ = ((3 * p).choose (2 * p)) * p := hmul
  exact Nat.mul_right_cancel hp0 hmul2.symm





theorem A357674_route_poly_congr (P t : ℤ) (h : t ≡ 1 [ZMOD P ^ 3]) :
    (3 * t) ^ 4 * (7 - 4 * t) ^ 3 ≡ 3 ^ 7 [ZMOD P ^ 5] := by
  rw [Int.modEq_iff_dvd]
  rcases h.dvd with ⟨q, hq⟩
  use -81 * P * q ^ 2 * (64 * P ^ 15 * q ^ 5 - 112 * P ^ 12 * q ^ 4 -
      84 * P ^ 9 * q ^ 3 + 203 * P ^ 6 * q ^ 2 + 28 * P ^ 3 * q - 126)
  have ht : t = 1 - P ^ 3 * q := by omega
  rw [ht]
  ring_nf





theorem A357674_route_product_congr (p T S2 : ℕ)
    (hT : (T : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3])
    (hS2 : (S2 : ℤ) ≡ 7 - 4 * (T : ℤ) [ZMOD (p : ℤ) ^ 5]) :
    ((3 * T) ^ 4 * S2 ^ 3 : ℕ) ≡ 3 ^ 7 [MOD p ^ 5] := by
  rw [Nat.modEq_iff_dvd]
  have hleft : (((3 * T) ^ 4 * S2 ^ 3 : ℕ) : ℤ) =
      (3 * (T : ℤ)) ^ 4 * (S2 : ℤ) ^ 3 := by norm_num
  rw [hleft]
  have hfac : (3 * (T : ℤ)) ^ 4 ≡ (3 * (T : ℤ)) ^ 4 [ZMOD (p : ℤ) ^ 5] :=
    Int.ModEq.refl _
  have hprod : (3 * (T : ℤ)) ^ 4 * (S2 : ℤ) ^ 3 ≡
      (3 * (T : ℤ)) ^ 4 * (7 - 4 * (T : ℤ)) ^ 3 [ZMOD (p : ℤ) ^ 5] := by
    exact hfac.mul (hS2.pow 3)
  have hpoly := A357674_route_poly_congr (p : ℤ) (T : ℤ) hT
  have hfinal := hprod.trans hpoly
  simpa [Int.natCast_pow] using hfinal.dvd





theorem A357674_conjecture_1_from_route (p T : ℕ)
    (hS1 : (∑ k ∈ Finset.range (2 * p + 1), (p + k - 1).choose k) = 3 * T)
    (hT : (T : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3])
    (hS2 : ((∑ k ∈ Finset.range (2 * p + 1), ((p + k - 1).choose k) ^ 2 : ℕ) : ℤ) ≡
      7 - 4 * (T : ℤ) [ZMOD (p : ℤ) ^ 5]) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  rw [A357674]
  rw [hS1]
  have hprod := A357674_route_product_congr p T
    (∑ k ∈ Finset.range (2 * p + 1), ((p + k - 1).choose k) ^ 2) hT hS2
  exact hprod.trans (by rw [A357674_one])



lemma isUnit_natCast_zmod_prime_pow_of_pos_lt (p r i : ℕ) (hp : p.Prime) (hr : 0 < r) (hi0 : 0 < i) (hip : i < p) :
    IsUnit (i : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    exact not_le_of_gt hip (Nat.le_of_dvd hi0 hdiv))

lemma natCast_inv_mul_eq_one (p r i : ℕ) (hp : p.Prime) (hr : 0 < r) (hi0 : 0 < i) (hip : i < p) :
    ((i : ZMod (p ^ r))⁻¹) * (i : ZMod (p ^ r)) = 1 := by
  exact ZMod.inv_mul_of_unit _ (isUnit_natCast_zmod_prime_pow_of_pos_lt p r i hp hr hi0 hip)

lemma choose_prod_aux (p r n : ℕ) (hp : p.Prime) (hr : 0 < r) (hn : n < p) :
    (((2 * p + n).choose n : ℕ) : ZMod (p ^ r)) =
      ∏ i ∈ Finset.Icc 1 n, (1 + (2 * p : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnlt : n < p := by omega
      have hsuccpos : 0 < n + 1 := by omega
      have hsucc_lt : n + 1 < p := hn
      have hunit : IsUnit ((n + 1 : ℕ) : ZMod (p ^ r)) :=
        isUnit_natCast_zmod_prime_pow_of_pos_lt p r (n+1) hp hr hsuccpos hsucc_lt
      have hrec := ih hnlt
      have hchoose := Nat.add_one_mul_choose_eq (2 * p + n) n
      -- `(2p+n+1) * C(2p+n,n) = C(2p+n+1,n+1) * (n+1)`
      have hcast : ((2 * p + n + 1 : ℕ) : ZMod (p ^ r)) *
            (((2 * p + n).choose n : ℕ) : ZMod (p ^ r)) =
          (((2 * p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) *
            ((n + 1 : ℕ) : ZMod (p ^ r)) := by
        simpa [Nat.cast_mul] using congrArg (fun x : ℕ => (x : ZMod (p ^ r))) hchoose
      have hinv : ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ * ((n + 1 : ℕ) : ZMod (p ^ r)) = 1 :=
        natCast_inv_mul_eq_one p r (n+1) hp hr hsuccpos hsucc_lt
      have hstep : (((2 * p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) =
          (((2 * p + n).choose n : ℕ) : ZMod (p ^ r)) *
            (((2 * p + n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
        calc
          (((2 * p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r))
              = (((2 * p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) *
                  (((n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
                    rw [ZMod.mul_inv_of_unit _ hunit, mul_one]
          _ = ((((2 * p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))) *
                  ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by ring_nf
          _ = (((2 * p + n + 1 : ℕ) : ZMod (p ^ r)) * (((2 * p + n).choose n : ℕ) : ZMod (p ^ r))) *
                  ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by rw [← hcast]
          _ = (((2 * p + n).choose n : ℕ) : ZMod (p ^ r)) *
              (((2 * p + n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by ring_nf
      have htop : 2 * p + (n + 1) = 2 * p + n + 1 := by omega
      rw [htop]
      rw [hstep, hrec]
      rw [Finset.prod_Icc_succ_top hsuccpos]
      congr 1
      have hfactor : (((2 * p + n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) =
          1 + (2 * p : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by
        have hcasttop : ((2 * p + n + 1 : ℕ) : ZMod (p ^ r)) =
            (2 * p : ZMod (p ^ r)) + ((n + 1 : ℕ) : ZMod (p ^ r)) := by
          norm_num [Nat.cast_add, Nat.cast_mul]
          ring
        rw [hcasttop]
        rw [add_mul, ZMod.mul_inv_of_unit _ hunit]
        ring
      exact hfactor

lemma p_pow_self_zmod_zero (p r : ℕ) : ((p : ZMod (p ^ r)) ^ r) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]

lemma inv_p_sub_expansion (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    (((p - i : ℕ) : ZMod (p ^ 3))⁻¹) =
      - ((i : ZMod (p ^ 3))⁻¹) - (p : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)^2 -
        (p : ZMod (p ^ 3))^2 * ((i : ZMod (p ^ 3))⁻¹)^3 := by
  let R := ZMod (p ^ 3)
  have hunit_i : IsUnit (i : R) := isUnit_natCast_zmod_prime_pow_of_pos_lt p 3 i hp (by norm_num) hi0 hip
  have hunit_pi : IsUnit ((p - i : ℕ) : R) := by
    apply isUnit_natCast_zmod_prime_pow_of_pos_lt p 3 (p - i) hp (by norm_num)
    · omega
    · omega
  apply_fun fun x : R => x * ((p - i : ℕ) : R)
  · change (((p - i : ℕ) : R)⁻¹ * ((p - i : ℕ) : R)) =
      (-((i : R)⁻¹) - (p : R) * ((i : R)⁻¹)^2 - (p : R)^2 * ((i : R)⁻¹)^3) * ((p - i : ℕ) : R)
    rw [ZMod.inv_mul_of_unit _ hunit_pi]
    have hpi : ((p - i : ℕ) : R) = (p : R) - (i : R) := by
      rw [Nat.cast_sub (le_of_lt hip)]
    rw [hpi]
    have hi_inv : ((i : R)⁻¹) * (i : R) = 1 := ZMod.inv_mul_of_unit _ hunit_i
    have hi_inv2 : ((i : R)⁻¹)^2 * (i : R) = (i : R)⁻¹ := by
      calc
        ((i : R)⁻¹)^2 * (i : R) = (i : R)⁻¹ * (((i : R)⁻¹) * (i : R)) := by ring
        _ = (i : R)⁻¹ := by rw [hi_inv, mul_one]
    have hi_inv3 : ((i : R)⁻¹)^3 * (i : R) = ((i : R)⁻¹)^2 := by
      calc
        ((i : R)⁻¹)^3 * (i : R) = ((i : R)⁻¹)^2 * (((i : R)⁻¹) * (i : R)) := by ring
        _ = ((i : R)⁻¹)^2 := by rw [hi_inv, mul_one]
    have hp3zero : (p : R)^3 = 0 := p_pow_self_zmod_zero p 3
    have t2 : ((i : R)⁻¹)^2 * (p : R) * (i : R) = (p : R) * (i : R)⁻¹ := by
      calc
        ((i : R)⁻¹)^2 * (p : R) * (i : R) = (p : R) * (((i : R)⁻¹)^2 * (i : R)) := by ring
        _ = (p : R) * (i : R)⁻¹ := by rw [hi_inv2]
    have t3 : ((i : R)⁻¹)^3 * (p : R)^2 * (i : R) = (p : R)^2 * ((i : R)⁻¹)^2 := by
      calc
        ((i : R)⁻¹)^3 * (p : R)^2 * (i : R) = (p : R)^2 * (((i : R)⁻¹)^3 * (i : R)) := by ring
        _ = (p : R)^2 * ((i : R)⁻¹)^2 := by rw [hi_inv3]
    have t4 : ((i : R)⁻¹)^3 * (p : R)^2 * (p : R) = 0 := by
      calc
        ((i : R)⁻¹)^3 * (p : R)^2 * (p : R) = ((i : R)⁻¹)^3 * (p : R)^3 := by ring
        _ = 0 := by rw [hp3zero, mul_zero]

    calc
      1 = -((i : R)⁻¹) * (p : R) + ((i : R)⁻¹) * (i : R)
          - ((i : R)⁻¹)^2 * (p : R) * (p : R) + ((i : R)⁻¹)^2 * (p : R) * (i : R)
          - ((i : R)⁻¹)^3 * (p : R)^2 * (p : R) + ((i : R)⁻¹)^3 * (p : R)^2 * (i : R) := by
            rw [hi_inv, t2, t3, t4]
            ring
      _ = (-((i : R)⁻¹) - (p : R) * ((i : R)⁻¹)^2 - (p : R)^2 * ((i : R)⁻¹)^3) * ((p : R) - (i : R)) := by
            ring
  · intro a b hab
    calc
      a = a * 1 := by rw [mul_one]
      _ = a * (((p - i : ℕ) : R) * ((p - i : ℕ) : R)⁻¹) := by rw [ZMod.mul_inv_of_unit _ hunit_pi]


      _ = (a * ((p - i : ℕ) : R)) * ((p - i : ℕ) : R)⁻¹ := by ring
      _ = (b * ((p - i : ℕ) : R)) * ((p - i : ℕ) : R)⁻¹ := by simpa using congrArg (fun x : R => x * (((p - i : ℕ) : R)⁻¹)) hab
      _ = b * (((p - i : ℕ) : R) * ((p - i : ℕ) : R)⁻¹) := by ring
      _ = b := by rw [ZMod.mul_inv_of_unit _ hunit_pi, mul_one]

lemma pair_factor_eq (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    (1 + (2 * p : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)) *
      (1 + (2 * p : ZMod (p ^ 3)) * (((p - i : ℕ) : ZMod (p ^ 3))⁻¹)) =
    1 - 6 * (p : ZMod (p ^ 3))^2 * ((i : ZMod (p ^ 3))⁻¹)^2 := by
  rw [inv_p_sub_expansion p i hp hi0 hip]
  have hp3zero : (p : ZMod (p ^ 3))^3 = 0 := p_pow_self_zmod_zero p 3
  have hp4zero : (p : ZMod (p ^ 3))^4 = 0 := by
    calc
      (p : ZMod (p ^ 3))^4 = (p : ZMod (p ^ 3))^3 * (p : ZMod (p ^ 3)) := by ring
      _ = 0 := by rw [hp3zero, zero_mul]
  ring_nf
  rw [hp3zero, hp4zero]
  ring



lemma Icc_one_pred_eq_range_erase_zero (p : ℕ) (hp0 : 0 < p) :
    Finset.Icc 1 (p - 1) = (Finset.range p).erase 0 := by
  ext i
  simp [Finset.mem_Icc]
  omega

lemma sum_range_zmod_eq_sum_univ (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    (∑ i ∈ Finset.range p, f (i : ZMod p)) = ∑ x : ZMod p, f x := by
  rw [Finset.sum_range]
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      change (∑ i : Fin (n + 1), f (i.val : ZMod (n + 1))) = ∑ x : ZMod (n + 1), f x
      conv_rhs =>
        arg 2
        intro x
        rw [← ZMod.natCast_zmod_val x]
      rfl

lemma inv_sq_sum_Icc_zmodp_zero (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^2) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : 0 < p := hp.pos
  rw [Icc_one_pred_eq_range_erase_zero p hp0]
  rw [Finset.sum_erase]
  · have hpow : (∑ i ∈ Finset.range p, ((i : ZMod p) ^ (p - 3))) = 0 := by
      rw [sum_range_zmod_eq_sum_univ p (fun x : ZMod p => x ^ (p - 3))]
      have hlt : p - 3 < Fintype.card (ZMod p) - 1 := by
        rw [ZMod.card]
        omega
      exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) (p - 3) hlt
    trans (∑ i ∈ Finset.range p, ((i : ZMod p) ^ (p - 3)))
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        have hpos : 0 < p - 3 := by omega
        simp [hpos.ne']
      · have hip : i < p := by simpa using hi
        have hunit : IsUnit (i : ZMod p) := by
          apply isUnit_iff_ne_zero.mpr
          intro hz
          have hdvd : p ∣ i := (ZMod.natCast_eq_zero_iff i p).1 hz
          exact not_le_of_gt hip (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hdvd)
        have hfermat : (i : ZMod p) ^ (p - 1) = 1 := by
          apply ZMod.pow_card_sub_one_eq_one
          exact IsUnit.ne_zero hunit
        have hpoweq : ((i : ZMod p)⁻¹)^2 = (i : ZMod p)^(p - 3) := by
          have hmul : ((i : ZMod p)⁻¹)^2 * (i : ZMod p)^2 = 1 := by
            rw [← mul_pow, ZMod.inv_mul_of_unit _ hunit]
            norm_num
          have hright : (i : ZMod p)^(p - 3) * (i : ZMod p)^2 = 1 := by
            rw [← pow_add]
            have hadd : p - 3 + 2 = p - 1 := by omega
            rw [hadd, hfermat]
          have hunit2 : IsUnit ((i : ZMod p)^2) := hunit.pow 2
          calc
            ((i : ZMod p)⁻¹)^2
                = ((i : ZMod p)⁻¹)^2 * (((i : ZMod p)^2) * (((i : ZMod p)^2)⁻¹)) := by
                    rw [ZMod.mul_inv_of_unit _ hunit2, mul_one]
            _ = (((i : ZMod p)⁻¹)^2 * (i : ZMod p)^2) * (((i : ZMod p)^2)⁻¹) := by ring
            _ = 1 * (((i : ZMod p)^2)⁻¹) := by rw [hmul]
            _ = ((i : ZMod p)^(p - 3) * (i : ZMod p)^2) * (((i : ZMod p)^2)⁻¹) := by rw [hright]
            _ = (i : ZMod p)^(p - 3) * (((i : ZMod p)^2) * (((i : ZMod p)^2)⁻¹)) := by ring
            _ = (i : ZMod p)^(p - 3) := by rw [ZMod.mul_inv_of_unit _ hunit2, mul_one]
        exact hpoweq
    · exact hpow
  · simp

lemma inv_sq_sum_upper_eq_half_zmodp (p h : ℕ) (hp : p.Prime) (hp_eq : p = 2 * h + 1) :
    (∑ i ∈ Finset.Icc (h + 1) (p - 1), (((i : ZMod p)⁻¹)^2)) =
      ∑ i ∈ Finset.Icc 1 h, (((i : ZMod p)⁻¹)^2) := by
  subst p
  haveI : Fact (Nat.Prime (2 * h + 1)) := ⟨hp⟩

  refine Finset.sum_bij (fun i _ => (2 * h + 1) - i) ?_ ?_ ?_ ?_
  · intro i hi
    simp [Finset.mem_Icc] at hi ⊢
    omega
  · intro a ha b hb hab
    simp [Finset.mem_Icc] at ha hb
    have hsub : 2 * h + 1 - a = 2 * h + 1 - b := hab
    omega
  · intro b hb
    refine ⟨(2 * h + 1) - b, ?_, ?_⟩
    · simp [Finset.mem_Icc] at hb ⊢
      omega
    · simp [Finset.mem_Icc] at hb
      change 2 * h + 1 - (2 * h + 1 - b) = b
      omega
  · intro i hi
    simp [Finset.mem_Icc] at hi
    have hpi : (((2 * h + 1) - i : ℕ) : ZMod (2 * h + 1)) = - (i : ZMod (2 * h + 1)) := by
      rw [Nat.cast_sub (by omega : i ≤ 2 * h + 1)]
      simp
    rw [hpi]
    have hinvneg : (- (i : ZMod (2 * h + 1)))⁻¹ = - ((i : ZMod (2 * h + 1))⁻¹) := inv_neg
    rw [hinvneg]
    ring

lemma inv_sq_sum_half_zmodp_zero (p h : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hp_eq : p = 2 * h + 1) :
    (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let f : ℕ → ZMod p := fun i => ((i : ZMod p)⁻¹)^2
  have hfull := inv_sq_sum_Icc_zmodp_zero p hp hp5
  have hfilter := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p - 1)) (fun i => i ≤ h) f
  have hleft : (Finset.Icc 1 (p - 1)).filter (fun i => i ≤ h) = Finset.Icc 1 h := by
    ext i
    simp [Finset.mem_Icc]
    omega
  have hright : (Finset.Icc 1 (p - 1)).filter (fun i => ¬ i ≤ h) = Finset.Icc (h + 1) (p - 1) := by
    ext i
    simp [Finset.mem_Icc]
    omega
  rw [hleft, hright] at hfilter
  have hupper := inv_sq_sum_upper_eq_half_zmodp p h hp hp_eq
  dsimp [f] at hfilter
  rw [hupper] at hfilter
  rw [hfull] at hfilter
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hsum : (2 : ZMod p) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2) = 0 := by
    simpa [two_mul] using hfilter
  have h2inv : (2 : ZMod p)⁻¹ * (2 : ZMod p) = 1 := inv_mul_cancel₀ htwo_ne
  calc
    (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2)
        = 1 * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2) := by rw [one_mul]
    _ = ((2 : ZMod p)⁻¹ * (2 : ZMod p)) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2) := by
      rw [h2inv]
    _ = (2 : ZMod p)⁻¹ * ((2 : ZMod p) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2)) := by ring
    _ = 0 := by rw [hsum, mul_zero]

lemma prod_Icc_one_two_mul_pair {M : Type*} [CommMonoid M] (h : ℕ) (F : ℕ → M) :
    (∏ i ∈ Finset.Icc 1 (2 * h), F i) =
      ∏ i ∈ Finset.Icc 1 h, (F i * F (2 * h + 1 - i)) := by
  classical
  have hfilter := Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (2 * h)) (fun i => i ≤ h) F
  have hleft : (Finset.Icc 1 (2 * h)).filter (fun i => i ≤ h) = Finset.Icc 1 h := by
    ext i
    simp [Finset.mem_Icc]
    omega
  have hright : (Finset.Icc 1 (2 * h)).filter (fun i => ¬ i ≤ h) = Finset.Icc (h + 1) (2 * h) := by
    ext i
    simp [Finset.mem_Icc]
    omega
  rw [hleft, hright] at hfilter
  have hupper : (∏ i ∈ Finset.Icc (h + 1) (2 * h), F i) =
      ∏ i ∈ Finset.Icc 1 h, F (2 * h + 1 - i) := by
    refine Finset.prod_bij (fun i _ => 2 * h + 1 - i) ?_ ?_ ?_ ?_
    · intro i hi
      simp [Finset.mem_Icc] at hi ⊢
      omega
    · intro a ha b hb hab
      simp [Finset.mem_Icc] at ha hb
      have hsub : 2 * h + 1 - a = 2 * h + 1 - b := hab
      omega
    · intro b hb
      refine ⟨2 * h + 1 - b, ?_, ?_⟩
      · simp [Finset.mem_Icc] at hb ⊢
        omega
      · simp [Finset.mem_Icc] at hb
        change 2 * h + 1 - (2 * h + 1 - b) = b
        omega
    · intro i hi
      simp [Finset.mem_Icc] at hi
      have harg : i = 2 * h + 1 - (2 * h + 1 - i) := by omega
      simpa using congrArg F harg
  rw [← hfilter, hupper]
  rw [Finset.prod_mul_distrib]

lemma p_sq_mul_eq_zero_of_castHom_eq_zero (p : ℕ) [NeZero p] (x : ZMod (p ^ 3))
    (h : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) x = 0) :
    (p : ZMod (p ^ 3)) ^ 2 * x = 0 := by
  rw [← ZMod.natCast_zmod_val x]
  have hx0 : ((x.val : ℕ) : ZMod p) = 0 := by
    simpa [ZMod.castHom_apply] using h
  have hdvd : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).1 hx0
  rcases hdvd with ⟨k, hk⟩
  rw [hk]
  norm_num [Nat.cast_mul, Nat.cast_pow]
  have hp3zero : (p : ZMod (p ^ 3)) ^ 3 = 0 := p_pow_self_zmod_zero p 3
  ring_nf
  rw [hp3zero]
  ring


lemma castHom_inv_sq_nat (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
        (((i : ZMod (p ^ 3))⁻¹)^2) = ((i : ZMod p)⁻¹)^2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hunit3 : IsUnit (i : ZMod (p ^ 3)) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p 3 i hp (by norm_num) hi0 hip
  have hmap_inv : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 3))⁻¹) =
      ((i : ZMod p)⁻¹) := by
    apply eq_inv_of_mul_eq_one_right
    calc
      (i : ZMod p) * ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 3))⁻¹)
          = ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)) := by simp
      _ = 1 := by rw [ZMod.mul_inv_of_unit _ hunit3]; simp
  rw [map_pow, hmap_inv]

lemma castHom_half_inv_sq_sum (p h : ℕ) (hp : p.Prime) (hp_eq : p = 2 * h + 1) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
      (∑ i ∈ Finset.Icc 1 h, ((i : ZMod (p ^ 3))⁻¹)^2) =
    ∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_Icc] at hi
  exact castHom_inv_sq_nat p i hp (by omega) (by omega)


lemma p_sq_mul_half_inv_sq_sum_zmodp3_zero (p h : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (p : ZMod (p ^ 3)) ^ 2 * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod (p ^ 3))⁻¹)^2) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply p_sq_mul_eq_zero_of_castHom_eq_zero p
  rw [castHom_half_inv_sq_sum p h hp hp_eq]
  exact inv_sq_sum_half_zmodp_zero p h hp hp5 hp_eq


lemma prod_one_add_mul_of_square_zero {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (c : R) (g : ι → R) (hc : c ^ 2 = 0) :
    (∏ i ∈ s, (1 + c * g i)) = 1 + c * (∑ i ∈ s, g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.prod_insert has, Finset.sum_insert has, ih]
    ring_nf
    rw [hc]
    ring

lemma T_super_zmod_of_odd (p h : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hp_eq : p = 2 * h + 1) :
    ((((3 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 3))) = 1 := by
  subst p
  haveI : Fact (Nat.Prime (2 * h + 1)) := ⟨hp⟩
  have hp5' : 5 ≤ 2 * h + 1 := hp5
  have hchoose := choose_prod_aux (2 * h + 1) 3 (2 * h) hp (by norm_num) (by omega : 2 * h < 2 * h + 1)
  have htop : 3 * (2 * h + 1) - 1 = 2 * (2 * h + 1) + 2 * h := by omega
  have hbot : 2 * h + 1 - 1 = 2 * h := by omega
  rw [htop, hbot]
  rw [hchoose]
  rw [prod_Icc_one_two_mul_pair h]
  trans ∏ i ∈ Finset.Icc 1 h,
      (1 - 6 * ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2)
  · apply Finset.prod_congr rfl
    intro i hi
    simp [Finset.mem_Icc] at hi
    simpa [mul_assoc] using pair_factor_eq (2 * h + 1) i hp (by omega) (by omega : i < 2 * h + 1)
  · let R := ZMod ((2 * h + 1) ^ 3)
    let c : R := ((2 * h + 1 : ℕ) : R) ^ 2
    let g : ℕ → R := fun i => -6 * ((i : R)⁻¹)^2
    have hc : c ^ 2 = 0 := by
      dsimp [c]
      have hp3zero : (((2 * h + 1 : ℕ) : R) ^ 3) = 0 := p_pow_self_zmod_zero (2 * h + 1) 3
      calc
        (((2 * h + 1 : ℕ) : R) ^ 2) ^ 2 = ((2 * h + 1 : ℕ) : R) ^ 4 := by ring
        _ = ((2 * h + 1 : ℕ) : R) ^ 3 * ((2 * h + 1 : ℕ) : R) := by ring
        _ = 0 := by rw [hp3zero, zero_mul]
    have hprod := prod_one_add_mul_of_square_zero (Finset.Icc 1 h) c g hc
    dsimp [c, g] at hprod
    have hsum0 := p_sq_mul_half_inv_sq_sum_zmodp3_zero (2 * h + 1) h hp hp5' rfl
    calc
      (∏ i ∈ Finset.Icc 1 h,
          (1 - 6 * ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
            ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2))
          = ∏ i ∈ Finset.Icc 1 h,
              (1 + ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
                (-6 * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2)) := by
              apply Finset.prod_congr rfl
              intro i hi
              ring
      _ = 1 + ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
          (∑ i ∈ Finset.Icc 1 h, -6 * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2) := hprod
      _ = 1 + ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
          (-6 * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2)) := by
              rw [← Finset.mul_sum]
      _ = 1 - 6 * (((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
              (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2)) := by ring
      _ = 1 := by rw [hsum0]; ring




lemma T_super_zmod (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((((3 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 3))) = 1 := by
  have hne2 : p ≠ 2 := by omega
  rcases hp.odd_of_ne_two hne2 with ⟨h, hp_eq⟩
  exact T_super_zmod_of_odd p h hp hp5 hp_eq

lemma T_super_int (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (((3 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3] := by
  have hz := T_super_zmod p hp hp5
  have hmod : (((3 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ (1 : ℤ) [ZMOD (p ^ 3)] := by
    exact (ZMod.intCast_eq_intCast_iff (((3 * p - 1).choose (p - 1) : ℕ) : ℤ) (1 : ℤ) (p ^ 3)).1 (by
      simpa using hz)
  simpa [Int.natCast_pow] using hmod


theorem A357674_T_supercongruence (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    (((3 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3] := by
  by_cases h3 : p = 3
  · subst p
    norm_num [Int.ModEq, Nat.choose]
  exact T_super_int p hp (A357674_prime_ge_five_of_ne_three p hp hp3 h3)






namespace A357674S2Progress

lemma isUnit_natCast_zmod_prime_pow_of_pos_lt (p r i : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hi0 : 0 < i) (hip : i < p) : IsUnit (i : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    exact not_le_of_gt hip (Nat.le_of_dvd hi0 hdiv))


lemma choose_prod_add_aux (p r m n : ℕ) (hp : p.Prime) (hr : 0 < r) (hn : n < p) :
    (((m + n).choose n : ℕ) : ZMod (p ^ r)) =
      ∏ i ∈ Finset.Icc 1 n,
        (1 + (m : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnlt : n < p := by omega
      have hsuccpos : 0 < n + 1 := by omega
      have hsucc_lt : n + 1 < p := hn
      have hunit : IsUnit ((n + 1 : ℕ) : ZMod (p ^ r)) :=
        isUnit_natCast_zmod_prime_pow_of_pos_lt p r (n + 1) hp hr hsuccpos hsucc_lt
      have hrec := ih hnlt
      have hchoose := Nat.add_one_mul_choose_eq (m + n) n
      have hcast : ((m + n + 1 : ℕ) : ZMod (p ^ r)) *
            (((m + n).choose n : ℕ) : ZMod (p ^ r)) =
          (((m + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) *
            ((n + 1 : ℕ) : ZMod (p ^ r)) := by
        simpa [Nat.cast_mul] using congrArg (fun x : ℕ => (x : ZMod (p ^ r))) hchoose
      have hstep : (((m + (n + 1)).choose (n + 1) : ℕ) : ZMod (p ^ r)) =
          (((m + n).choose n : ℕ) : ZMod (p ^ r)) *
            (((m + n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
        rw [show m + (n + 1) = m + n + 1 by omega]
        calc
          (((m + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r))
              = (((m + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) *
                  (((n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
                    rw [ZMod.mul_inv_of_unit _ hunit, mul_one]
          _ = ((((m + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))) *
                  ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by ring_nf
          _ = (((m + n + 1 : ℕ) : ZMod (p ^ r)) * (((m + n).choose n : ℕ) : ZMod (p ^ r))) *
                  ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by rw [← hcast]
          _ = (((m + n).choose n : ℕ) : ZMod (p ^ r)) *
              (((m + n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by ring_nf
      rw [hstep, hrec]
      rw [Finset.prod_Icc_succ_top hsuccpos]
      congr 1
      have hfactor : (((m + n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) =
          1 + (m : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by
        have hcasttop : ((m + n + 1 : ℕ) : ZMod (p ^ r)) =
            (m : ZMod (p ^ r)) + ((n + 1 : ℕ) : ZMod (p ^ r)) := by
          norm_num [Nat.cast_add, Nat.cast_mul]
          ring
        rw [hcasttop]
        rw [add_mul, ZMod.mul_inv_of_unit _ hunit]
        ring
      exact hfactor



def h1 (p k : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod (p ^ 5))⁻¹)


def h2 (p k : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 (k - 1), (((i : ZMod (p ^ 5))⁻¹) ^ 2)

section GeneralProduct

variable {α R : Type*} [DecidableEq α] [CommRing R]




theorem c_sq_mul_prod_one_add_sq_eq_of_pow_five_zero (s : Finset α) (c q : R) (f : α → R)
    (hc5 : c ^ 5 = 0) :
    c ^ 2 * q * (∏ i ∈ s, (1 + c * f i)) ^ 2 =
      c ^ 2 * q *
        (1 + (2 : R) * c * (∑ i ∈ s, f i) +
          c ^ 2 * ((2 : R) * (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2)) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s has ih
    rw [Finset.prod_insert has, Finset.sum_insert has, Finset.sum_insert has]
    have hc6 : c ^ 6 = 0 := by
      calc
        c ^ 6 = c ^ 5 * c := by ring
        _ = 0 := by simp [hc5]
    have hc7 : c ^ 7 = 0 := by
      calc
        c ^ 7 = c ^ 5 * c ^ 2 := by ring
        _ = 0 := by simp [hc5]
    have hc8 : c ^ 8 = 0 := by
      calc
        c ^ 8 = c ^ 5 * c ^ 3 := by ring
        _ = 0 := by simp [hc5]
    calc
      c ^ 2 * q * ((1 + c * f a) * ∏ i ∈ s, (1 + c * f i)) ^ 2
          = (1 + c * f a) ^ 2 *
              (c ^ 2 * q * (∏ i ∈ s, (1 + c * f i)) ^ 2) := by ring
      _ = (1 + c * f a) ^ 2 *
              (c ^ 2 * q *
                (1 + (2 : R) * c * (∑ i ∈ s, f i) +
                  c ^ 2 * ((2 : R) * (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2))) := by
            rw [ih]
      _ = c ^ 2 * q *
          (1 + (2 : R) * c * (f a + ∑ i ∈ s, f i) +
            c ^ 2 * ((2 : R) * (f a + ∑ i ∈ s, f i) ^ 2 -
              ((f a) ^ 2 + ∑ i ∈ s, (f i) ^ 2))) := by
            ring_nf
            simp [hc5, hc6]

end GeneralProduct




theorem lower_choose_shifted_product_zmod (p r k : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hk1 : 1 ≤ k) (hkp : k < p) :
    (((p + k - 1).choose k : ℕ) : ZMod (p ^ r)) =
      (p : ZMod (p ^ r)) * ((k : ZMod (p ^ r))⁻¹) *
        ∏ i ∈ Finset.Icc 1 (k - 1),
          (1 + (p : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹) := by
  have hkm1lt : k - 1 < p := by omega
  have hprod := choose_prod_add_aux p r p (k - 1) hp hr hkm1lt
  have htop : p + (k - 1) = p + k - 1 := by omega
  rw [htop] at hprod
  have hkpos : 0 < k := by omega
  have hkunit : IsUnit ((k : ℕ) : ZMod (p ^ r)) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p r k hp hr hkpos hkp
  have hrecNat := Nat.choose_succ_right_eq (p + k - 1) (k - 1)
  have hsucc : k - 1 + 1 = k := by omega
  have hsub : p + k - 1 - (k - 1) = p := by omega
  have hrec :
      (((p + k - 1).choose k : ℕ) : ZMod (p ^ r)) * (k : ZMod (p ^ r)) =
        (((p + k - 1).choose (k - 1) : ℕ) : ZMod (p ^ r)) * (p : ZMod (p ^ r)) := by
    have hcast := congrArg (fun x : ℕ => (x : ZMod (p ^ r))) hrecNat
    simpa [hsucc, hsub, Nat.cast_mul] using hcast
  calc
    (((p + k - 1).choose k : ℕ) : ZMod (p ^ r))
        = ((((p + k - 1).choose k : ℕ) : ZMod (p ^ r)) * (k : ZMod (p ^ r))) *
            ((k : ZMod (p ^ r))⁻¹) := by
              rw [mul_assoc, ZMod.mul_inv_of_unit _ hkunit, mul_one]
    _ = ((((p + k - 1).choose (k - 1) : ℕ) : ZMod (p ^ r)) * (p : ZMod (p ^ r))) *
            ((k : ZMod (p ^ r))⁻¹) := by rw [hrec]
    _ = (p : ZMod (p ^ r)) * ((k : ZMod (p ^ r))⁻¹) *
        ∏ i ∈ Finset.Icc 1 (k - 1),
          (1 + (p : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹) := by
          rw [hprod]
          ring






theorem lower_S2_summand_local_expansion (p k : ℕ) (hp : p.Prime)
    (hk1 : 1 ≤ k) (hkp : k < p) :
    ((((p + k - 1).choose k : ℕ) : ZMod (p ^ 5)) ^ 2) =
      (p : ZMod (p ^ 5)) ^ 2 * (((k : ZMod (p ^ 5))⁻¹) ^ 2) *
        (1 + (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * h1 p k +
          (p : ZMod (p ^ 5)) ^ 2 * ((2 : ZMod (p ^ 5)) * (h1 p k) ^ 2 - h2 p k)) := by
  classical
  let R := ZMod (p ^ 5)
  let P : R := ∏ i ∈ Finset.Icc 1 (k - 1),
          (1 + (p : R) * (i : R)⁻¹)
  have hchoose := lower_choose_shifted_product_zmod p 5 k hp (by norm_num) hk1 hkp
  change ((((p + k - 1).choose k : ℕ) : R) ^ 2) =
      (p : R) ^ 2 * (((k : R)⁻¹) ^ 2) *
        (1 + (2 : R) * (p : R) * h1 p k +
          (p : R) ^ 2 * ((2 : R) * (h1 p k) ^ 2 - h2 p k))
  change ((((p + k - 1).choose k : ℕ) : R) ^ 2) =
      (p : R) ^ 2 * (((k : R)⁻¹) ^ 2) *
        (1 + (2 : R) * (p : R) * (∑ i ∈ Finset.Icc 1 (k - 1), ((i : R)⁻¹)) +
          (p : R) ^ 2 * ((2 : R) * (∑ i ∈ Finset.Icc 1 (k - 1), ((i : R)⁻¹)) ^ 2 -
            ∑ i ∈ Finset.Icc 1 (k - 1), (((i : R)⁻¹) ^ 2)))
  have hp5zero : ((p : R) ^ 5) = 0 := by
    change ((p : ZMod (p ^ 5)) ^ 5) = 0
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (p ^ 5)
  have hexp := c_sq_mul_prod_one_add_sq_eq_of_pow_five_zero
      (α := ℕ) (R := R) (s := Finset.Icc 1 (k - 1)) (c := (p : R))
      (q := (((k : R)⁻¹) ^ 2)) (f := fun i => ((i : R)⁻¹)) hp5zero
  dsimp [P] at hexp
  rw [hchoose]
  calc
    ((p : R) * (k : R)⁻¹ * (∏ i ∈ Finset.Icc 1 (k - 1), (1 + (p : R) * (i : R)⁻¹))) ^ 2
        = (p : R) ^ 2 * (((k : R)⁻¹) ^ 2) *
            (∏ i ∈ Finset.Icc 1 (k - 1), (1 + (p : R) * (i : R)⁻¹)) ^ 2 := by ring
    _ = (p : R) ^ 2 * (((k : R)⁻¹) ^ 2) *
        (1 + (2 : R) * (p : R) * (∑ i ∈ Finset.Icc 1 (k - 1), (i : R)⁻¹) +
          (p : R) ^ 2 * ((2 : R) * (∑ i ∈ Finset.Icc 1 (k - 1), (i : R)⁻¹) ^ 2 -
            ∑ i ∈ Finset.Icc 1 (k - 1), ((i : R)⁻¹) ^ 2)) := by
          simpa [mul_assoc] using hexp

end A357674S2Progress







namespace Scratch
namespace BinomialRatioZMod


lemma isUnit_natCast_zmod_prime_pow_of_pos_lt (p r i : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hi0 : 0 < i) (hip : i < p) : IsUnit (i : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    exact not_le_of_gt hip (Nat.le_of_dvd hi0 hdiv))


lemma isUnit_three_mul_sub_natCast_zmod_prime_pow (p r n : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hn0 : 0 < n) (hnp : n < p) : IsUnit ((3 * p - n : ℕ) : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdiv
  have hp_dvd_3p : p ∣ 3 * p := dvd_mul_left p 3
  have hnle : n ≤ 3 * p := by
    have hp_pos : 0 < p := hp.pos
    omega
  have hsub : p ∣ n := by
    have := Nat.dvd_sub hp_dvd_3p hdiv
    simpa [Nat.sub_sub_self hnle] using this
  exact not_le_of_gt hnp (Nat.le_of_dvd hn0 hsub)




lemma choose_desc_step_zmod (p l : ℕ) (hp : p.Prime) (hlp : l + 1 < p) :
    (((3 * p - (l + 1) - 1).choose (p - 1) : ℕ) : ZMod (p ^ 5)) =
      (((3 * p - l - 1).choose (p - 1) : ℕ) : ZMod (p ^ 5)) *
        (((2 * p - l : ℕ) : ZMod (p ^ 5)) *
          (((3 * p - 1 - l : ℕ) : ZMod (p ^ 5))⁻¹)) := by
  classical
  let R := ZMod (p ^ 5)
  let n : ℕ := 3 * p - l - 2
  have hp_pos : 0 < p := hp.pos
  have hn_succ_den : n + 1 = 3 * p - 1 - l := by
    dsimp [n]
    omega
  have hn_succ_prev : n + 1 = 3 * p - l - 1 := by
    dsimp [n]
    omega
  have hn_left : n = 3 * p - (l + 1) - 1 := by
    dsimp [n]
    omega
  have hnum : n + 1 - (p - 1) = 2 * p - l := by
    dsimp [n]
    omega
  have hden_alt : 3 * p - 1 - l = 3 * p - (l + 1) := by omega
  have hden_unit : IsUnit (((3 * p - 1 - l : ℕ) : R)) := by
    rw [hden_alt]
    exact isUnit_three_mul_sub_natCast_zmod_prime_pow p 5 (l + 1) hp (by norm_num)
      (by omega) hlp
  have hrec := Nat.choose_mul_succ_eq n (p - 1)
  have hrecCast :
      (((n.choose (p - 1) * (n + 1) : ℕ) : R)) =
        ((((n + 1).choose (p - 1) * (n + 1 - (p - 1)) : ℕ) : R)) := by
    rw [hrec]
  have hrecR :
      (((n.choose (p - 1) : ℕ) : R) * (((n + 1 : ℕ) : R))) =
        ((((n + 1).choose (p - 1) : ℕ) : R) * (((n + 1 - (p - 1) : ℕ) : R))) := by
    simpa [Nat.cast_mul] using hrecCast
  have hstep_n :
      (((n.choose (p - 1) : ℕ) : R)) =
        ((((n + 1).choose (p - 1) : ℕ) : R) * (((n + 1 - (p - 1) : ℕ) : R))) *
          (((n + 1 : ℕ) : R)⁻¹) := by
    rw [← hrecR]
    rw [mul_assoc]
    rw [ZMod.mul_inv_of_unit _ (by simpa [hn_succ_den] using hden_unit)]
    rw [mul_one]
  rw [← hn_left, ← hn_succ_prev, ← hnum, ← hn_succ_den]
  rw [hstep_n]
  ring







theorem exact_binomial_ratio_zmod (p l : ℕ) (hp : p.Prime) (hlp : l < p) :
    (((3 * p - l - 1).choose (p - 1) : ℕ) : ZMod (p ^ 5)) =
      (((3 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 5)) *
        ∏ s ∈ Finset.range l,
          (((2 * p - s : ℕ) : ZMod (p ^ 5)) *
            (((3 * p - 1 - s : ℕ) : ZMod (p ^ 5))⁻¹)) := by
  classical
  induction l with
  | zero =>
      simp
  | succ l ih =>
      have hlp_l : l < p := by omega
      have hlp_step : l + 1 < p := by simpa [Nat.succ_eq_add_one] using hlp
      rw [choose_desc_step_zmod p l hp hlp_step]
      rw [ih hlp_l]
      rw [Finset.prod_range_succ]
      ring


end BinomialRatioZMod
end Scratch

namespace Scratch
namespace UpperRatioCoreExact




def exactCore (p l j : ℕ) : ZMod (p ^ 5) :=
  if j < l then
    (1 - (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹) *
      (1 - (3 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹)⁻¹
  else
    (1 - (3 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * (l : ZMod (p ^ 5))⁻¹)⁻¹

lemma isUnit_natCast_zmod_prime_pow_of_pos_lt (p r i : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hi0 : 0 < i) (hip : i < p) : IsUnit (i : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    exact not_le_of_gt hip (Nat.le_of_dvd hi0 hdiv))

lemma isUnit_three_mul_sub_natCast_zmod_prime_pow (p r n : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hn0 : 0 < n) (hnp : n < p) : IsUnit ((3 * p - n : ℕ) : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdiv
  have hp_dvd_3p : p ∣ 3 * p := dvd_mul_left p 3
  have hnle : n ≤ 3 * p := by
    have hp_pos : 0 < p := hp.pos
    omega
  have hsub : p ∣ n := by
    have := Nat.dvd_sub hp_dvd_3p hdiv
    simpa [Nat.sub_sub_self hnle] using this
  exact not_le_of_gt hnp (Nat.le_of_dvd hn0 hsub)

lemma cast_three_mul_sub (R : Type*) [Ring R] (p n : ℕ) (hn : n ≤ 3 * p) :
    (((3 * p - n : ℕ) : R)) = (3 : R) * (p : R) - (n : R) := by
  rw [Nat.cast_sub hn]
  norm_num [Nat.cast_mul]

lemma cast_two_mul_sub (R : Type*) [Ring R] (p n : ℕ) (hn : n ≤ 2 * p) :
    (((2 * p - n : ℕ) : R)) = (2 : R) * (p : R) - (n : R) := by
  rw [Nat.cast_sub hn]
  norm_num [Nat.cast_mul]

lemma core_of_lt (p l j : ℕ) (hp : p.Prime) (hj0 : 0 < j) (hjl : j < l) (hlp : l < p) :
    exactCore p l j =
      (((2 * p - j : ℕ) : ZMod (p ^ 5)) * (((3 * p - j : ℕ) : ZMod (p ^ 5))⁻¹)) := by
  classical
  let R := ZMod (p ^ 5)
  have hjp : j < p := by omega
  have hj_unit : IsUnit ((j : R)) := isUnit_natCast_zmod_prime_pow_of_pos_lt p 5 j hp (by norm_num) hj0 hjp
  have h3j_unit : IsUnit (((3 * p - j : ℕ) : R)) :=
    isUnit_three_mul_sub_natCast_zmod_prime_pow p 5 j hp (by norm_num) hj0 hjp
  have hjle2p : j ≤ 2 * p := by have hp_pos := hp.pos; omega
  have hjle3p : j ≤ 3 * p := by have hp_pos := hp.pos; omega
  have hj_inv_unit : IsUnit ((j : R)⁻¹) := by
    rw [isUnit_iff_exists]
    refine ⟨(j : R), ?_, ?_⟩
    · rw [mul_comm, ZMod.mul_inv_of_unit _ hj_unit]
    · rw [ZMod.mul_inv_of_unit _ hj_unit]
  have hden : (1 - (3 : R) * (p : R) * (j : R)⁻¹) =
      - (((3 * p - j : ℕ) : R) * (j : R)⁻¹) := by
    rw [cast_three_mul_sub R p j hjle3p]
    calc
      1 - (3 : R) * (p : R) * (j : R)⁻¹ =
          (j : R) * (j : R)⁻¹ - (3 : R) * (p : R) * (j : R)⁻¹ := by
            rw [ZMod.mul_inv_of_unit _ hj_unit]
      _ = -(((3 : R) * (p : R) - (j : R)) * (j : R)⁻¹) := by ring
  have hnum : (1 - (2 : R) * (p : R) * (j : R)⁻¹) =
      - (((2 * p - j : ℕ) : R) * (j : R)⁻¹) := by
    rw [cast_two_mul_sub R p j hjle2p]
    calc
      1 - (2 : R) * (p : R) * (j : R)⁻¹ =
          (j : R) * (j : R)⁻¹ - (2 : R) * (p : R) * (j : R)⁻¹ := by
            rw [ZMod.mul_inv_of_unit _ hj_unit]
      _ = -(((2 : R) * (p : R) - (j : R)) * (j : R)⁻¹) := by ring
  have hden_unit : IsUnit (1 - (3 : R) * (p : R) * (j : R)⁻¹) := by
    rw [hden]
    exact IsUnit.neg (IsUnit.mul h3j_unit hj_inv_unit)
  simp only [exactCore, hjl]
  rw [hnum, hden]
  simp only [if_true]
  -- clear the denominator by multiplying on the right by the unit denominator.
  apply (hden_unit.mul_left_inj).mp
  rw [hden]
  rw [mul_assoc]
  rw [show (-(((3 * p - j : ℕ) : R) * (j : R)⁻¹))⁻¹ *
        (-(((3 * p - j : ℕ) : R) * (j : R)⁻¹)) = 1 by
          rw [← hden]
          rw [mul_comm, ZMod.mul_inv_of_unit _ hden_unit]]
  rw [mul_one]
  rw [show ((((2 * p - j : ℕ) : R) * (((3 * p - j : ℕ) : R)⁻¹)) *
        (-(((3 * p - j : ℕ) : R) * (j : R)⁻¹))) =
        -(((2 * p - j : ℕ) : R) * ((((3 * p - j : ℕ) : R)⁻¹ * (((3 * p - j : ℕ) : R))) * (j : R)⁻¹)) by ring]
  rw [show (((3 * p - j : ℕ) : R)⁻¹ * ((3 * p - j : ℕ) : R) * (j : R)⁻¹) = (j : R)⁻¹ by
    rw [show (((3 * p - j : ℕ) : R)⁻¹ * ((3 * p - j : ℕ) : R)) = 1 by
      rw [mul_comm, ZMod.mul_inv_of_unit _ h3j_unit]]
    rw [one_mul]]

lemma endpoint_scalar (p l : ℕ) (hp : p.Prime) (hl0 : 0 < l) (hlp : l < p) :
    (- (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * (l : ZMod (p ^ 5))⁻¹) *
      (1 - (3 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * (l : ZMod (p ^ 5))⁻¹)⁻¹ =
        (((2 * p : ℕ) : ZMod (p ^ 5)) * (((3 * p - l : ℕ) : ZMod (p ^ 5))⁻¹)) := by
  classical
  let R := ZMod (p ^ 5)
  have hl_unit : IsUnit ((l : R)) := isUnit_natCast_zmod_prime_pow_of_pos_lt p 5 l hp (by norm_num) hl0 hlp
  have h3l_unit : IsUnit (((3 * p - l : ℕ) : R)) :=
    isUnit_three_mul_sub_natCast_zmod_prime_pow p 5 l hp (by norm_num) hl0 hlp
  have hlle3p : l ≤ 3 * p := by have hp_pos := hp.pos; omega
  have hl_inv_unit : IsUnit ((l : R)⁻¹) := by
    rw [isUnit_iff_exists]
    refine ⟨(l : R), ?_, ?_⟩
    · rw [mul_comm, ZMod.mul_inv_of_unit _ hl_unit]
    · rw [ZMod.mul_inv_of_unit _ hl_unit]
  have hden : (1 - (3 : R) * (p : R) * (l : R)⁻¹) =
      - (((3 * p - l : ℕ) : R) * (l : R)⁻¹) := by
    rw [cast_three_mul_sub R p l hlle3p]
    calc
      1 - (3 : R) * (p : R) * (l : R)⁻¹ =
          (l : R) * (l : R)⁻¹ - (3 : R) * (p : R) * (l : R)⁻¹ := by
            rw [ZMod.mul_inv_of_unit _ hl_unit]
      _ = -(((3 : R) * (p : R) - (l : R)) * (l : R)⁻¹) := by ring
  have hden_unit : IsUnit (1 - (3 : R) * (p : R) * (l : R)⁻¹) := by
    rw [hden]
    exact IsUnit.neg (IsUnit.mul h3l_unit hl_inv_unit)
  apply (hden_unit.mul_left_inj).mp
  rw [hden]
  rw [mul_assoc]
  rw [show (-(((3 * p - l : ℕ) : R) * (l : R)⁻¹))⁻¹ *
        (-(((3 * p - l : ℕ) : R) * (l : R)⁻¹)) = 1 by
          rw [← hden]
          rw [mul_comm, ZMod.mul_inv_of_unit _ hden_unit]]
  rw [mul_one]
  norm_num [Nat.cast_mul]
  have hmul_endpoint : (((2 : R) * (p : R) * (((3 * p - l : ℕ) : R)⁻¹)) *
      (-(((3 * p - l : ℕ) : R) * (l : R)⁻¹))) =
      - (((2 : R) * (p : R)) * ((((3 * p - l : ℕ) : R)⁻¹ * (((3 * p - l : ℕ) : R)) * (l : R)⁻¹))) := by
    ring
  rw [hmul_endpoint]
  rw [show (((3 * p - l : ℕ) : R)⁻¹ * ((3 * p - l : ℕ) : R) * (l : R)⁻¹) = (l : R)⁻¹ by
    rw [show (((3 * p - l : ℕ) : R)⁻¹ * ((3 * p - l : ℕ) : R)) = 1 by
      rw [mul_comm, ZMod.mul_inv_of_unit _ h3l_unit]]
    rw [one_mul]]




theorem upperRatioCore_exact (p l : ℕ) (hp : p.Prime) (hl1 : 1 ≤ l) (hlp : l < p) :
    (∏ s ∈ Finset.range l,
      (((2 * p - s : ℕ) : ZMod (p ^ 5)) * (((3 * p - 1 - s : ℕ) : ZMod (p ^ 5))⁻¹))) =
      (- (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * (l : ZMod (p ^ 5))⁻¹) *
        ∏ j ∈ Finset.Icc 1 l, exactCore p l j := by
  classical
  let R := ZMod (p ^ 5)
  -- Reindex the left-hand denominator by `j = s + 1` and the nonzero numerators by `j = s`.
  have hl0 : 0 < l := hl1
  have hL : (∏ s ∈ Finset.range l,
      (((2 * p - s : ℕ) : R) * (((3 * p - 1 - s : ℕ) : R)⁻¹))) =
      (((2 * p : ℕ) : R) * (((3 * p - l : ℕ) : R)⁻¹)) *
        ∏ j ∈ Finset.Icc 1 (l - 1),
          (((2 * p - j : ℕ) : R) * (((3 * p - j : ℕ) : R)⁻¹)) := by
    induction l with
    | zero => omega
    | succ n ih =>
        by_cases hn0 : n = 0
        · subst n
          simp
        · have hnpos : 0 < n := by
            cases n with
            | zero => contradiction
            | succ n => exact Nat.succ_pos n
          have hsimp : n + 1 - 1 = n := Nat.succ_sub_one n
          rw [Finset.prod_range_succ]
          simp only [hsimp]
          rw [ih (by omega) (by omega) hnpos]
          have hden_top : (3 * p - 1 - n) = (3 * p - (n + 1)) := by omega
          rw [hden_top]
          have hprod_n : (∏ j ∈ Finset.Icc 1 n,
              (((2 * p - j : ℕ) : R) * (((3 * p - j : ℕ) : R)⁻¹))) =
              (∏ j ∈ Finset.Icc 1 (n - 1),
                (((2 * p - j : ℕ) : R) * (((3 * p - j : ℕ) : R)⁻¹))) *
                (((2 * p - n : ℕ) : R) * (((3 * p - n : ℕ) : R)⁻¹)) := by
            have hn_pred : n - 1 + 1 = n := Nat.sub_add_cancel (show 1 ≤ n by omega)
            conv_lhs => rw [← hn_pred]
            rw [Finset.prod_Icc_succ_top (show 1 ≤ n - 1 + 1 by omega)]
            simp [hn_pred]
          rw [hprod_n]
          ring
  have hRprod : (∏ j ∈ Finset.Icc 1 l, exactCore p l j) =
      (∏ j ∈ Finset.Icc 1 (l - 1),
          (((2 * p - j : ℕ) : R) * (((3 * p - j : ℕ) : R)⁻¹))) *
        (1 - (3 : R) * (p : R) * (l : R)⁻¹)⁻¹ := by
    have hl_pred : l - 1 + 1 = l := Nat.sub_add_cancel hl1
    conv_lhs => rw [← hl_pred]
    rw [Finset.prod_Icc_succ_top (show 1 ≤ l - 1 + 1 by omega)]
    simp [hl_pred]
    congr 1
    · apply Finset.prod_congr rfl
      intro j hj
      have hj0 : 0 < j := by simp [Finset.mem_Icc] at hj; omega
      have hjl : j < l := by simp [Finset.mem_Icc] at hj; omega
      exact core_of_lt p l j hp hj0 hjl hlp
    · simp [exactCore]
  rw [hL, hRprod]
  rw [show (- (2 : R) * (p : R) * (l : R)⁻¹) *
      ((∏ j ∈ Finset.Icc 1 (l - 1), (((2 * p - j : ℕ) : R) * (((3 * p - j : ℕ) : R)⁻¹))) *
        (1 - (3 : R) * (p : R) * (l : R)⁻¹)⁻¹) =
      ((- (2 : R) * (p : R) * (l : R)⁻¹) *
        (1 - (3 : R) * (p : R) * (l : R)⁻¹)⁻¹) *
        (∏ j ∈ Finset.Icc 1 (l - 1), (((2 * p - j : ℕ) : R) * (((3 * p - j : ℕ) : R)⁻¹))) by ring]
  rw [endpoint_scalar p l hp hl0 hlp]

end UpperRatioCoreExact
end Scratch

namespace Scratch
namespace ExactCoreToTruncated



def exactCore (p l j : ℕ) : ZMod (p ^ 5) :=
  if j < l then
    (1 - (2 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹) *
      (1 - (3 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * (j : ZMod (p ^ 5))⁻¹)⁻¹
  else
    (1 - (3 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) * (l : ZMod (p ^ 5))⁻¹)⁻¹



def upperF (p l j : ℕ) : ZMod (p ^ 5) :=
  if j < l then ((j : ZMod (p ^ 5))⁻¹) else (3 : ZMod (p ^ 5)) * ((l : ZMod (p ^ 5))⁻¹)



def upperG (p l j : ℕ) : ZMod (p ^ 5) :=
  if j < l then (3 : ZMod (p ^ 5)) * (((j : ZMod (p ^ 5))⁻¹) ^ 2)
  else (9 : ZMod (p ^ 5)) * (((l : ZMod (p ^ 5))⁻¹) ^ 2)

lemma isUnit_natCast_zmod_prime_pow_of_pos_lt (p r i : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hi0 : 0 < i) (hip : i < p) : IsUnit (i : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    exact not_le_of_gt hip (Nat.le_of_dvd hi0 hdiv))

lemma isUnit_three_mul_sub_natCast_zmod_prime_pow (p r n : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hn0 : 0 < n) (hnp : n < p) : IsUnit ((3 * p - n : ℕ) : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdiv
  have hp_dvd_3p : p ∣ 3 * p := dvd_mul_left p 3
  have hnle : n ≤ 3 * p := by
    have hp_pos : 0 < p := hp.pos
    omega
  have hsub : p ∣ n := by
    have := Nat.dvd_sub hp_dvd_3p hdiv
    simpa [Nat.sub_sub_self hnle] using this
  exact not_le_of_gt hnp (Nat.le_of_dvd hn0 hsub)

lemma cast_three_mul_sub (R : Type*) [Ring R] (p n : ℕ) (hn : n ≤ 3 * p) :
    (((3 * p - n : ℕ) : R)) = (3 : R) * (p : R) - (n : R) := by
  rw [Nat.cast_sub hn]
  norm_num [Nat.cast_mul]

lemma zmod_p_cast_pow_five_eq_zero (p : ℕ) :
    let R := ZMod (p ^ 5); ((p : R) ^ 5) = 0 := by
  intro R
  change ((p : ZMod (p ^ 5)) ^ 5) = 0
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self (p ^ 5)

lemma upper_den_unit (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    let R := ZMod (p ^ 5)
    IsUnit (1 - (3 : R) * (p : R) * (i : R)⁻¹) := by
  intro R
  have hi_unit : IsUnit ((i : R)) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p 5 i hp (by norm_num) hi0 hip
  have h3i_unit : IsUnit (((3 * p - i : ℕ) : R)) :=
    isUnit_three_mul_sub_natCast_zmod_prime_pow p 5 i hp (by norm_num) hi0 hip
  have hile3p : i ≤ 3 * p := by
    have hp_pos := hp.pos
    omega
  have hi_inv_unit : IsUnit ((i : R)⁻¹) := by
    rw [isUnit_iff_exists]
    refine ⟨(i : R), ?_, ?_⟩
    · rw [mul_comm, ZMod.mul_inv_of_unit _ hi_unit]
    · rw [ZMod.mul_inv_of_unit _ hi_unit]
  have hden : (1 - (3 : R) * (p : R) * (i : R)⁻¹) =
      - (((3 * p - i : ℕ) : R) * (i : R)⁻¹) := by
    rw [cast_three_mul_sub R p i hile3p]
    calc
      1 - (3 : R) * (p : R) * (i : R)⁻¹ =
          (i : R) * (i : R)⁻¹ - (3 : R) * (p : R) * (i : R)⁻¹ := by
            rw [ZMod.mul_inv_of_unit _ hi_unit]
      _ = -(((3 : R) * (p : R) - (i : R)) * (i : R)⁻¹) := by ring
  rw [hden]
  exact IsUnit.neg (IsUnit.mul h3i_unit hi_inv_unit)

section GeneralProduct

variable {α R : Type*} [DecidableEq α] [CommRing R]



lemma left_mul_prod_sub_prod_eq_zero_of_factor_sub
    (s : Finset α) (d : R) (e t : α → R)
    (h : ∀ i ∈ s, d * (e i - t i) = 0) :
    d * ((∏ i ∈ s, e i) - (∏ i ∈ s, t i)) = 0 := by
  classical
  revert h
  refine Finset.induction_on s ?base ?step
  · intro h; simp
  · intro a s has ih h
    rw [Finset.prod_insert has, Finset.prod_insert has]
    have ha : d * (e a - t a) = 0 := h a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, d * (e i - t i) = 0 := by
      intro i hi
      exact h i (Finset.mem_insert_of_mem hi)
    have ihs := ih hs
    calc
      d * (e a * (∏ i ∈ s, e i) - t a * (∏ i ∈ s, t i))
          = (d * (e a - t a)) * (∏ i ∈ s, e i) +
              t a * (d * ((∏ i ∈ s, e i) - (∏ i ∈ s, t i))) := by ring
      _ = 0 := by simp [ha, ihs]



lemma prod_square_replace_of_factor_sub
    (s : Finset α) (d q : R) (e t : α → R)
    (h : ∀ i ∈ s, d * (e i - t i) = 0) :
    d * q * (∏ i ∈ s, e i) ^ 2 = d * q * (∏ i ∈ s, t i) ^ 2 := by
  classical
  have hprod := left_mul_prod_sub_prod_eq_zero_of_factor_sub (s := s) (d := d) (e := e) (t := t) h
  apply sub_eq_zero.mp
  calc
    d * q * (∏ i ∈ s, e i) ^ 2 - d * q * (∏ i ∈ s, t i) ^ 2
        = d * q * ((∏ i ∈ s, e i) ^ 2 - (∏ i ∈ s, t i) ^ 2) := by ring
    _ = q * (d * ((∏ i ∈ s, e i) - (∏ i ∈ s, t i))) *
          ((∏ i ∈ s, e i) + (∏ i ∈ s, t i)) := by ring
    _ = 0 := by simp [hprod]

end GeneralProduct

section InverseTruncation

variable {R : Type*} [CommRing R] [Inv R]




lemma inv_one_sub_trunc_killed (d a : R)
    (hmul : (1 - a) * (1 - a)⁻¹ = 1)
    (hcancel : ∀ z : R, (1 - a) * z = 0 → z = 0)
    (hd : d * a ^ 3 = 0) :
    d * ((1 - a)⁻¹ - (1 + a + a ^ 2)) = 0 := by
  apply hcancel
  calc
    (1 - a) * (d * ((1 - a)⁻¹ - (1 + a + a ^ 2)))
        = d * ((1 - a) * (1 - a)⁻¹ - (1 - a) * (1 + a + a ^ 2)) := by ring
    _ = d * (1 - (1 - a) * (1 + a + a ^ 2)) := by rw [hmul]
    _ = d * a ^ 3 := by ring
    _ = 0 := hd

end InverseTruncation



lemma exactCore_sub_truncated_killed (p l j : ℕ) (hp : p.Prime) (hlp : l < p)
    (hj : j ∈ Finset.Icc 1 l) :
    let R := ZMod (p ^ 5)
    (p : R) ^ 2 *
      (exactCore p l j -
        (1 + (p : R) * upperF p l j + (p : R) ^ 2 * upperG p l j)) = 0 := by
  classical
  intro R
  have hp5zero : ((p : R) ^ 5) = 0 := zmod_p_cast_pow_five_eq_zero p
  by_cases hlt : j < l
  · have hj0 : 0 < j := by
      simp [Finset.mem_Icc] at hj
      omega
    have hjp : j < p := by omega
    let x : R := (j : R)⁻¹
    let c : R := (p : R)
    have hunit : IsUnit (1 - (3 : R) * (p : R) * (j : R)⁻¹) :=
      upper_den_unit p j hp hj0 hjp
    have hmul : (1 - (3 : R) * (p : R) * (j : R)⁻¹) *
        (1 - (3 : R) * (p : R) * (j : R)⁻¹)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hunit
    have hcancel : ∀ z : R,
        (1 - (3 : R) * (p : R) * (j : R)⁻¹) * z = 0 → z = 0 := by
      intro z hz
      apply (hunit.mul_right_inj).mp
      simpa using hz
    have hd : (p : R) ^ 2 * ((3 : R) * (p : R) * (j : R)⁻¹) ^ 3 = 0 := by
      calc
        (p : R) ^ 2 * ((3 : R) * (p : R) * (j : R)⁻¹) ^ 3 =
            (27 : R) * (p : R) ^ 5 * ((j : R)⁻¹) ^ 3 := by ring
        _ = 0 := by simp [hp5zero]
    have hinv : (p : R) ^ 2 *
        ((1 - (3 : R) * (p : R) * (j : R)⁻¹)⁻¹ -
          (1 + (3 : R) * (p : R) * (j : R)⁻¹ +
            ((3 : R) * (p : R) * (j : R)⁻¹) ^ 2)) = 0 :=
      inv_one_sub_trunc_killed ((p : R) ^ 2)
        ((3 : R) * (p : R) * (j : R)⁻¹) hmul hcancel hd
    simp only [exactCore, upperF, upperG, hlt, if_true]
    calc
      (p : R) ^ 2 *
          ((1 - (2 : R) * (p : R) * (j : R)⁻¹) *
              (1 - (3 : R) * (p : R) * (j : R)⁻¹)⁻¹ -
            (1 + (p : R) * (j : R)⁻¹ +
              (p : R) ^ 2 * ((3 : R) * ((j : R)⁻¹) ^ 2)))
          = (1 - (2 : R) * (p : R) * (j : R)⁻¹) *
              ((p : R) ^ 2 *
                ((1 - (3 : R) * (p : R) * (j : R)⁻¹)⁻¹ -
                  (1 + (3 : R) * (p : R) * (j : R)⁻¹ +
                    ((3 : R) * (p : R) * (j : R)⁻¹) ^ 2))) -
              (18 : R) * (p : R) ^ 5 * ((j : R)⁻¹) ^ 3 := by ring
      _ = 0 := by simp [hinv, hp5zero]
  · have hl0 : 0 < l := by
      simp [Finset.mem_Icc] at hj
      omega
    let x : R := (l : R)⁻¹
    let c : R := (p : R)
    have hunit : IsUnit (1 - (3 : R) * (p : R) * (l : R)⁻¹) :=
      upper_den_unit p l hp hl0 hlp
    have hmul : (1 - (3 : R) * (p : R) * (l : R)⁻¹) *
        (1 - (3 : R) * (p : R) * (l : R)⁻¹)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hunit
    have hcancel : ∀ z : R,
        (1 - (3 : R) * (p : R) * (l : R)⁻¹) * z = 0 → z = 0 := by
      intro z hz
      apply (hunit.mul_right_inj).mp
      simpa using hz
    have hd : (p : R) ^ 2 * ((3 : R) * (p : R) * (l : R)⁻¹) ^ 3 = 0 := by
      calc
        (p : R) ^ 2 * ((3 : R) * (p : R) * (l : R)⁻¹) ^ 3 =
            (27 : R) * (p : R) ^ 5 * ((l : R)⁻¹) ^ 3 := by ring
        _ = 0 := by simp [hp5zero]
    have hinv : (p : R) ^ 2 *
        ((1 - (3 : R) * (p : R) * (l : R)⁻¹)⁻¹ -
          (1 + (3 : R) * (p : R) * (l : R)⁻¹ +
            ((3 : R) * (p : R) * (l : R)⁻¹) ^ 2)) = 0 :=
      inv_one_sub_trunc_killed ((p : R) ^ 2)
        ((3 : R) * (p : R) * (l : R)⁻¹) hmul hcancel hd
    simp only [exactCore, upperF, upperG, hlt, if_false]
    calc
      (p : R) ^ 2 *
          ((1 - (3 : R) * (p : R) * (l : R)⁻¹)⁻¹ -
            (1 + (p : R) * ((3 : R) * (l : R)⁻¹) +
              (p : R) ^ 2 * ((9 : R) * ((l : R)⁻¹) ^ 2)))
          = (p : R) ^ 2 *
              ((1 - (3 : R) * (p : R) * (l : R)⁻¹)⁻¹ -
                (1 + (3 : R) * (p : R) * (l : R)⁻¹ +
                  ((3 : R) * (p : R) * (l : R)⁻¹) ^ 2)) := by ring
      _ = 0 := hinv




theorem exactCore_product_square_eq_truncated (p l : ℕ) (hp : p.Prime)
    (hl1 : 1 ≤ l) (hlp : l < p) :
    let R := ZMod (p ^ 5)
    (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) *
        (∏ j ∈ Finset.Icc 1 l, exactCore p l j) ^ 2 =
      (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) *
        (∏ j ∈ Finset.Icc 1 l,
          (1 + (p : R) * upperF p l j + (p : R) ^ 2 * upperG p l j)) ^ 2 := by
  classical
  intro R
  have _hl0_from_hl1 : 0 < l := hl1

  let d : R := (p : R) ^ 2
  let q : R := (4 : R) * (((l : R)⁻¹) ^ 2)
  have hfac : ∀ j ∈ Finset.Icc 1 l,
      d * (exactCore p l j -
        (1 + (p : R) * upperF p l j + (p : R) ^ 2 * upperG p l j)) = 0 := by
    intro j hj
    dsimp [d]
    exact exactCore_sub_truncated_killed p l j hp hlp hj
  have hreplace := prod_square_replace_of_factor_sub
    (s := Finset.Icc 1 l) (d := d) (q := q)
    (e := exactCore p l)
    (t := fun j => (1 + (p : R) * upperF p l j + (p : R) ^ 2 * upperG p l j)) hfac
  calc
    (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) *
        (∏ j ∈ Finset.Icc 1 l, exactCore p l j) ^ 2
        = d * q * (∏ j ∈ Finset.Icc 1 l, exactCore p l j) ^ 2 := by
          dsimp [d, q]
          ring
    _ = d * q *
        (∏ j ∈ Finset.Icc 1 l,
          (1 + (p : R) * upperF p l j + (p : R) ^ 2 * upperG p l j)) ^ 2 := hreplace
    _ = (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) *
        (∏ j ∈ Finset.Icc 1 l,
          (1 + (p : R) * upperF p l j + (p : R) ^ 2 * upperG p l j)) ^ 2 := by
          dsimp [d, q]
          ring

end ExactCoreToTruncated
end Scratch

namespace A357674UpperRatioToT


def h1 (p l : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 (l - 1), ((i : ZMod (p ^ 5))⁻¹)


def h2 (p l : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 (l - 1), (((i : ZMod (p ^ 5))⁻¹) ^ 2)


def upperLocalExpansion (p l : ℕ) : ZMod (p ^ 5) :=
  let R := ZMod (p ^ 5)
  (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) *
    (1 + (2 : R) * (p : R) * h1 p l + (6 : R) * (p : R) * ((l : R)⁻¹) +
      (p : R) ^ 2 * ((2 : R) * (h1 p l) ^ 2 + (12 : R) * h1 p l * ((l : R)⁻¹) +
        (27 : R) * (((l : R)⁻¹) ^ 2) + (5 : R) * h2 p l))

section GeneralProduct

variable {α R : Type*} [DecidableEq α] [CommRing R]




theorem c_sq_mul_prod_one_add_linear_quad_sq_eq_of_pow_five_zero
    (s : Finset α) (c q : R) (f g : α → R) (hc5 : c ^ 5 = 0) :
    c ^ 2 * q * (∏ i ∈ s, (1 + c * f i + c ^ 2 * g i)) ^ 2 =
      c ^ 2 * q *
        (1 + (2 : R) * c * (∑ i ∈ s, f i) +
          c ^ 2 * ((2 : R) * (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2 +
            (2 : R) * (∑ i ∈ s, g i))) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s has ih
    rw [Finset.prod_insert has, Finset.sum_insert has, Finset.sum_insert has,
      Finset.sum_insert has]
    have hc6 : c ^ 6 = 0 := by
      calc
        c ^ 6 = c ^ 5 * c := by ring
        _ = 0 := by simp [hc5]
    have hc7 : c ^ 7 = 0 := by
      calc
        c ^ 7 = c ^ 5 * c ^ 2 := by ring
        _ = 0 := by simp [hc5]
    have hc8 : c ^ 8 = 0 := by
      calc
        c ^ 8 = c ^ 5 * c ^ 3 := by ring
        _ = 0 := by simp [hc5]
    calc
      c ^ 2 * q * ((1 + c * f a + c ^ 2 * g a) *
          ∏ i ∈ s, (1 + c * f i + c ^ 2 * g i)) ^ 2
          = (1 + c * f a + c ^ 2 * g a) ^ 2 *
              (c ^ 2 * q * (∏ i ∈ s, (1 + c * f i + c ^ 2 * g i)) ^ 2) := by ring
      _ = (1 + c * f a + c ^ 2 * g a) ^ 2 *
              (c ^ 2 * q *
                (1 + (2 : R) * c * (∑ i ∈ s, f i) +
                  c ^ 2 * ((2 : R) * (∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2 +
                    (2 : R) * (∑ i ∈ s, g i)))) := by rw [ih]
      _ = c ^ 2 * q *
          (1 + (2 : R) * c * (f a + ∑ i ∈ s, f i) +
            c ^ 2 * ((2 : R) * (f a + ∑ i ∈ s, f i) ^ 2 -
              ((f a) ^ 2 + ∑ i ∈ s, (f i) ^ 2) +
              (2 : R) * (g a + ∑ i ∈ s, g i))) := by
            ring_nf
            simp [hc5, hc6, hc7, hc8]





theorem square_drop_T_of_sq_sub_one_mul_c_sq_zero (c T a : R)
    (hT : (T ^ 2 - 1) * c ^ 2 = 0) :
    ((c * a) * T) ^ 2 = (c * a) ^ 2 := by
  have hz : c ^ 2 * (T ^ 2 - 1) = 0 := by
    calc
      c ^ 2 * (T ^ 2 - 1) = (T ^ 2 - 1) * c ^ 2 := by ring
      _ = 0 := hT
  calc
    ((c * a) * T) ^ 2 = c ^ 2 * a ^ 2 * T ^ 2 := by ring
    _ = c ^ 2 * a ^ 2 * (1 + (T ^ 2 - 1)) := by ring
    _ = c ^ 2 * a ^ 2 := by
      rw [show c ^ 2 * a ^ 2 * (1 + (T ^ 2 - 1)) =
          c ^ 2 * a ^ 2 + a ^ 2 * (c ^ 2 * (T ^ 2 - 1)) by ring]
      simp [hz]
    _ = (c * a) ^ 2 := by ring

end GeneralProduct

section UpperCore




def upperF (p l j : ℕ) : ZMod (p ^ 5) :=

  if j < l then ((j : ZMod (p ^ 5))⁻¹) else (3 : ZMod (p ^ 5)) * ((l : ZMod (p ^ 5))⁻¹)


def upperG (p l j : ℕ) : ZMod (p ^ 5) :=
  if j < l then (3 : ZMod (p ^ 5)) * (((j : ZMod (p ^ 5))⁻¹) ^ 2)
  else (9 : ZMod (p ^ 5)) * (((l : ZMod (p ^ 5))⁻¹) ^ 2)

lemma Icc_one_l_eq_insert_Icc_one_pred (l : ℕ) (hl1 : 1 ≤ l) :
    Finset.Icc 1 l = insert l (Finset.Icc 1 (l - 1)) := by
  ext j
  simp [Finset.mem_Icc]
  omega

lemma upperF_sum (p l : ℕ) (hl1 : 1 ≤ l) :
    (∑ j ∈ Finset.Icc 1 l, upperF p l j) = h1 p l + (3 : ZMod (p ^ 5)) * ((l : ZMod (p ^ 5))⁻¹) := by
  classical
  let R := ZMod (p ^ 5)
  rw [Icc_one_l_eq_insert_Icc_one_pred l hl1]
  have hnot : l ∉ Finset.Icc 1 (l - 1) := by
    simp [Finset.mem_Icc]
    omega
  rw [Finset.sum_insert hnot]
  have hsum : (∑ x ∈ Finset.Icc 1 (l - 1), upperF p l x) =
      ∑ x ∈ Finset.Icc 1 (l - 1), ((x : R)⁻¹) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxl : x < l := by
      simp [Finset.mem_Icc] at hx
      omega
    simp [upperF, hxl]
  rw [hsum]
  have hlf : upperF p l l = (3 : R) * ((l : R)⁻¹) := by simp [upperF]
  rw [hlf]
  simp [h1, add_comm]

lemma upperG_sum (p l : ℕ) (hl1 : 1 ≤ l) :
    (∑ j ∈ Finset.Icc 1 l, upperG p l j) =
      (3 : ZMod (p ^ 5)) * h2 p l + (9 : ZMod (p ^ 5)) * (((l : ZMod (p ^ 5))⁻¹) ^ 2) := by
  classical
  let R := ZMod (p ^ 5)
  rw [Icc_one_l_eq_insert_Icc_one_pred l hl1]
  have hnot : l ∉ Finset.Icc 1 (l - 1) := by
    simp [Finset.mem_Icc]
    omega
  rw [Finset.sum_insert hnot]
  have hsum : (∑ x ∈ Finset.Icc 1 (l - 1), upperG p l x) =
      ∑ x ∈ Finset.Icc 1 (l - 1), (3 : R) * (((x : R)⁻¹) ^ 2) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxl : x < l := by
      simp [Finset.mem_Icc] at hx
      omega
    simp [upperG, hxl]
  rw [hsum]
  have hlg : upperG p l l = (9 : R) * (((l : R)⁻¹) ^ 2) := by simp [upperG]
  rw [hlg]
  simp [h2, Finset.mul_sum, add_comm]

lemma upperF_sq_sum (p l : ℕ) (hl1 : 1 ≤ l) :
    (∑ j ∈ Finset.Icc 1 l, (upperF p l j) ^ 2) =
      h2 p l + (9 : ZMod (p ^ 5)) * (((l : ZMod (p ^ 5))⁻¹) ^ 2) := by
  classical
  let R := ZMod (p ^ 5)
  rw [Icc_one_l_eq_insert_Icc_one_pred l hl1]
  have hnot : l ∉ Finset.Icc 1 (l - 1) := by
    simp [Finset.mem_Icc]
    omega
  rw [Finset.sum_insert hnot]
  have hsum : (∑ x ∈ Finset.Icc 1 (l - 1), (upperF p l x) ^ 2) =
      ∑ x ∈ Finset.Icc 1 (l - 1), (((x : R)⁻¹) ^ 2) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxl : x < l := by
      simp [Finset.mem_Icc] at hx
      omega
    simp [upperF, hxl]
  rw [hsum]
  have hlf : (upperF p l l) ^ 2 = (9 : R) * (((l : R)⁻¹) ^ 2) := by
    simp [upperF]
    ring
  rw [hlf]
  simp [h2, add_comm]










theorem upper_ratio_truncated_core_sq_expansion (p l : ℕ) (hl1 : 1 ≤ l) :
    let R := ZMod (p ^ 5)
    (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) *
        (∏ j ∈ Finset.Icc 1 l,
          (1 + (p : R) * upperF p l j + (p : R) ^ 2 * upperG p l j)) ^ 2 =
      upperLocalExpansion p l := by
  classical
  let R := ZMod (p ^ 5)
  change (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) *
        (∏ j ∈ Finset.Icc 1 l,
          (1 + (p : R) * upperF p l j + (p : R) ^ 2 * upperG p l j)) ^ 2 =
      upperLocalExpansion p l
  have hp5zero : ((p : R) ^ 5) = 0 := by
    change ((p : ZMod (p ^ 5)) ^ 5) = 0
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (p ^ 5)
  have hexp := c_sq_mul_prod_one_add_linear_quad_sq_eq_of_pow_five_zero
      (α := ℕ) (R := R) (s := Finset.Icc 1 l) (c := (p : R))
      (q := (4 : R) * (((l : R)⁻¹) ^ 2))
      (f := upperF p l) (g := upperG p l) hp5zero
  rw [upperF_sum p l hl1, upperG_sum p l hl1, upperF_sq_sum p l hl1] at hexp
  rw [upperLocalExpansion]
  calc
    (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) *
        (∏ j ∈ Finset.Icc 1 l,
          (1 + (p : R) * upperF p l j + (p : R) ^ 2 * upperG p l j)) ^ 2
        = (p : R) ^ 2 * ((4 : R) * (((l : R)⁻¹) ^ 2)) *
        (∏ j ∈ Finset.Icc 1 l,
          (1 + (p : R) * upperF p l j + (p : R) ^ 2 * upperG p l j)) ^ 2 := by ring
    _ = (p : R) ^ 2 * ((4 : R) * (((l : R)⁻¹) ^ 2)) *
        (1 + (2 : R) * (p : R) * (h1 p l + (3 : R) * (l : R)⁻¹) +
          (p : R) ^ 2 *
            ((2 : R) * (h1 p l + (3 : R) * (l : R)⁻¹) ^ 2 -
              (h2 p l + (9 : R) * ((l : R)⁻¹) ^ 2) +
              (2 : R) * ((3 : R) * h2 p l + (9 : R) * ((l : R)⁻¹) ^ 2))) := by
          simpa [mul_assoc] using hexp
    _ = (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) *
        (1 + (2 : R) * (p : R) * h1 p l + (6 : R) * (p : R) * ((l : R)⁻¹) +
          (p : R) ^ 2 * ((2 : R) * (h1 p l) ^ 2 +
            (12 : R) * h1 p l * ((l : R)⁻¹) +
            (27 : R) * (((l : R)⁻¹) ^ 2) + (5 : R) * h2 p l)) := by ring



end UpperCore

end A357674UpperRatioToT

namespace Scratch
namespace UpperLocalExpansionFull


abbrev upperLocalExpansion (p l : ℕ) : ZMod (p ^ 5) :=
  A357674UpperRatioToT.upperLocalExpansion p l


lemma upper_exactCore_eq_trunc_exactCore (p l j : ℕ) :
    UpperRatioCoreExact.exactCore p l j = ExactCoreToTruncated.exactCore p l j := by
  by_cases h : j < l <;> simp [UpperRatioCoreExact.exactCore, ExactCoreToTruncated.exactCore, h]


lemma trunc_upperF_eq_expansion_upperF (p l j : ℕ) :
    ExactCoreToTruncated.upperF p l j = A357674UpperRatioToT.upperF p l j := by
  by_cases h : j < l <;> simp [ExactCoreToTruncated.upperF, A357674UpperRatioToT.upperF, h]


lemma trunc_upperG_eq_expansion_upperG (p l j : ℕ) :
    ExactCoreToTruncated.upperG p l j = A357674UpperRatioToT.upperG p l j := by
  by_cases h : j < l <;> simp [ExactCoreToTruncated.upperG, A357674UpperRatioToT.upperG, h]



lemma anchor_sq_sub_one_mul_p_sq_eq_zero (p : ℕ)
    (hT : ((((3 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3])) :
    let R := ZMod (p ^ 5)
    (((((3 * p - 1).choose (p - 1) : ℕ) : R) ^ 2 - 1) * (p : R) ^ 2) = 0 := by
  intro R
  let Tn : ℕ := (3 * p - 1).choose (p - 1)
  let Tz : ℤ := (Tn : ℤ)
  have hpow : Tz ^ 2 ≡ (1 : ℤ) ^ 2 [ZMOD (p : ℤ) ^ 3] := by
    dsimp [Tz, Tn]
    exact hT.pow 2
  have hdiv_pos : (p : ℤ) ^ 3 ∣ Tz ^ 2 - 1 := by
    have hdiv_neg : (p : ℤ) ^ 3 ∣ (1 : ℤ) ^ 2 - Tz ^ 2 :=
      Int.modEq_iff_dvd.mp hpow
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using Int.dvd_neg.mpr hdiv_neg
  have hdiv : ((p ^ 5 : ℕ) : ℤ) ∣ (Tz ^ 2 - 1) * (p : ℤ) ^ 2 := by
    obtain ⟨k, hk⟩ := hdiv_pos
    refine ⟨k, ?_⟩
    calc
      (Tz ^ 2 - 1) * (p : ℤ) ^ 2 = ((p : ℤ) ^ 3 * k) * (p : ℤ) ^ 2 := by rw [hk]
      _ = (p : ℤ) ^ 5 * k := by ring
      _ = ((p ^ 5 : ℕ) : ℤ) * k := by norm_num [Nat.cast_pow]
  have hcast : (((Tz ^ 2 - 1) * (p : ℤ) ^ 2 : ℤ) : R) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdiv
  simpa [R, Tn, Tz, Nat.cast_pow] using hcast




theorem upper_local_expansion
    (p l : ℕ) (hp : p.Prime) (hl1 : 1 ≤ l) (hlp : l < p)
    (hT : ((((3 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3])) :
    ((((3 * p - l - 1).choose (p - 1) : ℕ) : ZMod (p ^ 5)) ^ 2) =
      upperLocalExpansion p l := by
  classical
  let R := ZMod (p ^ 5)
  let T : R := (((3 * p - 1).choose (p - 1) : ℕ) : R)
  let E : R := ∏ j ∈ Finset.Icc 1 l, UpperRatioCoreExact.exactCore p l j
  let A : R := (-2 : R) * (l : R)⁻¹ * E
  have hratio := BinomialRatioZMod.exact_binomial_ratio_zmod p l hp hlp
  have hcore := UpperRatioCoreExact.upperRatioCore_exact p l hp hl1 hlp
  have hchoose : ((((3 * p - l - 1).choose (p - 1) : ℕ) : R)) = ((p : R) * A) * T := by
    dsimp [A, E, T]
    calc
      ((((3 * p - l - 1).choose (p - 1) : ℕ) : R)) =
          ((((3 * p - 1).choose (p - 1) : ℕ) : R)) *
            ∏ s ∈ Finset.range l,
              (((2 * p - s : ℕ) : R) * (((3 * p - 1 - s : ℕ) : R)⁻¹)) := hratio
      _ = ((((3 * p - 1).choose (p - 1) : ℕ) : R)) *
            ((- (2 : R) * (p : R) * (l : R)⁻¹) *
              ∏ j ∈ Finset.Icc 1 l, UpperRatioCoreExact.exactCore p l j) := by rw [hcore]
      _ = ((p : R) * ((-2 : R) * (l : R)⁻¹ *
              (∏ j ∈ Finset.Icc 1 l, UpperRatioCoreExact.exactCore p l j))) *
            ((((3 * p - 1).choose (p - 1) : ℕ) : R)) := by ring
  have hTdrop : (T ^ 2 - 1) * (p : R) ^ 2 = 0 := by
    dsimp [T]
    exact anchor_sq_sub_one_mul_p_sq_eq_zero p hT
  have hsquare_drop :
      ((((3 * p - l - 1).choose (p - 1) : ℕ) : R) ^ 2) =
        (4 : R) * (p : R) ^ 2 * ((l : R)⁻¹) ^ 2 * E ^ 2 := by
    calc
      ((((3 * p - l - 1).choose (p - 1) : ℕ) : R) ^ 2) = (((p : R) * A) * T) ^ 2 := by rw [hchoose]
      _ = ((p : R) * A) ^ 2 :=
        A357674UpperRatioToT.square_drop_T_of_sq_sub_one_mul_c_sq_zero
          (R := R) (c := (p : R)) (T := T) (a := A) hTdrop
      _ = (4 : R) * (p : R) ^ 2 * ((l : R)⁻¹) ^ 2 * E ^ 2 := by
        dsimp [A]
        ring
  have hprod_core :
      (∏ j ∈ Finset.Icc 1 l, UpperRatioCoreExact.exactCore p l j) =
        (∏ j ∈ Finset.Icc 1 l, ExactCoreToTruncated.exactCore p l j) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact upper_exactCore_eq_trunc_exactCore p l j
  have htrunc0 := ExactCoreToTruncated.exactCore_product_square_eq_truncated p l hp hl1 hlp
  have htrunc :
      (4 : R) * (p : R) ^ 2 * ((l : R)⁻¹) ^ 2 * E ^ 2 =
        (4 : R) * (p : R) ^ 2 * ((l : R)⁻¹) ^ 2 *
          (∏ j ∈ Finset.Icc 1 l,
            (1 + (p : R) * A357674UpperRatioToT.upperF p l j +
              (p : R) ^ 2 * A357674UpperRatioToT.upperG p l j)) ^ 2 := by
    dsimp [E]
    calc
      (4 : R) * (p : R) ^ 2 * ((l : R)⁻¹) ^ 2 *
          (∏ j ∈ Finset.Icc 1 l, UpperRatioCoreExact.exactCore p l j) ^ 2 =
        (4 : R) * (p : R) ^ 2 * ((l : R)⁻¹) ^ 2 *
          (∏ j ∈ Finset.Icc 1 l, ExactCoreToTruncated.exactCore p l j) ^ 2 := by rw [hprod_core]
      _ = (4 : R) * (p : R) ^ 2 * ((l : R)⁻¹) ^ 2 *
          (∏ j ∈ Finset.Icc 1 l,
            (1 + (p : R) * ExactCoreToTruncated.upperF p l j +
              (p : R) ^ 2 * ExactCoreToTruncated.upperG p l j)) ^ 2 := htrunc0
      _ = (4 : R) * (p : R) ^ 2 * ((l : R)⁻¹) ^ 2 *
          (∏ j ∈ Finset.Icc 1 l,
            (1 + (p : R) * A357674UpperRatioToT.upperF p l j +
              (p : R) ^ 2 * A357674UpperRatioToT.upperG p l j)) ^ 2 := by
            have hfgprod :
                (∏ j ∈ Finset.Icc 1 l,
                  (1 + (p : R) * ExactCoreToTruncated.upperF p l j +
                    (p : R) ^ 2 * ExactCoreToTruncated.upperG p l j)) =
                (∏ j ∈ Finset.Icc 1 l,
                  (1 + (p : R) * A357674UpperRatioToT.upperF p l j +
                    (p : R) ^ 2 * A357674UpperRatioToT.upperG p l j)) := by
              apply Finset.prod_congr rfl
              intro j hj
              rw [trunc_upperF_eq_expansion_upperF p l j, trunc_upperG_eq_expansion_upperG p l j]
            rw [hfgprod]
  have hexp := A357674UpperRatioToT.upper_ratio_truncated_core_sq_expansion p l hl1
  calc
    ((((3 * p - l - 1).choose (p - 1) : ℕ) : R) ^ 2) =
        (4 : R) * (p : R) ^ 2 * ((l : R)⁻¹) ^ 2 * E ^ 2 := hsquare_drop
    _ = (4 : R) * (p : R) ^ 2 * ((l : R)⁻¹) ^ 2 *
          (∏ j ∈ Finset.Icc 1 l,
            (1 + (p : R) * A357674UpperRatioToT.upperF p l j +
              (p : R) ^ 2 * A357674UpperRatioToT.upperG p l j)) ^ 2 := htrunc
    _ = upperLocalExpansion p l := by
      dsimp [upperLocalExpansion]
      exact hexp

end UpperLocalExpansionFull
end Scratch






namespace BSuperScratch

lemma choose_prod_aux (p r n : ℕ) (hp : p.Prime) (hr : 0 < r) (hn : n < p) :
    (((p + n).choose n : ℕ) : ZMod (p ^ r)) =
      ∏ i ∈ Finset.Icc 1 n, (1 + (p : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnlt : n < p := by omega
      have hsuccpos : 0 < n + 1 := by omega
      have hsucc_lt : n + 1 < p := hn
      have hunit : IsUnit ((n + 1 : ℕ) : ZMod (p ^ r)) :=
        isUnit_natCast_zmod_prime_pow_of_pos_lt p r (n+1) hp hr hsuccpos hsucc_lt
      have hrec := ih hnlt
      have hchoose := Nat.add_one_mul_choose_eq (p + n) n
      -- `(p+n+1) * C(p+n,n) = C(p+n+1,n+1) * (n+1)`
      have hcast : ((p + n + 1 : ℕ) : ZMod (p ^ r)) *
            (((p + n).choose n : ℕ) : ZMod (p ^ r)) =
          (((p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) *
            ((n + 1 : ℕ) : ZMod (p ^ r)) := by
        simpa [Nat.cast_mul] using congrArg (fun x : ℕ => (x : ZMod (p ^ r))) hchoose
      have hinv : ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ * ((n + 1 : ℕ) : ZMod (p ^ r)) = 1 :=
        natCast_inv_mul_eq_one p r (n+1) hp hr hsuccpos hsucc_lt
      have hstep : (((p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) =
          (((p + n).choose n : ℕ) : ZMod (p ^ r)) *
            (((p + n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
        calc
          (((p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r))
              = (((p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) *
                  (((n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
                    rw [ZMod.mul_inv_of_unit _ hunit, mul_one]
          _ = ((((p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))) *
                  ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by ring_nf
          _ = (((p + n + 1 : ℕ) : ZMod (p ^ r)) * (((p + n).choose n : ℕ) : ZMod (p ^ r))) *
                  ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by rw [← hcast]
          _ = (((p + n).choose n : ℕ) : ZMod (p ^ r)) *
              (((p + n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by ring_nf
      have htop : p + (n + 1) = p + n + 1 := by omega
      rw [htop]
      rw [hstep, hrec]
      rw [Finset.prod_Icc_succ_top hsuccpos]
      congr 1
      have hfactor : (((p + n + 1 : ℕ) : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) =
          1 + (p : ZMod (p ^ r)) * ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by
        have hcasttop : ((p + n + 1 : ℕ) : ZMod (p ^ r)) =
            (p : ZMod (p ^ r)) + ((n + 1 : ℕ) : ZMod (p ^ r)) := by
          norm_num [Nat.cast_add, Nat.cast_mul]
          ring
        rw [hcasttop]
        rw [add_mul, ZMod.mul_inv_of_unit _ hunit]
        ring
      exact hfactor


lemma pair_factor_eq (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    (1 + (p : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)) *
      (1 + (p : ZMod (p ^ 3)) * (((p - i : ℕ) : ZMod (p ^ 3))⁻¹)) =
    1 - 2 * (p : ZMod (p ^ 3))^2 * ((i : ZMod (p ^ 3))⁻¹)^2 := by
  rw [inv_p_sub_expansion p i hp hi0 hip]
  have hp3zero : (p : ZMod (p ^ 3))^3 = 0 := p_pow_self_zmod_zero p 3
  have hp4zero : (p : ZMod (p ^ 3))^4 = 0 := by
    calc
      (p : ZMod (p ^ 3))^4 = (p : ZMod (p ^ 3))^3 * (p : ZMod (p ^ 3)) := by ring
      _ = 0 := by rw [hp3zero, zero_mul]
  ring_nf
  rw [hp3zero, hp4zero]
  ring




lemma B_super_zmod_of_odd (p h : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hp_eq : p = 2 * h + 1) :
    ((((2 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 3))) = 1 := by
  subst p
  haveI : Fact (Nat.Prime (2 * h + 1)) := ⟨hp⟩
  have hp5' : 5 ≤ 2 * h + 1 := hp5
  have hchoose := choose_prod_aux (2 * h + 1) 3 (2 * h) hp (by norm_num) (by omega : 2 * h < 2 * h + 1)
  have htop : 2 * (2 * h + 1) - 1 = (2 * h + 1) + 2 * h := by omega
  have hbot : 2 * h + 1 - 1 = 2 * h := by omega
  rw [htop, hbot]
  rw [hchoose]
  rw [prod_Icc_one_two_mul_pair h]
  trans ∏ i ∈ Finset.Icc 1 h,
      (1 - 2 * ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2)
  · apply Finset.prod_congr rfl
    intro i hi
    simp [Finset.mem_Icc] at hi
    simpa [mul_assoc] using pair_factor_eq (2 * h + 1) i hp (by omega) (by omega : i < 2 * h + 1)
  · let R := ZMod ((2 * h + 1) ^ 3)
    let c : R := ((2 * h + 1 : ℕ) : R) ^ 2
    let g : ℕ → R := fun i => -2 * ((i : R)⁻¹)^2
    have hc : c ^ 2 = 0 := by
      dsimp [c]
      have hp3zero : (((2 * h + 1 : ℕ) : R) ^ 3) = 0 := p_pow_self_zmod_zero (2 * h + 1) 3
      calc
        (((2 * h + 1 : ℕ) : R) ^ 2) ^ 2 = ((2 * h + 1 : ℕ) : R) ^ 4 := by ring
        _ = ((2 * h + 1 : ℕ) : R) ^ 3 * ((2 * h + 1 : ℕ) : R) := by ring
        _ = 0 := by rw [hp3zero, zero_mul]
    have hprod := prod_one_add_mul_of_square_zero (Finset.Icc 1 h) c g hc
    dsimp [c, g] at hprod
    have hsum0 := p_sq_mul_half_inv_sq_sum_zmodp3_zero (2 * h + 1) h hp hp5' rfl
    calc
      (∏ i ∈ Finset.Icc 1 h,
          (1 - 2 * ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
            ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2))
          = ∏ i ∈ Finset.Icc 1 h,
              (1 + ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
                (-2 * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2)) := by
              apply Finset.prod_congr rfl
              intro i hi
              ring
      _ = 1 + ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
          (∑ i ∈ Finset.Icc 1 h, -2 * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2) := hprod
      _ = 1 + ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
          (-2 * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2)) := by
              rw [← Finset.mul_sum]
      _ = 1 - 2 * (((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
              (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2)) := by ring
      _ = 1 := by rw [hsum0]; ring




lemma B_super_zmod (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((((2 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 3))) = 1 := by
  have hne2 : p ≠ 2 := by omega
  rcases hp.odd_of_ne_two hne2 with ⟨h, hp_eq⟩
  exact B_super_zmod_of_odd p h hp hp5 hp_eq

lemma B_super_int (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (((2 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3] := by
  have hz := B_super_zmod p hp hp5
  have hmod : (((2 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ (1 : ℤ) [ZMOD (p ^ 3)] := by
    exact (ZMod.intCast_eq_intCast_iff (((2 * p - 1).choose (p - 1) : ℕ) : ℤ) (1 : ℤ) (p ^ 3)).1 (by
      simpa using hz)
  simpa [Int.natCast_pow] using hmod


/-- The endpoint `B = binom(2p-1,p-1)` in `ZMod (p^5)`. -/
def Bz (p : ℕ) : ZMod (p ^ 5) :=
  (((2 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 5))

/-- A `p^3` congruence to `1` implies the endpoint idempotent identity modulo `p^5`. -/
lemma Bz_sq_eq_two_mul_sub_one_of_B_super_int (p : ℕ)
    (hB : ((((2 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3])) :
    (Bz p) ^ 2 = (2 : ZMod (p ^ 5)) * Bz p - 1 := by
  let Bn : ℕ := (2 * p - 1).choose (p - 1)
  let B : ℤ := (Bn : ℤ)
  have hmod : B ≡ 1 [ZMOD (p : ℤ) ^ 3] := by
    simpa [B, Bn] using hB
  have hdiv_neg : (p : ℤ) ^ 3 ∣ 1 - B := Int.modEq_iff_dvd.mp hmod
  have hdiv_pos : (p : ℤ) ^ 3 ∣ B - 1 := by
    simpa [sub_eq_add_neg, add_comm] using Int.dvd_neg.mpr hdiv_neg
  obtain ⟨a, ha⟩ := hdiv_pos
  have hdiv : ((p ^ 5 : ℕ) : ℤ) ∣ B ^ 2 - 2 * B + 1 := by
    refine ⟨(p : ℤ) * a ^ 2, ?_⟩
    calc
      B ^ 2 - 2 * B + 1 = (B - 1) ^ 2 := by ring
      _ = ((p : ℤ) ^ 3 * a) ^ 2 := by rw [ha]
      _ = ((p : ℤ) ^ 5) * ((p : ℤ) * a ^ 2) := by ring
      _ = ((p ^ 5 : ℕ) : ℤ) * ((p : ℤ) * a ^ 2) := by norm_num [Nat.cast_pow]
  have hcast : (((B ^ 2 - 2 * B + 1 : ℤ) : ZMod (p ^ 5)) = 0) := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdiv
  have hpoly : (Bz p) ^ 2 - (2 : ZMod (p ^ 5)) * Bz p + 1 = 0 := by
    simpa [Bz, B, Bn, Nat.cast_pow, Int.cast_pow, Int.cast_ofNat] using hcast
  rw [← sub_eq_zero]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using hpoly

/-- For primes `p ≥ 5`, `(Bz p)^2 = 2*Bz p - 1` in `ZMod (p^5)`. -/
theorem Bz_sq_eq_two_mul_sub_one (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Bz p) ^ 2 = (2 : ZMod (p ^ 5)) * Bz p - 1 := by
  exact Bz_sq_eq_two_mul_sub_one_of_B_super_int p (B_super_int p hp hp5)

end BSuperScratch








namespace A357674Scratch






lemma Icc_one_pred_eq_range_erase_zero (p : ℕ) (hp0 : 0 < p) :
    Finset.Icc 1 (p - 1) = (Finset.range p).erase 0 := by
  ext i
  simp [Finset.mem_Icc]
  omega

lemma sum_range_zmod_eq_sum_univ (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    (∑ i ∈ Finset.range p, f (i : ZMod p)) = ∑ x : ZMod p, f x := by
  rw [Finset.sum_range]
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      conv_rhs =>
        arg 2
        intro x
        rw [← ZMod.natCast_zmod_val x]
      rfl



lemma inv_pow_sum_Icc_zmodp_zero (p k : ℕ) (hp : p.Prime) (hk0 : 0 < k)
    (hklt : k < p - 1) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^k) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : 0 < p := hp.pos
  rw [Icc_one_pred_eq_range_erase_zero p hp0]
  rw [Finset.sum_erase]
  · have hpow : (∑ i ∈ Finset.range p, ((i : ZMod p) ^ (p - 1 - k))) = 0 := by
      rw [sum_range_zmod_eq_sum_univ p (fun x : ZMod p => x ^ (p - 1 - k))]
      have hlt : p - 1 - k < Fintype.card (ZMod p) - 1 := by
        rw [ZMod.card]
        omega
      exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) (p - 1 - k) hlt
    trans (∑ i ∈ Finset.range p, ((i : ZMod p) ^ (p - 1 - k)))
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        have hpos : 0 < p - 1 - k := by omega
        simp [hk0.ne', hpos.ne']
      · have hip : i < p := by simpa using hi
        have hunit : IsUnit (i : ZMod p) := by
          apply isUnit_iff_ne_zero.mpr
          intro hz
          have hdvd : p ∣ i := (ZMod.natCast_eq_zero_iff i p).1 hz
          exact not_le_of_gt hip (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hdvd)
        have hfermat : (i : ZMod p) ^ (p - 1) = 1 := by
          apply ZMod.pow_card_sub_one_eq_one
          exact IsUnit.ne_zero hunit
        have hpoweq : ((i : ZMod p)⁻¹)^k = (i : ZMod p)^(p - 1 - k) := by
          have hmul : ((i : ZMod p)⁻¹)^k * (i : ZMod p)^k = 1 := by
            rw [← mul_pow, ZMod.inv_mul_of_unit _ hunit, one_pow]
          have hright : (i : ZMod p)^(p - 1 - k) * (i : ZMod p)^k = 1 := by
            rw [← pow_add]
            have hadd : p - 1 - k + k = p - 1 := by omega
            rw [hadd, hfermat]
          have hunitk : IsUnit ((i : ZMod p)^k) := hunit.pow k
          calc
            ((i : ZMod p)⁻¹)^k
                = ((i : ZMod p)⁻¹)^k * (((i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹)) := by
                    rw [ZMod.mul_inv_of_unit _ hunitk, mul_one]
            _ = (((i : ZMod p)⁻¹)^k * (i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹) := by ring
            _ = 1 * (((i : ZMod p)^k)⁻¹) := by rw [hmul]
            _ = ((i : ZMod p)^(p - 1 - k) * (i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹) := by rw [hright]
            _ = (i : ZMod p)^(p - 1 - k) * (((i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹)) := by ring
            _ = (i : ZMod p)^(p - 1 - k) := by rw [ZMod.mul_inv_of_unit _ hunitk, mul_one]
        exact hpoweq
    · exact hpow
  · simp [hk0.ne']

lemma inv_sum_Icc_zmodp_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)) = 0 := by
  simpa using inv_pow_sum_Icc_zmodp_zero p 1 hp (by norm_num) (by omega)


lemma inv_cube_sum_Icc_zmodp_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^3) = 0 := by
  exact inv_pow_sum_Icc_zmodp_zero p 3 hp (by norm_num) (by omega)

lemma inv_fourth_sum_Icc_zmodp_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^4) = 0 := by
  exact inv_pow_sum_Icc_zmodp_zero p 4 hp (by norm_num) (by omega)

lemma p_pow_self_zmod_zero (p r : ℕ) : ((p : ZMod (p ^ r)) ^ r) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]

lemma isUnit_natCast_zmod_prime_pow_of_pos_lt (p r i : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hi0 : 0 < i) (hip : i < p) : IsUnit (i : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    exact not_le_of_gt hip (Nat.le_of_dvd hi0 hdiv))

lemma inv_p_sub_expansion (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    (((p - i : ℕ) : ZMod (p ^ 3))⁻¹) =
      - ((i : ZMod (p ^ 3))⁻¹) - (p : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)^2 -
        (p : ZMod (p ^ 3))^2 * ((i : ZMod (p ^ 3))⁻¹)^3 := by
  let R := ZMod (p ^ 3)
  have hunit_i : IsUnit (i : R) := isUnit_natCast_zmod_prime_pow_of_pos_lt p 3 i hp (by norm_num) hi0 hip
  have hunit_pi : IsUnit ((p - i : ℕ) : R) := by
    apply isUnit_natCast_zmod_prime_pow_of_pos_lt p 3 (p - i) hp (by norm_num)
    · omega
    · omega
  apply_fun fun x : R => x * ((p - i : ℕ) : R)
  · change (((p - i : ℕ) : R)⁻¹ * ((p - i : ℕ) : R)) =
      (-((i : R)⁻¹) - (p : R) * ((i : R)⁻¹)^2 - (p : R)^2 * ((i : R)⁻¹)^3) * ((p - i : ℕ) : R)
    rw [ZMod.inv_mul_of_unit _ hunit_pi]
    have hpi : ((p - i : ℕ) : R) = (p : R) - (i : R) := by
      rw [Nat.cast_sub (le_of_lt hip)]
    rw [hpi]
    have hi_inv : ((i : R)⁻¹) * (i : R) = 1 := ZMod.inv_mul_of_unit _ hunit_i
    have hi_inv2 : ((i : R)⁻¹)^2 * (i : R) = (i : R)⁻¹ := by
      calc
        ((i : R)⁻¹)^2 * (i : R) = (i : R)⁻¹ * (((i : R)⁻¹) * (i : R)) := by ring
        _ = (i : R)⁻¹ := by rw [hi_inv, mul_one]
    have hi_inv3 : ((i : R)⁻¹)^3 * (i : R) = ((i : R)⁻¹)^2 := by
      calc
        ((i : R)⁻¹)^3 * (i : R) = ((i : R)⁻¹)^2 * (((i : R)⁻¹) * (i : R)) := by ring
        _ = ((i : R)⁻¹)^2 := by rw [hi_inv, mul_one]
    have hp3zero : (p : R)^3 = 0 := p_pow_self_zmod_zero p 3
    have t2 : ((i : R)⁻¹)^2 * (p : R) * (i : R) = (p : R) * (i : R)⁻¹ := by
      calc
        ((i : R)⁻¹)^2 * (p : R) * (i : R) = (p : R) * (((i : R)⁻¹)^2 * (i : R)) := by ring
        _ = (p : R) * (i : R)⁻¹ := by rw [hi_inv2]
    have t3 : ((i : R)⁻¹)^3 * (p : R)^2 * (i : R) = (p : R)^2 * ((i : R)⁻¹)^2 := by
      calc
        ((i : R)⁻¹)^3 * (p : R)^2 * (i : R) = (p : R)^2 * (((i : R)⁻¹)^3 * (i : R)) := by ring
        _ = (p : R)^2 * ((i : R)⁻¹)^2 := by rw [hi_inv3]
    have t4 : ((i : R)⁻¹)^3 * (p : R)^2 * (p : R) = 0 := by
      calc
        ((i : R)⁻¹)^3 * (p : R)^2 * (p : R) = ((i : R)⁻¹)^3 * (p : R)^3 := by ring
        _ = 0 := by rw [hp3zero, mul_zero]
    calc
      1 = -((i : R)⁻¹) * (p : R) + ((i : R)⁻¹) * (i : R)
          - ((i : R)⁻¹)^2 * (p : R) * (p : R) + ((i : R)⁻¹)^2 * (p : R) * (i : R)
          - ((i : R)⁻¹)^3 * (p : R)^2 * (p : R) + ((i : R)⁻¹)^3 * (p : R)^2 * (i : R) := by
            rw [hi_inv, t2, t3, t4]
            ring
      _ = (-((i : R)⁻¹) - (p : R) * ((i : R)⁻¹)^2 - (p : R)^2 * ((i : R)⁻¹)^3) * ((p : R) - (i : R)) := by
            ring
  · intro a b hab
    calc
      a = a * 1 := by rw [mul_one]
      _ = a * (((p - i : ℕ) : R) * ((p - i : ℕ) : R)⁻¹) := by rw [ZMod.mul_inv_of_unit _ hunit_pi]
      _ = (a * ((p - i : ℕ) : R)) * ((p - i : ℕ) : R)⁻¹ := by ring
      _ = (b * ((p - i : ℕ) : R)) * ((p - i : ℕ) : R)⁻¹ := by simpa using congrArg (fun x : R => x * (((p - i : ℕ) : R)⁻¹)) hab
      _ = b * (((p - i : ℕ) : R) * ((p - i : ℕ) : R)⁻¹) := by ring
      _ = b := by rw [ZMod.mul_inv_of_unit _ hunit_pi, mul_one]

lemma pair_inv_cube_mul_p_eq (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    (p : ZMod (p ^ 3)) *
      (((i : ZMod (p ^ 3))⁻¹)^3 + (((p - i : ℕ) : ZMod (p ^ 3))⁻¹)^3) =
    -3 * (p : ZMod (p ^ 3))^2 * ((i : ZMod (p ^ 3))⁻¹)^4 := by
  rw [inv_p_sub_expansion p i hp hi0 hip]
  have hp3zero : (p : ZMod (p ^ 3))^3 = 0 := p_pow_self_zmod_zero p 3
  have hp4zero : (p : ZMod (p ^ 3))^4 = 0 := by
    calc
      (p : ZMod (p ^ 3))^4 = (p : ZMod (p ^ 3))^3 * (p : ZMod (p ^ 3)) := by ring
      _ = 0 := by rw [hp3zero, zero_mul]
  have hp5zero : (p : ZMod (p ^ 3))^5 = 0 := by
    calc
      (p : ZMod (p ^ 3))^5 = (p : ZMod (p ^ 3))^3 * (p : ZMod (p ^ 3))^2 := by ring
      _ = 0 := by rw [hp3zero, zero_mul]
  have hp6zero : (p : ZMod (p ^ 3))^6 = 0 := by
    calc
      (p : ZMod (p ^ 3))^6 = (p : ZMod (p ^ 3))^3 * (p : ZMod (p ^ 3))^3 := by ring
      _ = 0 := by rw [hp3zero, zero_mul]
  have hp7zero : (p : ZMod (p ^ 3))^7 = 0 := by
    calc
      (p : ZMod (p ^ 3))^7 = (p : ZMod (p ^ 3))^3 * (p : ZMod (p ^ 3))^4 := by ring
      _ = 0 := by rw [hp3zero, zero_mul]
  ring_nf
  rw [hp3zero, hp4zero, hp5zero, hp6zero, hp7zero]
  ring

lemma inv_fourth_sum_upper_eq_half_zmodp (p h : ℕ) (hp : p.Prime) (hp_eq : p = 2 * h + 1) :
    (∑ i ∈ Finset.Icc (h + 1) (p - 1), (((i : ZMod p)⁻¹)^4)) =
      ∑ i ∈ Finset.Icc 1 h, (((i : ZMod p)⁻¹)^4) := by
  subst p
  haveI : Fact (Nat.Prime (2 * h + 1)) := ⟨hp⟩
  refine Finset.sum_bij (fun i _ => (2 * h + 1) - i) ?_ ?_ ?_ ?_
  · intro i hi
    simp [Finset.mem_Icc] at hi ⊢
    omega
  · intro a ha b hb hab
    simp [Finset.mem_Icc] at ha hb
    have hsub : 2 * h + 1 - a = 2 * h + 1 - b := hab
    omega
  · intro b hb
    refine ⟨(2 * h + 1) - b, ?_, ?_⟩
    · simp [Finset.mem_Icc] at hb ⊢
      omega
    · simp [Finset.mem_Icc] at hb
      change 2 * h + 1 - (2 * h + 1 - b) = b
      omega
  · intro i hi
    simp [Finset.mem_Icc] at hi
    have hpi : (((2 * h + 1) - i : ℕ) : ZMod (2 * h + 1)) = - (i : ZMod (2 * h + 1)) := by
      rw [Nat.cast_sub (by omega : i ≤ 2 * h + 1)]
      simp
    rw [hpi]
    have hinvneg : (- (i : ZMod (2 * h + 1)))⁻¹ = - ((i : ZMod (2 * h + 1))⁻¹) := inv_neg
    rw [hinvneg]
    ring

lemma inv_fourth_sum_half_zmodp_zero (p h : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^4) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let f : ℕ → ZMod p := fun i => ((i : ZMod p)⁻¹)^4
  have hfull := inv_fourth_sum_Icc_zmodp_zero p hp hp7
  have hfilter := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p - 1)) (fun i => i ≤ h) f
  have hleft : (Finset.Icc 1 (p - 1)).filter (fun i => i ≤ h) = Finset.Icc 1 h := by
    ext i
    simp [Finset.mem_Icc]
    omega
  have hright : (Finset.Icc 1 (p - 1)).filter (fun i => ¬ i ≤ h) = Finset.Icc (h + 1) (p - 1) := by
    ext i
    simp [Finset.mem_Icc]
    omega
  rw [hleft, hright] at hfilter
  have hupper := inv_fourth_sum_upper_eq_half_zmodp p h hp hp_eq
  dsimp [f] at hfilter
  rw [hupper] at hfilter
  rw [hfull] at hfilter
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hsum : (2 : ZMod p) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^4) = 0 := by
    simpa [two_mul] using hfilter
  have h2inv : (2 : ZMod p)⁻¹ * (2 : ZMod p) = 1 := inv_mul_cancel₀ htwo_ne
  calc
    (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^4)
        = 1 * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^4) := by rw [one_mul]
    _ = ((2 : ZMod p)⁻¹ * (2 : ZMod p)) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^4) := by
      rw [h2inv]
    _ = (2 : ZMod p)⁻¹ * ((2 : ZMod p) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^4)) := by ring
    _ = 0 := by rw [hsum, mul_zero]

lemma p_sq_mul_eq_zero_of_castHom_eq_zero (p : ℕ) [NeZero p] (x : ZMod (p ^ 3))
    (h : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) x = 0) :
    (p : ZMod (p ^ 3)) ^ 2 * x = 0 := by
  rw [← ZMod.natCast_zmod_val x]
  have hx0 : ((x.val : ℕ) : ZMod p) = 0 := by
    simpa [ZMod.castHom_apply] using h
  have hdvd : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).1 hx0
  rcases hdvd with ⟨k, hk⟩
  rw [hk]
  norm_num [Nat.cast_mul, Nat.cast_pow]
  have hp3zero : (p : ZMod (p ^ 3)) ^ 3 = 0 := p_pow_self_zmod_zero p 3
  ring_nf
  rw [hp3zero]
  ring

lemma castHom_inv_pow_nat (p i n : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
        (((i : ZMod (p ^ 3))⁻¹)^n) = ((i : ZMod p)⁻¹)^n := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hunit3 : IsUnit (i : ZMod (p ^ 3)) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p 3 i hp (by norm_num) hi0 hip
  have hmap_inv : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 3))⁻¹) =
      ((i : ZMod p)⁻¹) := by
    apply eq_inv_of_mul_eq_one_right
    calc
      (i : ZMod p) * ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 3))⁻¹)
          = ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)) := by simp
      _ = 1 := by rw [ZMod.mul_inv_of_unit _ hunit3]; simp
  rw [map_pow, hmap_inv]

lemma castHom_half_inv_fourth_sum (p h : ℕ) (hp : p.Prime) (hp_eq : p = 2 * h + 1) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
      (∑ i ∈ Finset.Icc 1 h, ((i : ZMod (p ^ 3))⁻¹)^4) =
    ∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^4 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_Icc] at hi
  exact castHom_inv_pow_nat p i 4 hp (by omega) (by omega)

lemma p_sq_mul_half_inv_fourth_sum_zmodp3_zero (p h : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (p : ZMod (p ^ 3)) ^ 2 * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod (p ^ 3))⁻¹)^4) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply p_sq_mul_eq_zero_of_castHom_eq_zero p
  rw [castHom_half_inv_fourth_sum p h hp hp_eq]
  exact inv_fourth_sum_half_zmodp_zero p h hp hp7 hp_eq

lemma prod_Icc_one_two_mul_pair_sum {M : Type*} [AddCommMonoid M] (h : ℕ) (F : ℕ → M) :
    (∑ i ∈ Finset.Icc 1 (2 * h), F i) =
      ∑ i ∈ Finset.Icc 1 h, (F i + F (2 * h + 1 - i)) := by
  classical
  have hfilter := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (2 * h)) (fun i => i ≤ h) F
  have hleft : (Finset.Icc 1 (2 * h)).filter (fun i => i ≤ h) = Finset.Icc 1 h := by
    ext i
    simp [Finset.mem_Icc]
    omega
  have hright : (Finset.Icc 1 (2 * h)).filter (fun i => ¬ i ≤ h) = Finset.Icc (h + 1) (2 * h) := by
    ext i
    simp [Finset.mem_Icc]
    omega
  rw [hleft, hright] at hfilter
  have hupper : (∑ i ∈ Finset.Icc (h + 1) (2 * h), F i) =
      ∑ i ∈ Finset.Icc 1 h, F (2 * h + 1 - i) := by
    refine Finset.sum_bij (fun i _ => 2 * h + 1 - i) ?_ ?_ ?_ ?_
    · intro i hi
      simp [Finset.mem_Icc] at hi ⊢
      omega
    · intro a ha b hb hab
      simp [Finset.mem_Icc] at ha hb
      have hsub : 2 * h + 1 - a = 2 * h + 1 - b := hab
      omega
    · intro b hb
      refine ⟨2 * h + 1 - b, ?_, ?_⟩
      · simp [Finset.mem_Icc] at hb ⊢
        omega
      · simp [Finset.mem_Icc] at hb
        change 2 * h + 1 - (2 * h + 1 - b) = b
        omega
    · intro i hi
      simp [Finset.mem_Icc] at hi
      have harg : i = 2 * h + 1 - (2 * h + 1 - i) := by omega
      simpa using congrArg F harg
  rw [← hfilter, hupper]
  rw [Finset.sum_add_distrib]

lemma harmonic_cube_zmodp3_p_mul_zero_of_odd (p h : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (p : ZMod (p ^ 3)) * (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod (p ^ 3))⁻¹)^3) = 0 := by
  subst p
  have hp7' : 7 ≤ 2 * h + 1 := hp7
  have hsum := prod_Icc_one_two_mul_pair_sum h (fun i => ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^3)
  have htop : 2 * h + 1 - 1 = 2 * h := by omega
  rw [htop]
  rw [hsum]
  rw [Finset.mul_sum]
  trans ∑ i ∈ Finset.Icc 1 h,
      (-3 * ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3))^2 * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^4)
  · apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_Icc] at hi
    simpa using pair_inv_cube_mul_p_eq (2 * h + 1) i hp (by omega) (by omega : i < 2 * h + 1)
  · rw [← Finset.mul_sum]
    have hzero := p_sq_mul_half_inv_fourth_sum_zmodp3_zero (2 * h + 1) h hp hp7' rfl
    calc
      -3 * ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3))^2 *
          (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^4)
          = -3 * (((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3))^2 *
          (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^4)) := by ring
      _ = 0 := by rw [hzero, mul_zero]

lemma harmonic_cube_zmodp3_p_mul_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 3)) * (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod (p ^ 3))⁻¹)^3) = 0 := by
  have hne2 : p ≠ 2 := by omega
  rcases hp.odd_of_ne_two hne2 with ⟨h, hp_eq⟩
  exact harmonic_cube_zmodp3_p_mul_zero_of_odd p h hp hp7 hp_eq


end A357674Scratch

namespace Scratch
namespace HarmonicBinomialIdentityZMod

noncomputable section


def H1 (p r n : ℕ) : ZMod (p ^ r) :=
  ∑ k ∈ Finset.Icc 1 n, (k : ZMod (p ^ r))⁻¹


def H2 (p r n : ℕ) : ZMod (p ^ r) :=
  ∑ k ∈ Finset.Icc 1 n, ((k : ZMod (p ^ r))⁻¹) ^ 2


def altBinomH2 (p r n : ℕ) : ZMod (p ^ r) :=
  ∑ k ∈ Finset.Icc 1 n,
    (-1 : ZMod (p ^ r)) ^ (k - 1) * (Nat.choose n k : ZMod (p ^ r)) *
      (((k : ZMod (p ^ r))⁻¹) ^ 2)


def H1r (p r n : ℕ) : ZMod (p ^ r) :=
  ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹)


def H2r (p r n : ℕ) : ZMod (p ^ r) :=
  ∑ j ∈ Finset.range n, ((((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)


def altBinomH1r (p r n : ℕ) : ZMod (p ^ r) :=
  ∑ j ∈ Finset.range n,
    (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n (j + 1) : ZMod (p ^ r)) *
      (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹)


def altBinomH2r (p r n : ℕ) : ZMod (p ^ r) :=
  ∑ j ∈ Finset.range n,
    (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n (j + 1) : ZMod (p ^ r)) *
      ((((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)

lemma isUnit_natCast_zmod_prime_pow_of_pos_lt (p r i : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hi0 : 0 < i) (hip : i < p) : IsUnit (i : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    exact not_le_of_gt hip (Nat.le_of_dvd hi0 hdiv))

lemma sum_Icc_one_eq_sum_range {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∑ k ∈ Finset.Icc 1 n, f k) = ∑ j ∈ Finset.range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]

lemma H1_eq_H1r (p r n : ℕ) : H1 p r n = H1r p r n := by
  simp [H1, H1r, sum_Icc_one_eq_sum_range]

lemma H2_eq_H2r (p r n : ℕ) : H2 p r n = H2r p r n := by
  simp [H2, H2r, sum_Icc_one_eq_sum_range]


lemma altBinomH2_eq_altBinomH2r (p r n : ℕ) : altBinomH2 p r n = altBinomH2r p r n := by
  rw [altBinomH2, altBinomH2r, sum_Icc_one_eq_sum_range]
  simp

lemma H1r_succ (p r n : ℕ) :
    H1r p r (n + 1) = H1r p r n + (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
  simp [H1r, Finset.sum_range_succ]

lemma H2r_succ (p r n : ℕ) :
    H2r p r (n + 1) = H2r p r n + ((((n + 1 : ℕ) : ZMod (p ^ r))⁻¹)^2) := by
  simp [H2r, Finset.sum_range_succ]

lemma alternating_choose_shift_sum (p r n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ZMod (p ^ r)) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r))) = 1 := by
  have hZ := (Int.alternating_sum_range_choose_eq_choose (n := n) (m := n + 1))
  have hZ0 :
      (∑ k ∈ Finset.range (n + 2),
        (-1 : ℤ) ^ k * ((Nat.choose (n + 1) k : ℕ) : ℤ)) = 0 := by
    simpa [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self (n + 1))] using hZ
  have hZ1 :
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ j * ((Nat.choose (n + 1) (j + 1) : ℕ) : ℤ)) = 1 := by
    rw [Finset.sum_range_succ'] at hZ0
    simp only [Nat.cast_one, Nat.choose_zero_right, pow_zero, mul_one] at hZ0
    have hZ1' :
        - (∑ j ∈ Finset.range (n + 1),
            (-1 : ℤ) ^ j * ((Nat.choose (n + 1) (j + 1) : ℕ) : ℤ)) + 1 = 0 := by
      simpa [pow_succ, Finset.sum_neg_distrib, mul_assoc] using hZ0
    linarith
  have hcast := congrArg (fun z : ℤ => (z : ZMod (p ^ r))) hZ1
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] at hcast
  simpa using hcast

lemma mul_choose_inv_succ_eq_shift (p r n j : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hjp : j + 1 < p) :
    ((n + 1 : ℕ) : ZMod (p ^ r)) *
        ((-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
          (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹)) =
      (-1 : ZMod (p ^ r)) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)) := by
  have hcast :
      ((n + 1 : ℕ) : ZMod (p ^ r)) * (Nat.choose n j : ZMod (p ^ r)) =
        (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)) * (((j + 1 : ℕ) : ZMod (p ^ r))) := by
    simpa [Nat.cast_mul] using congrArg (fun x : ℕ => (x : ZMod (p ^ r))) (Nat.add_one_mul_choose_eq n j)
  have hjunit : IsUnit (((j + 1 : ℕ) : ZMod (p ^ r))) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p r (j + 1) hp hr (by omega) hjp
  calc
    ((n + 1 : ℕ) : ZMod (p ^ r)) *
        ((-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
          (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹))
        = (-1 : ZMod (p ^ r)) ^ j * (((n + 1 : ℕ) : ZMod (p ^ r)) *
            (Nat.choose n j : ZMod (p ^ r))) * (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by ring
    _ = (-1 : ZMod (p ^ r)) ^ j * ((Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)) *
            (((j + 1 : ℕ) : ZMod (p ^ r)))) * (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by rw [hcast]
    _ = (-1 : ZMod (p ^ r)) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)) := by
      calc
        (-1 : ZMod (p ^ r)) ^ j * ((Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)) *
            (((j + 1 : ℕ) : ZMod (p ^ r)))) * (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹)
            = ((-1 : ZMod (p ^ r)) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r))) *
                ((((j + 1 : ℕ) : ZMod (p ^ r)) * (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹))) := by ring
        _ = (-1 : ZMod (p ^ r)) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)) := by
          rw [ZMod.mul_inv_of_unit _ hjunit, mul_one]

lemma alternating_choose_inv_succ_sum (p r n : ℕ) (hp : p.Prime) (hr : 0 < r) (hn : n + 1 < p) :
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
        (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹)) =
    (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
  have hnunit : IsUnit (((n + 1 : ℕ) : ZMod (p ^ r))) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p r (n + 1) hp hr (by omega) hn
  have hmul :
      ((n + 1 : ℕ) : ZMod (p ^ r)) *
        (∑ j ∈ Finset.range (n + 1),
          (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
            (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹)) = 1 := by
    rw [Finset.mul_sum]
    trans (∑ j ∈ Finset.range (n + 1),
      (-1 : ZMod (p ^ r)) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)))
    · apply Finset.sum_congr rfl
      intro j hj
      exact mul_choose_inv_succ_eq_shift p r n j hp hr (by
        have hjlt : j < n + 1 := by simpa using hj
        omega)
    · exact alternating_choose_shift_sum p r n
  calc
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
        (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹))
        = (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) *
            (((n + 1 : ℕ) : ZMod (p ^ r)) *
              (∑ j ∈ Finset.range (n + 1),
                (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
                  (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹))) := by
          rw [← mul_assoc, ZMod.inv_mul_of_unit _ hnunit, one_mul]
    _ = (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by rw [hmul, mul_one]

lemma altBinomH1r_succ (p r n : ℕ) (hp : p.Prime) (hr : 0 < r) (hn : n + 1 < p) :
    altBinomH1r p r (n + 1) = altBinomH1r p r n + (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
  rw [altBinomH1r]
  have hsplit :
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ZMod (p ^ r)) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)) *
          (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹)) =
      (∑ j ∈ Finset.range (n + 1),
        ((-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
            (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) +
         (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n (j + 1) : ZMod (p ^ r)) *
            (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.choose_succ_succ]
    norm_num
    ring
  rw [hsplit, Finset.sum_add_distrib]
  have htail :
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n (j + 1) : ZMod (p ^ r)) *
          (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹)) = altBinomH1r p r n := by
    rw [Finset.sum_range_succ]
    simp [altBinomH1r]
  rw [htail, alternating_choose_inv_succ_sum p r n hp hr hn]
  ring

theorem altBinomH1r_eq_H1r (p r n : ℕ) (hp : p.Prime) (hr : 0 < r) (hn : n < p) :
    altBinomH1r p r n = H1r p r n := by
  induction n with
  | zero => simp [altBinomH1r, H1r]
  | succ n ih =>
      have hn' : n < p := by omega
      rw [altBinomH1r_succ p r n hp hr hn, H1r_succ, ih hn']

lemma choose_inv_sq_eq_inv_succ_mul_shift (p r n j : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hn : n + 1 < p) (hj : j + 1 < p) :
    (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
        ((((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2) =
      (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) *
        ((-1 : ZMod (p ^ r)) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)) *
          (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹)) := by
  let R := ZMod (p ^ r)
  have hnunit : IsUnit (((n + 1 : ℕ) : R)) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p r (n + 1) hp hr (by omega) hn
  have hshift := mul_choose_inv_succ_eq_shift p r n j hp hr hj
  change (-1 : R) ^ j * (Nat.choose n j : R) * ((((j + 1 : ℕ) : R)⁻¹) ^ 2) =
      (((n + 1 : ℕ) : R)⁻¹) *
        ((-1 : R) ^ j * (Nat.choose (n + 1) (j + 1) : R) * (((j + 1 : ℕ) : R)⁻¹))
  calc
    (-1 : R) ^ j * (Nat.choose n j : R) * ((((j + 1 : ℕ) : R)⁻¹) ^ 2)
        = (((((n + 1 : ℕ) : R)⁻¹) * (((n + 1 : ℕ) : R))) *
              ((-1 : R) ^ j * (Nat.choose n j : R) * (((j + 1 : ℕ) : R)⁻¹))) *
            (((j + 1 : ℕ) : R)⁻¹) := by
          rw [show (((n + 1 : ℕ) : R)⁻¹) * (((n + 1 : ℕ) : R)) = 1 by
            exact ZMod.inv_mul_of_unit _ hnunit]
          ring
    _ = (((n + 1 : ℕ) : R)⁻¹) *
            (((n + 1 : ℕ) : R) *
              ((-1 : R) ^ j * (Nat.choose n j : R) * (((j + 1 : ℕ) : R)⁻¹))) *
            (((j + 1 : ℕ) : R)⁻¹) := by ring
    _ = (((n + 1 : ℕ) : R)⁻¹) *
          ((-1 : R) ^ j * (Nat.choose (n + 1) (j + 1) : R)) *
            (((j + 1 : ℕ) : R)⁻¹) := by rw [hshift]
    _ = (((n + 1 : ℕ) : R)⁻¹) *
        ((-1 : R) ^ j * (Nat.choose (n + 1) (j + 1) : R) * (((j + 1 : ℕ) : R)⁻¹)) := by ring

lemma altBinomH2r_succ (p r n : ℕ) (hp : p.Prime) (hr : 0 < r) (hn : n + 1 < p) :
    altBinomH2r p r (n + 1) =
      altBinomH2r p r n + H1r p r (n + 1) * (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
  rw [altBinomH2r]
  have hsplit :
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ZMod (p ^ r)) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)) *
          ((((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)) =
      (∑ j ∈ Finset.range (n + 1),
        ((-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
            ((((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2) +
         (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n (j + 1) : ZMod (p ^ r)) *
            ((((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.choose_succ_succ]
    norm_num
    ring
  rw [hsplit, Finset.sum_add_distrib]
  have htail :
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n (j + 1) : ZMod (p ^ r)) *
          ((((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)) = altBinomH2r p r n := by
    rw [Finset.sum_range_succ]
    simp [altBinomH2r]
  have hhead :
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
          ((((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)) =
        H1r p r (n + 1) * (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
    calc
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ZMod (p ^ r)) ^ j * (Nat.choose n j : ZMod (p ^ r)) *
          ((((j + 1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2))
          = (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) *
              (∑ j ∈ Finset.range (n + 1),
                (-1 : ZMod (p ^ r)) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod (p ^ r)) *
                  (((j + 1 : ℕ) : ZMod (p ^ r))⁻¹)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              exact choose_inv_sq_eq_inv_succ_mul_shift p r n j hp hr hn (by
                have hjlt : j < n + 1 := by simpa using hj
                omega)
      _ = (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) * altBinomH1r p r (n + 1) := by rfl
      _ = H1r p r (n + 1) * (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
          rw [altBinomH1r_eq_H1r p r (n + 1) hp hr hn]
          ring
  rw [htail, hhead]
  ring

theorem two_mul_altBinomH2r_eq_H1r_sq_add_H2r (p r n : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hn : n < p) :
    (2 : ZMod (p ^ r)) * altBinomH2r p r n = H1r p r n ^ 2 + H2r p r n := by
  induction n with
  | zero => simp [altBinomH2r, H1r, H2r]
  | succ n ih =>
      have hn' : n < p := by omega
      rw [altBinomH2r_succ p r n hp hr hn, H1r_succ, H2r_succ]
      calc
        (2 : ZMod (p ^ r)) *
            (altBinomH2r p r n + (H1r p r n + (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹)) *
              (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹))
            = ((2 : ZMod (p ^ r)) * altBinomH2r p r n) +
                ((2 : ZMod (p ^ r)) * H1r p r n * (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) +
                  (2 : ZMod (p ^ r)) * ((((n + 1 : ℕ) : ZMod (p ^ r))⁻¹)^2)) := by ring
        _ = (H1r p r n ^ 2 + H2r p r n) +
                ((2 : ZMod (p ^ r)) * H1r p r n * (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) +
                  (2 : ZMod (p ^ r)) * ((((n + 1 : ℕ) : ZMod (p ^ r))⁻¹)^2)) := by rw [ih hn']
        _ = (H1r p r n + (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹)) ^ 2 +
              (H2r p r n + (((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) ^ 2) := by ring

theorem altBinomH2r_eq_half_harmonic_square_add (p r n : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hn : n < p) (h2unit : IsUnit (2 : ZMod (p ^ r))) :
    altBinomH2r p r n = (H1r p r n ^ 2 + H2r p r n) * (2 : ZMod (p ^ r))⁻¹ := by
  have h := two_mul_altBinomH2r_eq_H1r_sq_add_H2r p r n hp hr hn
  calc
    altBinomH2r p r n = ((2 : ZMod (p ^ r)) * altBinomH2r p r n) * (2 : ZMod (p ^ r))⁻¹ := by
      calc
        altBinomH2r p r n = altBinomH2r p r n * ((2 : ZMod (p ^ r)) * (2 : ZMod (p ^ r))⁻¹) := by
          rw [ZMod.mul_inv_of_unit _ h2unit, mul_one]
        _ = ((2 : ZMod (p ^ r)) * altBinomH2r p r n) * (2 : ZMod (p ^ r))⁻¹ := by ring
    _ = (H1r p r n ^ 2 + H2r p r n) * (2 : ZMod (p ^ r))⁻¹ := by rw [h]

lemma isUnit_two_zmod_prime_pow_of_ne_two (p r : ℕ) (hp : p.Prime) (hr : 0 < r) (hp2 : p ≠ 2) :
    IsUnit (2 : ZMod (p ^ r)) := by
  apply isUnit_natCast_zmod_prime_pow_of_pos_lt p r 2 hp hr (by norm_num)
  have hpgt1 : 1 < p := hp.one_lt
  omega



theorem alt_binom_H2_zmod_odd (p r n : ℕ) (hp : p.Prime) (hr : 0 < r) (hn : n < p) (hp2 : p ≠ 2) :
    altBinomH2 p r n = ((H1 p r n)^2 + H2 p r n) * (2 : ZMod (p ^ r))⁻¹ := by
  rw [altBinomH2_eq_altBinomH2r, H1_eq_H1r, H2_eq_H2r]
  exact altBinomH2r_eq_half_harmonic_square_add p r n hp hr hn
    (isUnit_two_zmod_prime_pow_of_ne_two p r hp hr hp2)

end
end HarmonicBinomialIdentityZMod
end Scratch









namespace Scratch
namespace KeyDepthCongruencePrimeGeSevenScratch


def H2 (p : ℕ) : ZMod (p ^ 3) :=
  ∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod (p ^ 3))⁻¹) ^ 2)


def A (p : ℕ) : ZMod (p ^ 3) :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ∑ i ∈ Finset.Icc 1 (k - 1),
      ((i : ZMod (p ^ 3))⁻¹) * (((k : ZMod (p ^ 3))⁻¹) ^ 2)


def keyDepthCongruence (p : ℕ) : Prop :=
  (3 : ZMod (p ^ 3)) * H2 p =
    (2 : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) * A p


def H3 (p : ℕ) : ZMod (p ^ 3) :=
  ∑ k ∈ Finset.Icc 1 (p - 1), (((k : ZMod (p ^ 3))⁻¹) ^ 3)


def E2Initial (p k : ℕ) : ZMod (p ^ 3) :=
  ∑ j ∈ Finset.Icc 1 k,
    ∑ i ∈ Finset.Icc 1 (j - 1),
      ((i : ZMod (p ^ 3))⁻¹) * ((j : ZMod (p ^ 3))⁻¹)


def T (p : ℕ) : ZMod (p ^ 3) :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    E2Initial p k * (((k : ZMod (p ^ 3))⁻¹) ^ 2)


def alternatingH2SecondEvaluation (p : ℕ) : Prop :=
  Scratch.HarmonicBinomialIdentityZMod.altBinomH2 p 3 (p - 1) =
    - H2 p + (p : ZMod (p ^ 3)) * (A p + H3 p) -
      ((p : ZMod (p ^ 3)) ^ 2) * T p


lemma zmod_p_cast_pow_three_eq_zero (p : ℕ) :
    let R := ZMod (p ^ 3); ((p : R) ^ 3) = 0 := by
  intro R
  change ((p : ZMod (p ^ 3)) ^ 3) = 0
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self (p ^ 3)



lemma prod_Icc_one_sub_eq_second_order {R : Type*} [CommRing R]
    (c : R) (x : ℕ → R) (k : ℕ) (hc3 : c ^ 3 = 0) :
    (∏ i ∈ Finset.Icc 1 k, (1 - c * x i)) =
      1 - c * (∑ i ∈ Finset.Icc 1 k, x i) +
        c ^ 2 * (∑ j ∈ Finset.Icc 1 k, ∑ i ∈ Finset.Icc 1 (j - 1), x i * x j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have htop : 1 ≤ k + 1 := by omega
        have htop_old : 1 ≤ k := by omega
        rw [Finset.prod_Icc_succ_top htop, Finset.sum_Icc_succ_top htop,
          Finset.sum_Icc_succ_top htop]
        rw [ih]
        have hpair_top :
            (∑ i ∈ Finset.Icc 1 (k + 1 - 1), x i * x (k + 1)) =
              (∑ i ∈ Finset.Icc 1 k, x i * x (k + 1)) := by
          rw [Nat.add_sub_cancel]
        rw [hpair_top]
        rw [show (∑ i ∈ Finset.Icc 1 k, x i * x (k + 1)) =
            (∑ i ∈ Finset.Icc 1 k, x i) * x (k + 1) by
          rw [Finset.sum_mul]]
        ring_nf
        simp [hc3]



lemma choose_pred_product_zmod (p r k : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hk : k < p) :
    ((Nat.choose (p - 1) k : ℕ) : ZMod (p ^ r)) =
      ∏ i ∈ Finset.Icc 1 k,
        (((p - i : ℕ) : ZMod (p ^ r)) * ((i : ZMod (p ^ r))⁻¹)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < p := by omega
      have hsuccpos : 0 < k + 1 := by omega
      have hsucc_lt : k + 1 < p := hk
      have hden_unit : IsUnit (((k + 1 : ℕ) : ZMod (p ^ r))) :=
        Scratch.HarmonicBinomialIdentityZMod.isUnit_natCast_zmod_prime_pow_of_pos_lt
          p r (k + 1) hp hr hsuccpos hsucc_lt
      have hrec := Nat.choose_succ_right_eq (p - 1) k
      have hnum : p - 1 - k = p - (k + 1) := by omega
      have hcast :
          ((Nat.choose (p - 1) k : ℕ) : ZMod (p ^ r)) *
              (((p - 1 - k : ℕ) : ZMod (p ^ r))) =
            ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod (p ^ r)) *
              (((k + 1 : ℕ) : ZMod (p ^ r))) := by
        have hrec' := congrArg (fun x : ℕ => (x : ZMod (p ^ r))) hrec
        simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hrec'.symm
      have hstep :
          ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod (p ^ r)) =
            ((Nat.choose (p - 1) k : ℕ) : ZMod (p ^ r)) *
              ((((p - (k + 1) : ℕ) : ZMod (p ^ r))) *
                (((k + 1 : ℕ) : ZMod (p ^ r))⁻¹)) := by
        calc
          ((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod (p ^ r))
              = (((Nat.choose (p - 1) (k + 1) : ℕ) : ZMod (p ^ r)) *
                    (((k + 1 : ℕ) : ZMod (p ^ r)))) *
                  (((k + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
                    rw [mul_assoc, ZMod.mul_inv_of_unit _ hden_unit, mul_one]
          _ = (((Nat.choose (p - 1) k : ℕ) : ZMod (p ^ r)) *
                    (((p - 1 - k : ℕ) : ZMod (p ^ r)))) *
                  (((k + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by rw [← hcast]
          _ = ((Nat.choose (p - 1) k : ℕ) : ZMod (p ^ r)) *
              ((((p - (k + 1) : ℕ) : ZMod (p ^ r))) *
                (((k + 1 : ℕ) : ZMod (p ^ r))⁻¹)) := by rw [hnum]; ring
      rw [hstep, ih hklt]
      rw [Finset.prod_Icc_succ_top hsuccpos]

lemma choose_pred_factor_eq_neg_one_sub (p k i : ℕ) (hp : p.Prime)
    (hi : i ∈ Finset.Icc 1 k) (hk : k < p) :
    (((p - i : ℕ) : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)) =
      - (1 - (p : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)) := by
  let R := ZMod (p ^ 3)
  have hi_bounds : 1 ≤ i ∧ i ≤ k := by simpa [Finset.mem_Icc] using hi
  have hi0 : 0 < i := by omega
  have hip : i < p := by omega
  have hunit : IsUnit ((i : R)) :=
    Scratch.HarmonicBinomialIdentityZMod.isUnit_natCast_zmod_prime_pow_of_pos_lt
      p 3 i hp (by norm_num) hi0 hip
  have hle : i ≤ p := by omega
  change (((p - i : ℕ) : R) * ((i : R)⁻¹)) = - (1 - (p : R) * ((i : R)⁻¹))
  rw [Nat.cast_sub hle]
  calc
    ((p : R) - (i : R)) * (i : R)⁻¹
        = (p : R) * (i : R)⁻¹ - (i : R) * (i : R)⁻¹ := by ring
    _ = (p : R) * (i : R)⁻¹ - 1 := by rw [ZMod.mul_inv_of_unit _ hunit]
    _ = - (1 - (p : R) * ((i : R)⁻¹)) := by ring

lemma prod_neg_one_sub_Icc (p k : ℕ) :
    (∏ i ∈ Finset.Icc 1 k,
      (- (1 - (p : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)))) =
      (-1 : ZMod (p ^ 3)) ^ k *
        ∏ i ∈ Finset.Icc 1 k,
          (1 - (p : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp
      · have htop : 1 ≤ k + 1 := by omega
        rw [Finset.prod_Icc_succ_top htop, Finset.prod_Icc_succ_top htop, ih]
        rw [pow_succ]
        ring


theorem alternating_choose_pointwise_second_order (p k : ℕ) (hp : p.Prime)
    (hk1 : 1 ≤ k) (hk : k < p) :
    (-1 : ZMod (p ^ 3)) ^ (k - 1) * ((Nat.choose (p - 1) k : ℕ) : ZMod (p ^ 3)) =
      -1 + (p : ZMod (p ^ 3)) * (∑ i ∈ Finset.Icc 1 k, ((i : ZMod (p ^ 3))⁻¹)) -
        ((p : ZMod (p ^ 3)) ^ 2) * E2Initial p k := by
  let R := ZMod (p ^ 3)
  have hc3 : ((p : R) ^ 3) = 0 := zmod_p_cast_pow_three_eq_zero p
  have hchoose := choose_pred_product_zmod p 3 k hp (by norm_num) hk
  have hfac :
      (∏ i ∈ Finset.Icc 1 k,
        (((p - i : ℕ) : R) * ((i : R)⁻¹))) =
        ∏ i ∈ Finset.Icc 1 k,
          (-(1 - (p : R) * ((i : R)⁻¹))) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact choose_pred_factor_eq_neg_one_sub p k i hp hi hk
  have hprodneg :
      (∏ i ∈ Finset.Icc 1 k,
          (-(1 - (p : R) * ((i : R)⁻¹)))) =
        (-1 : R) ^ k *
          ∏ i ∈ Finset.Icc 1 k,
            (1 - (p : R) * ((i : R)⁻¹)) := by
    exact prod_neg_one_sub_Icc p k
  have hsign : (-1 : R) ^ (k - 1) * ((-1 : R) ^ k) = -1 := by
    have hkpow : (-1 : R) ^ k = (-1 : R) ^ (k - 1) * (-1 : R) := by
      calc
        (-1 : R) ^ k = (-1 : R) ^ ((k - 1) + 1) := by congr 1; omega
        _ = (-1 : R) ^ (k - 1) * (-1 : R) := by rw [pow_add, pow_one]
    rw [hkpow]
    have hsq : ((-1 : R) ^ (k - 1)) ^ 2 = 1 := by
      rw [← pow_mul]
      rw [show (k - 1) * 2 = 2 * (k - 1) by omega]
      rw [pow_mul]
      have hneg : (-1 : R) ^ 2 = 1 := by ring
      rw [hneg, one_pow]
    calc
      (-1 : R) ^ (k - 1) * ((-1 : R) ^ (k - 1) * (-1 : R))
          = ((-1 : R) ^ (k - 1)) ^ 2 * (-1 : R) := by ring
      _ = -1 := by rw [hsq]; ring
  have hexp :
      (∏ i ∈ Finset.Icc 1 k, (1 - (p : R) * ((i : R)⁻¹))) =
        1 - (p : R) * (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) +
          (p : R) ^ 2 * E2Initial p k := by
    simpa [E2Initial, R] using
      (prod_Icc_one_sub_eq_second_order (R := R) (p : R)
        (fun i => ((i : R)⁻¹)) k hc3)
  calc
    (-1 : R) ^ (k - 1) * ((Nat.choose (p - 1) k : ℕ) : R)
        = (-1 : R) ^ (k - 1) *
            ((-1 : R) ^ k *
              ∏ i ∈ Finset.Icc 1 k,
                (1 - (p : R) * ((i : R)⁻¹))) := by rw [hchoose, hfac, hprodneg]
    _ = ((-1 : R) ^ (k - 1) * (-1 : R) ^ k) *
            (∏ i ∈ Finset.Icc 1 k,
                (1 - (p : R) * ((i : R)⁻¹))) := by ring
    _ = - (∏ i ∈ Finset.Icc 1 k,
                (1 - (p : R) * ((i : R)⁻¹))) := by rw [hsign]; ring
    _ = -1 + (p : R) * (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) -
        ((p : R) ^ 2) * E2Initial p k := by rw [hexp]; ring

lemma harmonic_initial_mul_inv_sq_eq_A_add_H3 (p : ℕ) :
    (∑ k ∈ Finset.Icc 1 (p - 1),
      (∑ i ∈ Finset.Icc 1 k, ((i : ZMod (p ^ 3))⁻¹)) *
        (((k : ZMod (p ^ 3))⁻¹) ^ 2)) = A p + H3 p := by
  let R := ZMod (p ^ 3)
  have hpoint : ∀ k ∈ Finset.Icc 1 (p - 1),
      (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) * (((k : R)⁻¹) ^ 2) =
        (∑ i ∈ Finset.Icc 1 (k - 1), ((i : R)⁻¹) * (((k : R)⁻¹) ^ 2)) +
          (((k : R)⁻¹) ^ 3) := by
    intro k hkmem
    have hk_bounds : 1 ≤ k ∧ k ≤ p - 1 := by simpa [Finset.mem_Icc] using hkmem
    have hk1 : 1 ≤ k := hk_bounds.1
    have hsplit :
        (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) =
          (∑ i ∈ Finset.Icc 1 (k - 1), ((i : R)⁻¹)) + ((k : R)⁻¹) := by
      have htop : 1 ≤ k - 1 + 1 := by omega
      have h := Finset.sum_Icc_succ_top (f := fun i => ((i : R)⁻¹)) htop
      simpa [Nat.sub_add_cancel hk1] using h
    rw [hsplit]
    rw [show (∑ i ∈ Finset.Icc 1 (k - 1), (i : R)⁻¹ * (k : R)⁻¹ ^ 2) =
        (∑ i ∈ Finset.Icc 1 (k - 1), (i : R)⁻¹) * (k : R)⁻¹ ^ 2 by
      rw [Finset.sum_mul]]
    ring
  calc
    (∑ k ∈ Finset.Icc 1 (p - 1),
      (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) * (((k : R)⁻¹) ^ 2))
        = ∑ k ∈ Finset.Icc 1 (p - 1),
            ((∑ i ∈ Finset.Icc 1 (k - 1), ((i : R)⁻¹) * (((k : R)⁻¹) ^ 2)) +
              (((k : R)⁻¹) ^ 3)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hpoint k hk
    _ = A p + H3 p := by
      simp [A, H3, R, Finset.sum_add_distrib]


theorem alternatingH2SecondEvaluation_of_prime (p : ℕ) (hp : p.Prime) :
    alternatingH2SecondEvaluation p := by
  let R := ZMod (p ^ 3)
  have hpoint : ∀ k ∈ Finset.Icc 1 (p - 1),
      (-1 : R) ^ (k - 1) * ((Nat.choose (p - 1) k : ℕ) : R) * (((k : R)⁻¹) ^ 2) =
        (-1 + (p : R) * (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) -
          ((p : R) ^ 2) * E2Initial p k) * (((k : R)⁻¹) ^ 2) := by
    intro k hkmem
    have hk_bounds : 1 ≤ k ∧ k ≤ p - 1 := by simpa [Finset.mem_Icc] using hkmem
    have hk1 : 1 ≤ k := hk_bounds.1
    have hkp : k < p := by omega
    rw [alternating_choose_pointwise_second_order p k hp hk1 hkp]
  have hsum : Scratch.HarmonicBinomialIdentityZMod.altBinomH2 p 3 (p - 1) =
      ∑ k ∈ Finset.Icc 1 (p - 1),
        (-1 + (p : R) * (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) -
          ((p : R) ^ 2) * E2Initial p k) * (((k : R)⁻¹) ^ 2) := by
    simp [Scratch.HarmonicBinomialIdentityZMod.altBinomH2, R]
    apply Finset.sum_congr rfl
    intro k hk
    exact hpoint k hk
  dsimp [alternatingH2SecondEvaluation]
  rw [hsum]
  have hdist :
      (∑ k ∈ Finset.Icc 1 (p - 1),
        (-1 + (p : R) * (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) -
          ((p : R) ^ 2) * E2Initial p k) * (((k : R)⁻¹) ^ 2)) =
        - H2 p + (p : R) *
          (∑ k ∈ Finset.Icc 1 (p - 1),
            (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) * (((k : R)⁻¹) ^ 2)) -
          ((p : R) ^ 2) * T p := by
    calc
      (∑ k ∈ Finset.Icc 1 (p - 1),
        (-1 + (p : R) * (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) -
          ((p : R) ^ 2) * E2Initial p k) * (((k : R)⁻¹) ^ 2))
          = ∑ k ∈ Finset.Icc 1 (p - 1),
              (-( ((k : R)⁻¹) ^ 2) +
                (p : R) * ((∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) * (((k : R)⁻¹) ^ 2)) -
                ((p : R) ^ 2) * (E2Initial p k * (((k : R)⁻¹) ^ 2))) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = - H2 p + (p : R) *
          (∑ k ∈ Finset.Icc 1 (p - 1),
            (∑ i ∈ Finset.Icc 1 k, ((i : R)⁻¹)) * (((k : R)⁻¹) ^ 2)) -
          ((p : R) ^ 2) * T p := by
            simp [H2, T, R, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hdist, harmonic_initial_mul_inv_sq_eq_A_add_H3]


theorem alternatingH2SecondEvaluation_prime_ge_seven (p : ℕ) (hp : p.Prime) (_hp7 : 7 ≤ p) :
    alternatingH2SecondEvaluation p :=
  alternatingH2SecondEvaluation_of_prime p hp


def keyDepthReducedVanishings (p : ℕ) : Prop :=
  (Scratch.HarmonicBinomialIdentityZMod.H1 p 3 (p - 1)) ^ 2 = (0 : ZMod (p ^ 3)) ∧
  (p : ZMod (p ^ 3)) * H3 p = 0 ∧
  ((p : ZMod (p ^ 3)) ^ 2) * T p = 0


lemma inv_sq_sum_upper_eq_half_zmodp (p h : ℕ) (hp : p.Prime) (hp_eq : p = 2 * h + 1) :
    (∑ i ∈ Finset.Icc (h + 1) (p - 1), (((i : ZMod p)⁻¹)^2)) =
      ∑ i ∈ Finset.Icc 1 h, (((i : ZMod p)⁻¹)^2) := by
  subst p
  haveI : Fact (Nat.Prime (2 * h + 1)) := ⟨hp⟩
  refine Finset.sum_bij (fun i _ => (2 * h + 1) - i) ?_ ?_ ?_ ?_
  · intro i hi
    simp [Finset.mem_Icc] at hi ⊢
    omega
  · intro a ha b hb hab
    simp [Finset.mem_Icc] at ha hb
    have hsub : 2 * h + 1 - a = 2 * h + 1 - b := hab
    omega
  · intro b hb
    refine ⟨(2 * h + 1) - b, ?_, ?_⟩
    · simp [Finset.mem_Icc] at hb ⊢
      omega
    · simp [Finset.mem_Icc] at hb
      change 2 * h + 1 - (2 * h + 1 - b) = b
      omega
  · intro i hi
    simp [Finset.mem_Icc] at hi
    have hpi : (((2 * h + 1) - i : ℕ) : ZMod (2 * h + 1)) = - (i : ZMod (2 * h + 1)) := by
      rw [Nat.cast_sub (by omega : i ≤ 2 * h + 1)]
      simp
    rw [hpi]
    have hinvneg : (- (i : ZMod (2 * h + 1)))⁻¹ = - ((i : ZMod (2 * h + 1))⁻¹) := inv_neg
    rw [hinvneg]
    ring

lemma inv_sq_sum_half_zmodp_zero (p h : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let f : ℕ → ZMod p := fun i => ((i : ZMod p)⁻¹)^2
  have hfull : (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^2) = 0 := by
    exact A357674Scratch.inv_pow_sum_Icc_zmodp_zero p 2 hp (by norm_num) (by omega)
  have hfilter := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p - 1)) (fun i => i ≤ h) f
  have hleft : (Finset.Icc 1 (p - 1)).filter (fun i => i ≤ h) = Finset.Icc 1 h := by
    ext i
    simp [Finset.mem_Icc]
    omega
  have hright : (Finset.Icc 1 (p - 1)).filter (fun i => ¬ i ≤ h) = Finset.Icc (h + 1) (p - 1) := by
    ext i
    simp [Finset.mem_Icc]
    omega
  rw [hleft, hright] at hfilter
  have hupper := inv_sq_sum_upper_eq_half_zmodp p h hp hp_eq
  dsimp [f] at hfilter
  rw [hupper] at hfilter
  rw [hfull] at hfilter
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hsum : (2 : ZMod p) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2) = 0 := by
    simpa [two_mul] using hfilter
  have h2inv : (2 : ZMod p)⁻¹ * (2 : ZMod p) = 1 := inv_mul_cancel₀ htwo_ne
  calc
    (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2)
        = 1 * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2) := by rw [one_mul]
    _ = ((2 : ZMod p)⁻¹ * (2 : ZMod p)) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2) := by
      rw [h2inv]
    _ = (2 : ZMod p)⁻¹ * ((2 : ZMod p) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2)) := by ring
    _ = 0 := by rw [hsum, mul_zero]

lemma castHom_half_inv_sq_sum (p h : ℕ) (hp : p.Prime) (hp_eq : p = 2 * h + 1) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
      (∑ i ∈ Finset.Icc 1 h, ((i : ZMod (p ^ 3))⁻¹)^2) =
    ∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_Icc] at hi
  exact A357674Scratch.castHom_inv_pow_nat p i 2 hp (by omega) (by omega)

lemma p_sq_mul_half_inv_sq_sum_zmodp3_zero (p h : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (p : ZMod (p ^ 3)) ^ 2 * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod (p ^ 3))⁻¹)^2) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply A357674Scratch.p_sq_mul_eq_zero_of_castHom_eq_zero p
  rw [castHom_half_inv_sq_sum p h hp hp_eq]
  exact inv_sq_sum_half_zmodp_zero p h hp hp5 hp_eq




lemma harmonic_one_square_zmodp3_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (Scratch.HarmonicBinomialIdentityZMod.H1 p 3 (p - 1)) ^ 2 = (0 : ZMod (p ^ 3)) := by
  have hne2 : p ≠ 2 := by omega
  rcases hp.odd_of_ne_two hne2 with ⟨h, hp_eq⟩
  subst p
  let R := ZMod ((2 * h + 1) ^ 3)
  let P : R := ((2 * h + 1 : ℕ) : R)
  let S2 : R := ∑ i ∈ Finset.Icc 1 h, ((i : R)⁻¹)^2
  let S3 : R := ∑ i ∈ Finset.Icc 1 h, ((i : R)⁻¹)^3
  have hp7' : 7 ≤ 2 * h + 1 := hp7
  have hsum_pair := A357674Scratch.prod_Icc_one_two_mul_pair_sum h (fun i => ((i : R)⁻¹))
  have htop : 2 * h + 1 - 1 = 2 * h := by omega
  have hH1 : Scratch.HarmonicBinomialIdentityZMod.H1 (2 * h + 1) 3 (2 * h + 1 - 1) = -P * S2 - P ^ 2 * S3 := by
    rw [Scratch.HarmonicBinomialIdentityZMod.H1, htop]
    rw [hsum_pair]
    dsimp [S2, S3, P, R]
    calc
      (∑ i ∈ Finset.Icc 1 h,
          ((i : ZMod ((2 * h + 1) ^ 3))⁻¹ + (((2 * h + 1 - i : ℕ) : ZMod ((2 * h + 1) ^ 3))⁻¹)))
          = ∑ i ∈ Finset.Icc 1 h,
              (- ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2 -
                ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^3) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [Finset.mem_Icc] at hi
            rw [A357674Scratch.inv_p_sub_expansion (2 * h + 1) i hp (by omega) (by omega : i < 2 * h + 1)]
            ring
      _ = - ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) *
              (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2) -
            ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
              (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^3) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS2zero := p_sq_mul_half_inv_sq_sum_zmodp3_zero (2 * h + 1) h hp (by omega : 5 ≤ 2 * h + 1) rfl
  have hP3 : P ^ 3 = 0 := by
    dsimp [P, R]
    exact A357674Scratch.p_pow_self_zmod_zero (2 * h + 1) 3
  have hP4 : P ^ 4 = 0 := by
    calc
      P ^ 4 = P ^ 3 * P := by ring
      _ = 0 := by rw [hP3, zero_mul]
  rw [hH1]
  calc
    (-P * S2 - P ^ 2 * S3) ^ 2
        = (P ^ 2 * S2) * S2 + 2 * P ^ 3 * S2 * S3 + P ^ 4 * S3 ^ 2 := by ring
    _ = 0 := by
      change P ^ 2 * S2 = 0 at hS2zero
      rw [hS2zero, hP3, hP4]
      ring

lemma p_mul_H3_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 3)) * H3 p = 0 := by
  simpa [H3] using A357674Scratch.harmonic_cube_zmodp3_p_mul_zero p hp hp7



def H112 (p : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ∑ j ∈ Finset.Icc 1 (k - 1),
      ∑ i ∈ Finset.Icc 1 (j - 1),
        ((i : ZMod p)⁻¹) * ((j : ZMod p)⁻¹) * (((k : ZMod p)⁻¹) ^ 2)


def H13 (p : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ∑ i ∈ Finset.Icc 1 (k - 1),
      ((i : ZMod p)⁻¹) * (((k : ZMod p)⁻¹) ^ 3)


def H31 (p : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ∑ i ∈ Finset.Icc 1 (k - 1),
      (((i : ZMod p)⁻¹) ^ 3) * ((k : ZMod p)⁻¹)

lemma castHom_E2Initial_zmodp (p k : ℕ) (hp : p.Prime) (_hk1 : 1 ≤ k) (hkp : k < p) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) (E2Initial p k) =
      (∑ j ∈ Finset.Icc 1 k,
        ∑ i ∈ Finset.Icc 1 (j - 1),
          ((i : ZMod p)⁻¹) * ((j : ZMod p)⁻¹)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [E2Initial, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjb : 1 ≤ j ∧ j ≤ k := by simpa [Finset.mem_Icc] using hj
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hib : 1 ≤ i ∧ i ≤ j - 1 := by simpa [Finset.mem_Icc] using hi
  rw [map_mul]
  have hiinv :
      ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
        ((i : ZMod (p ^ 3))⁻¹) = ((i : ZMod p)⁻¹) := by
    simpa using A357674Scratch.castHom_inv_pow_nat p i 1 hp (by omega) (by omega)
  have hjinv :
      ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
        ((j : ZMod (p ^ 3))⁻¹) = ((j : ZMod p)⁻¹) := by
    simpa using A357674Scratch.castHom_inv_pow_nat p j 1 hp (by omega) (by omega)
  rw [hiinv, hjinv]

lemma castHom_T_eq_H112_add_H13 (p : ℕ) (hp : p.Prime) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) (T p) =
      H112 p + H13 p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [T, map_sum]
  calc
    (∑ k ∈ Finset.Icc 1 (p - 1),
        ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
          (E2Initial p k * ((k : ZMod (p ^ 3))⁻¹) ^ 2))
        = ∑ k ∈ Finset.Icc 1 (p - 1),
            ((∑ j ∈ Finset.Icc 1 k,
                ∑ i ∈ Finset.Icc 1 (j - 1),
                  ((i : ZMod p)⁻¹) * ((j : ZMod p)⁻¹)) * (((k : ZMod p)⁻¹) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkb : 1 ≤ k ∧ k ≤ p - 1 := by simpa [Finset.mem_Icc] using hk
          rw [map_mul, castHom_E2Initial_zmodp p k hp hkb.1 (by omega)]
          rw [A357674Scratch.castHom_inv_pow_nat p k 2 hp (by omega) (by omega)]
    _ = ∑ k ∈ Finset.Icc 1 (p - 1),
            ((∑ j ∈ Finset.Icc 1 (k - 1),
                ∑ i ∈ Finset.Icc 1 (j - 1),
                  ((i : ZMod p)⁻¹) * ((j : ZMod p)⁻¹) * (((k : ZMod p)⁻¹) ^ 2)) +
              (∑ i ∈ Finset.Icc 1 (k - 1),
                  ((i : ZMod p)⁻¹) * (((k : ZMod p)⁻¹) ^ 3))) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkb : 1 ≤ k ∧ k ≤ p - 1 := by simpa [Finset.mem_Icc] using hk
          have hsplit :
              (∑ j ∈ Finset.Icc 1 k,
                ∑ i ∈ Finset.Icc 1 (j - 1),
                  ((i : ZMod p)⁻¹) * ((j : ZMod p)⁻¹)) =
                (∑ j ∈ Finset.Icc 1 (k - 1),
                  ∑ i ∈ Finset.Icc 1 (j - 1),
                    ((i : ZMod p)⁻¹) * ((j : ZMod p)⁻¹)) +
                  (∑ i ∈ Finset.Icc 1 (k - 1),
                    ((i : ZMod p)⁻¹) * ((k : ZMod p)⁻¹)) := by
            have htop : 1 ≤ k - 1 + 1 := by omega
            simpa [Nat.sub_add_cancel hkb.1] using
              (Finset.sum_Icc_succ_top (f := fun j =>
                ∑ i ∈ Finset.Icc 1 (j - 1), ((i : ZMod p)⁻¹) * ((j : ZMod p)⁻¹)) htop)
          rw [hsplit]
          rw [add_mul]
          congr 1
          · rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_mul]
          · rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = H112 p + H13 p := by
          simp [H112, H13, Finset.sum_add_distrib]

lemma H31_eq_H13 (p : ℕ) (hp : p.Prime) : H31 p = H13 p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos

  let S : Finset ℕ := Finset.Icc 1 (p - 1)
  let D : Finset (Σ k : ℕ, ℕ) := S.sigma (fun k => Finset.Icc 1 (k - 1))
  rw [H31, H13]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  change
      (∑ x ∈ D, (((x.2 : ZMod p)⁻¹) ^ 3) * ((x.1 : ZMod p)⁻¹)) =
        (∑ x ∈ D, ((x.2 : ZMod p)⁻¹) * (((x.1 : ZMod p)⁻¹) ^ 3))
  refine Finset.sum_bij' (fun x _ => ⟨p - x.2, p - x.1⟩)
      (fun x _ => ⟨p - x.2, p - x.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx ⊢
    omega
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx ⊢
    omega
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx
    have hpk : p - (p - k) = k := by omega
    have hpi : p - (p - i) = i := by omega
    simp [hpk, hpi]
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx
    have hpk : p - (p - k) = k := by omega
    have hpi : p - (p - i) = i := by omega
    simp [hpk, hpi]
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx
    have hkcast : ((p - k : ℕ) : ZMod p) = - (k : ZMod p) := by
      rw [Nat.cast_sub (by omega : k ≤ p)]
      simp
    have hicast : ((p - i : ℕ) : ZMod p) = - (i : ZMod p) := by
      rw [Nat.cast_sub (by omega : i ≤ p)]
      simp
    simp [hkcast, hicast, inv_neg]
    ring


theorem power_sum_stuffle_H13_H31 (p : ℕ) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)) *
      (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 3)) =
        H13 p + H31 p +
          (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (p - 1)
  let R := ZMod p
  let f : ℕ → R := fun i => ((i : R)⁻¹)
  let g : ℕ → R := fun i => ((i : R)⁻¹)^3
  have hsplit (b : ℕ) (hb : b ∈ S) :
      (∑ a ∈ S, f a * g b) =
        (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
        (f b * g b) +
        (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by
    have hlt : S.filter (fun a => a < b) = Finset.Icc 1 (b - 1) := by
      ext a
      simp [S, Finset.mem_Icc] at hb ⊢
      omega
    have hnotlt : S.filter (fun a => ¬ a < b) = Finset.Icc b (p - 1) := by
      ext a
      simp [S, Finset.mem_Icc] at hb ⊢
      omega
    have htail : Finset.Icc b (p - 1) = insert b (Finset.Icc (b + 1) (p - 1)) := by
      have hbS : 1 ≤ b ∧ b ≤ p - 1 := by simpa [S, Finset.mem_Icc] using hb
      have hb_le : b ≤ p - 1 := hbS.2
      ext a
      simp [Finset.mem_Icc]
      constructor
      · intro ha
        by_cases hab : a = b
        · exact Or.inl hab
        · exact Or.inr (by omega)
      · intro ha
        rcases ha with h | h
        · subst a
          exact ⟨le_rfl, hb_le⟩
        · exact ⟨by omega, h.2⟩
    have hbnot : b ∉ Finset.Icc (b + 1) (p - 1) := by
      simp [Finset.mem_Icc]
    calc
      (∑ a ∈ S, f a * g b)
          = (∑ a ∈ S.filter (fun a => a < b), f a * g b) +
              (∑ a ∈ S.filter (fun a => ¬ a < b), f a * g b) := by
            rw [← Finset.sum_filter_add_sum_filter_not S (fun a => a < b) (fun a => f a * g b)]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
              (∑ a ∈ Finset.Icc b (p - 1), f a * g b) := by rw [hlt, hnotlt]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
              (∑ a ∈ insert b (Finset.Icc (b + 1) (p - 1)), f a * g b) := by rw [htail]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
              (f b * g b + ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by
            rw [Finset.sum_insert hbnot]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
          (f b * g b) +
          (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by ring
  have hupper :
      (∑ b ∈ S, ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) = H31 p := by
    rw [H31]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    let D₁ : Finset (Σ b : ℕ, ℕ) := S.sigma (fun b => Finset.Icc (b + 1) (p - 1))
    let D₂ : Finset (Σ a : ℕ, ℕ) := S.sigma (fun a => Finset.Icc 1 (a - 1))
    change (∑ x ∈ D₁, f x.2 * g x.1) =
        (∑ x ∈ D₂, ((x.2 : R)⁻¹)^3 * ((x.1 : R)⁻¹))
    refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1⟩) (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨b, a⟩
      simp [D₁, D₂, S, Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx
      rcases x with ⟨a, b⟩
      simp [D₁, D₂, S, Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx
      cases x
      simp
    · intro x hx
      cases x
      simp
    · intro x hx
      rcases x with ⟨b, a⟩
      simp [f, g]
      ring
  have hdiag :
      (∑ b ∈ S, f b * g b) =
        (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [S, f, g]
    ring
  calc
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)) *
      (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 3))
        = ∑ b ∈ S, ∑ a ∈ S, f a * g b := by
            simp [S, f, g, Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    _ = ∑ b ∈ S,
          ((∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
            (f b * g b) +
            (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b)) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hsplit b hb
    _ = (∑ b ∈ S, ∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
          (∑ b ∈ S, f b * g b) +
          (∑ b ∈ S, ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = H13 p + H31 p +
          (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
          rw [hupper, hdiag]
          simp [H13, S, f, g]
          ring

lemma H13_eq_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : H13 p = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP1 := A357674Scratch.inv_sum_Icc_zmodp_zero p hp hp7
  have hP3 := A357674Scratch.inv_cube_sum_Icc_zmodp_zero p hp hp7
  have hP4 := A357674Scratch.inv_fourth_sum_Icc_zmodp_zero p hp hp7
  have hstuff := power_sum_stuffle_H13_H31 p
  rw [hP1, zero_mul, H31_eq_H13 p hp, hP4] at hstuff
  have htwo : (2 : ZMod p) * H13 p = 0 := by
    simpa [two_mul, add_assoc] using hstuff.symm
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact (mul_eq_zero.mp htwo).resolve_left htwo_ne



theorem p_sq_mul_T_zero_of_H112_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (h112 : H112 p = 0) :
    ((p : ZMod (p ^ 3)) ^ 2) * T p = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply A357674Scratch.p_sq_mul_eq_zero_of_castHom_eq_zero p
  rw [castHom_T_eq_H112_add_H13 p hp, h112, H13_eq_zero p hp hp7, zero_add]



theorem keyDepthReducedVanishings_of_T
    (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hT : ((p : ZMod (p ^ 3)) ^ 2) * T p = 0) :
    keyDepthReducedVanishings p := by
  exact ⟨harmonic_one_square_zmodp3_zero p hp hp7, p_mul_H3_zero p hp hp7, hT⟩











theorem key_depth_congruence_prime_ge_seven_of_reduced_assumptions
    (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hEval : alternatingH2SecondEvaluation p)
    (hVanish : keyDepthReducedVanishings p) :
    keyDepthCongruence p := by
  let R := ZMod (p ^ 3)
  let S : R := Scratch.HarmonicBinomialIdentityZMod.altBinomH2 p 3 (p - 1)
  let X : R :=
    (Scratch.HarmonicBinomialIdentityZMod.H1 p 3 (p - 1)) ^ 2 + H2 p
  have hp2 : p ≠ 2 := by omega
  have hn : p - 1 < p := by omega
  have h2unit : IsUnit (2 : R) :=
    Scratch.HarmonicBinomialIdentityZMod.isUnit_two_zmod_prime_pow_of_ne_two
      p 3 hp (by norm_num) hp2
  have hAltRaw : S = X * (2 : R)⁻¹ := by
    dsimp [S, X, R]
    simpa [H2, Scratch.HarmonicBinomialIdentityZMod.H2] using
      (Scratch.HarmonicBinomialIdentityZMod.alt_binom_H2_zmod_odd
        p 3 (p - 1) hp (by norm_num) hn hp2)
  have hAltTwo : (2 : R) * S = X := by
    rw [hAltRaw]
    calc
      (2 : R) * (X * (2 : R)⁻¹) = X * ((2 : R) * (2 : R)⁻¹) := by ring
      _ = X := by rw [ZMod.mul_inv_of_unit _ h2unit, mul_one]
  have hEval' :
      S = - H2 p + (p : R) * (A p + H3 p) - ((p : R) ^ 2) * T p := by
    dsimp [S, R]
    simpa [alternatingH2SecondEvaluation] using hEval
  have hCompare :
      (2 : R) * (- H2 p + (p : R) * (A p + H3 p) - ((p : R) ^ 2) * T p) =
        (Scratch.HarmonicBinomialIdentityZMod.H1 p 3 (p - 1)) ^ 2 + H2 p := by
    calc
      (2 : R) * (- H2 p + (p : R) * (A p + H3 p) - ((p : R) ^ 2) * T p)
          = (2 : R) * S := by rw [hEval']
      _ = X := hAltTwo
      _ = (Scratch.HarmonicBinomialIdentityZMod.H1 p 3 (p - 1)) ^ 2 + H2 p := by
        dsimp [X]
  rcases hVanish with ⟨hH1sq, hpH3, hp2T⟩
  have hReduced :
      - (2 : R) * H2 p + (2 : R) * (p : R) * A p = H2 p := by
    calc
      - (2 : R) * H2 p + (2 : R) * (p : R) * A p
          = (2 : R) * (- H2 p + (p : R) * (A p + H3 p) - ((p : R) ^ 2) * T p) := by
            calc
              - (2 : R) * H2 p + (2 : R) * (p : R) * A p
                  = - (2 : R) * H2 p + (2 : R) * (p : R) * A p +
                      (2 : R) * ((p : R) * H3 p) - (2 : R) * (((p : R) ^ 2) * T p) := by
                    rw [hpH3, hp2T]
                    ring
              _ = (2 : R) * (- H2 p + (p : R) * (A p + H3 p) - ((p : R) ^ 2) * T p) := by
                    ring
      _ = (Scratch.HarmonicBinomialIdentityZMod.H1 p 3 (p - 1)) ^ 2 + H2 p := hCompare
      _ = H2 p := by rw [hH1sq, zero_add]
  have hTargetSymm : (2 : R) * (p : R) * A p = (3 : R) * H2 p := by
    calc
      (2 : R) * (p : R) * A p
          = (- (2 : R) * H2 p + (2 : R) * (p : R) * A p) + (2 : R) * H2 p := by ring
      _ = H2 p + (2 : R) * H2 p := by rw [hReduced]
      _ = (3 : R) * H2 p := by ring
  dsimp [keyDepthCongruence, R] at hTargetSymm ⊢
  exact hTargetSymm.symm


theorem key_depth_congruence_prime_ge_seven
    (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hEval : alternatingH2SecondEvaluation p)
    (hVanish : keyDepthReducedVanishings p) :
    keyDepthCongruence p :=
  key_depth_congruence_prime_ge_seven_of_reduced_assumptions p hp hp7 hEval hVanish

end KeyDepthCongruencePrimeGeSevenScratch
end Scratch



















namespace Scratch
namespace TailMasterCongruenceProgress


def Tz (p : ℕ) : ZMod (p ^ 5) :=
  (((3 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 5))


def Bz (p : ℕ) : ZMod (p ^ 5) :=
  (((2 * p - 1).choose (p - 1) : ℕ) : ZMod (p ^ 5))


def lowerH1 (p k : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod (p ^ 5))⁻¹)


def lowerH2 (p k : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 (k - 1), (((i : ZMod (p ^ 5))⁻¹) ^ 2)


def lowerLocal (p k : ℕ) : ZMod (p ^ 5) :=
  let R := ZMod (p ^ 5)
  (p : R) ^ 2 * (((k : R)⁻¹) ^ 2) *
    (1 + (2 : R) * (p : R) * lowerH1 p k +
      (p : R) ^ 2 * ((2 : R) * (lowerH1 p k) ^ 2 - lowerH2 p k))


def upperH1 (p l : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 (l - 1), ((i : ZMod (p ^ 5))⁻¹)


def upperH2 (p l : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 (l - 1), (((i : ZMod (p ^ 5))⁻¹) ^ 2)


def upperLocal (p l : ℕ) : ZMod (p ^ 5) :=
  let R := ZMod (p ^ 5)
  (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) *
    (1 + (2 : R) * (p : R) * upperH1 p l + (6 : R) * (p : R) * ((l : R)⁻¹) +
      (p : R) ^ 2 * ((2 : R) * (upperH1 p l) ^ 2 +
        (12 : R) * upperH1 p l * ((l : R)⁻¹) +
        (27 : R) * (((l : R)⁻¹) ^ 2) + (5 : R) * upperH2 p l))



def S2Z (p : ℕ) : ZMod (p ^ 5) :=
  ∑ k ∈ Finset.range (2 * p + 1),
    ((((p + k - 1).choose k : ℕ) : ZMod (p ^ 5)) ^ 2)


def lowerSummand (p k : ℕ) : ZMod (p ^ 5) :=
  ((((p + k - 1).choose k : ℕ) : ZMod (p ^ 5)) ^ 2)


def upperSummand (p l : ℕ) : ZMod (p ^ 5) :=
  ((((3 * p - l - 1).choose (p - 1) : ℕ) : ZMod (p ^ 5)) ^ 2)


def lowerBlock (p : ℕ) : ZMod (p ^ 5) :=
  ∑ k ∈ Finset.range p, if k = 0 then (1 : ZMod (p ^ 5)) else lowerLocal p k


def upperBlock (p : ℕ) : ZMod (p ^ 5) :=
  ∑ j ∈ Finset.range p,
    if j = 0 then (Bz p) ^ 2 else upperLocal p (p - j)


def tailSum (p : ℕ) : ZMod (p ^ 5) :=
  (∑ k ∈ Finset.Icc 1 (p - 1), lowerLocal p k) +
    (∑ l ∈ Finset.Icc 1 (p - 1), upperLocal p l)



def Hpow (p m : ℕ) : ZMod (p ^ 5) :=
  ∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod (p ^ 5))⁻¹) ^ m)


def prefixH12 (p : ℕ) : ZMod (p ^ 5) :=
  ∑ k ∈ Finset.Icc 1 (p - 1), lowerH1 p k * (((k : ZMod (p ^ 5))⁻¹) ^ 2)


def prefixH112 (p : ℕ) : ZMod (p ^ 5) :=
  ∑ k ∈ Finset.Icc 1 (p - 1), (lowerH1 p k) ^ 2 * (((k : ZMod (p ^ 5))⁻¹) ^ 2)


def prefixH13 (p : ℕ) : ZMod (p ^ 5) :=
  ∑ k ∈ Finset.Icc 1 (p - 1), lowerH1 p k * (((k : ZMod (p ^ 5))⁻¹) ^ 3)


def prefixH22 (p : ℕ) : ZMod (p ^ 5) :=
  ∑ k ∈ Finset.Icc 1 (p - 1), lowerH2 p k * (((k : ZMod (p ^ 5))⁻¹) ^ 2)

lemma lowerLocal_eq_collected (p k : ℕ) :
    lowerLocal p k =
      let R := ZMod (p ^ 5)
      (p : R) ^ 2 * (((k : R)⁻¹) ^ 2) +
      (2 : R) * (p : R) ^ 3 * (lowerH1 p k * (((k : R)⁻¹) ^ 2)) +
      (p : R) ^ 4 * (((2 : R) * (lowerH1 p k) ^ 2 - lowerH2 p k) * (((k : R)⁻¹) ^ 2)) := by
  dsimp [lowerLocal]
  ring

lemma upperLocal_eq_collected (p l : ℕ) :
    upperLocal p l =
      let R := ZMod (p ^ 5)
      (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) +
      (8 : R) * (p : R) ^ 3 * (upperH1 p l * (((l : R)⁻¹) ^ 2)) +
      (24 : R) * (p : R) ^ 3 * (((l : R)⁻¹) ^ 3) +
      (4 : R) * (p : R) ^ 4 *
        (((2 : R) * (upperH1 p l) ^ 2 +
          (12 : R) * upperH1 p l * ((l : R)⁻¹) +
          (27 : R) * (((l : R)⁻¹) ^ 2) + (5 : R) * upperH2 p l) *
          (((l : R)⁻¹) ^ 2)) := by
  dsimp [upperLocal]
  ring



lemma isUnit_natCast_zmod_prime_pow_of_pos_lt (p r i : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hi0 : 0 < i) (hip : i < p) : IsUnit (i : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    exact not_le_of_gt hip (Nat.le_of_dvd hi0 hdiv))

lemma natCast_inv_mul_eq_one (p r i : ℕ) (hp : p.Prime) (hr : 0 < r)
    (hi0 : 0 < i) (hip : i < p) :
    ((i : ZMod (p ^ r))⁻¹) * (i : ZMod (p ^ r)) = 1 := by
  exact ZMod.inv_mul_of_unit _
    (isUnit_natCast_zmod_prime_pow_of_pos_lt p r i hp hr hi0 hip)


lemma choose_prod_aux_general (a p r n : ℕ) (hp : p.Prime) (hr : 0 < r) (hn : n < p) :
    (((a * p + n).choose n : ℕ) : ZMod (p ^ r)) =
      ∏ i ∈ Finset.Icc 1 n,
        (1 + ((a * p : ℕ) : ZMod (p ^ r)) * (i : ZMod (p ^ r))⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnlt : n < p := by omega
      have hsuccpos : 0 < n + 1 := by omega
      have hsucc_lt : n + 1 < p := hn
      have hunit : IsUnit ((n + 1 : ℕ) : ZMod (p ^ r)) :=
        isUnit_natCast_zmod_prime_pow_of_pos_lt p r (n + 1) hp hr hsuccpos hsucc_lt
      have hrec := ih hnlt
      have hchoose := Nat.add_one_mul_choose_eq (a * p + n) n
      have hcast : ((a * p + n + 1 : ℕ) : ZMod (p ^ r)) *
            (((a * p + n).choose n : ℕ) : ZMod (p ^ r)) =
          (((a * p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) *
            ((n + 1 : ℕ) : ZMod (p ^ r)) := by
        simpa [Nat.cast_mul] using congrArg (fun x : ℕ => (x : ZMod (p ^ r))) hchoose
      have hstep : (((a * p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) =
          (((a * p + n).choose n : ℕ) : ZMod (p ^ r)) *
            (((a * p + n + 1 : ℕ) : ZMod (p ^ r)) *
              ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
        calc
          (((a * p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r))
              = (((a * p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) *
                  (((n + 1 : ℕ) : ZMod (p ^ r)) *
                    ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by
                    rw [ZMod.mul_inv_of_unit _ hunit, mul_one]
          _ = ((((a * p + n + 1).choose (n + 1) : ℕ) : ZMod (p ^ r)) *
                  ((n + 1 : ℕ) : ZMod (p ^ r))) *
                  ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by ring_nf
          _ = (((a * p + n + 1 : ℕ) : ZMod (p ^ r)) *
                  (((a * p + n).choose n : ℕ) : ZMod (p ^ r))) *
                  ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹ := by rw [← hcast]
          _ = (((a * p + n).choose n : ℕ) : ZMod (p ^ r)) *
              (((a * p + n + 1 : ℕ) : ZMod (p ^ r)) *
                ((n + 1 : ℕ) : ZMod (p ^ r))⁻¹) := by ring_nf
      have htop : a * p + (n + 1) = a * p + n + 1 := by omega
      rw [htop]
      rw [hstep, hrec]
      rw [Finset.prod_Icc_succ_top hsuccpos]
      congr 1
      have hcasttop : ((a * p + n + 1 : ℕ) : ZMod (p ^ r)) =
          ((a * p : ℕ) : ZMod (p ^ r)) + ((n + 1 : ℕ) : ZMod (p ^ r)) := by
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring
      rw [hcasttop]
      rw [add_mul, ZMod.mul_inv_of_unit _ hunit]
      ring

lemma Bz_prod (p : ℕ) (hp : p.Prime) :
    Bz p = ∏ i ∈ Finset.Icc 1 (p - 1),
      (1 + ((p : ℕ) : ZMod (p ^ 5)) * (i : ZMod (p ^ 5))⁻¹) := by
  have hp0 : 0 < p := hp.pos
  have h := choose_prod_aux_general 1 p 5 (p - 1) hp (by norm_num) (by omega)
  have htop : p + (p - 1) = 2 * p - 1 := by omega
  simpa [Bz, htop, one_mul] using h

lemma Tz_prod (p : ℕ) (hp : p.Prime) :
    Tz p = ∏ i ∈ Finset.Icc 1 (p - 1),
      (1 + (((2 * p : ℕ) : ZMod (p ^ 5))) * (i : ZMod (p ^ 5))⁻¹) := by
  have hp0 : 0 < p := hp.pos
  have h := choose_prod_aux_general 2 p 5 (p - 1) hp (by norm_num) (by omega)
  have htop : 2 * p + (p - 1) = 3 * p - 1 := by omega
  simpa [Tz, htop] using h

section ProductExpansion

variable {α R : Type*} [CommRing R]


def listESymm2 : List α → (α → R) → R
  | [], _ => 0
  | a :: t, f => f a * (t.map f).sum + listESymm2 t f


def listESymm3 : List α → (α → R) → R
  | [], _ => 0
  | a :: t, f => f a * listESymm2 t f + listESymm3 t f


def listESymm4 : List α → (α → R) → R
  | [], _ => 0
  | a :: t, f => f a * listESymm3 t f + listESymm4 t f


def listPowerSum (l : List α) (f : α → R) (m : ℕ) : R :=
  (l.map (fun a => (f a) ^ m)).sum


lemma two_mul_listESymm2_eq_power_sums (l : List α) (f : α → R) :
    (2 : R) * listESymm2 l f = (listPowerSum l f 1) ^ 2 - listPowerSum l f 2 := by
  induction l with
  | nil => simp [listESymm2, listPowerSum]
  | cons a t ih =>
      simp [listESymm2, listPowerSum] at ih ⊢
      linear_combination ih


lemma six_mul_listESymm3_eq_power_sums (l : List α) (f : α → R) :
    (6 : R) * listESymm3 l f =
      (listPowerSum l f 1) ^ 3 - (3 : R) * listPowerSum l f 1 * listPowerSum l f 2 +
        (2 : R) * listPowerSum l f 3 := by
  induction l with
  | nil => simp [listESymm3, listPowerSum]
  | cons a t ih =>
      have h2 := two_mul_listESymm2_eq_power_sums (l := t) (f := f)
      simp [listESymm3, listPowerSum] at ih h2 ⊢
      linear_combination (3 * f a) * h2 + ih


lemma twentyfour_mul_listESymm4_eq_power_sums (l : List α) (f : α → R) :
    (24 : R) * listESymm4 l f =
      (listPowerSum l f 1) ^ 4 - (6 : R) * (listPowerSum l f 1) ^ 2 * listPowerSum l f 2 +
        (3 : R) * (listPowerSum l f 2) ^ 2 +
        (8 : R) * listPowerSum l f 1 * listPowerSum l f 3 -
        (6 : R) * listPowerSum l f 4 := by
  induction l with
  | nil => simp [listESymm4, listPowerSum]
  | cons a t ih =>
      have h3 := six_mul_listESymm3_eq_power_sums (l := t) (f := f)
      simp [listESymm4, listPowerSum] at ih h3 ⊢
      linear_combination (4 * f a) * h3 + ih




theorem list_prod_one_add_eq_of_fifth_zero (l : List α) (c : R) (f : α → R)
    (hc5 : c ^ 5 = 0) :
    (l.map (fun i => 1 + c * f i)).prod =
      1 + c * (l.map f).sum + c ^ 2 * listESymm2 l f +
        c ^ 3 * listESymm3 l f + c ^ 4 * listESymm4 l f := by
  induction l with
  | nil => simp [listESymm2, listESymm3, listESymm4]
  | cons a t ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons,
        listESymm2, listESymm3, listESymm4]
      rw [ih]
      have hc6 : c ^ 6 = 0 := by
        calc c ^ 6 = c ^ 5 * c := by ring
          _ = 0 := by rw [hc5, zero_mul]
      ring_nf
      simp [hc5]


theorem finset_prod_one_add_eq_of_fifth_zero (s : Finset α) (c : R) (f : α → R)
    (hc5 : c ^ 5 = 0) :
    (∏ i ∈ s, (1 + c * f i)) =
      1 + c * (∑ i ∈ s, f i) + c ^ 2 * listESymm2 s.toList f +
        c ^ 3 * listESymm3 s.toList f + c ^ 4 * listESymm4 s.toList f := by
  classical
  have h := list_prod_one_add_eq_of_fifth_zero (α := α) (R := R) s.toList c f hc5
  have hprod : (s.toList.map (fun i => 1 + c * f i)).prod = ∏ i ∈ s, (1 + c * f i) := by
    simp
  have hsum : (s.toList.map f).sum = ∑ i ∈ s, f i := by
    simp
  rw [hprod, hsum] at h
  simpa using h

end ProductExpansion

lemma p_pow_five_zmod_zero (p : ℕ) : ((p : ZMod (p ^ 5)) ^ 5) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]

lemma nat_mul_p_pow_five_zmod_zero (a p : ℕ) :
    ((((a * p : ℕ) : ZMod (p ^ 5))) ^ 5) = 0 := by
  have hp5 : ((p : ZMod (p ^ 5)) ^ 5) = 0 := p_pow_five_zmod_zero p
  have hcast : (((a * p : ℕ) : ZMod (p ^ 5))) = (a : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) := by
    norm_num [Nat.cast_mul]
  rw [hcast]
  rw [mul_pow, hp5, mul_zero]


noncomputable def endpointPoly (p a : ℕ) : ZMod (p ^ 5) :=
  let R := ZMod (p ^ 5)
  let s := Finset.Icc 1 (p - 1)
  let c : R := ((a * p : ℕ) : R)
  let f : ℕ → R := fun i => (i : R)⁻¹
  1 + c * (∑ i ∈ s, f i) + c ^ 2 * listESymm2 s.toList f +
    c ^ 3 * listESymm3 s.toList f + c ^ 4 * listESymm4 s.toList f

lemma endpoint_prod_eq_endpointPoly (p a : ℕ) :
    (∏ i ∈ Finset.Icc 1 (p - 1),
      (1 + (((a * p : ℕ) : ZMod (p ^ 5))) * (i : ZMod (p ^ 5))⁻¹)) = endpointPoly p a := by
  dsimp [endpointPoly]
  exact finset_prod_one_add_eq_of_fifth_zero (s := Finset.Icc 1 (p - 1))
    (c := (((a * p : ℕ) : ZMod (p ^ 5))))
    (f := fun i : ℕ => (i : ZMod (p ^ 5))⁻¹)
    (nat_mul_p_pow_five_zmod_zero a p)

lemma Bz_eq_endpointPoly (p : ℕ) (hp : p.Prime) : Bz p = endpointPoly p 1 := by
  rw [Bz_prod p hp]
  simpa [one_mul] using endpoint_prod_eq_endpointPoly p 1

lemma Tz_eq_endpointPoly (p : ℕ) (hp : p.Prime) : Tz p = endpointPoly p 2 := by
  rw [Tz_prod p hp]
  exact endpoint_prod_eq_endpointPoly p 2





noncomputable def tailHarmonicRHS (p : ℕ) : ZMod (p ^ 5) :=
  -(2 : ZMod (p ^ 5)) * (endpointPoly p 1 - 1) -
    (6 : ZMod (p ^ 5)) * (endpointPoly p 2 - 1)





lemma tailSum_eq_sum_collected_locals (p : ℕ) :
    tailSum p =
      (∑ k ∈ Finset.Icc 1 (p - 1),
        (let R := ZMod (p ^ 5)
        (p : R) ^ 2 * (((k : R)⁻¹) ^ 2) +
        (2 : R) * (p : R) ^ 3 * (lowerH1 p k * (((k : R)⁻¹) ^ 2)) +
        (p : R) ^ 4 * (((2 : R) * (lowerH1 p k) ^ 2 - lowerH2 p k) * (((k : R)⁻¹) ^ 2)))) +
      (∑ l ∈ Finset.Icc 1 (p - 1),
        (let R := ZMod (p ^ 5)
        (4 : R) * (p : R) ^ 2 * (((l : R)⁻¹) ^ 2) +
        (8 : R) * (p : R) ^ 3 * (upperH1 p l * (((l : R)⁻¹) ^ 2)) +
        (24 : R) * (p : R) ^ 3 * (((l : R)⁻¹) ^ 3) +
        (4 : R) * (p : R) ^ 4 *
          (((2 : R) * (upperH1 p l) ^ 2 +
            (12 : R) * upperH1 p l * ((l : R)⁻¹) +
            (27 : R) * (((l : R)⁻¹) ^ 2) + (5 : R) * upperH2 p l) *
            (((l : R)⁻¹) ^ 2)))) := by
  dsimp [tailSum]
  rw [Finset.sum_congr rfl (fun k hk => lowerLocal_eq_collected p k)]
  rw [Finset.sum_congr rfl (fun k hk => upperLocal_eq_collected p k)]




lemma tailSum_eq_collected_harmonics (p : ℕ) :
    tailSum p =
      let R := ZMod (p ^ 5)
      (5 : R) * (p : R)^2 * Hpow p 2 +
      (10 : R) * (p : R)^3 * prefixH12 p +
      (24 : R) * (p : R)^3 * Hpow p 3 +
      (p : R)^4 * ((10 : R) * prefixH112 p + (19 : R) * prefixH22 p +
        (48 : R) * prefixH13 p + (108 : R) * Hpow p 4) := by
  let R := ZMod (p ^ 5)
  let s := Finset.Icc 1 (p - 1)
  rw [tailSum_eq_sum_collected_locals p]
  dsimp [Hpow, prefixH12, prefixH112, prefixH13, prefixH22, lowerH1, lowerH2, upperH1, upperH2]
  repeat rw [mul_add]
  simp only [Finset.mul_sum]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  set pp : ZMod (p ^ 5) := (p : ZMod (p ^ 5))
  set x : ZMod (p ^ 5) := ((k : ZMod (p ^ 5))⁻¹)
  set A : ZMod (p ^ 5) := ∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod (p ^ 5))⁻¹) with hA
  set B : ZMod (p ^ 5) := ∑ i ∈ Finset.Icc 1 (k - 1), (((i : ZMod (p ^ 5))⁻¹) ^ 2) with hB
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [← hA, ← hB]
  ring











lemma collected_tail_endpoint_algebra_24 {R : Type*} [CommRing R]
    (p P1 P2 P3 P4 A W112 W22 W13 e2 e3 e4 : R)
    (hE2 : (2 : R) * e2 = P1^2 - P2)
    (hP1sq : p^2 * P1^2 = 0)
    (hP3 : p^3 * P3 = 0)
    (hW112 : p^4 * W112 = 0)
    (hW22 : p^4 * W22 = 0)
    (hW13 : p^4 * W13 = 0)
    (hW4 : p^4 * P4 = 0)
    (hE3zero : p^3 * e3 = 0)
    (hE4zero : p^4 * e4 = 0)
    (hRel : (2 : R)*p*P1 + p^2*P2 = 0)
    (hKey : (3 : R)*p^2*P2 = (2 : R)*p^3*A) :
    (24 : R) *
      ((5 : R)*p^2*P2 + (10 : R)*p^3*A + (24 : R)*p^3*P3 +
        p^4*((10 : R)*W112 + (19 : R)*W22 + (48 : R)*W13 + (108 : R)*P4)) =
    (24 : R) *
      (-(14 : R)*p*P1 - (26 : R)*p^2*e2 - (50 : R)*p^3*e3 - (98 : R)*p^4*e4) := by
  have hKey' : (10 : R) * p^3 * A = (15 : R) * p^2 * P2 := by
    calc
      (10 : R) * p^3 * A = (5 : R) * ((2 : R) * p^3 * A) := by ring
      _ = (5 : R) * ((3 : R) * p^2 * P2) := by rw [← hKey]
      _ = (15 : R) * p^2 * P2 := by ring
  have hRel' : -(336 : R) * p * P1 = (168 : R) * p^2 * P2 := by
    calc
      -(336 : R) * p * P1 = -(168 : R) * ((2 : R) * p * P1) := by ring
      _ = -(168 : R) * (-(p^2 * P2)) := by
        have hh : (2 : R) * p * P1 = -(p^2 * P2) := by
          exact eq_neg_of_add_eq_zero_left hRel
        rw [hh]
      _ = (168 : R) * p^2 * P2 := by ring
  have hP3L : (576 : R) * p^3 * P3 = 0 := by
    calc (576 : R) * p^3 * P3 = (576 : R) * (p^3 * P3) := by ring
      _ = 0 := by rw [hP3, mul_zero]
  have hW112L : (240 : R) * p^4 * W112 = 0 := by
    calc (240 : R) * p^4 * W112 = (240 : R) * (p^4 * W112) := by ring
      _ = 0 := by rw [hW112, mul_zero]
  have hW22L : (456 : R) * p^4 * W22 = 0 := by
    calc (456 : R) * p^4 * W22 = (456 : R) * (p^4 * W22) := by ring
      _ = 0 := by rw [hW22, mul_zero]
  have hW13L : (1152 : R) * p^4 * W13 = 0 := by
    calc (1152 : R) * p^4 * W13 = (1152 : R) * (p^4 * W13) := by ring
      _ = 0 := by rw [hW13, mul_zero]
  have hW4L : (2592 : R) * p^4 * P4 = 0 := by
    calc (2592 : R) * p^4 * P4 = (2592 : R) * (p^4 * P4) := by ring
      _ = 0 := by rw [hW4, mul_zero]
  have hE3zero' : (1200 : R) * (p^3 * e3) = 0 := by rw [hE3zero, mul_zero]
  have hE4zero' : (2352 : R) * (p^4 * e4) = 0 := by rw [hE4zero, mul_zero]
  calc
    (24 : R) *
      ((5 : R)*p^2*P2 + (10 : R)*p^3*A + (24 : R)*p^3*P3 +
        p^4*((10 : R)*W112 + (19 : R)*W22 + (48 : R)*W13 + (108 : R)*P4))
        = (480 : R) * p^2 * P2 := by
          rw [hKey']
          linear_combination hP3L + hW112L + hW22L + hW13L + hW4L
    _ = (24 : R) *
      (-(14 : R)*p*P1 - (26 : R)*p^2*e2 - (50 : R)*p^3*e3 - (98 : R)*p^4*e4) := by
          rw [show (24 : R) * (-(14 : R)*p*P1 - (26 : R)*p^2*e2 - (50 : R)*p^3*e3 - (98 : R)*p^4*e4) =
              -(336 : R)*p*P1 - (312 : R)*p^2*((2 : R)*e2) - (1200 : R)*(p^3*e3) - (2352 : R)*(p^4*e4) by ring]
          rw [hE2]
          linear_combination (168 : R) * hRel + (312 : R) * hP1sq + hE3zero' + hE4zero'




lemma tailHarmonicRHS_eq_endpoint_coeffs (p : ℕ) :
    tailHarmonicRHS p =
      -(14 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) *
          (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod (p ^ 5))⁻¹)) -
        (26 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 2 *
          listESymm2 (Finset.Icc 1 (p - 1)).toList (fun i : ℕ => (i : ZMod (p ^ 5))⁻¹) -
        (50 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 3 *
          listESymm3 (Finset.Icc 1 (p - 1)).toList (fun i : ℕ => (i : ZMod (p ^ 5))⁻¹) -
        (98 : ZMod (p ^ 5)) * (p : ZMod (p ^ 5)) ^ 4 *
          listESymm4 (Finset.Icc 1 (p - 1)).toList (fun i : ℕ => (i : ZMod (p ^ 5))⁻¹) := by
  dsimp [tailHarmonicRHS, endpointPoly]
  norm_num [Nat.cast_mul]
  ring


lemma isUnit_natCast_zmod_prime_pow_of_coprime (p r n : ℕ) (hr : 0 < r) (hcop : Nat.Coprime n p) :
    IsUnit (n : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_pow_right_iff hr]
  exact hcop

lemma isUnit_24_zmod_prime_pow_five (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    IsUnit (24 : ZMod (p ^ 5)) := by
  apply isUnit_natCast_zmod_prime_pow_of_coprime <;> try norm_num
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    have hdiv' : p ∣ 2^3 * 3 := by simpa using hdiv
    rcases (Nat.Prime.dvd_mul hp).1 hdiv' with h2pow | h3
    · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h2pow
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2)).1 h2
      omega
    · have hp3eq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).1 h3
      omega)


lemma isUnit_6_zmod_prime_pow_five (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    IsUnit (6 : ZMod (p ^ 5)) := by
  apply isUnit_natCast_zmod_prime_pow_of_coprime <;> try norm_num
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    have hdiv' : p ∣ 2 * 3 := by simpa using hdiv
    rcases (Nat.Prime.dvd_mul hp).1 hdiv' with h2 | h3
    · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2)).1 h2
      omega
    · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)).1 h3
      omega)









lemma p_four_mul_eq_zero_of_castHom_eq_zero (p : ℕ) [NeZero p] (x : ZMod (p ^ 5))
    (h : ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p) x = 0) :
    (p : ZMod (p ^ 5)) ^ 4 * x = 0 := by
  rw [← ZMod.natCast_zmod_val x]
  have hx0 : ((x.val : ℕ) : ZMod p) = 0 := by
    simpa [ZMod.castHom_apply] using h
  have hdvd : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).1 hx0
  rcases hdvd with ⟨k, hk⟩
  rw [hk]
  norm_num [Nat.cast_mul, Nat.cast_pow]
  have hp5zero : (p : ZMod (p ^ 5)) ^ 5 = 0 := p_pow_five_zmod_zero p
  ring_nf
  rw [hp5zero]
  ring

lemma Icc_one_pred_eq_range_erase_zero (p : ℕ) (hp0 : 0 < p) :
    Finset.Icc 1 (p - 1) = (Finset.range p).erase 0 := by
  ext i
  simp [Finset.mem_Icc]
  omega

lemma sum_range_zmod_eq_sum_univ (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    (∑ i ∈ Finset.range p, f (i : ZMod p)) = ∑ x : ZMod p, f x := by
  rw [Finset.sum_range]
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      conv_rhs =>
        arg 2
        intro x
        rw [← ZMod.natCast_zmod_val x]
      rfl

lemma inv_pow_sum_Icc_zmodp_zero (p k : ℕ) (hp : p.Prime) (hk0 : 0 < k)
    (hklt : k < p - 1) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^k) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : 0 < p := hp.pos
  rw [Icc_one_pred_eq_range_erase_zero p hp0]
  rw [Finset.sum_erase]
  · have hpow : (∑ i ∈ Finset.range p, ((i : ZMod p) ^ (p - 1 - k))) = 0 := by
      rw [sum_range_zmod_eq_sum_univ p (fun x : ZMod p => x ^ (p - 1 - k))]
      have hlt : p - 1 - k < Fintype.card (ZMod p) - 1 := by
        rw [ZMod.card]
        omega
      exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) (p - 1 - k) hlt
    trans (∑ i ∈ Finset.range p, ((i : ZMod p) ^ (p - 1 - k)))
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        have hpos : 0 < p - 1 - k := by omega
        simp [hk0.ne', hpos.ne']
      · have hip : i < p := by simpa using hi
        have hunit : IsUnit (i : ZMod p) := by
          apply isUnit_iff_ne_zero.mpr
          intro hz
          have hdvd : p ∣ i := (ZMod.natCast_eq_zero_iff i p).1 hz
          exact not_le_of_gt hip (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hdvd)
        have hfermat : (i : ZMod p) ^ (p - 1) = 1 := by
          apply ZMod.pow_card_sub_one_eq_one
          exact IsUnit.ne_zero hunit
        have hpoweq : ((i : ZMod p)⁻¹)^k = (i : ZMod p)^(p - 1 - k) := by
          have hmul : ((i : ZMod p)⁻¹)^k * (i : ZMod p)^k = 1 := by
            rw [← mul_pow, ZMod.inv_mul_of_unit _ hunit, one_pow]
          have hright : (i : ZMod p)^(p - 1 - k) * (i : ZMod p)^k = 1 := by
            rw [← pow_add]
            have hadd : p - 1 - k + k = p - 1 := by omega
            rw [hadd, hfermat]
          have hunitk : IsUnit ((i : ZMod p)^k) := hunit.pow k
          calc
            ((i : ZMod p)⁻¹)^k
                = ((i : ZMod p)⁻¹)^k * (((i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹)) := by
                    rw [ZMod.mul_inv_of_unit _ hunitk, mul_one]
            _ = (((i : ZMod p)⁻¹)^k * (i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹) := by ring
            _ = 1 * (((i : ZMod p)^k)⁻¹) := by rw [hmul]
            _ = ((i : ZMod p)^(p - 1 - k) * (i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹) := by rw [hright]
            _ = (i : ZMod p)^(p - 1 - k) * (((i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹)) := by ring
            _ = (i : ZMod p)^(p - 1 - k) := by rw [ZMod.mul_inv_of_unit _ hunitk, mul_one]
        exact hpoweq
    · exact hpow
  · simp [hk0.ne']

lemma inv_fourth_sum_Icc_zmodp_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^4) = 0 := by
  exact inv_pow_sum_Icc_zmodp_zero p 4 hp (by norm_num) (by omega)

lemma inv_sum_Icc_zmodp_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)) = 0 := by
  simpa using inv_pow_sum_Icc_zmodp_zero p 1 hp (by norm_num) (by omega)

lemma inv_cube_sum_Icc_zmodp_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^3) = 0 := by
  exact inv_pow_sum_Icc_zmodp_zero p 3 hp (by norm_num) (by omega)


lemma castHom_inv_pow_nat_mod_five (p i n : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p)
        (((i : ZMod (p ^ 5))⁻¹)^n) = ((i : ZMod p)⁻¹)^n := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hunit5 : IsUnit (i : ZMod (p ^ 5)) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p 5 i hp (by norm_num) hi0 hip
  have hmap_inv : ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 5))⁻¹) =
      ((i : ZMod p)⁻¹) := by
    apply eq_inv_of_mul_eq_one_right
    calc
      (i : ZMod p) * ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 5))⁻¹)
          = ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 5)) * ((i : ZMod (p ^ 5))⁻¹)) := by simp
      _ = 1 := by rw [ZMod.mul_inv_of_unit _ hunit5]; simp
  rw [map_pow, hmap_inv]

lemma castHom_Hpow_mod_five (p n : ℕ) (hp : p.Prime) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p) (Hpow p n) =
      ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^n := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Hpow, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hib : 1 ≤ i ∧ i ≤ p - 1 := by simpa [Finset.mem_Icc] using hi
  exact castHom_inv_pow_nat_mod_five p i n hp (by omega) (by omega)




lemma p_pow_self_zmod_zero (p r : ℕ) : ((p : ZMod (p ^ r)) ^ r) = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]

lemma p_sq_mul_eq_zero_of_castHom_p5_to_p3_eq_zero (p : ℕ) [NeZero p]
    (x : ZMod (p ^ 5))
    (h : ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3)) x = 0) :
    (p : ZMod (p ^ 5)) ^ 2 * x = 0 := by
  rw [← ZMod.natCast_zmod_val x]
  have hx0 : ((x.val : ℕ) : ZMod (p ^ 3)) = 0 := by
    simpa [ZMod.castHom_apply] using h
  have hdvd : p ^ 3 ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ 3)).1 hx0
  rcases hdvd with ⟨k, hk⟩
  rw [hk]
  norm_num [Nat.cast_mul, Nat.cast_pow]
  have hp5zero : (p : ZMod (p ^ 5)) ^ 5 = 0 := p_pow_five_zmod_zero p
  ring_nf
  rw [hp5zero]
  ring

lemma castHom_inv_pow_nat_mod_five_to_three (p i n : ℕ) (hp : p.Prime)
    (hi0 : 0 < i) (hip : i < p) :
    ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3))
        (((i : ZMod (p ^ 5))⁻¹)^n) = ((i : ZMod (p ^ 3))⁻¹)^n := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hunit5 : IsUnit (i : ZMod (p ^ 5)) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p 5 i hp (by norm_num) hi0 hip
  have hunit3 : IsUnit (i : ZMod (p ^ 3)) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p 3 i hp (by norm_num) hi0 hip
  have hmap_inv : ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3))
      ((i : ZMod (p ^ 5))⁻¹) = ((i : ZMod (p ^ 3))⁻¹) := by
    apply IsUnit.mul_right_cancel hunit3
    calc
      ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3))
            ((i : ZMod (p ^ 5))⁻¹) * (i : ZMod (p ^ 3))
          = ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3))
              (((i : ZMod (p ^ 5))⁻¹) * (i : ZMod (p ^ 5))) := by
              rw [map_mul]
              simp
      _ = ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3)) (1 : ZMod (p ^ 5)) := by rw [ZMod.inv_mul_of_unit _ hunit5]
      _ = 1 := by exact map_one _
      _ = ((i : ZMod (p ^ 3))⁻¹) * (i : ZMod (p ^ 3)) := by rw [ZMod.inv_mul_of_unit _ hunit3]
  rw [map_pow, hmap_inv]

lemma castHom_Hpow_mod_five_to_three (p n : ℕ) (hp : p.Prime) :
    ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3)) (Hpow p n) =
      ∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod (p ^ 3))⁻¹)^n := by
  rw [Hpow, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hib : 1 ≤ i ∧ i ≤ p - 1 := by simpa [Finset.mem_Icc] using hi
  exact castHom_inv_pow_nat_mod_five_to_three p i n hp (by omega) (by omega)

lemma p_sq_mul_eq_zero_of_castHom_mod3_eq_zero (p : ℕ) [NeZero p] (x : ZMod (p ^ 3))
    (h : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) x = 0) :
    (p : ZMod (p ^ 3)) ^ 2 * x = 0 := by
  rw [← ZMod.natCast_zmod_val x]
  have hx0 : ((x.val : ℕ) : ZMod p) = 0 := by
    simpa [ZMod.castHom_apply] using h
  have hdvd : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).1 hx0
  rcases hdvd with ⟨k, hk⟩
  rw [hk]
  norm_num [Nat.cast_mul, Nat.cast_pow]
  have hp3zero : (p : ZMod (p ^ 3)) ^ 3 = 0 := p_pow_self_zmod_zero p 3
  ring_nf
  rw [hp3zero]
  ring

lemma castHom_inv_pow_nat_mod_three (p i n : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
        (((i : ZMod (p ^ 3))⁻¹)^n) = ((i : ZMod p)⁻¹)^n := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hunit3 : IsUnit (i : ZMod (p ^ 3)) :=
    isUnit_natCast_zmod_prime_pow_of_pos_lt p 3 i hp (by norm_num) hi0 hip
  have hunitp : IsUnit (i : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
      intro hdiv
      exact not_le_of_gt hip (Nat.le_of_dvd hi0 hdiv))
  have hmap_inv : ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 3))⁻¹) =
      ((i : ZMod p)⁻¹) := by
    apply IsUnit.mul_right_cancel hunitp
    calc
      ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) ((i : ZMod (p ^ 3))⁻¹) * (i : ZMod p)
          = ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) (((i : ZMod (p ^ 3))⁻¹) * (i : ZMod (p ^ 3))) := by
            rw [map_mul]
            simp
      _ = 1 := by rw [ZMod.inv_mul_of_unit _ hunit3]; simp
      _ = ((i : ZMod p)⁻¹) * (i : ZMod p) := by rw [ZMod.inv_mul_of_unit _ hunitp]
  rw [map_pow, hmap_inv]

lemma inv_p_sub_expansion_mod_three (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    (((p - i : ℕ) : ZMod (p ^ 3))⁻¹) =
      - ((i : ZMod (p ^ 3))⁻¹) - (p : ZMod (p ^ 3)) * ((i : ZMod (p ^ 3))⁻¹)^2 -
        (p : ZMod (p ^ 3))^2 * ((i : ZMod (p ^ 3))⁻¹)^3 := by
  let R := ZMod (p ^ 3)
  have hunit_i : IsUnit (i : R) := isUnit_natCast_zmod_prime_pow_of_pos_lt p 3 i hp (by norm_num) hi0 hip
  have hunit_pi : IsUnit ((p - i : ℕ) : R) := by
    apply isUnit_natCast_zmod_prime_pow_of_pos_lt p 3 (p - i) hp (by norm_num) <;> omega
  apply_fun fun x : R => x * ((p - i : ℕ) : R)
  · change (((p - i : ℕ) : R)⁻¹ * ((p - i : ℕ) : R)) =
      (-((i : R)⁻¹) - (p : R) * ((i : R)⁻¹)^2 - (p : R)^2 * ((i : R)⁻¹)^3) * ((p - i : ℕ) : R)
    rw [ZMod.inv_mul_of_unit _ hunit_pi]
    have hpi : ((p - i : ℕ) : R) = (p : R) - (i : R) := by rw [Nat.cast_sub (le_of_lt hip)]
    rw [hpi]
    have hi_inv : ((i : R)⁻¹) * (i : R) = 1 := ZMod.inv_mul_of_unit _ hunit_i
    have hi_inv2 : ((i : R)⁻¹)^2 * (i : R) = (i : R)⁻¹ := by
      calc
        ((i : R)⁻¹)^2 * (i : R) = (i : R)⁻¹ * (((i : R)⁻¹) * (i : R)) := by ring
        _ = (i : R)⁻¹ := by rw [hi_inv, mul_one]
    have hi_inv3 : ((i : R)⁻¹)^3 * (i : R) = ((i : R)⁻¹)^2 := by
      calc
        ((i : R)⁻¹)^3 * (i : R) = ((i : R)⁻¹)^2 * (((i : R)⁻¹) * (i : R)) := by ring
        _ = ((i : R)⁻¹)^2 := by rw [hi_inv, mul_one]
    have hp3zero : (p : R)^3 = 0 := p_pow_self_zmod_zero p 3
    have t2 : ((i : R)⁻¹)^2 * (p : R) * (i : R) = (p : R) * (i : R)⁻¹ := by
      calc
        ((i : R)⁻¹)^2 * (p : R) * (i : R) = (p : R) * (((i : R)⁻¹)^2 * (i : R)) := by ring
        _ = (p : R) * (i : R)⁻¹ := by rw [hi_inv2]
    have t3 : ((i : R)⁻¹)^3 * (p : R)^2 * (i : R) = (p : R)^2 * ((i : R)⁻¹)^2 := by
      calc
        ((i : R)⁻¹)^3 * (p : R)^2 * (i : R) = (p : R)^2 * (((i : R)⁻¹)^3 * (i : R)) := by ring
        _ = (p : R)^2 * ((i : R)⁻¹)^2 := by rw [hi_inv3]
    have t4 : ((i : R)⁻¹)^3 * (p : R)^2 * (p : R) = 0 := by
      calc
        ((i : R)⁻¹)^3 * (p : R)^2 * (p : R) = ((i : R)⁻¹)^3 * (p : R)^3 := by ring
        _ = 0 := by rw [hp3zero, mul_zero]
    calc
      1 = -((i : R)⁻¹) * (p : R) + ((i : R)⁻¹) * (i : R)
          - ((i : R)⁻¹)^2 * (p : R) * (p : R) + ((i : R)⁻¹)^2 * (p : R) * (i : R)
          - ((i : R)⁻¹)^3 * (p : R)^2 * (p : R) + ((i : R)⁻¹)^3 * (p : R)^2 * (i : R) := by
            rw [hi_inv, t2, t3, t4]; ring
      _ = (-((i : R)⁻¹) - (p : R) * ((i : R)⁻¹)^2 - (p : R)^2 * ((i : R)⁻¹)^3) * ((p : R) - (i : R)) := by ring
  · intro a b hab
    calc
      a = a * 1 := by rw [mul_one]
      _ = a * (((p - i : ℕ) : R) * ((p - i : ℕ) : R)⁻¹) := by rw [ZMod.mul_inv_of_unit _ hunit_pi]
      _ = (a * ((p - i : ℕ) : R)) * ((p - i : ℕ) : R)⁻¹ := by ring
      _ = (b * ((p - i : ℕ) : R)) * ((p - i : ℕ) : R)⁻¹ := by simpa using congrArg (fun x : R => x * (((p - i : ℕ) : R)⁻¹)) hab
      _ = b * (((p - i : ℕ) : R) * ((p - i : ℕ) : R)⁻¹) := by ring
      _ = b := by rw [ZMod.mul_inv_of_unit _ hunit_pi, mul_one]


lemma inv_p_sub_expansion_mod_five (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    (((p - i : ℕ) : ZMod (p ^ 5))⁻¹) =
      - ((i : ZMod (p ^ 5))⁻¹) - (p : ZMod (p ^ 5)) * ((i : ZMod (p ^ 5))⁻¹)^2 -
        (p : ZMod (p ^ 5))^2 * ((i : ZMod (p ^ 5))⁻¹)^3 -
        (p : ZMod (p ^ 5))^3 * ((i : ZMod (p ^ 5))⁻¹)^4 -
        (p : ZMod (p ^ 5))^4 * ((i : ZMod (p ^ 5))⁻¹)^5 := by
  let R := ZMod (p ^ 5)
  let P : R := (p : R)
  let I : R := (i : R)
  let a : R := (i : R)⁻¹
  have hunit_i : IsUnit (i : R) := isUnit_natCast_zmod_prime_pow_of_pos_lt p 5 i hp (by norm_num) hi0 hip
  have hunit_pi : IsUnit ((p - i : ℕ) : R) := by
    apply isUnit_natCast_zmod_prime_pow_of_pos_lt p 5 (p - i) hp (by norm_num) <;> omega
  have hpi : ((p - i : ℕ) : R) = P - I := by
    dsimp [P, I, R]
    rw [Nat.cast_sub (le_of_lt hip)]
  have haI : a * I = 1 := by
    dsimp [a, I, R]
    exact ZMod.inv_mul_of_unit _ hunit_i
  have hP5 : P ^ 5 = 0 := by
    dsimp [P, R]
    exact p_pow_five_zmod_zero p
  apply_fun fun x : R => x * ((p - i : ℕ) : R)
  · change (((p - i : ℕ) : R)⁻¹ * ((p - i : ℕ) : R)) =
        (- ((i : R)⁻¹) - (p : R) * ((i : R)⁻¹)^2 -
          (p : R)^2 * ((i : R)⁻¹)^3 - (p : R)^3 * ((i : R)⁻¹)^4 -
          (p : R)^4 * ((i : R)⁻¹)^5) * ((p - i : ℕ) : R)
    rw [ZMod.inv_mul_of_unit _ hunit_pi, hpi]
    change 1 = (-a - P * a^2 - P^2 * a^3 - P^3 * a^4 - P^4 * a^5) * (P - I)
    symm
    let Q : R := 1 + P * a + P^2 * a^2 + P^3 * a^3 + P^4 * a^4
    calc
      (-a - P * a^2 - P^2 * a^3 - P^3 * a^4 - P^4 * a^5) * (P - I)
          = (a * I - P * a) * Q := by
            dsimp [Q]
            ring
      _ = (1 - P * a) * Q := by rw [haI]
      _ = 1 - P^5 * a^5 := by
            dsimp [Q]
            ring
      _ = 1 := by rw [hP5]; ring
  · intro x y hxy
    calc
      x = x * 1 := by rw [mul_one]
      _ = x * (((p - i : ℕ) : R) * ((p - i : ℕ) : R)⁻¹) := by rw [ZMod.mul_inv_of_unit _ hunit_pi]
      _ = (x * ((p - i : ℕ) : R)) * ((p - i : ℕ) : R)⁻¹ := by ring
      _ = (y * ((p - i : ℕ) : R)) * ((p - i : ℕ) : R)⁻¹ := by simpa using congrArg (fun z : R => z * (((p - i : ℕ) : R)⁻¹)) hxy
      _ = y * (((p - i : ℕ) : R) * ((p - i : ℕ) : R)⁻¹) := by ring
      _ = y := by rw [ZMod.mul_inv_of_unit _ hunit_pi, mul_one]

lemma prod_Icc_one_two_mul_pair_sum {M : Type*} [AddCommMonoid M] (h : ℕ) (F : ℕ → M) :
    (∑ i ∈ Finset.Icc 1 (2 * h), F i) =
      ∑ i ∈ Finset.Icc 1 h, (F i + F (2 * h + 1 - i)) := by
  classical
  have hfilter := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (2 * h)) (fun i => i ≤ h) F
  have hleft : (Finset.Icc 1 (2 * h)).filter (fun i => i ≤ h) = Finset.Icc 1 h := by
    ext i; simp [Finset.mem_Icc]; omega
  have hright : (Finset.Icc 1 (2 * h)).filter (fun i => ¬ i ≤ h) = Finset.Icc (h + 1) (2 * h) := by
    ext i; simp [Finset.mem_Icc]; omega
  rw [hleft, hright] at hfilter
  have hupper : (∑ i ∈ Finset.Icc (h + 1) (2 * h), F i) =
      ∑ i ∈ Finset.Icc 1 h, F (2 * h + 1 - i) := by
    refine Finset.sum_bij (fun i _ => 2 * h + 1 - i) ?_ ?_ ?_ ?_
    · intro i hi; simp [Finset.mem_Icc] at hi ⊢; omega
    · intro a ha b hb hab
      simp [Finset.mem_Icc] at ha hb
      have hsub : 2 * h + 1 - a = 2 * h + 1 - b := hab
      omega
    · intro b hb
      refine ⟨2 * h + 1 - b, ?_, ?_⟩
      · simp [Finset.mem_Icc] at hb ⊢; omega
      · simp [Finset.mem_Icc] at hb
        change 2 * h + 1 - (2 * h + 1 - b) = b
        omega
    · intro i hi
      simp [Finset.mem_Icc] at hi
      have harg : i = 2 * h + 1 - (2 * h + 1 - i) := by omega
      simpa using congrArg F harg
  rw [← hfilter, hupper]
  rw [Finset.sum_add_distrib]

lemma inv_sq_sum_upper_eq_half_zmodp (p h : ℕ) (hp : p.Prime) (hp_eq : p = 2 * h + 1) :
    (∑ i ∈ Finset.Icc (h + 1) (p - 1), (((i : ZMod p)⁻¹)^2)) =
      ∑ i ∈ Finset.Icc 1 h, (((i : ZMod p)⁻¹)^2) := by
  subst p
  haveI : Fact (Nat.Prime (2 * h + 1)) := ⟨hp⟩
  refine Finset.sum_bij (fun i _ => (2 * h + 1) - i) ?_ ?_ ?_ ?_
  · intro i hi; simp [Finset.mem_Icc] at hi ⊢; omega
  · intro a ha b hb hab
    simp [Finset.mem_Icc] at ha hb
    have hsub : 2 * h + 1 - a = 2 * h + 1 - b := hab
    omega
  · intro b hb
    refine ⟨(2 * h + 1) - b, ?_, ?_⟩
    · simp [Finset.mem_Icc] at hb ⊢; omega
    · simp [Finset.mem_Icc] at hb
      change 2 * h + 1 - (2 * h + 1 - b) = b
      omega
  · intro i hi
    simp [Finset.mem_Icc] at hi
    have hpi : (((2 * h + 1) - i : ℕ) : ZMod (2 * h + 1)) = - (i : ZMod (2 * h + 1)) := by
      rw [Nat.cast_sub (by omega : i ≤ 2 * h + 1)]; simp
    rw [hpi]
    have hinvneg : (- (i : ZMod (2 * h + 1)))⁻¹ = - ((i : ZMod (2 * h + 1))⁻¹) := inv_neg
    rw [hinvneg]
    ring

lemma inv_fourth_sum_upper_eq_half_zmodp (p h : ℕ) (hp : p.Prime) (hp_eq : p = 2 * h + 1) :
    (∑ i ∈ Finset.Icc (h + 1) (p - 1), (((i : ZMod p)⁻¹)^4)) =
      ∑ i ∈ Finset.Icc 1 h, (((i : ZMod p)⁻¹)^4) := by
  subst p
  haveI : Fact (Nat.Prime (2 * h + 1)) := ⟨hp⟩
  refine Finset.sum_bij (fun i _ => (2 * h + 1) - i) ?_ ?_ ?_ ?_
  · intro i hi; simp [Finset.mem_Icc] at hi ⊢; omega
  · intro a ha b hb hab
    simp [Finset.mem_Icc] at ha hb
    have hsub : 2 * h + 1 - a = 2 * h + 1 - b := hab
    omega
  · intro b hb
    refine ⟨(2 * h + 1) - b, ?_, ?_⟩
    · simp [Finset.mem_Icc] at hb ⊢; omega
    · simp [Finset.mem_Icc] at hb
      change 2 * h + 1 - (2 * h + 1 - b) = b
      omega
  · intro i hi
    simp [Finset.mem_Icc] at hi
    have hpi : (((2 * h + 1) - i : ℕ) : ZMod (2 * h + 1)) = - (i : ZMod (2 * h + 1)) := by
      rw [Nat.cast_sub (by omega : i ≤ 2 * h + 1)]; simp
    rw [hpi]
    have hinvneg : (- (i : ZMod (2 * h + 1)))⁻¹ = - ((i : ZMod (2 * h + 1))⁻¹) := inv_neg
    rw [hinvneg]
    ring

lemma inv_sq_sum_half_zmodp_zero (p h : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let f : ℕ → ZMod p := fun i => ((i : ZMod p)⁻¹)^2
  have hfull : (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^2) = 0 := by
    exact inv_pow_sum_Icc_zmodp_zero p 2 hp (by norm_num) (by omega)
  have hfilter := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p - 1)) (fun i => i ≤ h) f
  have hleft : (Finset.Icc 1 (p - 1)).filter (fun i => i ≤ h) = Finset.Icc 1 h := by
    ext i; simp [Finset.mem_Icc]; omega
  have hright : (Finset.Icc 1 (p - 1)).filter (fun i => ¬ i ≤ h) = Finset.Icc (h + 1) (p - 1) := by
    ext i; simp [Finset.mem_Icc]; omega
  rw [hleft, hright] at hfilter
  have hupper := inv_sq_sum_upper_eq_half_zmodp p h hp hp_eq
  dsimp [f] at hfilter
  rw [hupper, hfull] at hfilter
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hsum : (2 : ZMod p) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^2) = 0 := by
    simpa [two_mul] using hfilter
  exact (mul_eq_zero.mp hsum).resolve_left htwo_ne

lemma inv_fourth_sum_half_zmodp_zero (p h : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^4) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let f : ℕ → ZMod p := fun i => ((i : ZMod p)⁻¹)^4
  have hfull := inv_fourth_sum_Icc_zmodp_zero p hp hp7
  have hfilter := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p - 1)) (fun i => i ≤ h) f
  have hleft : (Finset.Icc 1 (p - 1)).filter (fun i => i ≤ h) = Finset.Icc 1 h := by
    ext i; simp [Finset.mem_Icc]; omega
  have hright : (Finset.Icc 1 (p - 1)).filter (fun i => ¬ i ≤ h) = Finset.Icc (h + 1) (p - 1) := by
    ext i; simp [Finset.mem_Icc]; omega
  rw [hleft, hright] at hfilter
  have hupper := inv_fourth_sum_upper_eq_half_zmodp p h hp hp_eq
  dsimp [f] at hfilter
  rw [hupper, hfull] at hfilter
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hsum : (2 : ZMod p) * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^4) = 0 := by
    simpa [two_mul] using hfilter
  exact (mul_eq_zero.mp hsum).resolve_left htwo_ne

lemma castHom_half_inv_pow_sum_mod_three (p h e : ℕ) (hp : p.Prime) (hp_eq : p = 2 * h + 1) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
      (∑ i ∈ Finset.Icc 1 h, ((i : ZMod (p ^ 3))⁻¹)^e) =
    ∑ i ∈ Finset.Icc 1 h, ((i : ZMod p)⁻¹)^e := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_Icc] at hi
  exact castHom_inv_pow_nat_mod_three p i e hp (by omega) (by omega)

lemma p_sq_mul_half_inv_sq_sum_zmodp3_zero (p h : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (p : ZMod (p ^ 3)) ^ 2 * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod (p ^ 3))⁻¹)^2) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply p_sq_mul_eq_zero_of_castHom_mod3_eq_zero p
  rw [castHom_half_inv_pow_sum_mod_three p h 2 hp hp_eq]
  exact inv_sq_sum_half_zmodp_zero p h hp hp5 hp_eq

lemma p_sq_mul_half_inv_fourth_sum_zmodp3_zero (p h : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (p : ZMod (p ^ 3)) ^ 2 * (∑ i ∈ Finset.Icc 1 h, ((i : ZMod (p ^ 3))⁻¹)^4) = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply p_sq_mul_eq_zero_of_castHom_mod3_eq_zero p
  rw [castHom_half_inv_pow_sum_mod_three p h 4 hp hp_eq]
  exact inv_fourth_sum_half_zmodp_zero p h hp hp7 hp_eq

lemma pair_inv_cube_mul_p_eq_mod_three (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) :
    (p : ZMod (p ^ 3)) *
      (((i : ZMod (p ^ 3))⁻¹)^3 + (((p - i : ℕ) : ZMod (p ^ 3))⁻¹)^3) =
    -3 * (p : ZMod (p ^ 3))^2 * ((i : ZMod (p ^ 3))⁻¹)^4 := by
  rw [inv_p_sub_expansion_mod_three p i hp hi0 hip]
  have hp3zero : (p : ZMod (p ^ 3))^3 = 0 := p_pow_self_zmod_zero p 3
  have hp4zero : (p : ZMod (p ^ 3))^4 = 0 := by
    calc (p : ZMod (p ^ 3))^4 = (p : ZMod (p ^ 3))^3 * (p : ZMod (p ^ 3)) := by ring
      _ = 0 := by rw [hp3zero, zero_mul]
  have hp5zero : (p : ZMod (p ^ 3))^5 = 0 := by
    calc (p : ZMod (p ^ 3))^5 = (p : ZMod (p ^ 3))^3 * (p : ZMod (p ^ 3))^2 := by ring
      _ = 0 := by rw [hp3zero, zero_mul]
  have hp6zero : (p : ZMod (p ^ 3))^6 = 0 := by
    calc (p : ZMod (p ^ 3))^6 = (p : ZMod (p ^ 3))^3 * (p : ZMod (p ^ 3))^3 := by ring
      _ = 0 := by rw [hp3zero, zero_mul]
  have hp7zero : (p : ZMod (p ^ 3))^7 = 0 := by
    calc (p : ZMod (p ^ 3))^7 = (p : ZMod (p ^ 3))^3 * (p : ZMod (p ^ 3))^4 := by ring
      _ = 0 := by rw [hp3zero, zero_mul]
  ring_nf
  rw [hp3zero, hp4zero, hp5zero, hp6zero, hp7zero]
  ring

lemma harmonic_cube_zmodp3_p_mul_zero_of_odd (p h : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hp_eq : p = 2 * h + 1) :
    (p : ZMod (p ^ 3)) * (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod (p ^ 3))⁻¹)^3) = 0 := by
  subst p
  have hsum := prod_Icc_one_two_mul_pair_sum h (fun i => ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^3)
  have htop : 2 * h + 1 - 1 = 2 * h := by omega
  rw [htop, hsum, Finset.mul_sum]
  trans ∑ i ∈ Finset.Icc 1 h,
      (-3 * ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3))^2 * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^4)
  · apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_Icc] at hi
    simpa using pair_inv_cube_mul_p_eq_mod_three (2 * h + 1) i hp (by omega) (by omega : i < 2 * h + 1)
  · rw [← Finset.mul_sum]
    have hzero := p_sq_mul_half_inv_fourth_sum_zmodp3_zero (2 * h + 1) h hp hp7 rfl
    calc
      -3 * ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3))^2 *
          (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^4)
          = -3 * (((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3))^2 *
          (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^4)) := by ring
      _ = 0 := by rw [hzero, mul_zero]

lemma harmonic_cube_zmodp3_p_mul_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 3)) * (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod (p ^ 3))⁻¹)^3) = 0 := by
  have hne2 : p ≠ 2 := by omega
  rcases hp.odd_of_ne_two hne2 with ⟨h, hp_eq⟩
  exact harmonic_cube_zmodp3_p_mul_zero_of_odd p h hp hp7 hp_eq

lemma harmonic_one_square_zmodp3_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod (p ^ 3))⁻¹)) ^ 2 = 0 := by
  have hne2 : p ≠ 2 := by omega
  rcases hp.odd_of_ne_two hne2 with ⟨h, hp_eq⟩
  subst p
  let R := ZMod ((2 * h + 1) ^ 3)
  let P : R := ((2 * h + 1 : ℕ) : R)
  let S2 : R := ∑ i ∈ Finset.Icc 1 h, ((i : R)⁻¹)^2
  let S3 : R := ∑ i ∈ Finset.Icc 1 h, ((i : R)⁻¹)^3
  have hsum_pair := prod_Icc_one_two_mul_pair_sum h (fun i => ((i : R)⁻¹))
  have htop : 2 * h + 1 - 1 = 2 * h := by omega
  have hH1 : (∑ i ∈ Finset.Icc 1 (2 * h + 1 - 1), ((i : R)⁻¹)) = -P * S2 - P ^ 2 * S3 := by
    rw [htop, hsum_pair]
    dsimp [S2, S3, P, R]
    calc
      (∑ i ∈ Finset.Icc 1 h,
          ((i : ZMod ((2 * h + 1) ^ 3))⁻¹ + (((2 * h + 1 - i : ℕ) : ZMod ((2 * h + 1) ^ 3))⁻¹)))
          = ∑ i ∈ Finset.Icc 1 h,
              (- ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2 -
                ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 * ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^3) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [Finset.mem_Icc] at hi
            rw [inv_p_sub_expansion_mod_three (2 * h + 1) i hp (by omega) (by omega : i < 2 * h + 1)]
            ring
      _ = - ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) *
              (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^2) -
            ((2 * h + 1 : ℕ) : ZMod ((2 * h + 1) ^ 3)) ^ 2 *
              (∑ i ∈ Finset.Icc 1 h, ((i : ZMod ((2 * h + 1) ^ 3))⁻¹)^3) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS2zero := p_sq_mul_half_inv_sq_sum_zmodp3_zero (2 * h + 1) h hp (by omega : 5 ≤ 2 * h + 1) rfl
  have hP3 : P ^ 3 = 0 := by
    dsimp [P, R]
    exact p_pow_self_zmod_zero (2 * h + 1) 3
  have hP4 : P ^ 4 = 0 := by
    calc
      P ^ 4 = P ^ 3 * P := by ring
      _ = 0 := by rw [hP3, zero_mul]
  rw [hH1]
  calc
    (-P * S2 - P ^ 2 * S3) ^ 2
        = (P ^ 2 * S2) * S2 + 2 * P ^ 3 * S2 * S3 + P ^ 4 * S3 ^ 2 := by ring
    _ = 0 := by
      change P ^ 2 * S2 = 0 at hS2zero
      rw [hS2zero, hP3, hP4]
      ring



def H13modp (p : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ∑ i ∈ Finset.Icc 1 (k - 1),
      ((i : ZMod p)⁻¹) * (((k : ZMod p)⁻¹) ^ 3)


def H31modp (p : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ∑ i ∈ Finset.Icc 1 (k - 1),
      (((i : ZMod p)⁻¹) ^ 3) * ((k : ZMod p)⁻¹)

lemma H31modp_eq_H13modp (p : ℕ) (hp : p.Prime) : H31modp p = H13modp p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let S : Finset ℕ := Finset.Icc 1 (p - 1)
  let D : Finset (Σ k : ℕ, ℕ) := S.sigma (fun k => Finset.Icc 1 (k - 1))
  rw [H31modp, H13modp]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  change
      (∑ x ∈ D, (((x.2 : ZMod p)⁻¹) ^ 3) * ((x.1 : ZMod p)⁻¹)) =
        (∑ x ∈ D, ((x.2 : ZMod p)⁻¹) * (((x.1 : ZMod p)⁻¹) ^ 3))
  refine Finset.sum_bij' (fun x _ => ⟨p - x.2, p - x.1⟩)
      (fun x _ => ⟨p - x.2, p - x.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx ⊢
    omega
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx ⊢
    omega
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx
    have hpk : p - (p - k) = k := by omega
    have hpi : p - (p - i) = i := by omega
    simp [hpk, hpi]
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx
    have hpk : p - (p - k) = k := by omega
    have hpi : p - (p - i) = i := by omega
    simp [hpk, hpi]
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx
    have hkcast : ((p - k : ℕ) : ZMod p) = - (k : ZMod p) := by
      rw [Nat.cast_sub (by omega : k ≤ p)]
      simp
    have hicast : ((p - i : ℕ) : ZMod p) = - (i : ZMod p) := by
      rw [Nat.cast_sub (by omega : i ≤ p)]
      simp
    simp [hkcast, hicast, inv_neg]
    ring


theorem power_sum_stuffle_H13modp_H31modp (p : ℕ) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)) *
      (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 3)) =
        H13modp p + H31modp p +
          (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (p - 1)
  let R := ZMod p
  let f : ℕ → R := fun i => ((i : R)⁻¹)
  let g : ℕ → R := fun i => ((i : R)⁻¹)^3
  have hsplit (b : ℕ) (hb : b ∈ S) :
      (∑ a ∈ S, f a * g b) =
        (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
        (f b * g b) +
        (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by
    have hlt : S.filter (fun a => a < b) = Finset.Icc 1 (b - 1) := by
      ext a
      simp [S, Finset.mem_Icc] at hb ⊢
      omega
    have hnotlt : S.filter (fun a => ¬ a < b) = Finset.Icc b (p - 1) := by
      ext a
      simp [S, Finset.mem_Icc] at hb ⊢
      omega
    have htail : Finset.Icc b (p - 1) = insert b (Finset.Icc (b + 1) (p - 1)) := by
      have hbS : 1 ≤ b ∧ b ≤ p - 1 := by simpa [S, Finset.mem_Icc] using hb
      ext a
      simp [Finset.mem_Icc]
      constructor
      · intro ha
        by_cases hab : a = b
        · exact Or.inl hab
        · exact Or.inr (by omega)
      · intro ha
        rcases ha with h | h
        · subst a
          exact ⟨le_rfl, hbS.2⟩
        · exact ⟨by omega, h.2⟩
    have hbnot : b ∉ Finset.Icc (b + 1) (p - 1) := by
      simp [Finset.mem_Icc]
    calc
      (∑ a ∈ S, f a * g b)
          = (∑ a ∈ S.filter (fun a => a < b), f a * g b) +
              (∑ a ∈ S.filter (fun a => ¬ a < b), f a * g b) := by
            rw [← Finset.sum_filter_add_sum_filter_not S (fun a => a < b) (fun a => f a * g b)]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
              (∑ a ∈ Finset.Icc b (p - 1), f a * g b) := by rw [hlt, hnotlt]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
              (∑ a ∈ insert b (Finset.Icc (b + 1) (p - 1)), f a * g b) := by rw [htail]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
              (f b * g b + ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by
            rw [Finset.sum_insert hbnot]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
          (f b * g b) +
          (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by ring
  have hupper :
      (∑ b ∈ S, ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) = H31modp p := by
    rw [H31modp]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    let D₁ : Finset (Σ b : ℕ, ℕ) := S.sigma (fun b => Finset.Icc (b + 1) (p - 1))
    let D₂ : Finset (Σ a : ℕ, ℕ) := S.sigma (fun a => Finset.Icc 1 (a - 1))
    change (∑ x ∈ D₁, f x.2 * g x.1) =
        (∑ x ∈ D₂, ((x.2 : R)⁻¹)^3 * ((x.1 : R)⁻¹))
    refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1⟩) (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨b, a⟩
      simp [D₁, D₂, S, Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx
      rcases x with ⟨a, b⟩
      simp [D₁, D₂, S, Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx
      cases x
      simp
    · intro x hx
      cases x
      simp
    · intro x hx
      rcases x with ⟨b, a⟩
      simp [f, g]
      ring
  have hdiag :
      (∑ b ∈ S, f b * g b) =
        (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, g]
    ring
  calc
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)) *
      (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 3))
        = ∑ b ∈ S, ∑ a ∈ S, f a * g b := by
            simp [S, f, g, Finset.mul_sum, mul_comm]
    _ = ∑ b ∈ S,
          ((∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
            (f b * g b) +
            (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b)) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hsplit b hb
    _ = (∑ b ∈ S, ∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
          (∑ b ∈ S, f b * g b) +
          (∑ b ∈ S, ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = H13modp p + H31modp p +
          (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
          rw [hupper, hdiag]
          simp [H13modp, S, f, g]
          ring

lemma H13modp_eq_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : H13modp p = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP1 := inv_sum_Icc_zmodp_zero p hp hp7
  have hP3 := inv_cube_sum_Icc_zmodp_zero p hp hp7
  have hP4 := inv_fourth_sum_Icc_zmodp_zero p hp hp7
  have hstuff := power_sum_stuffle_H13modp_H31modp p
  rw [hP1, zero_mul, H31modp_eq_H13modp p hp, hP4] at hstuff
  have htwo : (2 : ZMod p) * H13modp p = 0 := by
    simpa [two_mul, add_assoc] using hstuff.symm
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact (mul_eq_zero.mp htwo).resolve_left htwo_ne

lemma castHom_prefixH13_mod_five (p : ℕ) (hp : p.Prime) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p) (prefixH13 p) = H13modp p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [prefixH13, H13modp]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkb : 1 ≤ k ∧ k ≤ p - 1 := by simpa [Finset.mem_Icc] using hk
  rw [map_mul]
  dsimp [lowerH1]
  change (ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p)
      (∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod (p ^ 5))⁻¹))) *
    (ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p)
      (((k : ZMod (p ^ 5))⁻¹)^3)) =
    ∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod p)⁻¹) * (((k : ZMod p)⁻¹) ^ 3)

  rw [map_sum]
  rw [castHom_inv_pow_nat_mod_five p k 3 hp (by omega) (by omega)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hib : 1 ≤ i ∧ i ≤ k - 1 := by simpa [Finset.mem_Icc] using hi
  congr 1
  simpa using castHom_inv_pow_nat_mod_five p i 1 hp (by omega) (by omega)


theorem hW13_from_H13_vanish (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 5))^4 * prefixH13 p = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply p_four_mul_eq_zero_of_castHom_eq_zero p
  rw [castHom_prefixH13_mod_five p hp]
  exact H13modp_eq_zero p hp hp7


def H22modp (p : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ∑ i ∈ Finset.Icc 1 (k - 1),
      (((i : ZMod p)⁻¹) ^ 2) * (((k : ZMod p)⁻¹) ^ 2)


theorem power_sum_stuffle_H22modp (p : ℕ) :
    (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 2)) *
      (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 2)) =
        (2 : ZMod p) * H22modp p +
          (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (p - 1)
  let R := ZMod p
  let f : ℕ → R := fun i => ((i : R)⁻¹)^2
  have hsplit (b : ℕ) (hb : b ∈ S) :
      (∑ a ∈ S, f a * f b) =
        (∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
        (f b * f b) +
        (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * f b) := by
    have hlt : S.filter (fun a => a < b) = Finset.Icc 1 (b - 1) := by
      ext a
      simp [S, Finset.mem_Icc] at hb ⊢
      omega
    have hnotlt : S.filter (fun a => ¬ a < b) = Finset.Icc b (p - 1) := by
      ext a
      simp [S, Finset.mem_Icc] at hb ⊢
      omega
    have htail : Finset.Icc b (p - 1) = insert b (Finset.Icc (b + 1) (p - 1)) := by
      have hbS : 1 ≤ b ∧ b ≤ p - 1 := by simpa [S, Finset.mem_Icc] using hb
      ext a
      simp [Finset.mem_Icc]
      constructor
      · intro ha
        by_cases hab : a = b
        · exact Or.inl hab
        · exact Or.inr (by omega)
      · intro ha
        rcases ha with h | h
        · subst a
          exact ⟨le_rfl, hbS.2⟩
        · exact ⟨by omega, h.2⟩
    have hbnot : b ∉ Finset.Icc (b + 1) (p - 1) := by
      simp [Finset.mem_Icc]
    calc
      (∑ a ∈ S, f a * f b)
          = (∑ a ∈ S.filter (fun a => a < b), f a * f b) +
              (∑ a ∈ S.filter (fun a => ¬ a < b), f a * f b) := by
            rw [← Finset.sum_filter_add_sum_filter_not S (fun a => a < b) (fun a => f a * f b)]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
              (∑ a ∈ Finset.Icc b (p - 1), f a * f b) := by rw [hlt, hnotlt]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
              (∑ a ∈ insert b (Finset.Icc (b + 1) (p - 1)), f a * f b) := by rw [htail]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
              (f b * f b + ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * f b) := by
            rw [Finset.sum_insert hbnot]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
          (f b * f b) +
          (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * f b) := by ring
  have hupper :
      (∑ b ∈ S, ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * f b) = H22modp p := by
    rw [H22modp]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    let D₁ : Finset (Σ b : ℕ, ℕ) := S.sigma (fun b => Finset.Icc (b + 1) (p - 1))
    let D₂ : Finset (Σ a : ℕ, ℕ) := S.sigma (fun a => Finset.Icc 1 (a - 1))
    change (∑ x ∈ D₁, f x.2 * f x.1) =
        (∑ x ∈ D₂, ((x.2 : R)⁻¹)^2 * (((x.1 : R)⁻¹)^2))
    refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1⟩) (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨b, a⟩
      simp [D₁, D₂, S, Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx
      rcases x with ⟨a, b⟩
      simp [D₁, D₂, S, Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx
      cases x
      simp
    · intro x hx
      cases x
      simp
    · intro x hx
      rcases x with ⟨b, a⟩
      simp [f]
      ring
  have hdiag :
      (∑ b ∈ S, f b * f b) =
        (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [f]
    ring
  calc
    (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 2)) *
      (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 2))
        = ∑ b ∈ S, ∑ a ∈ S, f a * f b := by
            simp [S, f, Finset.mul_sum, mul_comm]
    _ = ∑ b ∈ S,
          ((∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
            (f b * f b) +
            (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * f b)) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hsplit b hb
    _ = (∑ b ∈ S, ∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
          (∑ b ∈ S, f b * f b) +
          (∑ b ∈ S, ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * f b) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (2 : ZMod p) * H22modp p +
          (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
          rw [hupper, hdiag]
          simp [H22modp, S, f, two_mul]
          ring

lemma H22modp_eq_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : H22modp p = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP2 := inv_pow_sum_Icc_zmodp_zero p 2 hp (by norm_num) (by omega)
  have hP4 := inv_fourth_sum_Icc_zmodp_zero p hp hp7
  have hstuff := power_sum_stuffle_H22modp p
  rw [hP2, zero_mul, hP4] at hstuff
  have htwo : (2 : ZMod p) * H22modp p = 0 := by
    simpa using hstuff.symm
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact (mul_eq_zero.mp htwo).resolve_left htwo_ne

lemma castHom_prefixH22_mod_five (p : ℕ) (hp : p.Prime) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p) (prefixH22 p) = H22modp p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [prefixH22, H22modp]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkb : 1 ≤ k ∧ k ≤ p - 1 := by simpa [Finset.mem_Icc] using hk
  rw [map_mul]
  dsimp [lowerH2]
  change (ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p)
      (∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod (p ^ 5))⁻¹)^2)) *
    (ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p)
      (((k : ZMod (p ^ 5))⁻¹)^2)) =
    ∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod p)⁻¹)^2 * (((k : ZMod p)⁻¹) ^ 2)
  rw [map_sum]
  rw [castHom_inv_pow_nat_mod_five p k 2 hp (by omega) (by omega)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hib : 1 ≤ i ∧ i ≤ k - 1 := by simpa [Finset.mem_Icc] using hi
  congr 1
  simpa using castHom_inv_pow_nat_mod_five p i 2 hp (by omega) (by omega)


theorem hW22_from_modp (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 5))^4 * prefixH22 p = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply p_four_mul_eq_zero_of_castHom_eq_zero p
  rw [castHom_prefixH22_mod_five p hp]
  exact H22modp_eq_zero p hp hp7





namespace H112BinomialRoutePort

noncomputable section

lemma zmod_natCast_neg_sub_eq_add (p r N m : ℕ) (hN : N = p - 1 - r) (hm : m ≤ N) (hrp : r < p) :
    (-((N - m : ℕ) : ZMod p)) = (r + m + 1 : ZMod p) := by
  subst N
  have hle : m ≤ p - 1 - r := hm
  have hsum : r + m + 1 ≤ p := by omega
  have hsub : p - (r + m + 1) = p - 1 - r - m := by omega
  calc
    (-((p - 1 - r - m : ℕ) : ZMod p)) = -(((p - (r + m + 1) : ℕ) : ZMod p)) := by rw [hsub]
    _ = - (-(r + m + 1 : ZMod p)) := by
      rw [Nat.cast_sub (by omega : r + m + 1 ≤ p)]
      simp
    _ = (r + m + 1 : ZMod p) := by simp



lemma choose_reflect_zmod (p r N m : ℕ) (hp : p.Prime) (hN : N = p - 1 - r)
    (hr1 : 1 ≤ r) (hrp : r < p) (hm : m ≤ N) :
    ((Nat.choose (r + m) r : ℕ) : ZMod p) =
      (-1 : ZMod p) ^ m * ((Nat.choose N m : ℕ) : ZMod p) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmN : m ≤ N := by omega
      have hmsN : m + 1 ≤ N := hm
      have hm1p : m + 1 < p := by
        subst N
        omega
      have hunit : IsUnit ((m + 1 : ℕ) : ZMod p) := by
        rw [ZMod.isUnit_iff_coprime]
        exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
          intro hdiv
          exact not_le_of_gt hm1p (Nat.le_of_dvd (by omega) hdiv))
      have hchooseL : ((m + 1 : ℕ) : ZMod p) * ((Nat.choose (r + m + 1) r : ℕ) : ZMod p) =
          ((r + m + 1 : ℕ) : ZMod p) * ((Nat.choose (r + m) r : ℕ) : ZMod p) := by
        have h := Nat.choose_mul_succ_eq (r + m) r
        have h' := congrArg (fun x : ℕ => (x : ZMod p)) h
        -- `r+m+1-r = m+1`.
        simpa [Nat.cast_mul, show r + m + 1 - r = m + 1 by omega, mul_comm] using h'.symm
      have hchooseR : ((m + 1 : ℕ) : ZMod p) * ((Nat.choose N (m + 1) : ℕ) : ZMod p) =
          ((N - m : ℕ) : ZMod p) * ((Nat.choose N m : ℕ) : ZMod p) := by
        have h := Nat.choose_succ_right_eq N m
        have h' := congrArg (fun x : ℕ => (x : ZMod p)) h
        simpa [Nat.cast_mul, mul_comm] using h'
      apply hunit.mul_left_cancel
      calc
          ((m + 1 : ℕ) : ZMod p) * ((Nat.choose (r + (m + 1)) r : ℕ) : ZMod p)
              = ((m + 1 : ℕ) : ZMod p) * ((Nat.choose (r + m + 1) r : ℕ) : ZMod p) := by congr 2 <;> omega
          _ = ((r + m + 1 : ℕ) : ZMod p) * ((Nat.choose (r + m) r : ℕ) : ZMod p) := hchooseL
          _ = ((r + m + 1 : ℕ) : ZMod p) * ((-1 : ZMod p) ^ m * ((Nat.choose N m : ℕ) : ZMod p)) := by rw [ih hmN]
          _ = (-1 : ZMod p) ^ (m + 1) * (((N - m : ℕ) : ZMod p) * ((Nat.choose N m : ℕ) : ZMod p)) := by
            have hneg := zmod_natCast_neg_sub_eq_add p r N m hN hmN hrp
            have hcastadd : ((r + m + 1 : ℕ) : ZMod p) = (r : ZMod p) + (m : ZMod p) + 1 := by norm_num
            rw [hcastadd, ← hneg]
            ring
          _ = (-1 : ZMod p) ^ (m + 1) * (((m + 1 : ℕ) : ZMod p) * ((Nat.choose N (m + 1) : ℕ) : ZMod p)) := by rw [hchooseR]
          _ = ((m + 1 : ℕ) : ZMod p) * ((-1 : ZMod p) ^ (m + 1) * ((Nat.choose N (m + 1) : ℕ) : ZMod p)) := by ring

end


def H1 (p n : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 n, (k : ZMod p)⁻¹


def H2 (p n : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 n, ((k : ZMod p)⁻¹)^2


def E11 (p n : ℕ) : ZMod p :=
  ∑ b ∈ Finset.Icc 1 n,
    ∑ a ∈ Finset.Icc 1 (b - 1),
      ((a : ZMod p)⁻¹) * ((b : ZMod p)⁻¹)



def B11 (p n : ℕ) : ZMod p :=
  ∑ b ∈ Finset.Icc 1 n,
    ∑ a ∈ Finset.Icc 1 b,
      ((a : ZMod p)⁻¹) * ((b : ZMod p)⁻¹)

lemma H1_succ (p n : ℕ) :
    H1 p (n + 1) = H1 p n + (((n + 1 : ℕ) : ZMod p)⁻¹) := by
  rw [H1, H1]
  simpa using (Finset.sum_Icc_succ_top (f := fun k : ℕ => ((k : ZMod p)⁻¹)) (by omega : 1 ≤ n + 1))

lemma H2_succ (p n : ℕ) :
    H2 p (n + 1) = H2 p n + ((((n + 1 : ℕ) : ZMod p)⁻¹)^2) := by
  rw [H2, H2]
  simpa using (Finset.sum_Icc_succ_top (f := fun k : ℕ => ((k : ZMod p)⁻¹)^2) (by omega : 1 ≤ n + 1))

lemma E11_succ (p n : ℕ) :
    E11 p (n + 1) = E11 p n + H1 p n * (((n + 1 : ℕ) : ZMod p)⁻¹) := by
  rw [E11, E11, H1]
  have htop := Finset.sum_Icc_succ_top
    (f := fun b : ℕ => ∑ a ∈ Finset.Icc 1 (b - 1), ((a : ZMod p)⁻¹) * ((b : ZMod p)⁻¹))
    (by omega : 1 ≤ n + 1)
  rw [htop]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma B11_succ (p n : ℕ) :
    B11 p (n + 1) = B11 p n + H1 p (n + 1) * (((n + 1 : ℕ) : ZMod p)⁻¹) := by
  rw [B11, B11, H1]
  have htop := Finset.sum_Icc_succ_top
    (f := fun b : ℕ => ∑ a ∈ Finset.Icc 1 b, ((a : ZMod p)⁻¹) * ((b : ZMod p)⁻¹))
    (by omega : 1 ≤ n + 1)
  rw [htop]
  congr 1
  rw [Finset.sum_mul]



lemma two_mul_E11_eq_H1_sq_sub_H2 (p n : ℕ) :
    (2 : ZMod p) * E11 p n = (H1 p n)^2 - H2 p n := by
  induction n with
  | zero => simp [E11, H1, H2]
  | succ n ih =>
      rw [E11_succ, H1_succ, H2_succ]
      calc
        (2 : ZMod p) * (E11 p n + H1 p n * (((n + 1 : ℕ) : ZMod p)⁻¹))
            = (2 : ZMod p) * E11 p n + 2 * H1 p n * (((n + 1 : ℕ) : ZMod p)⁻¹) := by ring
        _ = (H1 p n ^ 2 - H2 p n) + 2 * H1 p n * (((n + 1 : ℕ) : ZMod p)⁻¹) := by rw [ih]
        _ = (H1 p n + (↑(n + 1) : ZMod p)⁻¹) ^ 2 -
              (H2 p n + (↑(n + 1) : ZMod p)⁻¹ ^ 2) := by ring


lemma two_mul_B11_eq_H1_sq_add_H2 (p n : ℕ) :
    (2 : ZMod p) * B11 p n = (H1 p n)^2 + H2 p n := by
  induction n with
  | zero => simp [B11, H1, H2]
  | succ n ih =>
      rw [B11_succ, H1_succ, H2_succ]
      calc
        (2 : ZMod p) * (B11 p n + (H1 p n + (((n + 1 : ℕ) : ZMod p)⁻¹)) * (((n + 1 : ℕ) : ZMod p)⁻¹))
            = (2 : ZMod p) * B11 p n + 2 * H1 p n * (((n + 1 : ℕ) : ZMod p)⁻¹) +
                2 * (((n + 1 : ℕ) : ZMod p)⁻¹)^2 := by ring
        _ = (H1 p n ^ 2 + H2 p n) + 2 * H1 p n * (((n + 1 : ℕ) : ZMod p)⁻¹) +
                2 * (((n + 1 : ℕ) : ZMod p)⁻¹)^2 := by rw [ih]
        _ = (H1 p n + (↑(n + 1) : ZMod p)⁻¹) ^ 2 +
              (H2 p n + (↑(n + 1) : ZMod p)⁻¹ ^ 2) := by ring

lemma two_ne_zero_zmod_of_prime_ge_three (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  intro hz
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
  have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega




lemma E11_eq_B11_of_H1_eq_H1_and_H2_eq_neg (p m n : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (h1 : H1 p m = H1 p n) (h2 : H2 p m = - H2 p n) :
    E11 p m = B11 p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hE := two_mul_E11_eq_H1_sq_sub_H2 p m
  have hB := two_mul_B11_eq_H1_sq_add_H2 p n
  rw [h1, h2] at hE
  have htwo : (2 : ZMod p) * E11 p m = (2 : ZMod p) * B11 p n := by
    rw [hE, hB]
    ring
  exact mul_left_cancel₀ (two_ne_zero_zmod_of_prime_ge_three p hp hp3) htwo

lemma Icc_one_pred_eq_range_erase_zero (p : ℕ) (hp0 : 0 < p) :
    Finset.Icc 1 (p - 1) = (Finset.range p).erase 0 := by
  ext i
  simp [Finset.mem_Icc]
  omega

lemma sum_range_zmod_eq_sum_univ (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) :
    (∑ i ∈ Finset.range p, f (i : ZMod p)) = ∑ x : ZMod p, f x := by
  rw [Finset.sum_range]
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      conv_rhs =>
        arg 2
        intro x
        rw [← ZMod.natCast_zmod_val x]
      rfl

lemma inv_pow_sum_Icc_zmodp_zero (p k : ℕ) (hp : p.Prime) (hk0 : 0 < k)
    (hklt : k < p - 1) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)^k) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : 0 < p := hp.pos
  rw [Icc_one_pred_eq_range_erase_zero p hp0]
  rw [Finset.sum_erase]
  · have hpow : (∑ i ∈ Finset.range p, ((i : ZMod p) ^ (p - 1 - k))) = 0 := by
      rw [sum_range_zmod_eq_sum_univ p (fun x : ZMod p => x ^ (p - 1 - k))]
      have hlt : p - 1 - k < Fintype.card (ZMod p) - 1 := by
        rw [ZMod.card]
        omega
      exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) (p - 1 - k) hlt
    trans (∑ i ∈ Finset.range p, ((i : ZMod p) ^ (p - 1 - k)))
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        have hpos : 0 < p - 1 - k := by omega
        simp [hk0.ne', hpos.ne']
      · have hip : i < p := by simpa using hi
        have hunit : IsUnit (i : ZMod p) := by
          apply isUnit_iff_ne_zero.mpr
          intro hz
          have hdvd : p ∣ i := (ZMod.natCast_eq_zero_iff i p).1 hz
          exact not_le_of_gt hip (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hdvd)
        have hfermat : (i : ZMod p) ^ (p - 1) = 1 := by
          apply ZMod.pow_card_sub_one_eq_one
          exact IsUnit.ne_zero hunit
        have hpoweq : ((i : ZMod p)⁻¹)^k = (i : ZMod p)^(p - 1 - k) := by
          have hmul : ((i : ZMod p)⁻¹)^k * (i : ZMod p)^k = 1 := by
            rw [← mul_pow, ZMod.inv_mul_of_unit _ hunit, one_pow]
          have hright : (i : ZMod p)^(p - 1 - k) * (i : ZMod p)^k = 1 := by
            rw [← pow_add]
            have hadd : p - 1 - k + k = p - 1 := by omega
            rw [hadd, hfermat]
          have hunitk : IsUnit ((i : ZMod p)^k) := hunit.pow k
          calc
            ((i : ZMod p)⁻¹)^k
                = ((i : ZMod p)⁻¹)^k * (((i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹)) := by
                    rw [ZMod.mul_inv_of_unit _ hunitk, mul_one]
            _ = (((i : ZMod p)⁻¹)^k * (i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹) := by ring
            _ = 1 * (((i : ZMod p)^k)⁻¹) := by rw [hmul]
            _ = ((i : ZMod p)^(p - 1 - k) * (i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹) := by rw [hright]
            _ = (i : ZMod p)^(p - 1 - k) * (((i : ZMod p)^k) * (((i : ZMod p)^k)⁻¹)) := by ring
            _ = (i : ZMod p)^(p - 1 - k) := by rw [ZMod.mul_inv_of_unit _ hunitk, mul_one]
        exact hpoweq
    · exact hpow
  · simp [hk0.ne']

lemma H1_full_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : H1 p (p - 1) = 0 := by
  simpa [H1] using inv_pow_sum_Icc_zmodp_zero p 1 hp (by norm_num) (by omega)

lemma H2_full_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : H2 p (p - 1) = 0 := by
  simpa [H2] using inv_pow_sum_Icc_zmodp_zero p 2 hp (by norm_num) (by omega)

lemma tail_H1_reflect (p c : ℕ) (hp : p.Prime) (hc1 : 1 ≤ c) (hcp : c ≤ p - 1) :
    (∑ i ∈ Finset.Icc c (p - 1), ((i : ZMod p)⁻¹)) = - H1 p (p - c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [H1]
  trans ∑ j ∈ Finset.Icc 1 (p - c), -((j : ZMod p)⁻¹)
  · refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
    · intro i hi
      simp [Finset.mem_Icc] at hi ⊢
      omega
    · intro a ha b hb hab
      simp [Finset.mem_Icc] at ha hb
      have hab' : p - a = p - b := hab
      omega
    · intro j hj
      refine ⟨p - j, ?_, ?_⟩
      · simp [Finset.mem_Icc] at hj ⊢
        omega
      · simp [Finset.mem_Icc] at hj
        have hsub : p - (p - j) = j := by omega
        simpa [hsub]
    · intro i hi
      simp [Finset.mem_Icc] at hi
      have hcast : ((p - i : ℕ) : ZMod p) = - (i : ZMod p) := by
        rw [Nat.cast_sub (by omega : i ≤ p)]
        simp
      rw [hcast]
      have hneg : (-(i : ZMod p))⁻¹ = -((i : ZMod p)⁻¹) := inv_neg
      rw [hneg]
      ring
  · rw [Finset.sum_neg_distrib]

lemma tail_H2_reflect (p c : ℕ) (hp : p.Prime) (hc1 : 1 ≤ c) (hcp : c ≤ p - 1) :
    (∑ i ∈ Finset.Icc c (p - 1), ((i : ZMod p)⁻¹)^2) = H2 p (p - c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [H2]
  refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
  · intro i hi
    simp [Finset.mem_Icc] at hi ⊢
    omega
  · intro a ha b hb hab
    simp [Finset.mem_Icc] at ha hb
    have hab' : p - a = p - b := hab
    omega
  · intro j hj
    refine ⟨p - j, ?_, ?_⟩
    · simp [Finset.mem_Icc] at hj ⊢
      omega
    · simp [Finset.mem_Icc] at hj
      have hsub : p - (p - j) = j := by omega
      simpa [hsub]
  · intro i hi
    simp [Finset.mem_Icc] at hi
    have hcast : ((p - i : ℕ) : ZMod p) = - (i : ZMod p) := by
      rw [Nat.cast_sub (by omega : i ≤ p)]
      simp
    rw [hcast]
    have hneg : (-(i : ZMod p))⁻¹ = -((i : ZMod p)⁻¹) := inv_neg
    rw [hneg]
    ring

lemma H1_prefix_reflect (p c : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hc1 : 1 ≤ c) (hcp : c ≤ p - 1) :
    H1 p (c - 1) = H1 p (p - c) := by
  have hsplit : H1 p (p - 1) = H1 p (c - 1) + ∑ i ∈ Finset.Icc c (p - 1), ((i : ZMod p)⁻¹) := by
    rw [H1, H1]
    have hfilter := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p - 1)) (fun i => i < c)
      (fun i : ℕ => ((i : ZMod p)⁻¹))
    have hleft : (Finset.Icc 1 (p - 1)).filter (fun i => i < c) = Finset.Icc 1 (c - 1) := by
      ext i
      simp [Finset.mem_Icc]
      omega
    have hright : (Finset.Icc 1 (p - 1)).filter (fun i => ¬ i < c) = Finset.Icc c (p - 1) := by
      ext i
      simp [Finset.mem_Icc]
      omega
    rw [hleft, hright] at hfilter
    exact hfilter.symm
  rw [H1_full_zero p hp hp7, tail_H1_reflect p c hp hc1 hcp] at hsplit
  have h : H1 p (c - 1) - H1 p (p - c) = 0 := by
    simpa [sub_eq_add_neg] using hsplit.symm
  exact sub_eq_zero.mp h

lemma H2_prefix_reflect (p c : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hc1 : 1 ≤ c) (hcp : c ≤ p - 1) :
    H2 p (c - 1) = - H2 p (p - c) := by
  have hsplit : H2 p (p - 1) = H2 p (c - 1) + ∑ i ∈ Finset.Icc c (p - 1), ((i : ZMod p)⁻¹)^2 := by
    rw [H2, H2]
    have hfilter := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p - 1)) (fun i => i < c)
      (fun i : ℕ => ((i : ZMod p)⁻¹)^2)
    have hleft : (Finset.Icc 1 (p - 1)).filter (fun i => i < c) = Finset.Icc 1 (c - 1) := by
      ext i
      simp [Finset.mem_Icc]
      omega
    have hright : (Finset.Icc 1 (p - 1)).filter (fun i => ¬ i < c) = Finset.Icc c (p - 1) := by
      ext i
      simp [Finset.mem_Icc]
      omega
    rw [hleft, hright] at hfilter
    exact hfilter.symm
  rw [H2_full_zero p hp hp7, tail_H2_reflect p c hp hc1 hcp] at hsplit
  exact eq_neg_of_add_eq_zero_left hsplit.symm



lemma E11_prefix_reflect_eq_B11 (p c : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hc1 : 1 ≤ c) (hcp : c ≤ p - 1) :
    E11 p (c - 1) = B11 p (p - c) := by
  exact E11_eq_B11_of_H1_eq_H1_and_H2_eq_neg p (c - 1) (p - c) hp (by omega)
    (H1_prefix_reflect p c hp hp7 hc1 hcp)
    (H2_prefix_reflect p c hp hp7 hc1 hcp)


def H112 (p : ℕ) : ZMod p :=
  ∑ c ∈ Finset.Icc 1 (p - 1),
    ∑ b ∈ Finset.Icc 1 (c - 1),
      ∑ a ∈ Finset.Icc 1 (b - 1),
        ((a : ZMod p)⁻¹) * ((b : ZMod p)⁻¹) * (((c : ZMod p)⁻¹)^2)

lemma H112_eq_sum_E11 (p : ℕ) :
    H112 p = ∑ c ∈ Finset.Icc 1 (p - 1), E11 p (c - 1) * (((c : ZMod p)⁻¹)^2) := by
  simp [H112, E11, Finset.sum_mul, mul_assoc]



lemma H112_eq_sum_B11 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    H112 p = ∑ n ∈ Finset.Icc 1 (p - 1), B11 p n * (((n : ZMod p)⁻¹)^2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [H112_eq_sum_E11]
  trans ∑ c ∈ Finset.Icc 1 (p - 1), B11 p (p - c) * ((((p - c : ℕ) : ZMod p)⁻¹)^2)
  · apply Finset.sum_congr rfl
    intro c hc
    have hcb : 1 ≤ c ∧ c ≤ p - 1 := by simpa [Finset.mem_Icc] using hc
    rw [E11_prefix_reflect_eq_B11 p c hp hp7 hcb.1 hcb.2]
    have hcast : ((c : ZMod p)) = -((p - c : ℕ) : ZMod p) := by
      have hc_le_p : c ≤ p := by omega
      rw [Nat.cast_sub (R := ZMod p) hc_le_p]
      simp
    rw [hcast]
    have hneg : (-(((p - c : ℕ) : ZMod p)))⁻¹ = -((((p - c : ℕ) : ZMod p)⁻¹)) := inv_neg
    rw [hneg]
    ring
  · refine Finset.sum_bij (fun c _ => p - c) ?_ ?_ ?_ ?_
    · intro c hc
      simp [Finset.mem_Icc] at hc ⊢
      omega
    · intro a ha b hb hab
      simp [Finset.mem_Icc] at ha hb
      have hab' : p - a = p - b := hab
      omega
    · intro n hn
      refine ⟨p - n, ?_, ?_⟩
      · simp [Finset.mem_Icc] at hn ⊢
        omega
      · simp [Finset.mem_Icc] at hn
        have hsub : p - (p - n) = n := by omega
        simpa [hsub]
    · intro c hc
      simp






lemma H1_full_zero_ge_three (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) : H1 p (p - 1) = 0 := by
  simpa [H1] using inv_pow_sum_Icc_zmodp_zero p 1 hp (by norm_num) (by omega)

lemma H1_prefix_reflect_ge_three (p c : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hc1 : 1 ≤ c) (hcp : c ≤ p - 1) :
    H1 p (c - 1) = H1 p (p - c) := by
  have hsplit : H1 p (p - 1) = H1 p (c - 1) + ∑ i ∈ Finset.Icc c (p - 1), ((i : ZMod p)⁻¹) := by
    rw [H1, H1]
    have hfilter := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p - 1)) (fun i => i < c)
      (fun i : ℕ => ((i : ZMod p)⁻¹))
    have hleft : (Finset.Icc 1 (p - 1)).filter (fun i => i < c) = Finset.Icc 1 (c - 1) := by
      ext i
      simp [Finset.mem_Icc]
      omega
    have hright : (Finset.Icc 1 (p - 1)).filter (fun i => ¬ i < c) = Finset.Icc c (p - 1) := by
      ext i
      simp [Finset.mem_Icc]
      omega
    rw [hleft, hright] at hfilter
    exact hfilter.symm
  rw [H1_full_zero_ge_three p hp hp3, tail_H1_reflect p c hp hc1 hcp] at hsplit
  have h : H1 p (c - 1) - H1 p (p - c) = 0 := by
    simpa [sub_eq_add_neg] using hsplit.symm
  exact sub_eq_zero.mp h

lemma isUnit_natCast_zmod_prime_of_pos_lt (p i : ℕ) (hp : p.Prime)
    (hi0 : 0 < i) (hip : i < p) : IsUnit (i : ZMod p) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.symm <| (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hdiv
    exact not_le_of_gt hip (Nat.le_of_dvd hi0 hdiv))

lemma sum_Icc_one_eq_sum_range {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∑ k ∈ Finset.Icc 1 n, f k) = ∑ j ∈ Finset.range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, Finset.sum_range_succ]

lemma alternating_choose_shift_sum_zmod (p n : ℕ) :
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p)) = 1 := by
  have hZ := (Int.alternating_sum_range_choose_eq_choose (n := n) (m := n + 1))
  have hZ0 :
      (∑ k ∈ Finset.range (n + 2),
        (-1 : ℤ) ^ k * ((Nat.choose (n + 1) k : ℕ) : ℤ)) = 0 := by
    simpa [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self (n + 1))] using hZ
  have hZ1 :
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ j * ((Nat.choose (n + 1) (j + 1) : ℕ) : ℤ)) = 1 := by
    rw [Finset.sum_range_succ'] at hZ0
    simp only [Nat.cast_one, Nat.choose_zero_right, pow_zero, mul_one] at hZ0
    have hZ1' :
        - (∑ j ∈ Finset.range (n + 1),
            (-1 : ℤ) ^ j * ((Nat.choose (n + 1) (j + 1) : ℕ) : ℤ)) + 1 = 0 := by
      simpa [pow_succ, Finset.sum_neg_distrib, mul_assoc] using hZ0
    linarith
  have hcast := congrArg (fun z : ℤ => (z : ZMod p)) hZ1
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] at hcast
  simpa using hcast

lemma mul_choose_inv_succ_eq_shift_zmod (p n j : ℕ) (hp : p.Prime)
    (hjp : j + 1 < p) :
    ((n + 1 : ℕ) : ZMod p) *
        ((-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) *
          (((j + 1 : ℕ) : ZMod p)⁻¹)) =
      (-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p) := by
  have hcast :
      ((n + 1 : ℕ) : ZMod p) * (Nat.choose n j : ZMod p) =
        (Nat.choose (n + 1) (j + 1) : ZMod p) * (((j + 1 : ℕ) : ZMod p)) := by
    simpa [Nat.cast_mul] using congrArg (fun x : ℕ => (x : ZMod p)) (Nat.add_one_mul_choose_eq n j)
  have hjunit : IsUnit (((j + 1 : ℕ) : ZMod p)) :=
    isUnit_natCast_zmod_prime_of_pos_lt p (j + 1) hp (by omega) hjp
  calc
    ((n + 1 : ℕ) : ZMod p) *
        ((-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) *
          (((j + 1 : ℕ) : ZMod p)⁻¹))
        = (-1 : ZMod p) ^ j * (((n + 1 : ℕ) : ZMod p) *
            (Nat.choose n j : ZMod p)) * (((j + 1 : ℕ) : ZMod p)⁻¹) := by ring
    _ = (-1 : ZMod p) ^ j * ((Nat.choose (n + 1) (j + 1) : ZMod p) *
            (((j + 1 : ℕ) : ZMod p))) * (((j + 1 : ℕ) : ZMod p)⁻¹) := by rw [hcast]
    _ = (-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p) := by
      calc
        (-1 : ZMod p) ^ j * ((Nat.choose (n + 1) (j + 1) : ZMod p) *
            (((j + 1 : ℕ) : ZMod p))) * (((j + 1 : ℕ) : ZMod p)⁻¹)
            = ((-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p)) *
                ((((j + 1 : ℕ) : ZMod p) * (((j + 1 : ℕ) : ZMod p)⁻¹))) := by ring
        _ = (-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p) := by
          rw [ZMod.mul_inv_of_unit _ hjunit, mul_one]

lemma alternating_choose_inv_succ_sum_zmod (p n : ℕ) (hp : p.Prime) (hn : n + 1 < p) :
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) *
        (((j + 1 : ℕ) : ZMod p)⁻¹)) =
    (((n + 1 : ℕ) : ZMod p)⁻¹) := by
  have hnunit : IsUnit (((n + 1 : ℕ) : ZMod p)) :=
    isUnit_natCast_zmod_prime_of_pos_lt p (n + 1) hp (by omega) hn
  have hmul :
      ((n + 1 : ℕ) : ZMod p) *
        (∑ j ∈ Finset.range (n + 1),
          (-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) *
            (((j + 1 : ℕ) : ZMod p)⁻¹)) = 1 := by
    rw [Finset.mul_sum]
    trans (∑ j ∈ Finset.range (n + 1),
      (-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p))
    · apply Finset.sum_congr rfl
      intro j hj
      exact mul_choose_inv_succ_eq_shift_zmod p n j hp (by
        have hjlt : j < n + 1 := by simpa using hj
        omega)
    · exact alternating_choose_shift_sum_zmod p n
  calc
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) *
        (((j + 1 : ℕ) : ZMod p)⁻¹))
        = (((n + 1 : ℕ) : ZMod p)⁻¹) *
            (((n + 1 : ℕ) : ZMod p) *
              (∑ j ∈ Finset.range (n + 1),
                (-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) *
                  (((j + 1 : ℕ) : ZMod p)⁻¹))) := by
          rw [← mul_assoc, ZMod.inv_mul_of_unit _ hnunit, one_mul]
    _ = (((n + 1 : ℕ) : ZMod p)⁻¹) := by rw [hmul, mul_one]

lemma choose_inv_sq_eq_inv_succ_mul_shift_zmod (p n j : ℕ) (hp : p.Prime)
    (hn : n + 1 < p) (hj : j + 1 < p) :
    (-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) *
        ((((j + 1 : ℕ) : ZMod p)⁻¹) ^ 2) =
      (((n + 1 : ℕ) : ZMod p)⁻¹) *
        ((-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p) *
          (((j + 1 : ℕ) : ZMod p)⁻¹)) := by
  have hnunit : IsUnit (((n + 1 : ℕ) : ZMod p)) :=
    isUnit_natCast_zmod_prime_of_pos_lt p (n + 1) hp (by omega) hn
  have hshift := mul_choose_inv_succ_eq_shift_zmod p n j hp hj
  calc
    (-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) * ((((j + 1 : ℕ) : ZMod p)⁻¹) ^ 2)
        = (((((n + 1 : ℕ) : ZMod p)⁻¹) * (((n + 1 : ℕ) : ZMod p))) *
              ((-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) * (((j + 1 : ℕ) : ZMod p)⁻¹))) *
            (((j + 1 : ℕ) : ZMod p)⁻¹) := by
          rw [show (((n + 1 : ℕ) : ZMod p)⁻¹) * (((n + 1 : ℕ) : ZMod p)) = 1 by
            exact ZMod.inv_mul_of_unit _ hnunit]
          ring
    _ = (((n + 1 : ℕ) : ZMod p)⁻¹) *
            (((n + 1 : ℕ) : ZMod p) *
              ((-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) * (((j + 1 : ℕ) : ZMod p)⁻¹))) *
            (((j + 1 : ℕ) : ZMod p)⁻¹) := by ring
    _ = (((n + 1 : ℕ) : ZMod p)⁻¹) *
          ((-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p)) *
            (((j + 1 : ℕ) : ZMod p)⁻¹) := by rw [hshift]
    _ = (((n + 1 : ℕ) : ZMod p)⁻¹) *
        ((-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p) * (((j + 1 : ℕ) : ZMod p)⁻¹)) := by ring

lemma alt_choose_inv_sum_eq_range_H1_zmod (p n : ℕ) (hp : p.Prime) (hn : n < p) :
    (∑ j ∈ Finset.range n,
      (-1 : ZMod p) ^ j * (Nat.choose n (j + 1) : ZMod p) *
        (((j + 1 : ℕ) : ZMod p)⁻¹)) =
      ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ZMod p)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn' : n < p := by omega
      have hns : n + 1 < p := hn
      have hsplit :
          (∑ j ∈ Finset.range (n + 1),
            (-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p) *
              (((j + 1 : ℕ) : ZMod p)⁻¹)) =
          (∑ j ∈ Finset.range (n + 1),
            ((-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) * (((j + 1 : ℕ) : ZMod p)⁻¹) +
             (-1 : ZMod p) ^ j * (Nat.choose n (j + 1) : ZMod p) * (((j + 1 : ℕ) : ZMod p)⁻¹))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Nat.choose_succ_succ]
        norm_num
        ring
      rw [hsplit, Finset.sum_add_distrib]
      have htail :
          (∑ j ∈ Finset.range (n + 1),
            (-1 : ZMod p) ^ j * (Nat.choose n (j + 1) : ZMod p) * (((j + 1 : ℕ) : ZMod p)⁻¹)) =
          ∑ j ∈ Finset.range n,
            (-1 : ZMod p) ^ j * (Nat.choose n (j + 1) : ZMod p) * (((j + 1 : ℕ) : ZMod p)⁻¹) := by
        rw [Finset.sum_range_succ]
        simp
      rw [htail, alternating_choose_inv_succ_sum_zmod p n hp hns, ih hn']
      rw [Finset.sum_range_succ]
      ring


lemma shifted_alt_choose_inv_sq_sum_zmod (p n : ℕ) (hp : p.Prime) (hn : n + 1 < p) :
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) *
        ((((j + 1 : ℕ) : ZMod p)⁻¹) ^ 2)) =
      (∑ j ∈ Finset.range (n + 1), (((j + 1 : ℕ) : ZMod p)⁻¹)) *
        (((n + 1 : ℕ) : ZMod p)⁻¹) := by
  calc
    (∑ j ∈ Finset.range (n + 1),
      (-1 : ZMod p) ^ j * (Nat.choose n j : ZMod p) *
        ((((j + 1 : ℕ) : ZMod p)⁻¹) ^ 2))
      = (((n + 1 : ℕ) : ZMod p)⁻¹) *
          (∑ j ∈ Finset.range (n + 1),
            (-1 : ZMod p) ^ j * (Nat.choose (n + 1) (j + 1) : ZMod p) *
              (((j + 1 : ℕ) : ZMod p)⁻¹)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact choose_inv_sq_eq_inv_succ_mul_shift_zmod p n j hp hn (by
          have hjlt : j < n + 1 := by simpa using hj
          omega)
    _ = (((n + 1 : ℕ) : ZMod p)⁻¹) *
          (∑ j ∈ Finset.range (n + 1), (((j + 1 : ℕ) : ZMod p)⁻¹)) := by
        rw [alt_choose_inv_sum_eq_range_H1_zmod p (n + 1) hp hn]
    _ = (∑ j ∈ Finset.range (n + 1), (((j + 1 : ℕ) : ZMod p)⁻¹)) *
          (((n + 1 : ℕ) : ZMod p)⁻¹) := by ring

lemma neg_one_pow_self_mul (R : Type*) [CommRing R] (j : ℕ) :
    (-1 : R) ^ j * (-1 : R) ^ j = 1 := by
  rw [← pow_add, ← two_mul]
  rw [pow_mul]
  have hsq : (-1 : R) ^ 2 = 1 := by ring
  rw [hsq, one_pow]

lemma neg_one_pow_sub_eq_mul (R : Type*) [CommRing R] (N j : ℕ) (hj : j ≤ N) :
    (-1 : R) ^ (N - j) = (-1 : R) ^ N * (-1 : R) ^ j := by
  calc
    (-1 : R) ^ (N - j) = (-1 : R) ^ (N - j) * 1 := by ring
    _ = (-1 : R) ^ (N - j) * ((-1 : R) ^ j * (-1 : R) ^ j) := by
      rw [neg_one_pow_self_mul R j]
    _ = ((-1 : R) ^ (N - j) * (-1 : R) ^ j) * (-1 : R) ^ j := by ring
    _ = (-1 : R) ^ N * (-1 : R) ^ j := by
      rw [← pow_add, show N - j + j = N by omega]

lemma neg_one_pow_mul_sub_eq (R : Type*) [CommRing R] (N j : ℕ) (hj : j ≤ N) :
    (-1 : R) ^ N * (-1 : R) ^ (N - j) = (-1 : R) ^ j := by
  rw [neg_one_pow_sub_eq_mul R N j hj]
  calc
    (-1 : R) ^ N * ((-1 : R) ^ N * (-1 : R) ^ j)
        = ((-1 : R) ^ N * (-1 : R) ^ N) * (-1 : R) ^ j := by ring
    _ = (-1 : R) ^ j := by rw [neg_one_pow_self_mul R N]; ring


lemma neg_one_pow_p_sub_eq_r_pred (p r : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hr1 : 1 ≤ r) (hrp : r < p) :
    (-1 : ZMod p) ^ (p - r) = (-1 : ZMod p) ^ (r - 1) := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨a, ha⟩ := hpodd
  have hprod : (-1 : ZMod p) ^ (p - r) * (-1 : ZMod p) ^ (r - 1) = 1 := by
    rw [← pow_add, show p - r + (r - 1) = p - 1 by omega]
    have hp1 : p - 1 = a + a := by omega
    rw [hp1, pow_add]
    exact neg_one_pow_self_mul (ZMod p) a
  calc
    (-1 : ZMod p) ^ (p - r) = (-1 : ZMod p) ^ (p - r) * 1 := by ring
    _ = (-1 : ZMod p) ^ (p - r) * ((-1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) ^ (r - 1)) := by
      rw [neg_one_pow_self_mul (ZMod p) (r - 1)]
    _ = ((-1 : ZMod p) ^ (p - r) * (-1 : ZMod p) ^ (r - 1)) * (-1 : ZMod p) ^ (r - 1) := by ring
    _ = (-1 : ZMod p) ^ (r - 1) := by rw [hprod]; ring



theorem inner_sum_identity (p r : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr1 : 1 ≤ r) (hrp : r < p) :
    (∑ n ∈ Finset.Icc r (p - 1), ((Nat.choose n r : ℕ) : ZMod p) * (((n : ZMod p)⁻¹)^2)) =
      (-1 : ZMod p)^(r-1) * H1 p (r-1) * ((r : ZMod p)⁻¹) := by
  let N := p - 1 - r
  have hN : N = p - 1 - r := rfl
  have hNp : N + 1 < p := by dsimp [N]; omega
  haveI : Fact p.Prime := ⟨hp⟩

  have hN1 : N + 1 = p - r := by dsimp [N]; omega
  have h_reindex :
      (∑ n ∈ Finset.Icc r (p - 1), ((Nat.choose n r : ℕ) : ZMod p) * (((n : ZMod p)⁻¹)^2)) =
      ∑ m ∈ Finset.range (N + 1), ((Nat.choose (r + m) r : ℕ) : ZMod p) * ((((r + m : ℕ) : ZMod p)⁻¹)^2) := by
    refine Finset.sum_bij (fun n _ => n - r) ?_ ?_ ?_ ?_
    · intro n hn
      simp [Finset.mem_Icc] at hn ⊢
      dsimp [N]
      omega
    · intro a ha b hb hab
      simp [Finset.mem_Icc] at ha hb
      change a - r = b - r at hab
      have har : r ≤ a := ha.1
      have hbr : r ≤ b := hb.1
      omega
    · intro m hm
      refine ⟨r + m, ?_, ?_⟩
      · simp [Finset.mem_Icc] at hm ⊢
        dsimp [N] at hm
        omega
      · simp
    · intro n hn
      simp [Finset.mem_Icc] at hn
      have hn' : r + (n - r) = n := by omega
      simp [hn']
  rw [h_reindex]
  have h_reflect :
      (∑ m ∈ Finset.range (N + 1), ((Nat.choose (r + m) r : ℕ) : ZMod p) * ((((r + m : ℕ) : ZMod p)⁻¹)^2)) =
      ∑ m ∈ Finset.range (N + 1),
        (-1 : ZMod p)^m * ((Nat.choose N m : ℕ) : ZMod p) * ((((r + m : ℕ) : ZMod p)⁻¹)^2) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmle : m ≤ N := by simpa using hm
    rw [choose_reflect_zmod p r N m hp hN hr1 hrp hmle]
  rw [h_reflect]
  have h_reverse :
      (∑ m ∈ Finset.range (N + 1),
        (-1 : ZMod p)^m * ((Nat.choose N m : ℕ) : ZMod p) * ((((r + m : ℕ) : ZMod p)⁻¹)^2)) =
      (-1 : ZMod p)^N *
        (∑ j ∈ Finset.range (N + 1),
          (-1 : ZMod p)^j * ((Nat.choose N j : ℕ) : ZMod p) * ((((j + 1 : ℕ) : ZMod p)⁻¹)^2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun m _ => N - m) ?_ ?_ ?_ ?_
    · intro m hm
      simp at hm ⊢
    · intro a ha b hb hab
      simp at ha hb
      change N - a = N - b at hab
      have haN : a ≤ N := by omega
      have hbN : b ≤ N := by omega
      omega
    · intro j hj
      refine ⟨N - j, ?_, ?_⟩
      · simp at hj ⊢
      · simp at hj
        have hsub : N - (N - j) = j := by omega
        simpa [hsub]
    · intro m hm
      have hmle : m ≤ N := by simpa using hm
      have hchoose : Nat.choose N (N - m) = Nat.choose N m := by
        rw [Nat.choose_symm hmle]
      have hcast : ((r + m : ℕ) : ZMod p) = -(((N - m + 1 : ℕ) : ZMod p)) := by
        have hle : N - m + 1 ≤ p := by dsimp [N]; omega
        have hnat : r + m = p - (N - m + 1) := by dsimp [N]; omega
        rw [hnat, Nat.cast_sub (R := ZMod p) hle]
        simp
      rw [hchoose, hcast]
      have hinv : (-(((N - m + 1 : ℕ) : ZMod p)))⁻¹ = -((((N - m + 1 : ℕ) : ZMod p)⁻¹)) := by
        let x : ZMod p := ((N - m + 1 : ℕ) : ZMod p)
        change (-x)⁻¹ = -x⁻¹
        exact @inv_neg (ZMod p) _ _ x
      rw [hinv]
      have hsgn := neg_one_pow_mul_sub_eq (ZMod p) N m hmle
      rw [← hsgn]
      ring
  rw [h_reverse]
  rw [shifted_alt_choose_inv_sq_sum_zmod p N hp hNp]
  have hrange_H1 : (∑ j ∈ Finset.range (N + 1), (((j + 1 : ℕ) : ZMod p)⁻¹)) = H1 p (p - r) := by
    rw [← sum_Icc_one_eq_sum_range (N + 1) (fun k : ℕ => ((k : ZMod p)⁻¹)), H1, hN1]
  rw [hrange_H1]
  have hH : H1 p (p - r) = H1 p (r - 1) := by
    exact (H1_prefix_reflect_ge_three p r hp hp3 hr1 (by omega)).symm
  rw [hH]
  have hinv_pr : (((N + 1 : ℕ) : ZMod p)⁻¹) = -(((r : ℕ) : ZMod p)⁻¹) := by
    rw [hN1]
    have hcast : ((p - r : ℕ) : ZMod p) = -((r : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (R := ZMod p) (by omega : r ≤ p)]
      simp
    rw [hcast]
    let x : ZMod p := (r : ZMod p)
    change (-x)⁻¹ = -x⁻¹
    exact @inv_neg (ZMod p) _ _ x
  rw [hinv_pr]
  have hsign : (-1 : ZMod p)^N * -1 = (-1 : ZMod p)^(r - 1) := by
    have hNp' : N + 1 = p - r := hN1
    calc
      (-1 : ZMod p)^N * -1 = (-1 : ZMod p)^(N + 1) := by rw [pow_succ]
      _ = (-1 : ZMod p)^(p - r) := by rw [hNp']
      _ = (-1 : ZMod p)^(r - 1) := neg_one_pow_p_sub_eq_r_pred p r hp hp3 hr1 hrp
  calc
    (-1 : ZMod p) ^ N * (H1 p (r - 1) * -((r : ZMod p)⁻¹))
        = ((-1 : ZMod p)^N * -1) * H1 p (r - 1) * ((r : ZMod p)⁻¹) := by ring
    _ = (-1 : ZMod p) ^ (r - 1) * H1 p (r - 1) * ((r : ZMod p)⁻¹) := by rw [hsign]



def AltB (p n : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 n,
    (-1 : ZMod p) ^ (k - 1) * ((Nat.choose n k : ℕ) : ZMod p) * (((k : ZMod p)⁻¹)^2)

lemma AltB_succ (p n : ℕ) (hp : p.Prime) (hn : n + 1 < p) :
    AltB p (n + 1) = AltB p n + H1 p (n + 1) * (((n + 1 : ℕ) : ZMod p)⁻¹) := by
  rw [AltB, AltB]
  rw [sum_Icc_one_eq_sum_range (n + 1), sum_Icc_one_eq_sum_range n]
  simp only [Nat.add_sub_cancel_right]

  have hsplit :
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ZMod p) ^ j * ((Nat.choose (n + 1) (j + 1) : ℕ) : ZMod p) *
          ((((j + 1 : ℕ) : ZMod p)⁻¹)^2)) =
      (∑ j ∈ Finset.range (n + 1),
        ((-1 : ZMod p) ^ j * ((Nat.choose n j : ℕ) : ZMod p) *
            ((((j + 1 : ℕ) : ZMod p)⁻¹)^2) +
         (-1 : ZMod p) ^ j * ((Nat.choose n (j + 1) : ℕ) : ZMod p) *
            ((((j + 1 : ℕ) : ZMod p)⁻¹)^2))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.choose_succ_succ]
    norm_num
    ring
  rw [hsplit, Finset.sum_add_distrib]
  have htail :
      (∑ j ∈ Finset.range (n + 1),
        (-1 : ZMod p) ^ j * ((Nat.choose n (j + 1) : ℕ) : ZMod p) *
          ((((j + 1 : ℕ) : ZMod p)⁻¹)^2)) =
        ∑ j ∈ Finset.range n,
          (-1 : ZMod p) ^ j * ((Nat.choose n (j + 1) : ℕ) : ZMod p) *
            ((((j + 1 : ℕ) : ZMod p)⁻¹)^2) := by
    rw [Finset.sum_range_succ]
    simp
  have hhead := shifted_alt_choose_inv_sq_sum_zmod p n hp hn
  rw [hhead, htail]
  have hH : (∑ j ∈ Finset.range (n + 1), (((j + 1 : ℕ) : ZMod p)⁻¹)) = H1 p (n + 1) := by
    rw [← sum_Icc_one_eq_sum_range (n + 1) (fun k : ℕ => ((k : ZMod p)⁻¹)), H1]
  rw [hH]
  ring

lemma AltB_eq_B11 (p n : ℕ) (hp : p.Prime) (hn : n < p) :
    AltB p n = B11 p n := by
  induction n with
  | zero => simp [AltB, B11]
  | succ n ih =>
      have hn' : n < p := by omega
      rw [AltB_succ p n hp hn, B11_succ, ih hn']


def H13 (p : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1), H1 p (k - 1) * (((k : ZMod p)⁻¹)^3)



lemma H112_eq_H13 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : H112 p = H13 p := by
  rw [H112_eq_sum_B11 p hp hp7]
  have hBtoAlt :
      (∑ n ∈ Finset.Icc 1 (p - 1), B11 p n * (((n : ZMod p)⁻¹)^2)) =
      ∑ n ∈ Finset.Icc 1 (p - 1), AltB p n * (((n : ZMod p)⁻¹)^2) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnb : 1 ≤ n ∧ n ≤ p - 1 := by simpa [Finset.mem_Icc] using hn
    rw [← AltB_eq_B11 p n hp (by omega)]
  rw [hBtoAlt]
  simp only [AltB]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_sigma']
  let D₁ : Finset (Σ n : ℕ, ℕ) := (Finset.Icc 1 (p - 1)).sigma (fun n => Finset.Icc 1 n)
  let D₂ : Finset (Σ r : ℕ, ℕ) := (Finset.Icc 1 (p - 1)).sigma (fun r => Finset.Icc r (p - 1))
  change (∑ x ∈ D₁,
      ((-1 : ZMod p) ^ (x.2 - 1) * ((Nat.choose x.1 x.2 : ℕ) : ZMod p) * (((x.2 : ZMod p)⁻¹)^2)) * (((x.1 : ZMod p)⁻¹)^2)) = H13 p
  have hswap :
      (∑ x ∈ D₁,
      ((-1 : ZMod p) ^ (x.2 - 1) * ((Nat.choose x.1 x.2 : ℕ) : ZMod p) * (((x.2 : ZMod p)⁻¹)^2)) * (((x.1 : ZMod p)⁻¹)^2)) =
      (∑ y ∈ D₂,
        ((-1 : ZMod p) ^ (y.1 - 1) * (((y.1 : ZMod p)⁻¹)^2)) *
          (((Nat.choose y.2 y.1 : ℕ) : ZMod p) * (((y.2 : ZMod p)⁻¹)^2))) := by
    refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1⟩) (fun y _ => ⟨y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨n,r⟩
      simp [D₁, D₂, Finset.mem_Icc] at hx ⊢
      omega
    · intro y hy
      rcases y with ⟨r,n⟩
      simp [D₁, D₂, Finset.mem_Icc] at hy ⊢
      omega
    · intro x hx
      cases x
      simp
    · intro y hy
      cases y
      simp
    · intro x hx
      rcases x with ⟨n,r⟩
      ring
  rw [hswap]
  have hinner :
      (∑ y ∈ D₂,
        ((-1 : ZMod p) ^ (y.1 - 1) * (((y.1 : ZMod p)⁻¹)^2)) *
          (((Nat.choose y.2 y.1 : ℕ) : ZMod p) * (((y.2 : ZMod p)⁻¹)^2))) =
      ∑ r ∈ Finset.Icc 1 (p - 1),
        ((-1 : ZMod p) ^ (r - 1) * (((r : ZMod p)⁻¹)^2)) *
          (∑ n ∈ Finset.Icc r (p - 1), ((Nat.choose n r : ℕ) : ZMod p) * (((n : ZMod p)⁻¹)^2)) := by
    dsimp [D₂]
    rw [Finset.sum_sigma]
    simp [Finset.mul_sum]
  rw [hinner]
  have hsimpl :
      (∑ r ∈ Finset.Icc 1 (p - 1),
        ((-1 : ZMod p) ^ (r - 1) * (((r : ZMod p)⁻¹)^2)) *
          (∑ n ∈ Finset.Icc r (p - 1), ((Nat.choose n r : ℕ) : ZMod p) * (((n : ZMod p)⁻¹)^2))) =
      H13 p := by
    rw [H13]
    apply Finset.sum_congr rfl
    intro r hr
    have hrb : 1 ≤ r ∧ r ≤ p - 1 := by simpa [Finset.mem_Icc] using hr
    rw [inner_sum_identity p r hp (by omega) hrb.1 (by omega)]
    have hsgn : (-1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) ^ (r - 1) = 1 := neg_one_pow_self_mul (ZMod p) (r - 1)
    calc
      ((-1 : ZMod p) ^ (r - 1) * ((r : ZMod p)⁻¹ ^ 2)) *
          ((-1 : ZMod p) ^ (r - 1) * H1 p (r - 1) * (r : ZMod p)⁻¹)
          = (((-1 : ZMod p) ^ (r - 1) * (-1 : ZMod p) ^ (r - 1)) * H1 p (r - 1)) *
              (((r : ZMod p)⁻¹)^2 * (r : ZMod p)⁻¹) := by ring
      _ = H1 p (r - 1) * (((r : ZMod p)⁻¹)^3) := by
            rw [hsgn]
            ring
  exact hsimpl


def H31 (p : ℕ) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1),
    ∑ i ∈ Finset.Icc 1 (k - 1),
      (((i : ZMod p)⁻¹) ^ 3) * ((k : ZMod p)⁻¹)

lemma H31_eq_H13 (p : ℕ) (hp : p.Prime) : H31 p = H13 p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos

  let S : Finset ℕ := Finset.Icc 1 (p - 1)
  let D : Finset (Σ k : ℕ, ℕ) := S.sigma (fun k => Finset.Icc 1 (k - 1))
  rw [H31, H13]
  simp_rw [H1]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  change
      (∑ x ∈ D, (((x.2 : ZMod p)⁻¹) ^ 3) * ((x.1 : ZMod p)⁻¹)) =
        (∑ x ∈ D, ((x.2 : ZMod p)⁻¹) * (((x.1 : ZMod p)⁻¹) ^ 3))
  refine Finset.sum_bij' (fun x _ => ⟨p - x.2, p - x.1⟩)
      (fun x _ => ⟨p - x.2, p - x.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx ⊢
    omega
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx ⊢
    omega
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx
    have hpk : p - (p - k) = k := by omega
    have hpi : p - (p - i) = i := by omega
    simp [hpk, hpi]
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx
    have hpk : p - (p - k) = k := by omega
    have hpi : p - (p - i) = i := by omega
    simp [hpk, hpi]
  · intro x hx
    rcases x with ⟨k, i⟩
    simp [D, S, Finset.mem_Icc] at hx
    have hkcast : ((p - k : ℕ) : ZMod p) = - (k : ZMod p) := by
      rw [Nat.cast_sub (by omega : k ≤ p)]
      simp
    have hicast : ((p - i : ℕ) : ZMod p) = - (i : ZMod p) := by
      rw [Nat.cast_sub (by omega : i ≤ p)]
      simp
    simp [hkcast, hicast, inv_neg]
    ring


theorem power_sum_stuffle_H13_H31 (p : ℕ) :
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)) *
      (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 3)) =
        H13 p + H31 p +
          (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (p - 1)
  let R := ZMod p
  let f : ℕ → R := fun i => ((i : R)⁻¹)
  let g : ℕ → R := fun i => ((i : R)⁻¹)^3
  have hsplit (b : ℕ) (hb : b ∈ S) :
      (∑ a ∈ S, f a * g b) =
        (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
        (f b * g b) +
        (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by
    have hlt : S.filter (fun a => a < b) = Finset.Icc 1 (b - 1) := by
      ext a
      simp [S, Finset.mem_Icc] at hb ⊢
      omega
    have hnotlt : S.filter (fun a => ¬ a < b) = Finset.Icc b (p - 1) := by
      ext a
      simp [S, Finset.mem_Icc] at hb ⊢
      omega
    have htail : Finset.Icc b (p - 1) = insert b (Finset.Icc (b + 1) (p - 1)) := by
      have hbS : 1 ≤ b ∧ b ≤ p - 1 := by simpa [S, Finset.mem_Icc] using hb
      have hb_le : b ≤ p - 1 := hbS.2
      ext a
      simp [Finset.mem_Icc]
      constructor
      · intro ha
        by_cases hab : a = b
        · exact Or.inl hab
        · exact Or.inr (by omega)
      · intro ha
        rcases ha with h | h
        · subst a
          exact ⟨le_rfl, hb_le⟩
        · exact ⟨by omega, h.2⟩
    have hbnot : b ∉ Finset.Icc (b + 1) (p - 1) := by
      simp [Finset.mem_Icc]
    calc
      (∑ a ∈ S, f a * g b)
          = (∑ a ∈ S.filter (fun a => a < b), f a * g b) +
              (∑ a ∈ S.filter (fun a => ¬ a < b), f a * g b) := by
            rw [← Finset.sum_filter_add_sum_filter_not S (fun a => a < b) (fun a => f a * g b)]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
              (∑ a ∈ Finset.Icc b (p - 1), f a * g b) := by rw [hlt, hnotlt]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
              (∑ a ∈ insert b (Finset.Icc (b + 1) (p - 1)), f a * g b) := by rw [htail]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
              (f b * g b + ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by
            rw [Finset.sum_insert hbnot]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
          (f b * g b) +
          (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by ring
  have hupper :
      (∑ b ∈ S, ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) = H31 p := by
    rw [H31]
    rw [Finset.sum_sigma', Finset.sum_sigma']
    let D₁ : Finset (Σ b : ℕ, ℕ) := S.sigma (fun b => Finset.Icc (b + 1) (p - 1))
    let D₂ : Finset (Σ a : ℕ, ℕ) := S.sigma (fun a => Finset.Icc 1 (a - 1))
    change (∑ x ∈ D₁, f x.2 * g x.1) =
        (∑ x ∈ D₂, ((x.2 : R)⁻¹)^3 * ((x.1 : R)⁻¹))
    refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1⟩) (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨b, a⟩
      simp [D₁, D₂, S, Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx
      rcases x with ⟨a, b⟩
      simp [D₁, D₂, S, Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx
      cases x
      simp
    · intro x hx
      cases x
      simp
    · intro x hx
      rcases x with ⟨b, a⟩
      simp [f, g]
      ring
  have hdiag :
      (∑ b ∈ S, f b * g b) =
        (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, g]
    ring
  calc
    (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)) *
      (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 3))
        = ∑ b ∈ S, ∑ a ∈ S, f a * g b := by
            simp [S, f, g, Finset.mul_sum, mul_comm]
    _ = ∑ b ∈ S,
          ((∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
            (f b * g b) +
            (∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b)) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hsplit b hb
    _ = (∑ b ∈ S, ∑ a ∈ Finset.Icc 1 (b - 1), f a * g b) +
          (∑ b ∈ S, f b * g b) +
          (∑ b ∈ S, ∑ a ∈ Finset.Icc (b + 1) (p - 1), f a * g b) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = H13 p + H31 p +
          (∑ i ∈ Finset.Icc 1 (p - 1), (((i : ZMod p)⁻¹) ^ 4)) := by
          rw [hupper, hdiag]
          simp [H13, H1, S, f, g, Finset.sum_mul]
          ring


theorem H13_eq_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : H13 p = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hP1 := inv_pow_sum_Icc_zmodp_zero p 1 hp (by norm_num) (by omega)
  have hP1' : (∑ i ∈ Finset.Icc 1 (p - 1), ((i : ZMod p)⁻¹)) = 0 := by
    simpa using hP1
  have hP3 := inv_pow_sum_Icc_zmodp_zero p 3 hp (by norm_num) (by omega)
  have hP4 := inv_pow_sum_Icc_zmodp_zero p 4 hp (by norm_num) (by omega)
  have hstuff := power_sum_stuffle_H13_H31 p
  rw [hP1', hP3, zero_mul, H31_eq_H13 p hp, hP4] at hstuff
  have htwo : (2 : ZMod p) * H13 p = 0 := by
    simpa [two_mul, add_assoc] using hstuff.symm
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact (mul_eq_zero.mp htwo).resolve_left htwo_ne


theorem H112_eq_zero (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : H112 p = 0 := by
  rw [H112_eq_H13 p hp hp7, H13_eq_zero p hp hp7]



end H112BinomialRoutePort



lemma prefix_square_decomp_modp (p k : ℕ) :
    (∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod p)⁻¹)) ^ 2 =
      (2 : ZMod p) *
        (∑ b ∈ Finset.Icc 1 (k - 1),
          ∑ a ∈ Finset.Icc 1 (b - 1), ((a : ZMod p)⁻¹) * ((b : ZMod p)⁻¹)) +
        (∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod p)⁻¹)^2) := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (k - 1)
  let R := ZMod p
  let f : ℕ → R := fun i => ((i : R)⁻¹)
  have hsplit (b : ℕ) (hb : b ∈ S) :
      (∑ a ∈ S, f a * f b) =
        (∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
        (f b * f b) +
        (∑ a ∈ Finset.Icc (b + 1) (k - 1), f a * f b) := by
    have hlt : S.filter (fun a => a < b) = Finset.Icc 1 (b - 1) := by
      ext a
      simp [S, Finset.mem_Icc] at hb ⊢
      omega
    have hnotlt : S.filter (fun a => ¬ a < b) = Finset.Icc b (k - 1) := by
      ext a
      simp [S, Finset.mem_Icc] at hb ⊢
      omega
    have htail : Finset.Icc b (k - 1) = insert b (Finset.Icc (b + 1) (k - 1)) := by
      have hbS : 1 ≤ b ∧ b ≤ k - 1 := by simpa [S, Finset.mem_Icc] using hb
      ext a
      simp [Finset.mem_Icc]
      constructor
      · intro ha
        by_cases hab : a = b
        · exact Or.inl hab
        · exact Or.inr (by omega)
      · intro ha
        rcases ha with h | h
        · subst a
          exact ⟨le_rfl, hbS.2⟩
        · exact ⟨by omega, h.2⟩
    have hbnot : b ∉ Finset.Icc (b + 1) (k - 1) := by simp [Finset.mem_Icc]
    calc
      (∑ a ∈ S, f a * f b)
          = (∑ a ∈ S.filter (fun a => a < b), f a * f b) +
              (∑ a ∈ S.filter (fun a => ¬ a < b), f a * f b) := by
            rw [← Finset.sum_filter_add_sum_filter_not S (fun a => a < b) (fun a => f a * f b)]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
              (∑ a ∈ Finset.Icc b (k - 1), f a * f b) := by rw [hlt, hnotlt]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
              (∑ a ∈ insert b (Finset.Icc (b + 1) (k - 1)), f a * f b) := by rw [htail]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
              (f b * f b + ∑ a ∈ Finset.Icc (b + 1) (k - 1), f a * f b) := by
            rw [Finset.sum_insert hbnot]
      _ = (∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
          (f b * f b) +
          (∑ a ∈ Finset.Icc (b + 1) (k - 1), f a * f b) := by ring
  have hupper :
      (∑ b ∈ S, ∑ a ∈ Finset.Icc (b + 1) (k - 1), f a * f b) =
        (∑ b ∈ S, ∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    let D₁ : Finset (Σ b : ℕ, ℕ) := S.sigma (fun b => Finset.Icc (b + 1) (k - 1))
    let D₂ : Finset (Σ a : ℕ, ℕ) := S.sigma (fun a => Finset.Icc 1 (a - 1))
    change (∑ x ∈ D₁, f x.2 * f x.1) = (∑ x ∈ D₂, f x.2 * f x.1)
    refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1⟩) (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rcases x with ⟨b, a⟩
      simp [D₁, D₂, S, Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx
      rcases x with ⟨a, b⟩
      simp [D₁, D₂, S, Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx; cases x; simp
    · intro x hx; cases x; simp
    · intro x hx
      rcases x with ⟨b, a⟩
      ring
  have hdiag : (∑ b ∈ S, f b * f b) = ∑ i ∈ S, f i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    (∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod p)⁻¹)) ^ 2
        = (∑ i ∈ S, f i) * (∑ i ∈ S, f i) := by simp [S, f, pow_two]
    _ = ∑ b ∈ S, ∑ a ∈ S, f a * f b := by simp [Finset.mul_sum, mul_comm]
    _ = ∑ b ∈ S,
          ((∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
            (f b * f b) + (∑ a ∈ Finset.Icc (b + 1) (k - 1), f a * f b)) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hsplit b hb
    _ = (∑ b ∈ S, ∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
          (∑ b ∈ S, f b * f b) +
          (∑ b ∈ S, ∑ a ∈ Finset.Icc (b + 1) (k - 1), f a * f b) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (2 : R) * (∑ b ∈ S, ∑ a ∈ Finset.Icc 1 (b - 1), f a * f b) +
          (∑ i ∈ S, f i ^ 2) := by
          rw [hupper, hdiag]
          ring
    _ = (2 : ZMod p) *
        (∑ b ∈ Finset.Icc 1 (k - 1),
          ∑ a ∈ Finset.Icc 1 (b - 1), ((a : ZMod p)⁻¹) * ((b : ZMod p)⁻¹)) +
        (∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod p)⁻¹)^2) := by simp [S, f]

lemma castHom_prefixH112_mod_five (p : ℕ) (hp : p.Prime) :
    ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p) (prefixH112 p) =
      (2 : ZMod p) * H112BinomialRoutePort.H112 p + H22modp p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [prefixH112]
  rw [map_sum]
  calc
    (∑ x ∈ Finset.Icc 1 (p - 1),
      ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p)
        (lowerH1 p x ^ 2 * ((x : ZMod (p ^ 5))⁻¹) ^ 2))
        = ∑ k ∈ Finset.Icc 1 (p - 1),
            ((∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod p)⁻¹)) ^ 2) * (((k : ZMod p)⁻¹)^2) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkb : 1 ≤ k ∧ k ≤ p - 1 := by simpa [Finset.mem_Icc] using hk
          rw [map_mul, map_pow]
          dsimp [lowerH1]
          change (ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p)
              (∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod (p ^ 5))⁻¹))) ^ 2 *
            (ZMod.castHom (dvd_pow_self p (by norm_num : 5 ≠ 0)) (ZMod p)
              (((k : ZMod (p ^ 5))⁻¹)^2)) =
            (∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod p)⁻¹)) ^ 2 * (((k : ZMod p)⁻¹)^2)
          rw [map_sum]
          rw [castHom_inv_pow_nat_mod_five p k 2 hp (by omega) (by omega)]
          congr 1
          apply congrArg (fun y : ZMod p => y ^ 2)
          apply Finset.sum_congr rfl
          intro i hi
          have hib : 1 ≤ i ∧ i ≤ k - 1 := by simpa [Finset.mem_Icc] using hi
          simpa using castHom_inv_pow_nat_mod_five p i 1 hp (by omega) (by omega)
    _ = ∑ k ∈ Finset.Icc 1 (p - 1),
          (((2 : ZMod p) *
            (∑ b ∈ Finset.Icc 1 (k - 1),
              ∑ a ∈ Finset.Icc 1 (b - 1), ((a : ZMod p)⁻¹) * ((b : ZMod p)⁻¹)) +
            (∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod p)⁻¹)^2)) * (((k : ZMod p)⁻¹)^2)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [prefix_square_decomp_modp p k]
    _ = (2 : ZMod p) * H112BinomialRoutePort.H112 p + H22modp p := by
          rw [H112BinomialRoutePort.H112, H22modp]
          simp_rw [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
          ring_nf



theorem hW112_from_modp (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 5))^4 * prefixH112 p = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply p_four_mul_eq_zero_of_castHom_eq_zero p
  rw [castHom_prefixH112_mod_five p hp]
  rw [H112BinomialRoutePort.H112_eq_zero p hp hp7, H22modp_eq_zero p hp hp7]
  ring




lemma castHom_prefixH12_mod_five_to_three (p : ℕ) (hp : p.Prime) :
    ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3)) (prefixH12 p) =
      Scratch.KeyDepthCongruencePrimeGeSevenScratch.A p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [prefixH12, Scratch.KeyDepthCongruencePrimeGeSevenScratch.A]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkb : 1 ≤ k ∧ k ≤ p - 1 := by simpa [Finset.mem_Icc] using hk
  rw [map_mul]
  dsimp [lowerH1]
  change (ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3))
      (∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod (p ^ 5))⁻¹))) *
    (ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3))
      (((k : ZMod (p ^ 5))⁻¹)^2)) =
    ∑ i ∈ Finset.Icc 1 (k - 1), ((i : ZMod (p ^ 3))⁻¹) * (((k : ZMod (p ^ 3))⁻¹) ^ 2)
  rw [map_sum]
  rw [castHom_inv_pow_nat_mod_five_to_three p k 2 hp (by omega) (by omega)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hib : 1 ≤ i ∧ i ≤ k - 1 := by simpa [Finset.mem_Icc] using hi
  congr 1
  simpa using castHom_inv_pow_nat_mod_five_to_three p i 1 hp (by omega) (by omega)



theorem key_depth_congruence_zmod_three_from_port (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    Scratch.KeyDepthCongruencePrimeGeSevenScratch.keyDepthCongruence p := by
  have hEval : Scratch.KeyDepthCongruencePrimeGeSevenScratch.alternatingH2SecondEvaluation p :=
    Scratch.KeyDepthCongruencePrimeGeSevenScratch.alternatingH2SecondEvaluation_prime_ge_seven p hp hp7
  have h112 : Scratch.KeyDepthCongruencePrimeGeSevenScratch.H112 p = 0 := by
    simpa [Scratch.KeyDepthCongruencePrimeGeSevenScratch.H112, H112BinomialRoutePort.H112] using
      (H112BinomialRoutePort.H112_eq_zero p hp hp7)
  have hT : ((p : ZMod (p ^ 3)) ^ 2) * Scratch.KeyDepthCongruencePrimeGeSevenScratch.T p = 0 :=
    Scratch.KeyDepthCongruencePrimeGeSevenScratch.p_sq_mul_T_zero_of_H112_zero p hp hp7 h112
  have hVanish : Scratch.KeyDepthCongruencePrimeGeSevenScratch.keyDepthReducedVanishings p :=
    Scratch.KeyDepthCongruencePrimeGeSevenScratch.keyDepthReducedVanishings_of_T p hp hp7 hT
  exact Scratch.KeyDepthCongruencePrimeGeSevenScratch.key_depth_congruence_prime_ge_seven p hp hp7 hEval hVanish




theorem hKey_from_key_depth (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
  (3 : ZMod (p^5))*(p : ZMod (p^5))^2*Hpow p 2 =
  (2 : ZMod (p^5))*(p : ZMod (p^5))^3*prefixH12 p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let R5 := ZMod (p ^ 5)
  let x : R5 := (3 : R5) * Hpow p 2 - (2 : R5) * (p : R5) * prefixH12 p
  have hxcast : ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3)) x = 0 := by
    have hkey := key_depth_congruence_zmod_three_from_port p hp hp7
    dsimp only [x]
    change ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3))
        (((3 : R5) * Hpow p 2) - ((2 : R5) * (p : R5) * prefixH12 p)) = 0
    simp only [map_sub, map_mul, map_natCast]
    rw [castHom_Hpow_mod_five_to_three p 2 hp]
    rw [castHom_prefixH12_mod_five_to_three p hp]
    have hkey0 : (3 : ZMod (p ^ 3)) * Scratch.KeyDepthCongruencePrimeGeSevenScratch.H2 p -
        (2 : ZMod (p ^ 3)) * (p : ZMod (p ^ 3)) * Scratch.KeyDepthCongruencePrimeGeSevenScratch.A p = 0 := by
      rw [hkey]
      ring
    have h3map : ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3)) (3 : R5) =
        (3 : ZMod (p ^ 3)) := by
      exact ZMod.cast_natCast (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) 3
    have h2map : ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3)) (2 : R5) =
        (2 : ZMod (p ^ 3)) := by
      exact ZMod.cast_natCast (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) 2
    rw [h3map, h2map]
    simpa [Scratch.KeyDepthCongruencePrimeGeSevenScratch.H2] using hkey0
  have hxzero : (p : R5) ^ 2 * x = 0 :=
    p_sq_mul_eq_zero_of_castHom_p5_to_p3_eq_zero p x hxcast
  dsimp [x, R5] at hxzero
  linear_combination hxzero




theorem p_four_mul_Hpow_eq_zero_of_pos_lt (p n : ℕ) (hp : p.Prime) (hn0 : 0 < n) (hnlt : n < p - 1) :
    (p : ZMod (p ^ 5))^4 * Hpow p n = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply p_four_mul_eq_zero_of_castHom_eq_zero p
  rw [castHom_Hpow_mod_five p n hp]
  exact inv_pow_sum_Icc_zmodp_zero p n hp hn0 hnlt


theorem hE4zero_from_newton_power_sums (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 5))^4 *
      listESymm4 (Finset.Icc 1 (p - 1)).toList (fun i : ℕ => (i : ZMod (p ^ 5))⁻¹) = 0 := by
  let R := ZMod (p ^ 5)
  let S := Finset.Icc 1 (p - 1)
  let f : ℕ → R := fun i => (i : R)⁻¹
  have hNewton : (24 : R) * listESymm4 S.toList f =
      (Hpow p 1)^4 - (6 : R) * (Hpow p 1)^2 * Hpow p 2 +
        (3 : R) * (Hpow p 2)^2 + (8 : R) * Hpow p 1 * Hpow p 3 -
        (6 : R) * Hpow p 4 := by
    have h := twentyfour_mul_listESymm4_eq_power_sums (l := S.toList) (f := f)
    simpa [Hpow, listPowerSum, S, f] using h
  have hP1 : (p : R)^4 * Hpow p 1 = 0 :=
    p_four_mul_Hpow_eq_zero_of_pos_lt p 1 hp (by norm_num) (by omega)
  have hP2 : (p : R)^4 * Hpow p 2 = 0 :=
    p_four_mul_Hpow_eq_zero_of_pos_lt p 2 hp (by norm_num) (by omega)
  have hP3 : (p : R)^4 * Hpow p 3 = 0 :=
    p_four_mul_Hpow_eq_zero_of_pos_lt p 3 hp (by norm_num) (by omega)
  have hP4 : (p : R)^4 * Hpow p 4 = 0 :=
    p_four_mul_Hpow_eq_zero_of_pos_lt p 4 hp (by norm_num) (by omega)
  apply (isUnit_24_zmod_prime_pow_five p hp hp7).mul_left_cancel
  calc
    (24 : R) * ((p : R)^4 * listESymm4 S.toList f)
        = (p : R)^4 * ((24 : R) * listESymm4 S.toList f) := by ring
    _ = (p : R)^4 * ((Hpow p 1)^4 - (6 : R) * (Hpow p 1)^2 * Hpow p 2 +
        (3 : R) * (Hpow p 2)^2 + (8 : R) * Hpow p 1 * Hpow p 3 -
        (6 : R) * Hpow p 4) := by rw [hNewton]
    _ = 0 := by
      linear_combination ((Hpow p 1)^3) * hP1 + (-(6 : R) * (Hpow p 1)^2) * hP2 +
        ((3 : R) * Hpow p 2) * hP2 + ((8 : R) * Hpow p 1) * hP3 + (-(6 : R)) * hP4
    _ = (24 : R) * 0 := by ring



theorem hW4_from_power_sum_modp (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 5))^4 * Hpow p 4 = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply p_four_mul_eq_zero_of_castHom_eq_zero p
  rw [castHom_Hpow_mod_five p 4 hp]
  exact inv_fourth_sum_Icc_zmodp_zero p hp hp7





theorem hP1sq_from_pairing (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 5))^2 * (Hpow p 1)^2 = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply p_sq_mul_eq_zero_of_castHom_p5_to_p3_eq_zero p
  rw [map_pow]
  rw [castHom_Hpow_mod_five_to_three p 1 hp]
  simpa using harmonic_one_square_zmodp3_zero p hp hp7



theorem hP3_from_pairing (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (p : ZMod (p ^ 5))^3 * Hpow p 3 = 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let x : ZMod (p ^ 5) := (p : ZMod (p ^ 5)) * Hpow p 3
  have hx : ZMod.castHom (Nat.pow_dvd_pow p (by norm_num : 3 ≤ 5)) (ZMod (p ^ 3)) x = 0 := by
    rw [show x = (p : ZMod (p ^ 5)) * Hpow p 3 by rfl]
    rw [map_mul]
    rw [castHom_Hpow_mod_five_to_three p 3 hp]
    simpa using harmonic_cube_zmodp3_p_mul_zero p hp hp7
  have hxzero := p_sq_mul_eq_zero_of_castHom_p5_to_p3_eq_zero p x hx
  dsimp [x] at hxzero
  calc
    (p : ZMod (p ^ 5))^3 * Hpow p 3 = (p : ZMod (p ^ 5))^2 * ((p : ZMod (p ^ 5)) * Hpow p 3) := by ring
    _ = 0 := hxzero




theorem hRel_from_pairing (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (2 : ZMod (p^5))*(p : ZMod (p^5))*Hpow p 1 + (p : ZMod (p^5))^2*Hpow p 2 = 0 := by
  let R := ZMod (p ^ 5)
  let S : Finset ℕ := Finset.Icc 1 (p - 1)
  let P : R := (p : R)
  have hH : Hpow p 1 =
      - Hpow p 1 - P * Hpow p 2 - P^2 * Hpow p 3 - P^3 * Hpow p 4 - P^4 * Hpow p 5 := by
    rw [Hpow]
    change (∑ i ∈ S, ((i : R)⁻¹)^1) =
      - Hpow p 1 - P * Hpow p 2 - P^2 * Hpow p 3 - P^3 * Hpow p 4 - P^4 * Hpow p 5
    simp only [pow_one]
    calc
      (∑ i ∈ S, ((i : R)⁻¹)) = ∑ i ∈ S, (((p - i : ℕ) : R)⁻¹) := by
        refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
        · intro i hi
          simp [S, Finset.mem_Icc] at hi ⊢
          omega
        · intro a ha b hb hab
          simp [S, Finset.mem_Icc] at ha hb
          have hsub : p - a = p - b := hab
          omega
        · intro b hb
          refine ⟨p - b, ?_, ?_⟩
          · simp [S, Finset.mem_Icc] at hb ⊢
            omega
          · simp [S, Finset.mem_Icc] at hb
            change p - (p - b) = b
            omega
        · intro i hi
          simp [S, Finset.mem_Icc] at hi
          have hppi : p - (p - i) = i := by omega
          simp [hppi]
      _ = ∑ i ∈ S,
            (- ((i : R)⁻¹) - P * ((i : R)⁻¹)^2 -
              P^2 * ((i : R)⁻¹)^3 - P^3 * ((i : R)⁻¹)^4 -
              P^4 * ((i : R)⁻¹)^5) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hib : 1 ≤ i ∧ i ≤ p - 1 := by simpa [S, Finset.mem_Icc] using hi
        simpa [R, P] using inv_p_sub_expansion_mod_five p i hp (by omega) (by omega)
      _ = - Hpow p 1 - P * Hpow p 2 - P^2 * Hpow p 3 - P^3 * Hpow p 4 - P^4 * Hpow p 5 := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        rw [Finset.sum_neg_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
        simp [Hpow, S, R, P]
  have hsum0 : (2 : R) * Hpow p 1 + P * Hpow p 2 + P^2 * Hpow p 3 + P^3 * Hpow p 4 + P^4 * Hpow p 5 = 0 := by
    linear_combination hH
  have hbig : (2 : R) * P * Hpow p 1 + P^2 * Hpow p 2 + P^3 * Hpow p 3 + P^4 * Hpow p 4 + P^5 * Hpow p 5 = 0 := by
    linear_combination P * hsum0
  have hP3 : P^3 * Hpow p 3 = 0 := by
    simpa [R, P] using hP3_from_pairing p hp hp7
  have hW4 : P^4 * Hpow p 4 = 0 := by
    simpa [R, P] using hW4_from_power_sum_modp p hp hp7
  have hP5 : P^5 * Hpow p 5 = 0 := by
    have hp5zero : P^5 = 0 := by
      dsimp [P, R]
      exact p_pow_five_zmod_zero p
    rw [hp5zero, zero_mul]
  change (2 : R) * P * Hpow p 1 + P^2 * Hpow p 2 = 0
  linear_combination hbig - hP3 - hW4 - hP5



theorem hE3zero_from_newton (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hRel : (2 : ZMod (p ^ 5))*(p : ZMod (p ^ 5))*Hpow p 1 +
        (p : ZMod (p ^ 5))^2*Hpow p 2 = 0) :
    (p : ZMod (p ^ 5))^3 *
      listESymm3 (Finset.Icc 1 (p - 1)).toList (fun i : ℕ => (i : ZMod (p ^ 5))⁻¹) = 0 := by
  let R := ZMod (p ^ 5)
  let S := Finset.Icc 1 (p - 1)
  let f : ℕ → R := fun i => (i : R)⁻¹
  let P1 : R := Hpow p 1
  let P2 : R := Hpow p 2
  let P3 : R := Hpow p 3
  have hNewton : (6 : R) * listESymm3 S.toList f =
      P1 ^ 3 - (3 : R) * P1 * P2 + (2 : R) * P3 := by
    have h := six_mul_listESymm3_eq_power_sums (l := S.toList) (f := f)
    simpa [Hpow, listPowerSum, S, f, P1, P2, P3] using h
  have hP1sq : (p : R)^2 * P1^2 = 0 := by
    simpa [R, P1] using hP1sq_from_pairing p hp hp7
  have hP3 : (p : R)^3 * P3 = 0 := by
    simpa [R, P3] using hP3_from_pairing p hp hp7
  have hRel' : (2 : R) * (p : R) * P1 + (p : R)^2 * P2 = 0 := by
    simpa [R, P1, P2] using hRel
  have hP1P2 : (p : R)^3 * P1 * P2 = 0 := by
    linear_combination ((p : R) * P1) * hRel' - (2 : R) * hP1sq
  apply (isUnit_6_zmod_prime_pow_five p hp hp7).mul_left_cancel
  calc
    (6 : R) * ((p : R)^3 * listESymm3 S.toList f)
        = (p : R)^3 * ((6 : R) * listESymm3 S.toList f) := by ring
    _ = (p : R)^3 * (P1 ^ 3 - (3 : R) * P1 * P2 + (2 : R) * P3) := by rw [hNewton]
    _ = 0 := by
      linear_combination ((p : R) * P1) * hP1sq + (-(3 : R)) * hP1P2 + (2 : R) * hP3
    _ = (6 : R) * 0 := by ring



theorem tailSum_eq_endpointPoly_combo_from_harmonic_assumptions (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hP1sq : (p : ZMod (p ^ 5))^2 * (Hpow p 1)^2 = 0)
    (hP3 : (p : ZMod (p ^ 5))^3 * Hpow p 3 = 0)
    (hW112 : (p : ZMod (p ^ 5))^4 * prefixH112 p = 0)
    (hW22 : (p : ZMod (p ^ 5))^4 * prefixH22 p = 0)
    (hW13 : (p : ZMod (p ^ 5))^4 * prefixH13 p = 0)
    (hW4 : (p : ZMod (p ^ 5))^4 * Hpow p 4 = 0)
    (hE3zero : (p : ZMod (p ^ 5))^3 * listESymm3 (Finset.Icc 1 (p - 1)).toList (fun i : ℕ => (i : ZMod (p ^ 5))⁻¹) = 0)
    (hE4zero : (p : ZMod (p ^ 5))^4 * listESymm4 (Finset.Icc 1 (p - 1)).toList (fun i : ℕ => (i : ZMod (p ^ 5))⁻¹) = 0)
    (hRel : (2 : ZMod (p ^ 5))*(p : ZMod (p ^ 5))*Hpow p 1 + (p : ZMod (p ^ 5))^2*Hpow p 2 = 0)
    (hKey : (3 : ZMod (p ^ 5))*(p : ZMod (p ^ 5))^2*Hpow p 2 =
      (2 : ZMod (p ^ 5))*(p : ZMod (p ^ 5))^3*prefixH12 p) :
    tailSum p = tailHarmonicRHS p := by
  let R := ZMod (p ^ 5)
  let S := Finset.Icc 1 (p - 1)
  let f : ℕ → R := fun i => (i : R)⁻¹
  have hE2 : (2 : R) * listESymm2 S.toList f = (Hpow p 1)^2 - Hpow p 2 := by
    have h := two_mul_listESymm2_eq_power_sums (l := S.toList) (f := f)
    simpa [Hpow, listPowerSum, S, f] using h
  have h24 := collected_tail_endpoint_algebra_24
    (p := (p : R)) (P1 := Hpow p 1) (P2 := Hpow p 2) (P3 := Hpow p 3)
    (P4 := Hpow p 4) (A := prefixH12 p) (W112 := prefixH112 p)
    (W22 := prefixH22 p) (W13 := prefixH13 p)
    (e2 := listESymm2 S.toList f) (e3 := listESymm3 S.toList f) (e4 := listESymm4 S.toList f)
    hE2 hP1sq hP3 hW112 hW22 hW13 hW4 hE3zero hE4zero hRel hKey
  have htail := tailSum_eq_collected_harmonics p
  have hrhs := tailHarmonicRHS_eq_endpoint_coeffs p
  apply (isUnit_24_zmod_prime_pow_five p hp hp7).mul_left_cancel
  calc
    (24 : R) * tailSum p = (24 : R) *
      ((5 : R)*(p : R)^2*Hpow p 2 + (10 : R)*(p : R)^3*prefixH12 p +
        (24 : R)*(p : R)^3*Hpow p 3 +
        (p : R)^4*((10 : R)*prefixH112 p + (19 : R)*prefixH22 p +
          (48 : R)*prefixH13 p + (108 : R)*Hpow p 4)) := by rw [htail]
    _ = (24 : R) *
      (-(14 : R)*(p : R)*Hpow p 1 - (26 : R)*(p : R)^2*listESymm2 S.toList f -
        (50 : R)*(p : R)^3*listESymm3 S.toList f - (98 : R)*(p : R)^4*listESymm4 S.toList f) := h24
    _ = (24 : R) * tailHarmonicRHS p := by
      rw [hrhs]
      simp [Hpow, S, f]
      ring






theorem tailSum_eq_endpointPoly_combo_from_remaining_assumptions (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hP1sq : (p : ZMod (p ^ 5))^2 * (Hpow p 1)^2 = 0)
    (hP3 : (p : ZMod (p ^ 5))^3 * Hpow p 3 = 0)
    (hW112 : (p : ZMod (p ^ 5))^4 * prefixH112 p = 0)
    (hW22 : (p : ZMod (p ^ 5))^4 * prefixH22 p = 0)
    (hE3zero : (p : ZMod (p ^ 5))^3 * listESymm3 (Finset.Icc 1 (p - 1)).toList (fun i : ℕ => (i : ZMod (p ^ 5))⁻¹) = 0)
    (hRel : (2 : ZMod (p ^ 5))*(p : ZMod (p ^ 5))*Hpow p 1 + (p : ZMod (p ^ 5))^2*Hpow p 2 = 0)
    (hKey : (3 : ZMod (p ^ 5))*(p : ZMod (p ^ 5))^2*Hpow p 2 =
      (2 : ZMod (p ^ 5))*(p : ZMod (p ^ 5))^3*prefixH12 p) :
    tailSum p = tailHarmonicRHS p := by
  exact tailSum_eq_endpointPoly_combo_from_harmonic_assumptions p hp hp7
    hP1sq hP3 hW112 hW22 (hW13_from_H13_vanish p hp hp7)
    (hW4_from_power_sum_modp p hp hp7) hE3zero
    (hE4zero_from_newton_power_sums p hp hp7) hRel hKey


theorem tailSum_eq_endpointPoly_combo_prime_ge_seven (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    tailSum p = tailHarmonicRHS p := by
  have hRel := hRel_from_pairing p hp hp7
  exact tailSum_eq_endpointPoly_combo_from_remaining_assumptions p hp hp7
    (hP1sq_from_pairing p hp hp7)
    (hP3_from_pairing p hp hp7)
    (hW112_from_modp p hp hp7)
    (hW22_from_modp p hp hp7)
    (hE3zero_from_newton p hp hp7 hRel)
    hRel
    (hKey_from_key_depth p hp hp7)




theorem tail_master_congruence_from_tailHarmonicRHS (p : ℕ) (hp : p.Prime)
    (hharm : tailSum p = tailHarmonicRHS p) :
    tailSum p =
      -(2 : ZMod (p ^ 5)) * (Bz p - 1) - (6 : ZMod (p ^ 5)) * (Tz p - 1) := by
  rw [Bz_eq_endpointPoly p hp, Tz_eq_endpointPoly p hp]
  exact hharm





def tailSum_eq_endpointPoly_combo (p : ℕ) : Prop :=
  tailSum p = tailHarmonicRHS p





theorem endpoint_master_identity_from_tail_and_B_quadratic (p : ℕ)
    (htail : tailSum p =
      -(2 : ZMod (p ^ 5)) * (Bz p - 1) - (6 : ZMod (p ^ 5)) * (Tz p - 1))
    (hB : (Bz p) ^ 2 = (2 : ZMod (p ^ 5)) * Bz p - 1) :
    (1 : ZMod (p ^ 5)) + (Bz p) ^ 2 + tailSum p =
      (8 : ZMod (p ^ 5)) - (6 : ZMod (p ^ 5)) * Tz p := by
  rw [htail, hB]
  ring

lemma range_eq_insert_Icc_one_pred (p : ℕ) (hp0 : 0 < p) :
    Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
  ext i
  simp [Finset.mem_Icc]
  omega

lemma lowerBlock_eq_endpoint_add_Icc (p : ℕ) (hp0 : 0 < p) :
    lowerBlock p = (1 : ZMod (p ^ 5)) + ∑ k ∈ Finset.Icc 1 (p - 1), lowerLocal p k := by
  classical
  rw [lowerBlock, range_eq_insert_Icc_one_pred p hp0]
  rw [Finset.sum_insert]
  · congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : ¬ k = 0 := by
      simp [Finset.mem_Icc] at hk
      omega
    simp [hk0]
  · simp [Finset.mem_Icc]

lemma upperBlock_eq_endpoint_add_Icc (p : ℕ) (hp0 : 0 < p) :
    upperBlock p = (Bz p) ^ 2 + ∑ l ∈ Finset.Icc 1 (p - 1), upperLocal p l := by
  classical
  rw [upperBlock, range_eq_insert_Icc_one_pred p hp0]
  rw [Finset.sum_insert]
  · simp only [if_true]
    congr 1
    refine Finset.sum_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
    · intro j hj
      simp [Finset.mem_Icc] at hj ⊢
      omega
    · intro a ha b hb hab
      simp [Finset.mem_Icc] at ha hb
      have hsub : p - a = p - b := hab
      omega
    · intro l hl
      refine ⟨p - l, ?_, ?_⟩
      · simp [Finset.mem_Icc] at hl ⊢
        omega
      · simp [Finset.mem_Icc] at hl
        change p - (p - l) = l
        omega
    · intro j hj
      simp [Finset.mem_Icc] at hj
      have hj0 : ¬ j = 0 := by omega
      simp [hj0]
  · simp [Finset.mem_Icc]

lemma lowerBlock_add_upperBlock_eq_endpoint_tail (p : ℕ) (hp0 : 0 < p) :
    lowerBlock p + upperBlock p =
      (1 : ZMod (p ^ 5)) + (Bz p) ^ 2 + tailSum p := by
  rw [lowerBlock_eq_endpoint_add_Icc p hp0, upperBlock_eq_endpoint_add_Icc p hp0]
  dsimp [tailSum]
  ring

lemma zmod_T_sq_eq_two_mul_sub_one_of_modEq_one_mod_p3 (p : ℕ)
    (hT : ((((3 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3])) :
    (Tz p) ^ 2 = (2 : ZMod (p ^ 5)) * Tz p - 1 := by
  let Tn : ℕ := (3 * p - 1).choose (p - 1)
  let T : ℤ := (Tn : ℤ)
  have hmod : T ≡ 1 [ZMOD (p : ℤ) ^ 3] := by
    simpa [T, Tn] using hT
  have hdiv_neg : (p : ℤ) ^ 3 ∣ 1 - T := Int.modEq_iff_dvd.mp hmod
  have hdiv_pos : (p : ℤ) ^ 3 ∣ T - 1 := by
    simpa [sub_eq_add_neg, add_comm] using Int.dvd_neg.mpr hdiv_neg
  obtain ⟨a, ha⟩ := hdiv_pos
  have hdiv : ((p ^ 5 : ℕ) : ℤ) ∣ T ^ 2 - 2 * T + 1 := by
    refine ⟨(p : ℤ) * a ^ 2, ?_⟩
    calc
      T ^ 2 - 2 * T + 1 = (T - 1) ^ 2 := by ring
      _ = ((p : ℤ) ^ 3 * a) ^ 2 := by rw [ha]
      _ = ((p : ℤ) ^ 5) * ((p : ℤ) * a ^ 2) := by ring
      _ = ((p ^ 5 : ℕ) : ℤ) * ((p : ℤ) * a ^ 2) := by norm_num [Nat.cast_pow]
  have hcast : (((T ^ 2 - 2 * T + 1 : ℤ) : ZMod (p ^ 5)) = 0) := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdiv
  have hpoly : (Tz p) ^ 2 - (2 : ZMod (p ^ 5)) * Tz p + 1 = 0 := by
    simpa [Tz, T, Tn, Nat.cast_pow, Int.cast_pow, Int.cast_ofNat] using hcast
  rw [← sub_eq_zero]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using hpoly


theorem S2_supercongruence_from_local (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p)
    (hLower : ∀ k, 1 ≤ k → k < p → lowerSummand p k = lowerLocal p k)
    (hUpper : ∀ l, 1 ≤ l → l < p → upperSummand p l = upperLocal p l)
    (hT : ((((3 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3]))
    (hB : (Bz p) ^ 2 = (2 : ZMod (p ^ 5)) * Bz p - 1) :
    S2Z p = (7 : ZMod (p ^ 5)) - (4 : ZMod (p ^ 5)) * Tz p := by
  classical
  let R := ZMod (p ^ 5)
  have hp0 : 0 < p := by omega
  have hTquad : (Tz p) ^ 2 = (2 : R) * Tz p - 1 :=
    zmod_T_sq_eq_two_mul_sub_one_of_modEq_one_mod_p3 p hT

  let f : ℕ → R := fun k => ((((p + k - 1).choose k : ℕ) : R) ^ 2)

  have hsplit : S2Z p = (∑ k ∈ Finset.range p, f k) +
        (∑ j ∈ Finset.range p, f (p + j)) + f (2 * p) := by
    dsimp [S2Z, f]
    rw [show 2 * p + 1 = p + (p + 1) by omega]
    rw [Finset.sum_range_add]
    rw [Finset.sum_range_succ (f := fun j =>
      ((((p + (p + j) - 1).choose (p + j) : ℕ) : R) ^ 2))]
    rw [show p + p = 2 * p by omega]
    ring

  have hlowerBlockExact : (∑ k ∈ Finset.range p, f k) = lowerBlock p := by
    dsimp [lowerBlock, f, lowerSummand]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hklt : k < p := by simpa using hk
      have hk1 : 1 ≤ k := by omega
      simp [hk0]
      change lowerSummand p k = lowerLocal p k
      exact hLower k hk1 hklt

  have hupperBlockExact : (∑ j ∈ Finset.range p, f (p + j)) = upperBlock p := by
    dsimp [upperBlock, f, upperSummand, Bz]
    apply Finset.sum_congr rfl
    intro j hj
    have hjp : j < p := by simpa using hj
    by_cases hj0 : j = 0
    · subst j
      have hchoose : (p + (p + 0) - 1).choose (p + 0) = (2 * p - 1).choose (p - 1) := by
        have htop : p + (p + 0) - 1 = 2 * p - 1 := by omega
        rw [htop]
        apply Nat.choose_symm_of_eq_add
        omega
      change (((((p + (p + 0) - 1).choose (p + 0) : ℕ) : R) ^ 2) =
        ((((2 * p - 1).choose (p - 1) : ℕ) : R) ^ 2))
      exact congrArg (fun n : ℕ => (((n : R) ^ 2))) hchoose
    · have hjpos : 0 < j := by omega
      have hl1 : 1 ≤ p - j := by omega
      have hlp : p - j < p := by omega
      have htop : p + (p + j) - 1 = 3 * p - (p - j) - 1 := by omega
      have hchoose : (p + (p + j) - 1).choose (p + j) =
          (3 * p - (p - j) - 1).choose (p - 1) := by
        rw [htop]
        apply Nat.choose_symm_of_eq_add
        omega
      simp [hj0, hchoose]
      change upperSummand p (p - j) = upperLocal p (p - j)
      exact hUpper (p - j) hl1 hlp

  have hendpointExact : f (2 * p) = (Tz p) ^ 2 := by
    dsimp [f, Tz]
    have hchoose : (p + 2 * p - 1).choose (2 * p) = (3 * p - 1).choose (p - 1) := by
      have htop : p + 2 * p - 1 = 3 * p - 1 := by omega
      rw [htop]
      apply Nat.choose_symm_of_eq_add
      omega
    simp [hchoose]

  have htailHarmonic : tailSum_eq_endpointPoly_combo p :=
    tailSum_eq_endpointPoly_combo_prime_ge_seven p hp hp7
  have htail : tailSum p =
      -(2 : R) * (Bz p - 1) - (6 : R) * (Tz p - 1) :=
    tail_master_congruence_from_tailHarmonicRHS p hp htailHarmonic
  have hEndpointMaster : (1 : R) + (Bz p) ^ 2 + tailSum p =
      (8 : R) - (6 : R) * Tz p :=
    endpoint_master_identity_from_tail_and_B_quadratic p htail hB
  have hMaster : lowerBlock p + upperBlock p = (8 : R) - (6 : R) * Tz p := by
    rw [lowerBlock_add_upperBlock_eq_endpoint_tail p hp0]
    exact hEndpointMaster

  calc
    S2Z p = lowerBlock p + upperBlock p + (Tz p) ^ 2 := by
      rw [hsplit, hlowerBlockExact, hupperBlockExact, hendpointExact]
    _ = ((8 : R) - (6 : R) * Tz p) + ((2 : R) * Tz p - 1) := by
      rw [hMaster, hTquad]
    _ = (7 : R) - (4 : R) * Tz p := by ring


end TailMasterCongruenceProgress
end Scratch

theorem A357674_S2_supercongruence (p : ℕ) (hp : p.Prime) (hp7 : p ≥ 7) :
    ((∑ k ∈ Finset.range (2 * p + 1), ((p + k - 1).choose k) ^ 2 : ℕ) : ℤ) ≡
      7 - 4 * (((3 * p - 1).choose (p - 1) : ℕ) : ℤ) [ZMOD (p : ℤ) ^ 5] := by
  let R := ZMod (p ^ 5)
  have hp7' : 7 ≤ p := hp7
  have hT : ((((3 * p - 1).choose (p - 1) : ℕ) : ℤ) ≡ 1 [ZMOD (p : ℤ) ^ 3]) :=
    A357674_T_supercongruence p hp (by omega)
  have hLower : ∀ k, 1 ≤ k → k < p →
      Scratch.TailMasterCongruenceProgress.lowerSummand p k =
        Scratch.TailMasterCongruenceProgress.lowerLocal p k := by
    intro k hk1 hkp
    have h := A357674S2Progress.lower_S2_summand_local_expansion p k hp hk1 hkp
    simpa [Scratch.TailMasterCongruenceProgress.lowerSummand,
      Scratch.TailMasterCongruenceProgress.lowerLocal,
      A357674S2Progress.h1, A357674S2Progress.h2] using h
  have hUpper : ∀ l, 1 ≤ l → l < p →
      Scratch.TailMasterCongruenceProgress.upperSummand p l =
        Scratch.TailMasterCongruenceProgress.upperLocal p l := by
    intro l hl1 hlp
    have h := Scratch.UpperLocalExpansionFull.upper_local_expansion p l hp hl1 hlp hT
    simpa [Scratch.TailMasterCongruenceProgress.upperSummand,
      Scratch.TailMasterCongruenceProgress.upperLocal,
      Scratch.UpperLocalExpansionFull.upperLocalExpansion,
      A357674UpperRatioToT.upperLocalExpansion,
      A357674UpperRatioToT.h1, A357674UpperRatioToT.h2] using h
  have hB0 := BSuperScratch.Bz_sq_eq_two_mul_sub_one p hp (by omega : 5 ≤ p)
  have hB : (Scratch.TailMasterCongruenceProgress.Bz p) ^ 2 =
      (2 : ZMod (p ^ 5)) * Scratch.TailMasterCongruenceProgress.Bz p - 1 := by
    simpa [Scratch.TailMasterCongruenceProgress.Bz, BSuperScratch.Bz] using hB0
  have hz := Scratch.TailMasterCongruenceProgress.S2_supercongruence_from_local p hp hp7'
    hLower hUpper hT hB
  have hzint : (((∑ k ∈ Finset.range (2 * p + 1), ((p + k - 1).choose k) ^ 2 : ℕ) : ℤ) : ZMod (p ^ 5)) =
      ((7 - 4 * (((3 * p - 1).choose (p - 1) : ℕ) : ℤ) : ℤ) : ZMod (p ^ 5)) := by
    simpa [Scratch.TailMasterCongruenceProgress.S2Z, Scratch.TailMasterCongruenceProgress.Tz,
      Nat.cast_sum, Nat.cast_pow, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using hz
  have hmod : (((∑ k ∈ Finset.range (2 * p + 1), ((p + k - 1).choose k) ^ 2 : ℕ) : ℤ) ≡
      (7 - 4 * (((3 * p - 1).choose (p - 1) : ℕ) : ℤ) : ℤ) [ZMOD (p ^ 5)]) := by
    exact (ZMod.intCast_eq_intCast_iff _ _ (p ^ 5)).1 hzint
  simpa [Int.natCast_pow] using hmod




theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  by_cases h3 : p = 3
  · subst p
    exact A357674_conjecture_1_p3
  by_cases h5 : p = 5
  · subst p
    exact A357674_conjecture_1_p5
  have hp0 : 0 < p := hp.pos
  have hp5 : 5 ≤ p := A357674_prime_ge_five_of_ne_three p hp hp3 h3
  have hp7 : 7 ≤ p := A357674_prime_ge_seven_of_ne_five p hp hp5 h5
  exact A357674_conjecture_1_from_route p ((3 * p - 1).choose (p - 1))
    (A357674_S1_eq_three_mul_T p hp0)
    (A357674_T_supercongruence p hp hp3)
    (A357674_S2_supercongruence p hp hp7)









