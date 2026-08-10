import FormalConjectures.Util.ProblemImports
open Nat
open Finset Nat.ModEq

#check ZMod.natCast_eq_natCast_iff
#check Nat.prime_iff_fac_equiv_neg_one
#check Finset.prod_Ico_consecutive
#check Finset.prod_Ico_succ_top
#check Finset.prod_Ico_id_eq_factorial
#check Nat.nth_strictMono
#check Nat.infinite_setOf_prime
#check Nat.nth_lt_nth
#check Nat.prime_nth_prime
#check Nat.le_nth_of_lt_nth_succ
#check Nat.Prime.odd_of_ne_two

lemma factorial_eq_split_zmod (p q : ℕ) (hp1 : 1 ≤ p) (hpq : p + 2 ≤ q) :
    (((q - 1)! : ℕ) : ZMod q) =
      ((p.factorial : ℕ) : ZMod q) * (((Finset.Icc (p + 1) (q - 2)).prod id : ℕ) : ZMod q) * (((q - 1 : ℕ) : ZMod q)) := by
  have hqpos : 0 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hp1' : 1 ≤ p + 1 := by omega
  have hpq1 : p + 1 ≤ q - 1 := by omega
  have hq1 : 1 ≤ q - 1 := by omega
  calc
    (((q - 1)! : ℕ) : ZMod q)
        = ((∏ x ∈ Finset.Ico 1 ((q - 1) + 1), x : ℕ) : ZMod q) := by
            rw [Finset.prod_Ico_id_eq_factorial]
    _ = ∏ x ∈ Finset.Ico 1 ((q - 1) + 1), (x : ZMod q) := by
            simp only [Finset.prod_natCast, id]
    _ = (∏ x ∈ Finset.Ico 1 (q - 1), (x : ZMod q)) * ((q - 1 : ℕ) : ZMod q) := by
            rw [Finset.prod_Ico_succ_top hq1]
    _ = ((∏ x ∈ Finset.Ico 1 (p + 1), (x : ZMod q)) *
            (∏ x ∈ Finset.Ico (p + 1) (q - 1), (x : ZMod q))) * (((q - 1 : ℕ) : ZMod q)) := by
            rw [← Finset.prod_Ico_consecutive (fun x : ℕ => (x : ZMod q)) hp1' hpq1]
    _ = ((p.factorial : ℕ) : ZMod q) * (((Finset.Icc (p + 1) (q - 2)).prod id : ℕ) : ZMod q) * (((q - 1 : ℕ) : ZMod q)) := by
            have hfac : (∏ x ∈ Finset.Ico 1 (p + 1), (x : ZMod q)) = ((p.factorial : ℕ) : ZMod q) := by
              rw [← Finset.prod_Ico_id_eq_factorial, Finset.prod_natCast]
            have hI : Finset.Ico (p + 1) (q - 1) = Finset.Icc (p + 1) (q - 2) := by
              rw [← Finset.Ico_add_one_right_eq_Icc]
              congr
              omega
            rw [hfac, hI]
            simp only [Finset.prod_natCast, id]

lemma zmod_nat_sub_one_eq_neg_one (q : ℕ) (hq : 0 < q) :
    (((q - 1 : ℕ) : ZMod q)) = -1 := by
  apply eq_neg_of_add_eq_zero_left
  have hnat : (q - 1) + 1 = q := Nat.sub_add_cancel hq
  have h : ((((q - 1) + 1 : ℕ) : ZMod q)) = 0 := by
    rw [hnat]
    exact ZMod.natCast_self q
  simpa [Nat.cast_add] using h

lemma factorial_W_mul_eq_one_zmod (p q : ℕ) (hp1 : 1 ≤ p) (hpq : p + 2 ≤ q) (hqprime : Nat.Prime q) :
    ((p.factorial : ℕ) : ZMod q) * (((Finset.Icc (p + 1) (q - 2)).prod id : ℕ) : ZMod q) = 1 := by
  have hqpos : 0 < q := hqprime.pos
  have hqne1 : q ≠ 1 := hqprime.ne_one
  have hfacWilson : (((q - 1)! : ℕ) : ZMod q) = -1 :=
    (Nat.prime_iff_fac_equiv_neg_one hqne1).mp hqprime
  have hsplit := factorial_eq_split_zmod p q hp1 hpq
  rw [hsplit, zmod_nat_sub_one_eq_neg_one q hqpos] at hfacWilson
  -- A * W * (-1) = -1, hence A * W = 1
  have := congrArg Neg.neg hfacWilson
  simpa [neg_mul, mul_assoc] using this

lemma factorial_congr_iff_W_congr (p q : ℕ) (hp1 : 1 ≤ p) (hpq : p + 2 ≤ q) (hqprime : Nat.Prime q) :
    (Nat.factorial p ≡ 1 [MOD q]) ↔
      (((Finset.Icc (p + 1) (q - 2)).prod id) ≡ 1 [MOD q]) := by
  let W : ℕ := (Finset.Icc (p + 1) (q - 2)).prod id
  have hmul : ((p.factorial : ℕ) : ZMod q) * (W : ZMod q) = 1 := by
    simpa [W] using factorial_W_mul_eq_one_zmod p q hp1 hpq hqprime
  constructor
  · intro hA
    have hAz : ((p.factorial : ℕ) : ZMod q) = (((1 : ℕ) : ZMod q)) :=
      (ZMod.natCast_eq_natCast_iff _ _ q).2 hA
    have hWz : (W : ZMod q) = (((1 : ℕ) : ZMod q)) := by
      simpa [hAz] using hmul
    exact (ZMod.natCast_eq_natCast_iff W 1 q).1 hWz
  · intro hW
    have hWz : (W : ZMod q) = (((1 : ℕ) : ZMod q)) :=
      (ZMod.natCast_eq_natCast_iff W 1 q).2 hW
    have hAz : ((p.factorial : ℕ) : ZMod q) = (((1 : ℕ) : ZMod q)) := by
      simpa [hWz] using hmul
    exact (ZMod.natCast_eq_natCast_iff (Nat.factorial p) 1 q).1 hAz


example : Nat.count Nat.Prime 7841 = 990 := by
  native_decide

example : Nat.nth Nat.Prime 990 = 7841 := by
  rw [show 990 = Nat.count Nat.Prime 7841 by native_decide]
  exact Nat.nth_count (by norm_num : Nat.Prime 7841)

example : Nat.factorial 7841 ≡ 1 [MOD 7853] := by
  native_decide


example : Nat.nth Nat.Prime 991 = 7853 := by
  rw [show 991 = Nat.count Nat.Prime 7853 by native_decide]
  exact Nat.nth_count (by norm_num : Nat.Prime 7853)


#check Nat.Prime.eq_two_or_odd'

lemma nth_prime_990_eq_7841 : Nat.nth Nat.Prime 990 = 7841 := by
  rw [show 990 = Nat.count Nat.Prime 7841 by native_decide]
  exact Nat.nth_count (by norm_num : Nat.Prime 7841)

lemma nth_prime_991_eq_7853 : Nat.nth Nat.Prime 991 = 7853 := by
  rw [show 991 = Nat.count Nat.Prime 7853 by native_decide]
  exact Nat.nth_count (by norm_num : Nat.Prime 7853)

lemma congr_exception_991 :
    let Pk := Nat.nth Nat.Prime (991 - 1)
    let Pk_succ := Nat.nth Nat.Prime 991
    Nat.factorial Pk ≡ 1 [MOD Pk_succ] := by
  dsimp
  rw [nth_prime_990_eq_7841, nth_prime_991_eq_7853]
  native_decide

/-- test full theorem -/
theorem test_oeis_1359_conjecture_6 :
  ∀ (k : ℕ), k > 1 →
  let Pk      := Nat.nth Nat.Prime (k - 1);
  let Pk_succ := Nat.nth Nat.Prime k;
  let Congruence := Nat.factorial Pk ≡ 1 [MOD Pk_succ];
  let IsLesserTwinPrime := Nat.Prime (Pk + 2);
  let Wk_prod : ℕ := Finset.prod (Finset.Icc (Pk + 1) (Pk_succ - 2)) id;
  Iff Congruence (
    IsLesserTwinPrime ∨
    (k = 991) ∨
    (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])
  ) := by
  intro k hk
  dsimp only
  let p := Nat.nth Nat.Prime (k - 1)
  let q := Nat.nth Nat.Prime k
  have hksucc : (k - 1) + 1 = k := by omega
  have hpprime : Nat.Prime p := by simpa [p] using Nat.prime_nth_prime (k - 1)
  have hqprime : Nat.Prime q := by simpa [q] using Nat.prime_nth_prime k
  have hp_lt_q : p < q := by
    have : k - 1 < k := by omega
    simpa [p, q] using (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 this
  have hidxpos : 0 < k - 1 := by omega
  have htwo_lt_p : 2 < p := by
    have : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime (k - 1) :=
      (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 hidxpos
    simpa [p, Nat.nth_prime_zero_eq_two] using this
  have hp1 : 1 ≤ p := by omega
  have hq_ne_p1 : q ≠ p + 1 := by
    intro h
    have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
    have hqodd : Odd q := hqprime.odd_of_ne_two (by omega)
    rcases hpodd with ⟨a, ha⟩
    rcases hqodd with ⟨b, hb⟩
    omega
  have hpq2 : p + 2 ≤ q := by omega
  have hiffW : (Nat.factorial p ≡ 1 [MOD q]) ↔
      ((Finset.Icc (p + 1) (q - 2)).prod id ≡ 1 [MOD q]) :=
    factorial_congr_iff_W_congr p q hp1 hpq2 hqprime
  have hNoPrimeBeforeQ : ∀ {r : ℕ}, Nat.Prime r → r < q → r ≤ p := by
    intro r hr hrt
    have hrt' : r < Nat.nth Nat.Prime ((k - 1) + 1) := by simpa [q, hksucc] using hrt
    simpa [p] using Nat.le_nth_of_lt_nth_succ (p := Nat.Prime) hrt' hr
  constructor
  · intro hCong
    have hW : (Finset.Icc (p + 1) (q - 2)).prod id ≡ 1 [MOD q] := hiffW.mp hCong
    by_cases hgap : q - p > 2
    · right; right
      exact ⟨hgap, hW⟩
    · left
      have hq_eq : q = p + 2 := by omega
      simpa [p, ← hq_eq] using hqprime
  · intro hRhs
    rcases hRhs with hTwin | hRest
    · have hq_eq : q = p + 2 := by
        by_contra hneq
        have hlt : p + 2 < q := by omega
        have hle : p + 2 ≤ p := hNoPrimeBeforeQ hTwin hlt
        omega
      have hW : (Finset.Icc (p + 1) (q - 2)).prod id ≡ 1 [MOD q] := by
        have hI : Finset.Icc (p + 1) (q - 2) = ∅ := by
          rw [hq_eq]
          exact Icc_eq_empty (by omega)
        simpa [hI] using (Nat.ModEq.refl (n := q) 1)
      exact hiffW.mpr hW
    · rcases hRest with hk991 | hgapW
      · have hCong991 := congr_exception_991
        subst k
        simpa [p, q] using hCong991
      · exact hiffW.mpr hgapW.2

