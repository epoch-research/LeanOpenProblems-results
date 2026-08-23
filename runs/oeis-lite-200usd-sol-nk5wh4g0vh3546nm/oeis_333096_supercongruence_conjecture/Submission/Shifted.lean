import Submission.Generic
open Nat Finset BigOperators Int

def chooseSub (N B d : ℕ) : ℕ :=
  if d ≤ B then N.choose (B-d) else 0

private lemma factorial_choose_shift (B Y d e : ℕ) (hjA : d+e ≤ B+Y) :
    (d+e).factorial * (B+Y).choose (d+e) * chooseSub (B+Y-(d+e)) B d =
      (B+Y).choose B * d.factorial * e.factorial * B.choose d * Y.choose e := by
  by_cases hdB : d ≤ B
  · rw [chooseSub, if_pos hdB]
    by_cases heY : e ≤ Y
    · have harg : B-d ≤ B+Y-(d+e) := by omega
      have hrem : B+Y-(d+e)-(B-d) = Y-e := by omega
      have hArem : B+Y-(d+e) + (d+e) = B+Y := by omega
      have hBrem : B-d+d=B := by omega
      have hYrem : Y-e+e=Y := by omega
      apply Nat.mul_right_cancel (by positivity : 0 < (B-d).factorial * (Y-e).factorial)
      have h1 := Nat.choose_mul_factorial_mul_factorial hjA
      have h2 := Nat.choose_mul_factorial_mul_factorial harg
      have h3 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right B Y)
      have h4 := Nat.choose_mul_factorial_mul_factorial hdB
      have h5 := Nat.choose_mul_factorial_mul_factorial heY
      rw [hrem] at h2
      rw [show B+Y-B=Y by omega] at h3
      calc
        ((d+e).factorial * (B+Y).choose (d+e) *
            (B+Y-(d+e)).choose (B-d)) * ((B-d).factorial * (Y-e).factorial)
            = (B+Y).choose (d+e) * (d+e).factorial *
                ((B+Y-(d+e)).choose (B-d) * (B-d).factorial * (Y-e).factorial) := by ring
        _ = (B+Y).choose (d+e) * (d+e).factorial * (B+Y-(d+e)).factorial := by rw [h2]
        _ = (B+Y).factorial := h1
        _ = (B+Y).choose B * B.factorial * Y.factorial := h3.symm
        _ = (B+Y).choose B *
              (B.choose d * d.factorial * (B-d).factorial) *
              (Y.choose e * e.factorial * (Y-e).factorial) := by rw [h4, h5]
        _ = ((B+Y).choose B * d.factorial * e.factorial * B.choose d * Y.choose e) *
              ((B-d).factorial * (Y-e).factorial) := by ring
    · have hlt : B+Y-(d+e) < B-d := by omega
      have hYe : Y.choose e = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [Nat.choose_eq_zero_of_lt hlt, hYe]
      simp
  · rw [chooseSub, if_neg hdB, Nat.choose_eq_zero_of_lt (by omega : B < d)]
    simp

private lemma factorial_val_add_three_le {p j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hne : d ≠ e) (hj : j = d+e) :
    padicValNat p j.factorial + 3 ≤ j := by
  letI : Fact p.Prime := ⟨hp⟩
  have hv := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p
    (show j ≠ 0 by omega)
  have hp4 : 4 ≤ p-1 := by omega
  have hv4 : 4 * padicValNat p j.factorial < j :=
    (Nat.mul_le_mul_right (padicValNat p j.factorial) hp4).trans_lt hv
  omega

lemma paired_shifted_choose_term_dvd
    {p lev B Y d e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB : p^lev ∣ B) (hY : p^lev ∣ Y)
    (hd : 0 < d) (he : 0 < e) (hne : d ≠ e)
    (hjA : d+e ≤ B+Y) :
    ((p : ℤ)^(3*(lev+1))) ∣
      (p : ℤ)^(d+e) * ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e) := by
  letI : Fact p.Prime := ⟨hp⟩
  let T : ℤ := ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e)
  rw [show (p : ℤ)^(d+e) * ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e) =
      (p : ℤ)^(d+e) * T by dsimp [T]; ring]

  by_cases hT : T = 0
  · change (p : ℤ)^(3*(lev+1)) ∣ (p : ℤ)^(d+e) * T
    rw [hT, mul_zero]
    exact dvd_zero _
  have hf1 := factorial_choose_shift B Y d e hjA
  have hf2 := factorial_choose_shift B Y e d (by omega)
  have hfac : ((d+e).factorial : ℤ) * T =
      ((B+Y).choose B : ℤ) * (d.factorial : ℤ) * e.factorial *
        ((B.choose d : ℤ) * Y.choose e - B.choose e * Y.choose d) := by
    dsimp [T]
    have hf1z : (((d+e).factorial * (B+Y).choose (d+e) *
          chooseSub (B+Y-(d+e)) B d : ℕ) : ℤ) =
        (((B+Y).choose B * d.factorial * e.factorial * B.choose d * Y.choose e : ℕ) : ℤ) := by
      exact_mod_cast hf1
    have hf2z : (((d+e).factorial * (B+Y).choose (d+e) *
          chooseSub (B+Y-(d+e)) B e : ℕ) : ℤ) =
        (((B+Y).choose B * e.factorial * d.factorial * B.choose e * Y.choose d : ℕ) : ℤ) := by
      rw [← show e+d=d+e by omega]
      exact_mod_cast hf2
    calc
      ((d+e).factorial : ℤ) *
          (((B+Y).choose (d+e) : ℤ) *
            ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e))
          = (((d+e).factorial * (B+Y).choose (d+e) *
              chooseSub (B+Y-(d+e)) B d : ℕ) : ℤ) -
            (((d+e).factorial * (B+Y).choose (d+e) *
              chooseSub (B+Y-(d+e)) B e : ℕ) : ℤ) := by push_cast; ring
      _ = _ := by rw [hf1z, hf2z]; push_cast; ring
  have hbase := factorial_choose_det_level_dvd hB hY hd he
  have hprod : ((p : ℤ)^(3*lev)) ∣ ((d+e).factorial : ℤ) * T := by
    rw [hfac]
    convert dvd_mul_of_dvd_right hbase ((B+Y).choose B : ℤ) using 1 <;> ring
  have hvalprod : 3*lev ≤ padicValInt p (((d+e).factorial : ℤ) * T) :=
    (padicValInt_dvd_iff (3*lev) _).mp hprod |>.resolve_left
      (mul_ne_zero (by positivity) hT)
  have hsplit : padicValInt p (((d+e).factorial : ℤ) * T) =
      padicValNat p (d+e).factorial + padicValInt p T := by
    rw [padicValInt.mul (by positivity) hT, padicValInt.of_nat]
  have hfacval := factorial_val_add_three_le hp hp5 hd he hne rfl
  have hgoalval : 3*(lev+1) ≤ padicValInt p ((p : ℤ)^(d+e) * T) := by
    rw [padicValInt.mul (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) hT]
    change 3*(lev+1) ≤ padicValNat p (p^(d+e)) + padicValInt p T
    rw [padicValNat.prime_pow]
    rw [hsplit] at hvalprod
    omega
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr hgoalval)

lemma paired_shifted_choose_term_dvd_total
    {p L B Y d e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hprod : ((p : ℤ)^L) ∣ (B : ℤ)*Y*((Y : ℤ)-B))
    (hd : 0 < d) (he : 0 < e) (hne : d ≠ e)
    (hjA : d+e ≤ B+Y) :
    ((p : ℤ)^(L+3)) ∣
      (p : ℤ)^(d+e) * ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e) := by
  letI : Fact p.Prime := ⟨hp⟩
  let T : ℤ := ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e)
  rw [show (p : ℤ)^(d+e) * ((B+Y).choose (d+e) : ℤ) *
        ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e) =
      (p : ℤ)^(d+e) * T by dsimp [T]; ring]
  by_cases hT : T=0
  · rw [hT, mul_zero]
    exact dvd_zero _
  have hf1 := factorial_choose_shift B Y d e hjA
  have hf2 := factorial_choose_shift B Y e d (by omega)
  have hfac : ((d+e).factorial : ℤ) * T =
      ((B+Y).choose B : ℤ) * (d.factorial : ℤ) * e.factorial *
        ((B.choose d : ℤ) * Y.choose e - B.choose e * Y.choose d) := by
    dsimp [T]
    have hf1z : (((d+e).factorial * (B+Y).choose (d+e) *
          chooseSub (B+Y-(d+e)) B d : ℕ) : ℤ) =
        (((B+Y).choose B * d.factorial * e.factorial * B.choose d * Y.choose e : ℕ) : ℤ) := by
      exact_mod_cast hf1
    have hf2z : (((d+e).factorial * (B+Y).choose (d+e) *
          chooseSub (B+Y-(d+e)) B e : ℕ) : ℤ) =
        (((B+Y).choose B * e.factorial * d.factorial * B.choose e * Y.choose d : ℕ) : ℤ) := by
      rw [← show e+d=d+e by omega]
      exact_mod_cast hf2
    calc
      ((d+e).factorial : ℤ) *
          (((B+Y).choose (d+e) : ℤ) *
            ((chooseSub (B+Y-(d+e)) B d : ℤ) - chooseSub (B+Y-(d+e)) B e))
          = (((d+e).factorial * (B+Y).choose (d+e) *
              chooseSub (B+Y-(d+e)) B d : ℕ) : ℤ) -
            (((d+e).factorial * (B+Y).choose (d+e) *
              chooseSub (B+Y-(d+e)) B e : ℕ) : ℤ) := by push_cast; ring
      _ = _ := by rw [hf1z,hf2z]; push_cast; ring
  have hbase := factorial_choose_det_of_product_dvd hprod hd he
  have hwhole : ((p : ℤ)^L) ∣ ((d+e).factorial : ℤ)*T := by
    rw [hfac]
    convert dvd_mul_of_dvd_right hbase ((B+Y).choose B : ℤ) using 1 <;> ring
  have hval : L ≤ padicValInt p (((d+e).factorial : ℤ)*T) :=
    (padicValInt_dvd_iff L _).mp hwhole |>.resolve_left
      (mul_ne_zero (by positivity) hT)
  have hsplit : padicValInt p (((d+e).factorial : ℤ)*T) =
      padicValNat p (d+e).factorial + padicValInt p T := by
    rw [padicValInt.mul (by positivity) hT, padicValInt.of_nat]
  have hvfac := factorial_val_add_three_le hp hp5 hd he hne rfl
  have hgoal : L+3 ≤ padicValInt p ((p : ℤ)^(d+e)*T) := by
    rw [padicValInt.mul (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)) hT]
    change L+3 ≤ padicValNat p (p^(d+e)) + padicValInt p T
    rw [padicValNat.prime_pow]
    rw [hsplit] at hval
    omega
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr hgoal)
