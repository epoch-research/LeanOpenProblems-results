import FormalConjectures.Util.ProblemImports

open Nat

/-- Fuel-based binary modular exponentiation: computes `b^e % m` when `e < 2^fuel`. -/
def mpow (m b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | (fuel+1), e =>
      if e = 0 then 1 % m
      else
        let h := mpow m b fuel (e / 2)
        let sq := (h * h) % m
        if e % 2 = 1 then (sq * b) % m else sq

-- quick evaluation test

theorem mpow_correct (m b : ℕ) : ∀ (fuel e : ℕ), e < 2^fuel → mpow m b fuel e = b^e % m := by
  intro fuel
  induction fuel with
  | zero => intro e he; simp at he; subst he; simp [mpow]
  | succ f ih =>
    intro e he
    rw [mpow]
    by_cases he0 : e = 0
    · subst he0; simp
    · simp only [he0, if_false]
      have hlt : e / 2 < 2^f := by
        have : e < 2^(f+1) := he
        rw [pow_succ] at this
        omega
      have ihe := ih (e/2) hlt
      have hsq : (b^(e/2) % m * (b^(e/2) % m)) % m = b^(2*(e/2)) % m := by
        rw [← Nat.mul_mod, ← pow_add, two_mul]
      by_cases hpar : e % 2 = 1
      · simp only [hpar, if_true]
        rw [ihe, hsq]
        conv_rhs => rw [show e = 2*(e/2)+1 from by omega, pow_succ]
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      · simp only [hpar, if_false]
        rw [ihe, hsq]
        congr 2
        omega

theorem reduce_exp (p d X : ℕ) (hp : 2^d % p = 1) : 2^X % p = 2^(X % d) % p := by
  conv_lhs => rw [← Nat.div_add_mod X d, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hp]
  rw [one_pow, ← Nat.mul_mod, Nat.one_mul]

theorem period (d a b Q K : ℕ) (hd : d = 2^a * b) (hcop : Nat.Coprime (2^a) b)
    (hbdvd : b ∣ 2^K - 1) (han : a ≤ 26) (hQ : 1 ≤ Q) (hK : K = 58 * Q) (n : ℕ) :
    2^(58*n+26) % d = 2^(58*(n%Q)+26) % d := by
  -- step lemma
  have hstep : ∀ y, a ≤ y → 2^(y+K) % d = 2^y % d := by
    intro y hy
    have hpow : 2^y ≤ 2^(y+K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hdvd : d ∣ 2^(y+K) - 2^y := by
      have heq : 2^(y+K) - 2^y = 2^y * (2^K - 1) := by
        rw [pow_add, Nat.mul_sub, Nat.mul_one]
      rw [heq, hd]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
      · exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) _
      · exact Dvd.dvd.mul_left hbdvd _
    have := (Nat.modEq_iff_dvd' hpow).mpr hdvd
    exact this.symm
  -- iterate: 2^(y + K*q) % d = 2^y % d
  have hiter : ∀ q y, a ≤ y → 2^(y + K*q) % d = 2^y % d := by
    intro q
    induction q with
    | zero => intro y hy; simp
    | succ j ih =>
      intro y hy
      have : y + K*(j+1) = (y + K*j) + K := by ring
      rw [this, hstep _ (by omega), ih y hy]
  have hn : n = Q*(n/Q) + n%Q := (Nat.div_add_mod n Q).symm
  have hsplit : 58*n+26 = (58*(n%Q)+26) + K*(n/Q) := by
    conv_lhs => rw [hn]
    rw [hK]; ring
  rw [hsplit, hiter _ _ (by omega)]

theorem div_key (p R : ℕ) (hp : 3 ≤ p) (hR : R < p) (hdv : p ∣ R + 3) : R = p - 3 := by
  obtain ⟨c, hc⟩ := hdv
  have hcle : c ≤ 1 := by nlinarith
  have hcge : 1 ≤ c := by nlinarith
  have hc1 : c = 1 := le_antisymm hcle hcge
  subst hc1; omega

theorem master (p d a b Q n : ℕ)
    (hp3 : 3 ≤ p)
    (hQ : 1 ≤ Q) (hQb : Q ≤ 1000)
    (hd : d = 2^a * b) (hd1 : 1 ≤ d) (hdp : d < 2^64)
    (han : a ≤ 26)
    (hcop : Nat.Coprime (2^a) b)
    (hord : 2^d % p = 1)
    (hbdvd : b ∣ 2^(58*Q) - 1)
    (hf : mpow p 2 64 ((mpow d 2 64 (58*(n%Q)+26) + 2) % d) ≠ (p-3) % p) :
    ¬ (p ∣ 2^(2^(58*n+26)+2) + 3) := by
  intro hdvd
  have hnQ : n % Q < Q := Nat.mod_lt _ hQ
  -- exponent bound for the inner mpow
  have hb1 : 58*(n%Q)+26 < 2^64 := by
    have : n % Q ≤ 999 := by omega
    calc 58*(n%Q)+26 ≤ 58*999+26 := by omega
      _ < 2^64 := by norm_num
  set e0 := 58*(n%Q)+26 with he0
  have hmpd : mpow d 2 64 e0 = 2^e0 % d := mpow_correct d 2 64 e0 hb1
  -- periodicity
  have hper : 2^(58*n+26) % d = 2^e0 % d :=
    period d a b Q (58*Q) hd hcop hbdvd han hQ rfl n
  -- define W'
  set W' := (mpow d 2 64 e0 + 2) % d with hW'
  have hW'lt : W' < d := Nat.mod_lt _ (by omega)
  have hW'64 : W' < 2^64 := lt_trans hW'lt hdp
  -- (2^(58n+26)+2) % d = W'
  have hWmodd : (2^(58*n+26)+2) % d = W' := by
    rw [hW', hmpd]
    conv_lhs => rw [Nat.add_mod, hper]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
  -- outer reduction
  have hred : 2^(2^(58*n+26)+2) % p = 2^W' % p := by
    rw [reduce_exp p d (2^(58*n+26)+2) hord, hWmodd]
  have hmpp : mpow p 2 64 W' = 2^W' % p := mpow_correct p 2 64 W' hW'64
  have hRlt : mpow p 2 64 W' < p := by rw [hmpp]; exact Nat.mod_lt _ (by omega)
  -- from hdvd get p ∣ R+3
  have h2W : 2^(2^(58*n+26)+2) % p = mpow p 2 64 W' := by rw [hred, hmpp]
  have hcong : 2^(2^(58*n+26)+2) ≡ mpow p 2 64 W' [MOD p] := by
    unfold Nat.ModEq; rw [h2W, Nat.mod_eq_of_lt hRlt]
  have hcong3 : 2^(2^(58*n+26)+2) + 3 ≡ mpow p 2 64 W' + 3 [MOD p] := hcong.add_right 3
  have h0 : (2^(2^(58*n+26)+2) + 3) ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hdvd
  have hdvR : p ∣ mpow p 2 64 W' + 3 := Nat.modEq_zero_iff_dvd.mp (hcong3.symm.trans h0)
  have hkey := div_key p (mpow p 2 64 W') hp3 hRlt hdvR
  apply hf
  rw [hkey, Nat.mod_eq_of_lt (by omega)]


theorem dvd_of_mpow (b K : ℕ) (hK : K < 2^64) (h : mpow b 2 64 K = 1) : b ∣ 2^K - 1 := by
  have hc := mpow_correct b 2 64 K hK
  rw [h] at hc
  have h2 : 2^K % b = 1 := hc.symm
  have hdm := Nat.div_add_mod (2^K) b
  rw [h2] at hdm
  exact ⟨2^K / b, by omega⟩

theorem mod_of_mpow (p d : ℕ) (hd : d < 2^64) (h : mpow p 2 64 d = 1) : 2^d % p = 1 := by
  have hc := mpow_correct p 2 64 d hd
  rw [h] at hc; exact hc.symm

theorem dvd_1399 (n : ℕ) : (1399:ℕ) ∣ 2^(2^(58*n+26)+2)+3 := by
  have hper : 2^(58*n+26) % 233 = 2^26 % 233 := by
    have h := period 233 0 233 1 58 (by norm_num) (by decide) (by decide)
      (by norm_num) (by norm_num) (by norm_num) n
    have he : (58*(n%1)+26) = 26 := by omega
    rw [he] at h; exact h
  have hred : 2^(2^(58*n+26)+2) % 1399 = 1396 := by
    rw [reduce_exp 1399 233 _ (by decide)]
    have h206 : (2^(58*n+26)+2) % 233 = 206 := by rw [Nat.add_mod, hper]; decide
    rw [h206]; decide
  have hz : (2^(2^(58*n+26)+2)+3) % 1399 = 0 := by rw [Nat.add_mod, hred]
  exact Nat.dvd_of_mod_eq_zero hz

theorem arith (n : ℕ)
    (h1 : ¬ (∃ m : ℕ, 58*n+26 = 10*m+2))
    (h2 : ¬ (∃ m : ℕ, 58*n+26 = 36*m+16 ∧ m % 5 ≠ 1))
    (h3 : ¬ (∃ m : ℕ, 58*n+26 = 84*m+22 ∧ m % 5 ≠ 0)) :
    n % 5 ≠ 2 ∧ n % 18 ≠ 11 ∧ n % 42 ≠ 26 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hc; exact h1 ⟨29*(n/5)+14, by omega⟩
  · intro hc
    by_cases h5 : n % 5 = 2
    · exact h1 ⟨29*(n/5)+14, by omega⟩
    · exact h2 ⟨29*(n/18)+18, by omega, by omega⟩
  · intro hc
    by_cases h5 : n % 5 = 2
    · exact h1 ⟨29*(n/5)+14, by omega⟩
    · exact h3 ⟨29*(n/42)+18, by omega, by omega⟩

theorem ndp_2 (n : ℕ) : ¬ ((2:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  have he : (2:ℕ) ∣ 2^(2^(58*n+26)+2) := by
    apply dvd_pow_self
    positivity
  omega

set_option maxRecDepth 100000 in
theorem chk_3 : ∀ j, j < 1 → mpow 3 2 64 ((mpow 2 2 64 (58*j+26)+2)%2) ≠ 0 := by decide

set_option maxRecDepth 100000 in
theorem ord_3 : mpow 3 2 64 2 = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_3 (n : ℕ) : ¬ ((3:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 3 2 1 1 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 3 2 (by norm_num) ord_3) (one_dvd _)
  exact chk_3 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_5 : ∀ j, j < 1 → mpow 5 2 64 ((mpow 4 2 64 (58*j+26)+2)%4) ≠ 2 := by decide

set_option maxRecDepth 100000 in
theorem ord_5 : mpow 5 2 64 4 = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_5 (n : ℕ) : ¬ ((5:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 5 4 2 1 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 5 4 (by norm_num) ord_5) (one_dvd _)
  exact chk_5 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_7 : ∀ j, j < 1 → mpow 7 2 64 ((mpow 3 2 64 (58*j+26)+2)%3) ≠ 4 := by decide

set_option maxRecDepth 100000 in
theorem ord_7 : mpow 7 2 64 3 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_7 : mpow 3 2 64 (58*1) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_7 (n : ℕ) : ¬ ((7:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 7 3 0 3 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 7 3 (by norm_num) ord_7) (dvd_of_mpow 3 (58*1) (by norm_num) per_7)
  exact chk_7 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_11 : ∀ j, j < 2 → mpow 11 2 64 ((mpow 10 2 64 (58*j+26)+2)%10) ≠ 8 := by decide

set_option maxRecDepth 100000 in
theorem ord_11 : mpow 11 2 64 10 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_11 : mpow 5 2 64 (58*2) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_11 (n : ℕ) : ¬ ((11:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 11 10 1 5 2 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 11 10 (by norm_num) ord_11) (dvd_of_mpow 5 (58*2) (by norm_num) per_11)
  exact chk_11 (n % 2) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_13 : ∀ j, j < 1 → mpow 13 2 64 ((mpow 12 2 64 (58*j+26)+2)%12) ≠ 10 := by decide

set_option maxRecDepth 100000 in
theorem ord_13 : mpow 13 2 64 12 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_13 : mpow 3 2 64 (58*1) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_13 (n : ℕ) : ¬ ((13:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 13 12 2 3 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 13 12 (by norm_num) ord_13) (dvd_of_mpow 3 (58*1) (by norm_num) per_13)
  exact chk_13 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_17 : ∀ j, j < 1 → mpow 17 2 64 ((mpow 8 2 64 (58*j+26)+2)%8) ≠ 14 := by decide

set_option maxRecDepth 100000 in
theorem ord_17 : mpow 17 2 64 8 = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_17 (n : ℕ) : ¬ ((17:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 17 8 3 1 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 17 8 (by norm_num) ord_17) (one_dvd _)
  exact chk_17 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_19 : ∀ j, j < 3 → mpow 19 2 64 ((mpow 18 2 64 (58*j+26)+2)%18) ≠ 16 := by decide

set_option maxRecDepth 100000 in
theorem ord_19 : mpow 19 2 64 18 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_19 : mpow 9 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_19 (n : ℕ) : ¬ ((19:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 19 18 1 9 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 19 18 (by norm_num) ord_19) (dvd_of_mpow 9 (58*3) (by norm_num) per_19)
  exact chk_19 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_23 : ∀ j, j < 5 → mpow 23 2 64 ((mpow 11 2 64 (58*j+26)+2)%11) ≠ 20 := by decide

set_option maxRecDepth 100000 in
theorem ord_23 : mpow 23 2 64 11 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_23 : mpow 11 2 64 (58*5) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_23 (n : ℕ) : ¬ ((23:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 23 11 0 11 5 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 23 11 (by norm_num) ord_23) (dvd_of_mpow 11 (58*5) (by norm_num) per_23)
  exact chk_23 (n % 5) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_29 : ∀ j, j < 3 → mpow 29 2 64 ((mpow 28 2 64 (58*j+26)+2)%28) ≠ 26 := by decide

set_option maxRecDepth 100000 in
theorem ord_29 : mpow 29 2 64 28 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_29 : mpow 7 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_29 (n : ℕ) : ¬ ((29:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 29 28 2 7 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 29 28 (by norm_num) ord_29) (dvd_of_mpow 7 (58*3) (by norm_num) per_29)
  exact chk_29 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_31 : ∀ j, j < 2 → mpow 31 2 64 ((mpow 5 2 64 (58*j+26)+2)%5) ≠ 28 := by decide

set_option maxRecDepth 100000 in
theorem ord_31 : mpow 31 2 64 5 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_31 : mpow 5 2 64 (58*2) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_31 (n : ℕ) : ¬ ((31:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 31 5 0 5 2 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 31 5 (by norm_num) ord_31) (dvd_of_mpow 5 (58*2) (by norm_num) per_31)
  exact chk_31 (n % 2) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_37 : ∀ j, j < 3 → mpow 37 2 64 ((mpow 36 2 64 (58*j+26)+2)%36) ≠ 34 := by decide

set_option maxRecDepth 100000 in
theorem ord_37 : mpow 37 2 64 36 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_37 : mpow 9 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_37 (n : ℕ) : ¬ ((37:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 37 36 2 9 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 37 36 (by norm_num) ord_37) (dvd_of_mpow 9 (58*3) (by norm_num) per_37)
  exact chk_37 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_41 : ∀ j, j < 2 → mpow 41 2 64 ((mpow 20 2 64 (58*j+26)+2)%20) ≠ 38 := by decide

set_option maxRecDepth 100000 in
theorem ord_41 : mpow 41 2 64 20 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_41 : mpow 5 2 64 (58*2) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_41 (n : ℕ) : ¬ ((41:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 41 20 2 5 2 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 41 20 (by norm_num) ord_41) (dvd_of_mpow 5 (58*2) (by norm_num) per_41)
  exact chk_41 (n % 2) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_43 : ∀ j, j < 3 → mpow 43 2 64 ((mpow 14 2 64 (58*j+26)+2)%14) ≠ 40 := by decide

set_option maxRecDepth 100000 in
theorem ord_43 : mpow 43 2 64 14 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_43 : mpow 7 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_43 (n : ℕ) : ¬ ((43:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 43 14 1 7 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 43 14 (by norm_num) ord_43) (dvd_of_mpow 7 (58*3) (by norm_num) per_43)
  exact chk_43 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_47 : ∀ j, j < 11 → mpow 47 2 64 ((mpow 23 2 64 (58*j+26)+2)%23) ≠ 44 := by decide

set_option maxRecDepth 100000 in
theorem ord_47 : mpow 47 2 64 23 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_47 : mpow 23 2 64 (58*11) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_47 (n : ℕ) : ¬ ((47:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 47 23 0 23 11 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 47 23 (by norm_num) ord_47) (dvd_of_mpow 23 (58*11) (by norm_num) per_47)
  exact chk_47 (n % 11) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_53 : ∀ j, j < 6 → mpow 53 2 64 ((mpow 52 2 64 (58*j+26)+2)%52) ≠ 50 := by decide

set_option maxRecDepth 100000 in
theorem ord_53 : mpow 53 2 64 52 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_53 : mpow 13 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_53 (n : ℕ) : ¬ ((53:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 53 52 2 13 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 53 52 (by norm_num) ord_53) (dvd_of_mpow 13 (58*6) (by norm_num) per_53)
  exact chk_53 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_59 : ∀ j, j < 14 → mpow 59 2 64 ((mpow 58 2 64 (58*j+26)+2)%58) ≠ 56 := by decide

set_option maxRecDepth 100000 in
theorem ord_59 : mpow 59 2 64 58 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_59 : mpow 29 2 64 (58*14) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_59 (n : ℕ) : ¬ ((59:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 59 58 1 29 14 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 59 58 (by norm_num) ord_59) (dvd_of_mpow 29 (58*14) (by norm_num) per_59)
  exact chk_59 (n % 14) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_61 : ∀ j, j < 2 → mpow 61 2 64 ((mpow 60 2 64 (58*j+26)+2)%60) ≠ 58 := by decide

set_option maxRecDepth 100000 in
theorem ord_61 : mpow 61 2 64 60 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_61 : mpow 15 2 64 (58*2) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_61 (n : ℕ) : ¬ ((61:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 61 60 2 15 2 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 61 60 (by norm_num) ord_61) (dvd_of_mpow 15 (58*2) (by norm_num) per_61)
  exact chk_61 (n % 2) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_67 : ∀ j, j < 5 → j ≠ 2 → mpow 67 2 64 ((mpow 66 2 64 (58*j+26)+2)%66) ≠ 64 := by decide

set_option maxRecDepth 100000 in
theorem ord_67 : mpow 67 2 64 66 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_67 : mpow 33 2 64 (58*5) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_67 (n : ℕ) (hh : n%5≠2) : ¬ ((67:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 67 66 1 33 5 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 67 66 (by norm_num) ord_67) (dvd_of_mpow 33 (58*5) (by norm_num) per_67)
  refine chk_67 (n % 5) (Nat.mod_lt _ (by norm_num)) ?_
  omega

set_option maxRecDepth 100000 in
theorem chk_71 : ∀ j, j < 6 → mpow 71 2 64 ((mpow 35 2 64 (58*j+26)+2)%35) ≠ 68 := by decide

set_option maxRecDepth 100000 in
theorem ord_71 : mpow 71 2 64 35 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_71 : mpow 35 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_71 (n : ℕ) : ¬ ((71:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 71 35 0 35 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 71 35 (by norm_num) ord_71) (dvd_of_mpow 35 (58*6) (by norm_num) per_71)
  exact chk_71 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_73 : ∀ j, j < 3 → mpow 73 2 64 ((mpow 9 2 64 (58*j+26)+2)%9) ≠ 70 := by decide

set_option maxRecDepth 100000 in
theorem ord_73 : mpow 73 2 64 9 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_73 : mpow 9 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_73 (n : ℕ) : ¬ ((73:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 73 9 0 9 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 73 9 (by norm_num) ord_73) (dvd_of_mpow 9 (58*3) (by norm_num) per_73)
  exact chk_73 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_79 : ∀ j, j < 6 → mpow 79 2 64 ((mpow 39 2 64 (58*j+26)+2)%39) ≠ 76 := by decide

set_option maxRecDepth 100000 in
theorem ord_79 : mpow 79 2 64 39 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_79 : mpow 39 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_79 (n : ℕ) : ¬ ((79:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 79 39 0 39 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 79 39 (by norm_num) ord_79) (dvd_of_mpow 39 (58*6) (by norm_num) per_79)
  exact chk_79 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_83 : ∀ j, j < 10 → mpow 83 2 64 ((mpow 82 2 64 (58*j+26)+2)%82) ≠ 80 := by decide

set_option maxRecDepth 100000 in
theorem ord_83 : mpow 83 2 64 82 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_83 : mpow 41 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_83 (n : ℕ) : ¬ ((83:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 83 82 1 41 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 83 82 (by norm_num) ord_83) (dvd_of_mpow 41 (58*10) (by norm_num) per_83)
  exact chk_83 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_89 : ∀ j, j < 5 → mpow 89 2 64 ((mpow 11 2 64 (58*j+26)+2)%11) ≠ 86 := by decide

set_option maxRecDepth 100000 in
theorem ord_89 : mpow 89 2 64 11 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_89 : mpow 11 2 64 (58*5) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_89 (n : ℕ) : ¬ ((89:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 89 11 0 11 5 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 89 11 (by norm_num) ord_89) (dvd_of_mpow 11 (58*5) (by norm_num) per_89)
  exact chk_89 (n % 5) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_97 : ∀ j, j < 1 → mpow 97 2 64 ((mpow 48 2 64 (58*j+26)+2)%48) ≠ 94 := by decide

set_option maxRecDepth 100000 in
theorem ord_97 : mpow 97 2 64 48 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_97 : mpow 3 2 64 (58*1) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_97 (n : ℕ) : ¬ ((97:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 97 48 4 3 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 97 48 (by norm_num) ord_97) (dvd_of_mpow 3 (58*1) (by norm_num) per_97)
  exact chk_97 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_101 : ∀ j, j < 10 → mpow 101 2 64 ((mpow 100 2 64 (58*j+26)+2)%100) ≠ 98 := by decide

set_option maxRecDepth 100000 in
theorem ord_101 : mpow 101 2 64 100 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_101 : mpow 25 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_101 (n : ℕ) : ¬ ((101:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 101 100 2 25 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 101 100 (by norm_num) ord_101) (dvd_of_mpow 25 (58*10) (by norm_num) per_101)
  exact chk_101 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_103 : ∀ j, j < 4 → mpow 103 2 64 ((mpow 51 2 64 (58*j+26)+2)%51) ≠ 100 := by decide

set_option maxRecDepth 100000 in
theorem ord_103 : mpow 103 2 64 51 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_103 : mpow 51 2 64 (58*4) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_103 (n : ℕ) : ¬ ((103:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 103 51 0 51 4 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 103 51 (by norm_num) ord_103) (dvd_of_mpow 51 (58*4) (by norm_num) per_103)
  exact chk_103 (n % 4) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_107 : ∀ j, j < 26 → mpow 107 2 64 ((mpow 106 2 64 (58*j+26)+2)%106) ≠ 104 := by decide

set_option maxRecDepth 100000 in
theorem ord_107 : mpow 107 2 64 106 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_107 : mpow 53 2 64 (58*26) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_107 (n : ℕ) : ¬ ((107:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 107 106 1 53 26 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 107 106 (by norm_num) ord_107) (dvd_of_mpow 53 (58*26) (by norm_num) per_107)
  exact chk_107 (n % 26) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_109 : ∀ j, j < 3 → mpow 109 2 64 ((mpow 36 2 64 (58*j+26)+2)%36) ≠ 106 := by decide

set_option maxRecDepth 100000 in
theorem ord_109 : mpow 109 2 64 36 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_109 : mpow 9 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_109 (n : ℕ) : ¬ ((109:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 109 36 2 9 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 109 36 (by norm_num) ord_109) (dvd_of_mpow 9 (58*3) (by norm_num) per_109)
  exact chk_109 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_113 : ∀ j, j < 3 → mpow 113 2 64 ((mpow 28 2 64 (58*j+26)+2)%28) ≠ 110 := by decide

set_option maxRecDepth 100000 in
theorem ord_113 : mpow 113 2 64 28 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_113 : mpow 7 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_113 (n : ℕ) : ¬ ((113:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 113 28 2 7 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 113 28 (by norm_num) ord_113) (dvd_of_mpow 7 (58*3) (by norm_num) per_113)
  exact chk_113 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_127 : ∀ j, j < 3 → mpow 127 2 64 ((mpow 7 2 64 (58*j+26)+2)%7) ≠ 124 := by decide

set_option maxRecDepth 100000 in
theorem ord_127 : mpow 127 2 64 7 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_127 : mpow 7 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_127 (n : ℕ) : ¬ ((127:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 127 7 0 7 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 127 7 (by norm_num) ord_127) (dvd_of_mpow 7 (58*3) (by norm_num) per_127)
  exact chk_127 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_131 : ∀ j, j < 6 → mpow 131 2 64 ((mpow 130 2 64 (58*j+26)+2)%130) ≠ 128 := by decide

set_option maxRecDepth 100000 in
theorem ord_131 : mpow 131 2 64 130 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_131 : mpow 65 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_131 (n : ℕ) : ¬ ((131:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 131 130 1 65 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 131 130 (by norm_num) ord_131) (dvd_of_mpow 65 (58*6) (by norm_num) per_131)
  exact chk_131 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_137 : ∀ j, j < 4 → mpow 137 2 64 ((mpow 68 2 64 (58*j+26)+2)%68) ≠ 134 := by decide

set_option maxRecDepth 100000 in
theorem ord_137 : mpow 137 2 64 68 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_137 : mpow 17 2 64 (58*4) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_137 (n : ℕ) : ¬ ((137:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 137 68 2 17 4 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 137 68 (by norm_num) ord_137) (dvd_of_mpow 17 (58*4) (by norm_num) per_137)
  exact chk_137 (n % 4) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_139 : ∀ j, j < 11 → mpow 139 2 64 ((mpow 138 2 64 (58*j+26)+2)%138) ≠ 136 := by decide

set_option maxRecDepth 100000 in
theorem ord_139 : mpow 139 2 64 138 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_139 : mpow 69 2 64 (58*11) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_139 (n : ℕ) : ¬ ((139:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 139 138 1 69 11 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 139 138 (by norm_num) ord_139) (dvd_of_mpow 69 (58*11) (by norm_num) per_139)
  exact chk_139 (n % 11) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_149 : ∀ j, j < 18 → mpow 149 2 64 ((mpow 148 2 64 (58*j+26)+2)%148) ≠ 146 := by decide

set_option maxRecDepth 100000 in
theorem ord_149 : mpow 149 2 64 148 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_149 : mpow 37 2 64 (58*18) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_149 (n : ℕ) : ¬ ((149:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 149 148 2 37 18 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 149 148 (by norm_num) ord_149) (dvd_of_mpow 37 (58*18) (by norm_num) per_149)
  exact chk_149 (n % 18) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_151 : ∀ j, j < 2 → mpow 151 2 64 ((mpow 15 2 64 (58*j+26)+2)%15) ≠ 148 := by decide

set_option maxRecDepth 100000 in
theorem ord_151 : mpow 151 2 64 15 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_151 : mpow 15 2 64 (58*2) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_151 (n : ℕ) : ¬ ((151:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 151 15 0 15 2 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 151 15 (by norm_num) ord_151) (dvd_of_mpow 15 (58*2) (by norm_num) per_151)
  exact chk_151 (n % 2) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_157 : ∀ j, j < 6 → mpow 157 2 64 ((mpow 52 2 64 (58*j+26)+2)%52) ≠ 154 := by decide

set_option maxRecDepth 100000 in
theorem ord_157 : mpow 157 2 64 52 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_157 : mpow 13 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_157 (n : ℕ) : ¬ ((157:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 157 52 2 13 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 157 52 (by norm_num) ord_157) (dvd_of_mpow 13 (58*6) (by norm_num) per_157)
  exact chk_157 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_163 : ∀ j, j < 27 → mpow 163 2 64 ((mpow 162 2 64 (58*j+26)+2)%162) ≠ 160 := by decide

set_option maxRecDepth 100000 in
theorem ord_163 : mpow 163 2 64 162 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_163 : mpow 81 2 64 (58*27) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_163 (n : ℕ) : ¬ ((163:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 163 162 1 81 27 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 163 162 (by norm_num) ord_163) (dvd_of_mpow 81 (58*27) (by norm_num) per_163)
  exact chk_163 (n % 27) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_167 : ∀ j, j < 41 → mpow 167 2 64 ((mpow 83 2 64 (58*j+26)+2)%83) ≠ 164 := by decide

set_option maxRecDepth 100000 in
theorem ord_167 : mpow 167 2 64 83 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_167 : mpow 83 2 64 (58*41) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_167 (n : ℕ) : ¬ ((167:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 167 83 0 83 41 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 167 83 (by norm_num) ord_167) (dvd_of_mpow 83 (58*41) (by norm_num) per_167)
  exact chk_167 (n % 41) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_173 : ∀ j, j < 7 → mpow 173 2 64 ((mpow 172 2 64 (58*j+26)+2)%172) ≠ 170 := by decide

set_option maxRecDepth 100000 in
theorem ord_173 : mpow 173 2 64 172 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_173 : mpow 43 2 64 (58*7) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_173 (n : ℕ) : ¬ ((173:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 173 172 2 43 7 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 173 172 (by norm_num) ord_173) (dvd_of_mpow 43 (58*7) (by norm_num) per_173)
  exact chk_173 (n % 7) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_179 : ∀ j, j < 11 → mpow 179 2 64 ((mpow 178 2 64 (58*j+26)+2)%178) ≠ 176 := by decide

set_option maxRecDepth 100000 in
theorem ord_179 : mpow 179 2 64 178 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_179 : mpow 89 2 64 (58*11) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_179 (n : ℕ) : ¬ ((179:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 179 178 1 89 11 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 179 178 (by norm_num) ord_179) (dvd_of_mpow 89 (58*11) (by norm_num) per_179)
  exact chk_179 (n % 11) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_181 : ∀ j, j < 6 → mpow 181 2 64 ((mpow 180 2 64 (58*j+26)+2)%180) ≠ 178 := by decide

set_option maxRecDepth 100000 in
theorem ord_181 : mpow 181 2 64 180 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_181 : mpow 45 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_181 (n : ℕ) : ¬ ((181:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 181 180 2 45 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 181 180 (by norm_num) ord_181) (dvd_of_mpow 45 (58*6) (by norm_num) per_181)
  exact chk_181 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_191 : ∀ j, j < 18 → mpow 191 2 64 ((mpow 95 2 64 (58*j+26)+2)%95) ≠ 188 := by decide

set_option maxRecDepth 100000 in
theorem ord_191 : mpow 191 2 64 95 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_191 : mpow 95 2 64 (58*18) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_191 (n : ℕ) : ¬ ((191:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 191 95 0 95 18 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 191 95 (by norm_num) ord_191) (dvd_of_mpow 95 (58*18) (by norm_num) per_191)
  exact chk_191 (n % 18) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_193 : ∀ j, j < 1 → mpow 193 2 64 ((mpow 96 2 64 (58*j+26)+2)%96) ≠ 190 := by decide

set_option maxRecDepth 100000 in
theorem ord_193 : mpow 193 2 64 96 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_193 : mpow 3 2 64 (58*1) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_193 (n : ℕ) : ¬ ((193:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 193 96 5 3 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 193 96 (by norm_num) ord_193) (dvd_of_mpow 3 (58*1) (by norm_num) per_193)
  exact chk_193 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_197 : ∀ j, j < 21 → mpow 197 2 64 ((mpow 196 2 64 (58*j+26)+2)%196) ≠ 194 := by decide

set_option maxRecDepth 100000 in
theorem ord_197 : mpow 197 2 64 196 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_197 : mpow 49 2 64 (58*21) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_197 (n : ℕ) : ¬ ((197:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 197 196 2 49 21 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 197 196 (by norm_num) ord_197) (dvd_of_mpow 49 (58*21) (by norm_num) per_197)
  exact chk_197 (n % 21) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_199 : ∀ j, j < 15 → mpow 199 2 64 ((mpow 99 2 64 (58*j+26)+2)%99) ≠ 196 := by decide

set_option maxRecDepth 100000 in
theorem ord_199 : mpow 199 2 64 99 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_199 : mpow 99 2 64 (58*15) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_199 (n : ℕ) : ¬ ((199:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 199 99 0 99 15 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 199 99 (by norm_num) ord_199) (dvd_of_mpow 99 (58*15) (by norm_num) per_199)
  exact chk_199 (n % 15) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_211 : ∀ j, j < 6 → mpow 211 2 64 ((mpow 210 2 64 (58*j+26)+2)%210) ≠ 208 := by decide

set_option maxRecDepth 100000 in
theorem ord_211 : mpow 211 2 64 210 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_211 : mpow 105 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_211 (n : ℕ) : ¬ ((211:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 211 210 1 105 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 211 210 (by norm_num) ord_211) (dvd_of_mpow 105 (58*6) (by norm_num) per_211)
  exact chk_211 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_223 : ∀ j, j < 18 → mpow 223 2 64 ((mpow 37 2 64 (58*j+26)+2)%37) ≠ 220 := by decide

set_option maxRecDepth 100000 in
theorem ord_223 : mpow 223 2 64 37 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_223 : mpow 37 2 64 (58*18) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_223 (n : ℕ) : ¬ ((223:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 223 37 0 37 18 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 223 37 (by norm_num) ord_223) (dvd_of_mpow 37 (58*18) (by norm_num) per_223)
  exact chk_223 (n % 18) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_227 : ∀ j, j < 14 → mpow 227 2 64 ((mpow 226 2 64 (58*j+26)+2)%226) ≠ 224 := by decide

set_option maxRecDepth 100000 in
theorem ord_227 : mpow 227 2 64 226 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_227 : mpow 113 2 64 (58*14) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_227 (n : ℕ) : ¬ ((227:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 227 226 1 113 14 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 227 226 (by norm_num) ord_227) (dvd_of_mpow 113 (58*14) (by norm_num) per_227)
  exact chk_227 (n % 14) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_229 : ∀ j, j < 9 → mpow 229 2 64 ((mpow 76 2 64 (58*j+26)+2)%76) ≠ 226 := by decide

set_option maxRecDepth 100000 in
theorem ord_229 : mpow 229 2 64 76 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_229 : mpow 19 2 64 (58*9) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_229 (n : ℕ) : ¬ ((229:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 229 76 2 19 9 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 229 76 (by norm_num) ord_229) (dvd_of_mpow 19 (58*9) (by norm_num) per_229)
  exact chk_229 (n % 9) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_233 : ∀ j, j < 14 → mpow 233 2 64 ((mpow 29 2 64 (58*j+26)+2)%29) ≠ 230 := by decide

set_option maxRecDepth 100000 in
theorem ord_233 : mpow 233 2 64 29 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_233 : mpow 29 2 64 (58*14) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_233 (n : ℕ) : ¬ ((233:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 233 29 0 29 14 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 233 29 (by norm_num) ord_233) (dvd_of_mpow 29 (58*14) (by norm_num) per_233)
  exact chk_233 (n % 14) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_239 : ∀ j, j < 12 → mpow 239 2 64 ((mpow 119 2 64 (58*j+26)+2)%119) ≠ 236 := by decide

set_option maxRecDepth 100000 in
theorem ord_239 : mpow 239 2 64 119 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_239 : mpow 119 2 64 (58*12) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_239 (n : ℕ) : ¬ ((239:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 239 119 0 119 12 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 239 119 (by norm_num) ord_239) (dvd_of_mpow 119 (58*12) (by norm_num) per_239)
  exact chk_239 (n % 12) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_241 : ∀ j, j < 1 → mpow 241 2 64 ((mpow 24 2 64 (58*j+26)+2)%24) ≠ 238 := by decide

set_option maxRecDepth 100000 in
theorem ord_241 : mpow 241 2 64 24 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_241 : mpow 3 2 64 (58*1) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_241 (n : ℕ) : ¬ ((241:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 241 24 3 3 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 241 24 (by norm_num) ord_241) (dvd_of_mpow 3 (58*1) (by norm_num) per_241)
  exact chk_241 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_251 : ∀ j, j < 10 → mpow 251 2 64 ((mpow 50 2 64 (58*j+26)+2)%50) ≠ 248 := by decide

set_option maxRecDepth 100000 in
theorem ord_251 : mpow 251 2 64 50 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_251 : mpow 25 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_251 (n : ℕ) : ¬ ((251:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 251 50 1 25 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 251 50 (by norm_num) ord_251) (dvd_of_mpow 25 (58*10) (by norm_num) per_251)
  exact chk_251 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_257 : ∀ j, j < 1 → mpow 257 2 64 ((mpow 16 2 64 (58*j+26)+2)%16) ≠ 254 := by decide

set_option maxRecDepth 100000 in
theorem ord_257 : mpow 257 2 64 16 = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_257 (n : ℕ) : ¬ ((257:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 257 16 4 1 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 257 16 (by norm_num) ord_257) (one_dvd _)
  exact chk_257 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_263 : ∀ j, j < 65 → mpow 263 2 64 ((mpow 131 2 64 (58*j+26)+2)%131) ≠ 260 := by decide

set_option maxRecDepth 100000 in
theorem ord_263 : mpow 263 2 64 131 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_263 : mpow 131 2 64 (58*65) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_263 (n : ℕ) : ¬ ((263:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 263 131 0 131 65 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 263 131 (by norm_num) ord_263) (dvd_of_mpow 131 (58*65) (by norm_num) per_263)
  exact chk_263 (n % 65) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_269 : ∀ j, j < 33 → mpow 269 2 64 ((mpow 268 2 64 (58*j+26)+2)%268) ≠ 266 := by decide

set_option maxRecDepth 100000 in
theorem ord_269 : mpow 269 2 64 268 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_269 : mpow 67 2 64 (58*33) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_269 (n : ℕ) : ¬ ((269:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 269 268 2 67 33 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 269 268 (by norm_num) ord_269) (dvd_of_mpow 67 (58*33) (by norm_num) per_269)
  exact chk_269 (n % 33) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_271 : ∀ j, j < 18 → j ≠ 11 → mpow 271 2 64 ((mpow 135 2 64 (58*j+26)+2)%135) ≠ 268 := by decide

set_option maxRecDepth 100000 in
theorem ord_271 : mpow 271 2 64 135 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_271 : mpow 135 2 64 (58*18) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_271 (n : ℕ) (hh : n%18≠11) : ¬ ((271:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 271 135 0 135 18 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 271 135 (by norm_num) ord_271) (dvd_of_mpow 135 (58*18) (by norm_num) per_271)
  refine chk_271 (n % 18) (Nat.mod_lt _ (by norm_num)) ?_
  omega

set_option maxRecDepth 100000 in
theorem chk_277 : ∀ j, j < 11 → mpow 277 2 64 ((mpow 92 2 64 (58*j+26)+2)%92) ≠ 274 := by decide

set_option maxRecDepth 100000 in
theorem ord_277 : mpow 277 2 64 92 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_277 : mpow 23 2 64 (58*11) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_277 (n : ℕ) : ¬ ((277:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 277 92 2 23 11 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 277 92 (by norm_num) ord_277) (dvd_of_mpow 23 (58*11) (by norm_num) per_277)
  exact chk_277 (n % 11) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_281 : ∀ j, j < 6 → mpow 281 2 64 ((mpow 70 2 64 (58*j+26)+2)%70) ≠ 278 := by decide

set_option maxRecDepth 100000 in
theorem ord_281 : mpow 281 2 64 70 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_281 : mpow 35 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_281 (n : ℕ) : ¬ ((281:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 281 70 1 35 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 281 70 (by norm_num) ord_281) (dvd_of_mpow 35 (58*6) (by norm_num) per_281)
  exact chk_281 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_283 : ∀ j, j < 23 → mpow 283 2 64 ((mpow 94 2 64 (58*j+26)+2)%94) ≠ 280 := by decide

set_option maxRecDepth 100000 in
theorem ord_283 : mpow 283 2 64 94 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_283 : mpow 47 2 64 (58*23) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_283 (n : ℕ) : ¬ ((283:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 283 94 1 47 23 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 283 94 (by norm_num) ord_283) (dvd_of_mpow 47 (58*23) (by norm_num) per_283)
  exact chk_283 (n % 23) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_293 : ∀ j, j < 9 → mpow 293 2 64 ((mpow 292 2 64 (58*j+26)+2)%292) ≠ 290 := by decide

set_option maxRecDepth 100000 in
theorem ord_293 : mpow 293 2 64 292 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_293 : mpow 73 2 64 (58*9) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_293 (n : ℕ) : ¬ ((293:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 293 292 2 73 9 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 293 292 (by norm_num) ord_293) (dvd_of_mpow 73 (58*9) (by norm_num) per_293)
  exact chk_293 (n % 9) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_307 : ∀ j, j < 4 → mpow 307 2 64 ((mpow 102 2 64 (58*j+26)+2)%102) ≠ 304 := by decide

set_option maxRecDepth 100000 in
theorem ord_307 : mpow 307 2 64 102 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_307 : mpow 51 2 64 (58*4) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_307 (n : ℕ) : ¬ ((307:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 307 102 1 51 4 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 307 102 (by norm_num) ord_307) (dvd_of_mpow 51 (58*4) (by norm_num) per_307)
  exact chk_307 (n % 4) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_311 : ∀ j, j < 10 → mpow 311 2 64 ((mpow 155 2 64 (58*j+26)+2)%155) ≠ 308 := by decide

set_option maxRecDepth 100000 in
theorem ord_311 : mpow 311 2 64 155 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_311 : mpow 155 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_311 (n : ℕ) : ¬ ((311:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 311 155 0 155 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 311 155 (by norm_num) ord_311) (dvd_of_mpow 155 (58*10) (by norm_num) per_311)
  exact chk_311 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_313 : ∀ j, j < 6 → mpow 313 2 64 ((mpow 156 2 64 (58*j+26)+2)%156) ≠ 310 := by decide

set_option maxRecDepth 100000 in
theorem ord_313 : mpow 313 2 64 156 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_313 : mpow 39 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_313 (n : ℕ) : ¬ ((313:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 313 156 2 39 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 313 156 (by norm_num) ord_313) (dvd_of_mpow 39 (58*6) (by norm_num) per_313)
  exact chk_313 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_317 : ∀ j, j < 39 → mpow 317 2 64 ((mpow 316 2 64 (58*j+26)+2)%316) ≠ 314 := by decide

set_option maxRecDepth 100000 in
theorem ord_317 : mpow 317 2 64 316 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_317 : mpow 79 2 64 (58*39) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_317 (n : ℕ) : ¬ ((317:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 317 316 2 79 39 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 317 316 (by norm_num) ord_317) (dvd_of_mpow 79 (58*39) (by norm_num) per_317)
  exact chk_317 (n % 39) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_331 : ∀ j, j < 2 → mpow 331 2 64 ((mpow 30 2 64 (58*j+26)+2)%30) ≠ 328 := by decide

set_option maxRecDepth 100000 in
theorem ord_331 : mpow 331 2 64 30 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_331 : mpow 15 2 64 (58*2) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_331 (n : ℕ) : ¬ ((331:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 331 30 1 15 2 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 331 30 (by norm_num) ord_331) (dvd_of_mpow 15 (58*2) (by norm_num) per_331)
  exact chk_331 (n % 2) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_337 : ∀ j, j < 3 → mpow 337 2 64 ((mpow 21 2 64 (58*j+26)+2)%21) ≠ 334 := by decide

set_option maxRecDepth 100000 in
theorem ord_337 : mpow 337 2 64 21 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_337 : mpow 21 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_337 (n : ℕ) : ¬ ((337:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 337 21 0 21 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 337 21 (by norm_num) ord_337) (dvd_of_mpow 21 (58*3) (by norm_num) per_337)
  exact chk_337 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_347 : ∀ j, j < 86 → mpow 347 2 64 ((mpow 346 2 64 (58*j+26)+2)%346) ≠ 344 := by decide

set_option maxRecDepth 100000 in
theorem ord_347 : mpow 347 2 64 346 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_347 : mpow 173 2 64 (58*86) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_347 (n : ℕ) : ¬ ((347:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 347 346 1 173 86 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 347 346 (by norm_num) ord_347) (dvd_of_mpow 173 (58*86) (by norm_num) per_347)
  exact chk_347 (n % 86) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_349 : ∀ j, j < 14 → mpow 349 2 64 ((mpow 348 2 64 (58*j+26)+2)%348) ≠ 346 := by decide

set_option maxRecDepth 100000 in
theorem ord_349 : mpow 349 2 64 348 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_349 : mpow 87 2 64 (58*14) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_349 (n : ℕ) : ¬ ((349:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 349 348 2 87 14 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 349 348 (by norm_num) ord_349) (dvd_of_mpow 87 (58*14) (by norm_num) per_349)
  exact chk_349 (n % 14) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_353 : ∀ j, j < 5 → mpow 353 2 64 ((mpow 88 2 64 (58*j+26)+2)%88) ≠ 350 := by decide

set_option maxRecDepth 100000 in
theorem ord_353 : mpow 353 2 64 88 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_353 : mpow 11 2 64 (58*5) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_353 (n : ℕ) : ¬ ((353:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 353 88 3 11 5 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 353 88 (by norm_num) ord_353) (dvd_of_mpow 11 (58*5) (by norm_num) per_353)
  exact chk_353 (n % 5) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_359 : ∀ j, j < 89 → mpow 359 2 64 ((mpow 179 2 64 (58*j+26)+2)%179) ≠ 356 := by decide

set_option maxRecDepth 100000 in
theorem ord_359 : mpow 359 2 64 179 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_359 : mpow 179 2 64 (58*89) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_359 (n : ℕ) : ¬ ((359:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 359 179 0 179 89 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 359 179 (by norm_num) ord_359) (dvd_of_mpow 179 (58*89) (by norm_num) per_359)
  exact chk_359 (n % 89) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_367 : ∀ j, j < 30 → mpow 367 2 64 ((mpow 183 2 64 (58*j+26)+2)%183) ≠ 364 := by decide

set_option maxRecDepth 100000 in
theorem ord_367 : mpow 367 2 64 183 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_367 : mpow 183 2 64 (58*30) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_367 (n : ℕ) : ¬ ((367:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 367 183 0 183 30 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 367 183 (by norm_num) ord_367) (dvd_of_mpow 183 (58*30) (by norm_num) per_367)
  exact chk_367 (n % 30) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_373 : ∀ j, j < 5 → mpow 373 2 64 ((mpow 372 2 64 (58*j+26)+2)%372) ≠ 370 := by decide

set_option maxRecDepth 100000 in
theorem ord_373 : mpow 373 2 64 372 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_373 : mpow 93 2 64 (58*5) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_373 (n : ℕ) : ¬ ((373:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 373 372 2 93 5 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 373 372 (by norm_num) ord_373) (dvd_of_mpow 93 (58*5) (by norm_num) per_373)
  exact chk_373 (n % 5) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_379 : ∀ j, j < 9 → mpow 379 2 64 ((mpow 378 2 64 (58*j+26)+2)%378) ≠ 376 := by decide

set_option maxRecDepth 100000 in
theorem ord_379 : mpow 379 2 64 378 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_379 : mpow 189 2 64 (58*9) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_379 (n : ℕ) : ¬ ((379:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 379 378 1 189 9 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 379 378 (by norm_num) ord_379) (dvd_of_mpow 189 (58*9) (by norm_num) per_379)
  exact chk_379 (n % 9) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_383 : ∀ j, j < 95 → mpow 383 2 64 ((mpow 191 2 64 (58*j+26)+2)%191) ≠ 380 := by decide

set_option maxRecDepth 100000 in
theorem ord_383 : mpow 383 2 64 191 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_383 : mpow 191 2 64 (58*95) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_383 (n : ℕ) : ¬ ((383:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 383 191 0 191 95 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 383 191 (by norm_num) ord_383) (dvd_of_mpow 191 (58*95) (by norm_num) per_383)
  exact chk_383 (n % 95) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_389 : ∀ j, j < 24 → mpow 389 2 64 ((mpow 388 2 64 (58*j+26)+2)%388) ≠ 386 := by decide

set_option maxRecDepth 100000 in
theorem ord_389 : mpow 389 2 64 388 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_389 : mpow 97 2 64 (58*24) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_389 (n : ℕ) : ¬ ((389:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 389 388 2 97 24 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 389 388 (by norm_num) ord_389) (dvd_of_mpow 97 (58*24) (by norm_num) per_389)
  exact chk_389 (n % 24) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_397 : ∀ j, j < 5 → mpow 397 2 64 ((mpow 44 2 64 (58*j+26)+2)%44) ≠ 394 := by decide

set_option maxRecDepth 100000 in
theorem ord_397 : mpow 397 2 64 44 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_397 : mpow 11 2 64 (58*5) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_397 (n : ℕ) : ¬ ((397:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 397 44 2 11 5 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 397 44 (by norm_num) ord_397) (dvd_of_mpow 11 (58*5) (by norm_num) per_397)
  exact chk_397 (n % 5) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_401 : ∀ j, j < 10 → mpow 401 2 64 ((mpow 200 2 64 (58*j+26)+2)%200) ≠ 398 := by decide

set_option maxRecDepth 100000 in
theorem ord_401 : mpow 401 2 64 200 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_401 : mpow 25 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_401 (n : ℕ) : ¬ ((401:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 401 200 3 25 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 401 200 (by norm_num) ord_401) (dvd_of_mpow 25 (58*10) (by norm_num) per_401)
  exact chk_401 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_409 : ∀ j, j < 4 → mpow 409 2 64 ((mpow 204 2 64 (58*j+26)+2)%204) ≠ 406 := by decide

set_option maxRecDepth 100000 in
theorem ord_409 : mpow 409 2 64 204 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_409 : mpow 51 2 64 (58*4) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_409 (n : ℕ) : ¬ ((409:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 409 204 2 51 4 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 409 204 (by norm_num) ord_409) (dvd_of_mpow 51 (58*4) (by norm_num) per_409)
  exact chk_409 (n % 4) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_419 : ∀ j, j < 45 → mpow 419 2 64 ((mpow 418 2 64 (58*j+26)+2)%418) ≠ 416 := by decide

set_option maxRecDepth 100000 in
theorem ord_419 : mpow 419 2 64 418 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_419 : mpow 209 2 64 (58*45) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_419 (n : ℕ) : ¬ ((419:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 419 418 1 209 45 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 419 418 (by norm_num) ord_419) (dvd_of_mpow 209 (58*45) (by norm_num) per_419)
  exact chk_419 (n % 45) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_421 : ∀ j, j < 6 → mpow 421 2 64 ((mpow 420 2 64 (58*j+26)+2)%420) ≠ 418 := by decide

set_option maxRecDepth 100000 in
theorem ord_421 : mpow 421 2 64 420 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_421 : mpow 105 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_421 (n : ℕ) : ¬ ((421:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 421 420 2 105 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 421 420 (by norm_num) ord_421) (dvd_of_mpow 105 (58*6) (by norm_num) per_421)
  exact chk_421 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_431 : ∀ j, j < 7 → mpow 431 2 64 ((mpow 43 2 64 (58*j+26)+2)%43) ≠ 428 := by decide

set_option maxRecDepth 100000 in
theorem ord_431 : mpow 431 2 64 43 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_431 : mpow 43 2 64 (58*7) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_431 (n : ℕ) : ¬ ((431:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 431 43 0 43 7 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 431 43 (by norm_num) ord_431) (dvd_of_mpow 43 (58*7) (by norm_num) per_431)
  exact chk_431 (n % 7) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_433 : ∀ j, j < 3 → mpow 433 2 64 ((mpow 72 2 64 (58*j+26)+2)%72) ≠ 430 := by decide

set_option maxRecDepth 100000 in
theorem ord_433 : mpow 433 2 64 72 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_433 : mpow 9 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_433 (n : ℕ) : ¬ ((433:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 433 72 3 9 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 433 72 (by norm_num) ord_433) (dvd_of_mpow 9 (58*3) (by norm_num) per_433)
  exact chk_433 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_439 : ∀ j, j < 9 → mpow 439 2 64 ((mpow 73 2 64 (58*j+26)+2)%73) ≠ 436 := by decide

set_option maxRecDepth 100000 in
theorem ord_439 : mpow 439 2 64 73 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_439 : mpow 73 2 64 (58*9) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_439 (n : ℕ) : ¬ ((439:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 439 73 0 73 9 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 439 73 (by norm_num) ord_439) (dvd_of_mpow 73 (58*9) (by norm_num) per_439)
  exact chk_439 (n % 9) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_443 : ∀ j, j < 12 → mpow 443 2 64 ((mpow 442 2 64 (58*j+26)+2)%442) ≠ 440 := by decide

set_option maxRecDepth 100000 in
theorem ord_443 : mpow 443 2 64 442 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_443 : mpow 221 2 64 (58*12) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_443 (n : ℕ) : ¬ ((443:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 443 442 1 221 12 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 443 442 (by norm_num) ord_443) (dvd_of_mpow 221 (58*12) (by norm_num) per_443)
  exact chk_443 (n % 12) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_449 : ∀ j, j < 3 → mpow 449 2 64 ((mpow 224 2 64 (58*j+26)+2)%224) ≠ 446 := by decide

set_option maxRecDepth 100000 in
theorem ord_449 : mpow 449 2 64 224 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_449 : mpow 7 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_449 (n : ℕ) : ¬ ((449:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 449 224 5 7 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 449 224 (by norm_num) ord_449) (dvd_of_mpow 7 (58*3) (by norm_num) per_449)
  exact chk_449 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_457 : ∀ j, j < 9 → mpow 457 2 64 ((mpow 76 2 64 (58*j+26)+2)%76) ≠ 454 := by decide

set_option maxRecDepth 100000 in
theorem ord_457 : mpow 457 2 64 76 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_457 : mpow 19 2 64 (58*9) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_457 (n : ℕ) : ¬ ((457:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 457 76 2 19 9 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 457 76 (by norm_num) ord_457) (dvd_of_mpow 19 (58*9) (by norm_num) per_457)
  exact chk_457 (n % 9) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_461 : ∀ j, j < 22 → mpow 461 2 64 ((mpow 460 2 64 (58*j+26)+2)%460) ≠ 458 := by decide

set_option maxRecDepth 100000 in
theorem ord_461 : mpow 461 2 64 460 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_461 : mpow 115 2 64 (58*22) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_461 (n : ℕ) : ¬ ((461:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 461 460 2 115 22 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 461 460 (by norm_num) ord_461) (dvd_of_mpow 115 (58*22) (by norm_num) per_461)
  exact chk_461 (n % 22) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_463 : ∀ j, j < 15 → mpow 463 2 64 ((mpow 231 2 64 (58*j+26)+2)%231) ≠ 460 := by decide

set_option maxRecDepth 100000 in
theorem ord_463 : mpow 463 2 64 231 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_463 : mpow 231 2 64 (58*15) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_463 (n : ℕ) : ¬ ((463:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 463 231 0 231 15 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 463 231 (by norm_num) ord_463) (dvd_of_mpow 231 (58*15) (by norm_num) per_463)
  exact chk_463 (n % 15) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_467 : ∀ j, j < 1 → mpow 467 2 64 ((mpow 466 2 64 (58*j+26)+2)%466) ≠ 464 := by decide

set_option maxRecDepth 100000 in
theorem ord_467 : mpow 467 2 64 466 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_467 : mpow 233 2 64 (58*1) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_467 (n : ℕ) : ¬ ((467:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 467 466 1 233 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 467 466 (by norm_num) ord_467) (dvd_of_mpow 233 (58*1) (by norm_num) per_467)
  exact chk_467 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_479 : ∀ j, j < 119 → mpow 479 2 64 ((mpow 239 2 64 (58*j+26)+2)%239) ≠ 476 := by decide

set_option maxRecDepth 100000 in
theorem ord_479 : mpow 479 2 64 239 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_479 : mpow 239 2 64 (58*119) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_479 (n : ℕ) : ¬ ((479:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 479 239 0 239 119 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 479 239 (by norm_num) ord_479) (dvd_of_mpow 239 (58*119) (by norm_num) per_479)
  exact chk_479 (n % 119) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_487 : ∀ j, j < 81 → mpow 487 2 64 ((mpow 243 2 64 (58*j+26)+2)%243) ≠ 484 := by decide

set_option maxRecDepth 100000 in
theorem ord_487 : mpow 487 2 64 243 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_487 : mpow 243 2 64 (58*81) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_487 (n : ℕ) : ¬ ((487:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 487 243 0 243 81 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 487 243 (by norm_num) ord_487) (dvd_of_mpow 243 (58*81) (by norm_num) per_487)
  exact chk_487 (n % 81) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_491 : ∀ j, j < 42 → mpow 491 2 64 ((mpow 490 2 64 (58*j+26)+2)%490) ≠ 488 := by decide

set_option maxRecDepth 100000 in
theorem ord_491 : mpow 491 2 64 490 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_491 : mpow 245 2 64 (58*42) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_491 (n : ℕ) : ¬ ((491:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 491 490 1 245 42 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 491 490 (by norm_num) ord_491) (dvd_of_mpow 245 (58*42) (by norm_num) per_491)
  exact chk_491 (n % 42) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_499 : ∀ j, j < 41 → mpow 499 2 64 ((mpow 166 2 64 (58*j+26)+2)%166) ≠ 496 := by decide

set_option maxRecDepth 100000 in
theorem ord_499 : mpow 499 2 64 166 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_499 : mpow 83 2 64 (58*41) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_499 (n : ℕ) : ¬ ((499:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 499 166 1 83 41 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 499 166 (by norm_num) ord_499) (dvd_of_mpow 83 (58*41) (by norm_num) per_499)
  exact chk_499 (n % 41) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_503 : ∀ j, j < 25 → mpow 503 2 64 ((mpow 251 2 64 (58*j+26)+2)%251) ≠ 500 := by decide

set_option maxRecDepth 100000 in
theorem ord_503 : mpow 503 2 64 251 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_503 : mpow 251 2 64 (58*25) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_503 (n : ℕ) : ¬ ((503:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 503 251 0 251 25 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 503 251 (by norm_num) ord_503) (dvd_of_mpow 251 (58*25) (by norm_num) per_503)
  exact chk_503 (n % 25) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_509 : ∀ j, j < 7 → mpow 509 2 64 ((mpow 508 2 64 (58*j+26)+2)%508) ≠ 506 := by decide

set_option maxRecDepth 100000 in
theorem ord_509 : mpow 509 2 64 508 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_509 : mpow 127 2 64 (58*7) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_509 (n : ℕ) : ¬ ((509:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 509 508 2 127 7 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 509 508 (by norm_num) ord_509) (dvd_of_mpow 127 (58*7) (by norm_num) per_509)
  exact chk_509 (n % 7) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_521 : ∀ j, j < 6 → mpow 521 2 64 ((mpow 260 2 64 (58*j+26)+2)%260) ≠ 518 := by decide

set_option maxRecDepth 100000 in
theorem ord_521 : mpow 521 2 64 260 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_521 : mpow 65 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_521 (n : ℕ) : ¬ ((521:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 521 260 2 65 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 521 260 (by norm_num) ord_521) (dvd_of_mpow 65 (58*6) (by norm_num) per_521)
  exact chk_521 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_523 : ∀ j, j < 42 → j ≠ 26 → mpow 523 2 64 ((mpow 522 2 64 (58*j+26)+2)%522) ≠ 520 := by decide

set_option maxRecDepth 100000 in
theorem ord_523 : mpow 523 2 64 522 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_523 : mpow 261 2 64 (58*42) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_523 (n : ℕ) (hh : n%42≠26) : ¬ ((523:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 523 522 1 261 42 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 523 522 (by norm_num) ord_523) (dvd_of_mpow 261 (58*42) (by norm_num) per_523)
  refine chk_523 (n % 42) (Nat.mod_lt _ (by norm_num)) ?_
  omega

set_option maxRecDepth 100000 in
theorem chk_541 : ∀ j, j < 18 → mpow 541 2 64 ((mpow 540 2 64 (58*j+26)+2)%540) ≠ 538 := by decide

set_option maxRecDepth 100000 in
theorem ord_541 : mpow 541 2 64 540 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_541 : mpow 135 2 64 (58*18) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_541 (n : ℕ) : ¬ ((541:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 541 540 2 135 18 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 541 540 (by norm_num) ord_541) (dvd_of_mpow 135 (58*18) (by norm_num) per_541)
  exact chk_541 (n % 18) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_547 : ∀ j, j < 6 → mpow 547 2 64 ((mpow 546 2 64 (58*j+26)+2)%546) ≠ 544 := by decide

set_option maxRecDepth 100000 in
theorem ord_547 : mpow 547 2 64 546 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_547 : mpow 273 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_547 (n : ℕ) : ¬ ((547:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 547 546 1 273 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 547 546 (by norm_num) ord_547) (dvd_of_mpow 273 (58*6) (by norm_num) per_547)
  exact chk_547 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_557 : ∀ j, j < 69 → mpow 557 2 64 ((mpow 556 2 64 (58*j+26)+2)%556) ≠ 554 := by decide

set_option maxRecDepth 100000 in
theorem ord_557 : mpow 557 2 64 556 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_557 : mpow 139 2 64 (58*69) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_557 (n : ℕ) : ¬ ((557:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 557 556 2 139 69 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 557 556 (by norm_num) ord_557) (dvd_of_mpow 139 (58*69) (by norm_num) per_557)
  exact chk_557 (n % 69) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_563 : ∀ j, j < 35 → mpow 563 2 64 ((mpow 562 2 64 (58*j+26)+2)%562) ≠ 560 := by decide

set_option maxRecDepth 100000 in
theorem ord_563 : mpow 563 2 64 562 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_563 : mpow 281 2 64 (58*35) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_563 (n : ℕ) : ¬ ((563:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 563 562 1 281 35 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 563 562 (by norm_num) ord_563) (dvd_of_mpow 281 (58*35) (by norm_num) per_563)
  exact chk_563 (n % 35) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_569 : ∀ j, j < 35 → mpow 569 2 64 ((mpow 284 2 64 (58*j+26)+2)%284) ≠ 566 := by decide

set_option maxRecDepth 100000 in
theorem ord_569 : mpow 569 2 64 284 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_569 : mpow 71 2 64 (58*35) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_569 (n : ℕ) : ¬ ((569:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 569 284 2 71 35 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 569 284 (by norm_num) ord_569) (dvd_of_mpow 71 (58*35) (by norm_num) per_569)
  exact chk_569 (n % 35) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_571 : ∀ j, j < 9 → mpow 571 2 64 ((mpow 114 2 64 (58*j+26)+2)%114) ≠ 568 := by decide

set_option maxRecDepth 100000 in
theorem ord_571 : mpow 571 2 64 114 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_571 : mpow 57 2 64 (58*9) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_571 (n : ℕ) : ¬ ((571:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 571 114 1 57 9 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 571 114 (by norm_num) ord_571) (dvd_of_mpow 57 (58*9) (by norm_num) per_571)
  exact chk_571 (n % 9) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_577 : ∀ j, j < 3 → mpow 577 2 64 ((mpow 144 2 64 (58*j+26)+2)%144) ≠ 574 := by decide

set_option maxRecDepth 100000 in
theorem ord_577 : mpow 577 2 64 144 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_577 : mpow 9 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_577 (n : ℕ) : ¬ ((577:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 577 144 4 9 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 577 144 (by norm_num) ord_577) (dvd_of_mpow 9 (58*3) (by norm_num) per_577)
  exact chk_577 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_587 : ∀ j, j < 146 → mpow 587 2 64 ((mpow 586 2 64 (58*j+26)+2)%586) ≠ 584 := by decide

set_option maxRecDepth 100000 in
theorem ord_587 : mpow 587 2 64 586 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_587 : mpow 293 2 64 (58*146) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_587 (n : ℕ) : ¬ ((587:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 587 586 1 293 146 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 587 586 (by norm_num) ord_587) (dvd_of_mpow 293 (58*146) (by norm_num) per_587)
  exact chk_587 (n % 146) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_593 : ∀ j, j < 18 → mpow 593 2 64 ((mpow 148 2 64 (58*j+26)+2)%148) ≠ 590 := by decide

set_option maxRecDepth 100000 in
theorem ord_593 : mpow 593 2 64 148 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_593 : mpow 37 2 64 (58*18) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_593 (n : ℕ) : ¬ ((593:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 593 148 2 37 18 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 593 148 (by norm_num) ord_593) (dvd_of_mpow 37 (58*18) (by norm_num) per_593)
  exact chk_593 (n % 18) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_599 : ∀ j, j < 66 → mpow 599 2 64 ((mpow 299 2 64 (58*j+26)+2)%299) ≠ 596 := by decide

set_option maxRecDepth 100000 in
theorem ord_599 : mpow 599 2 64 299 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_599 : mpow 299 2 64 (58*66) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_599 (n : ℕ) : ¬ ((599:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 599 299 0 299 66 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 599 299 (by norm_num) ord_599) (dvd_of_mpow 299 (58*66) (by norm_num) per_599)
  exact chk_599 (n % 66) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_601 : ∀ j, j < 10 → mpow 601 2 64 ((mpow 25 2 64 (58*j+26)+2)%25) ≠ 598 := by decide

set_option maxRecDepth 100000 in
theorem ord_601 : mpow 601 2 64 25 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_601 : mpow 25 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_601 (n : ℕ) : ¬ ((601:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 601 25 0 25 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 601 25 (by norm_num) ord_601) (dvd_of_mpow 25 (58*10) (by norm_num) per_601)
  exact chk_601 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_607 : ∀ j, j < 50 → mpow 607 2 64 ((mpow 303 2 64 (58*j+26)+2)%303) ≠ 604 := by decide

set_option maxRecDepth 100000 in
theorem ord_607 : mpow 607 2 64 303 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_607 : mpow 303 2 64 (58*50) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_607 (n : ℕ) : ¬ ((607:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 607 303 0 303 50 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 607 303 (by norm_num) ord_607) (dvd_of_mpow 303 (58*50) (by norm_num) per_607)
  exact chk_607 (n % 50) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_613 : ∀ j, j < 12 → mpow 613 2 64 ((mpow 612 2 64 (58*j+26)+2)%612) ≠ 610 := by decide

set_option maxRecDepth 100000 in
theorem ord_613 : mpow 613 2 64 612 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_613 : mpow 153 2 64 (58*12) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_613 (n : ℕ) : ¬ ((613:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 613 612 2 153 12 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 613 612 (by norm_num) ord_613) (dvd_of_mpow 153 (58*12) (by norm_num) per_613)
  exact chk_613 (n % 12) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_617 : ∀ j, j < 15 → mpow 617 2 64 ((mpow 154 2 64 (58*j+26)+2)%154) ≠ 614 := by decide

set_option maxRecDepth 100000 in
theorem ord_617 : mpow 617 2 64 154 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_617 : mpow 77 2 64 (58*15) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_617 (n : ℕ) : ¬ ((617:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 617 154 1 77 15 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 617 154 (by norm_num) ord_617) (dvd_of_mpow 77 (58*15) (by norm_num) per_617)
  exact chk_617 (n % 15) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_619 : ∀ j, j < 51 → mpow 619 2 64 ((mpow 618 2 64 (58*j+26)+2)%618) ≠ 616 := by decide

set_option maxRecDepth 100000 in
theorem ord_619 : mpow 619 2 64 618 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_619 : mpow 309 2 64 (58*51) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_619 (n : ℕ) : ¬ ((619:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 619 618 1 309 51 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 619 618 (by norm_num) ord_619) (dvd_of_mpow 309 (58*51) (by norm_num) per_619)
  exact chk_619 (n % 51) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_631 : ∀ j, j < 6 → mpow 631 2 64 ((mpow 45 2 64 (58*j+26)+2)%45) ≠ 628 := by decide

set_option maxRecDepth 100000 in
theorem ord_631 : mpow 631 2 64 45 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_631 : mpow 45 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_631 (n : ℕ) : ¬ ((631:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 631 45 0 45 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 631 45 (by norm_num) ord_631) (dvd_of_mpow 45 (58*6) (by norm_num) per_631)
  exact chk_631 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_641 : ∀ j, j < 1 → mpow 641 2 64 ((mpow 64 2 64 (58*j+26)+2)%64) ≠ 638 := by decide

set_option maxRecDepth 100000 in
theorem ord_641 : mpow 641 2 64 64 = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_641 (n : ℕ) : ¬ ((641:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 641 64 6 1 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 641 64 (by norm_num) ord_641) (one_dvd _)
  exact chk_641 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_643 : ∀ j, j < 53 → mpow 643 2 64 ((mpow 214 2 64 (58*j+26)+2)%214) ≠ 640 := by decide

set_option maxRecDepth 100000 in
theorem ord_643 : mpow 643 2 64 214 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_643 : mpow 107 2 64 (58*53) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_643 (n : ℕ) : ¬ ((643:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 643 214 1 107 53 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 643 214 (by norm_num) ord_643) (dvd_of_mpow 107 (58*53) (by norm_num) per_643)
  exact chk_643 (n % 53) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_647 : ∀ j, j < 36 → mpow 647 2 64 ((mpow 323 2 64 (58*j+26)+2)%323) ≠ 644 := by decide

set_option maxRecDepth 100000 in
theorem ord_647 : mpow 647 2 64 323 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_647 : mpow 323 2 64 (58*36) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_647 (n : ℕ) : ¬ ((647:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 647 323 0 323 36 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 647 323 (by norm_num) ord_647) (dvd_of_mpow 323 (58*36) (by norm_num) per_647)
  exact chk_647 (n % 36) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_653 : ∀ j, j < 81 → mpow 653 2 64 ((mpow 652 2 64 (58*j+26)+2)%652) ≠ 650 := by decide

set_option maxRecDepth 100000 in
theorem ord_653 : mpow 653 2 64 652 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_653 : mpow 163 2 64 (58*81) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_653 (n : ℕ) : ¬ ((653:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 653 652 2 163 81 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 653 652 (by norm_num) ord_653) (dvd_of_mpow 163 (58*81) (by norm_num) per_653)
  exact chk_653 (n % 81) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_659 : ∀ j, j < 69 → mpow 659 2 64 ((mpow 658 2 64 (58*j+26)+2)%658) ≠ 656 := by decide

set_option maxRecDepth 100000 in
theorem ord_659 : mpow 659 2 64 658 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_659 : mpow 329 2 64 (58*69) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_659 (n : ℕ) : ¬ ((659:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 659 658 1 329 69 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 659 658 (by norm_num) ord_659) (dvd_of_mpow 329 (58*69) (by norm_num) per_659)
  exact chk_659 (n % 69) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_661 : ∀ j, j < 10 → mpow 661 2 64 ((mpow 660 2 64 (58*j+26)+2)%660) ≠ 658 := by decide

set_option maxRecDepth 100000 in
theorem ord_661 : mpow 661 2 64 660 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_661 : mpow 165 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_661 (n : ℕ) : ¬ ((661:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 661 660 2 165 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 661 660 (by norm_num) ord_661) (dvd_of_mpow 165 (58*10) (by norm_num) per_661)
  exact chk_661 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_673 : ∀ j, j < 1 → mpow 673 2 64 ((mpow 48 2 64 (58*j+26)+2)%48) ≠ 670 := by decide

set_option maxRecDepth 100000 in
theorem ord_673 : mpow 673 2 64 48 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_673 : mpow 3 2 64 (58*1) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_673 (n : ℕ) : ¬ ((673:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 673 48 4 3 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 673 48 (by norm_num) ord_673) (dvd_of_mpow 3 (58*1) (by norm_num) per_673)
  exact chk_673 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_677 : ∀ j, j < 78 → mpow 677 2 64 ((mpow 676 2 64 (58*j+26)+2)%676) ≠ 674 := by decide

set_option maxRecDepth 100000 in
theorem ord_677 : mpow 677 2 64 676 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_677 : mpow 169 2 64 (58*78) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_677 (n : ℕ) : ¬ ((677:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 677 676 2 169 78 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 677 676 (by norm_num) ord_677) (dvd_of_mpow 169 (58*78) (by norm_num) per_677)
  exact chk_677 (n % 78) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_683 : ∀ j, j < 5 → mpow 683 2 64 ((mpow 22 2 64 (58*j+26)+2)%22) ≠ 680 := by decide

set_option maxRecDepth 100000 in
theorem ord_683 : mpow 683 2 64 22 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_683 : mpow 11 2 64 (58*5) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_683 (n : ℕ) : ¬ ((683:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 683 22 1 11 5 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 683 22 (by norm_num) ord_683) (dvd_of_mpow 11 (58*5) (by norm_num) per_683)
  exact chk_683 (n % 5) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_691 : ∀ j, j < 22 → mpow 691 2 64 ((mpow 230 2 64 (58*j+26)+2)%230) ≠ 688 := by decide

set_option maxRecDepth 100000 in
theorem ord_691 : mpow 691 2 64 230 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_691 : mpow 115 2 64 (58*22) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_691 (n : ℕ) : ¬ ((691:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 691 230 1 115 22 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 691 230 (by norm_num) ord_691) (dvd_of_mpow 115 (58*22) (by norm_num) per_691)
  exact chk_691 (n % 22) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_701 : ∀ j, j < 30 → mpow 701 2 64 ((mpow 700 2 64 (58*j+26)+2)%700) ≠ 698 := by decide

set_option maxRecDepth 100000 in
theorem ord_701 : mpow 701 2 64 700 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_701 : mpow 175 2 64 (58*30) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_701 (n : ℕ) : ¬ ((701:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 701 700 2 175 30 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 701 700 (by norm_num) ord_701) (dvd_of_mpow 175 (58*30) (by norm_num) per_701)
  exact chk_701 (n % 30) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_709 : ∀ j, j < 1 → mpow 709 2 64 ((mpow 708 2 64 (58*j+26)+2)%708) ≠ 706 := by decide

set_option maxRecDepth 100000 in
theorem ord_709 : mpow 709 2 64 708 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_709 : mpow 177 2 64 (58*1) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_709 (n : ℕ) : ¬ ((709:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 709 708 2 177 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 709 708 (by norm_num) ord_709) (dvd_of_mpow 177 (58*1) (by norm_num) per_709)
  exact chk_709 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_719 : ∀ j, j < 179 → mpow 719 2 64 ((mpow 359 2 64 (58*j+26)+2)%359) ≠ 716 := by decide

set_option maxRecDepth 100000 in
theorem ord_719 : mpow 719 2 64 359 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_719 : mpow 359 2 64 (58*179) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_719 (n : ℕ) : ¬ ((719:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 719 359 0 359 179 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 719 359 (by norm_num) ord_719) (dvd_of_mpow 359 (58*179) (by norm_num) per_719)
  exact chk_719 (n % 179) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_727 : ∀ j, j < 55 → mpow 727 2 64 ((mpow 121 2 64 (58*j+26)+2)%121) ≠ 724 := by decide

set_option maxRecDepth 100000 in
theorem ord_727 : mpow 727 2 64 121 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_727 : mpow 121 2 64 (58*55) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_727 (n : ℕ) : ¬ ((727:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 727 121 0 121 55 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 727 121 (by norm_num) ord_727) (dvd_of_mpow 121 (58*55) (by norm_num) per_727)
  exact chk_727 (n % 55) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_733 : ∀ j, j < 30 → mpow 733 2 64 ((mpow 244 2 64 (58*j+26)+2)%244) ≠ 730 := by decide

set_option maxRecDepth 100000 in
theorem ord_733 : mpow 733 2 64 244 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_733 : mpow 61 2 64 (58*30) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_733 (n : ℕ) : ¬ ((733:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 733 244 2 61 30 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 733 244 (by norm_num) ord_733) (dvd_of_mpow 61 (58*30) (by norm_num) per_733)
  exact chk_733 (n % 30) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_739 : ∀ j, j < 10 → mpow 739 2 64 ((mpow 246 2 64 (58*j+26)+2)%246) ≠ 736 := by decide

set_option maxRecDepth 100000 in
theorem ord_739 : mpow 739 2 64 246 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_739 : mpow 123 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_739 (n : ℕ) : ¬ ((739:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 739 246 1 123 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 739 246 (by norm_num) ord_739) (dvd_of_mpow 123 (58*10) (by norm_num) per_739)
  exact chk_739 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_743 : ∀ j, j < 78 → mpow 743 2 64 ((mpow 371 2 64 (58*j+26)+2)%371) ≠ 740 := by decide

set_option maxRecDepth 100000 in
theorem ord_743 : mpow 743 2 64 371 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_743 : mpow 371 2 64 (58*78) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_743 (n : ℕ) : ¬ ((743:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 743 371 0 371 78 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 743 371 (by norm_num) ord_743) (dvd_of_mpow 371 (58*78) (by norm_num) per_743)
  exact chk_743 (n % 78) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_751 : ∀ j, j < 50 → mpow 751 2 64 ((mpow 375 2 64 (58*j+26)+2)%375) ≠ 748 := by decide

set_option maxRecDepth 100000 in
theorem ord_751 : mpow 751 2 64 375 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_751 : mpow 375 2 64 (58*50) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_751 (n : ℕ) : ¬ ((751:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 751 375 0 375 50 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 751 375 (by norm_num) ord_751) (dvd_of_mpow 375 (58*50) (by norm_num) per_751)
  exact chk_751 (n % 50) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_757 : ∀ j, j < 9 → mpow 757 2 64 ((mpow 756 2 64 (58*j+26)+2)%756) ≠ 754 := by decide

set_option maxRecDepth 100000 in
theorem ord_757 : mpow 757 2 64 756 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_757 : mpow 189 2 64 (58*9) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_757 (n : ℕ) : ¬ ((757:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 757 756 2 189 9 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 757 756 (by norm_num) ord_757) (dvd_of_mpow 189 (58*9) (by norm_num) per_757)
  exact chk_757 (n % 9) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_761 : ∀ j, j < 18 → mpow 761 2 64 ((mpow 380 2 64 (58*j+26)+2)%380) ≠ 758 := by decide

set_option maxRecDepth 100000 in
theorem ord_761 : mpow 761 2 64 380 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_761 : mpow 95 2 64 (58*18) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_761 (n : ℕ) : ¬ ((761:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 761 380 2 95 18 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 761 380 (by norm_num) ord_761) (dvd_of_mpow 95 (58*18) (by norm_num) per_761)
  exact chk_761 (n % 18) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_769 : ∀ j, j < 1 → mpow 769 2 64 ((mpow 384 2 64 (58*j+26)+2)%384) ≠ 766 := by decide

set_option maxRecDepth 100000 in
theorem ord_769 : mpow 769 2 64 384 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_769 : mpow 3 2 64 (58*1) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_769 (n : ℕ) : ¬ ((769:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 769 384 7 3 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 769 384 (by norm_num) ord_769) (dvd_of_mpow 3 (58*1) (by norm_num) per_769)
  exact chk_769 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_773 : ∀ j, j < 48 → mpow 773 2 64 ((mpow 772 2 64 (58*j+26)+2)%772) ≠ 770 := by decide

set_option maxRecDepth 100000 in
theorem ord_773 : mpow 773 2 64 772 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_773 : mpow 193 2 64 (58*48) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_773 (n : ℕ) : ¬ ((773:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 773 772 2 193 48 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 773 772 (by norm_num) ord_773) (dvd_of_mpow 193 (58*48) (by norm_num) per_773)
  exact chk_773 (n % 48) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_787 : ∀ j, j < 65 → mpow 787 2 64 ((mpow 786 2 64 (58*j+26)+2)%786) ≠ 784 := by decide

set_option maxRecDepth 100000 in
theorem ord_787 : mpow 787 2 64 786 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_787 : mpow 393 2 64 (58*65) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_787 (n : ℕ) : ¬ ((787:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 787 786 1 393 65 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 787 786 (by norm_num) ord_787) (dvd_of_mpow 393 (58*65) (by norm_num) per_787)
  exact chk_787 (n % 65) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_797 : ∀ j, j < 99 → mpow 797 2 64 ((mpow 796 2 64 (58*j+26)+2)%796) ≠ 794 := by decide

set_option maxRecDepth 100000 in
theorem ord_797 : mpow 797 2 64 796 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_797 : mpow 199 2 64 (58*99) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_797 (n : ℕ) : ¬ ((797:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 797 796 2 199 99 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 797 796 (by norm_num) ord_797) (dvd_of_mpow 199 (58*99) (by norm_num) per_797)
  exact chk_797 (n % 99) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_809 : ∀ j, j < 50 → mpow 809 2 64 ((mpow 404 2 64 (58*j+26)+2)%404) ≠ 806 := by decide

set_option maxRecDepth 100000 in
theorem ord_809 : mpow 809 2 64 404 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_809 : mpow 101 2 64 (58*50) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_809 (n : ℕ) : ¬ ((809:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 809 404 2 101 50 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 809 404 (by norm_num) ord_809) (dvd_of_mpow 101 (58*50) (by norm_num) per_809)
  exact chk_809 (n % 50) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_811 : ∀ j, j < 18 → mpow 811 2 64 ((mpow 270 2 64 (58*j+26)+2)%270) ≠ 808 := by decide

set_option maxRecDepth 100000 in
theorem ord_811 : mpow 811 2 64 270 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_811 : mpow 135 2 64 (58*18) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_811 (n : ℕ) : ¬ ((811:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 811 270 1 135 18 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 811 270 (by norm_num) ord_811) (dvd_of_mpow 135 (58*18) (by norm_num) per_811)
  exact chk_811 (n % 18) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_821 : ∀ j, j < 10 → mpow 821 2 64 ((mpow 820 2 64 (58*j+26)+2)%820) ≠ 818 := by decide

set_option maxRecDepth 100000 in
theorem ord_821 : mpow 821 2 64 820 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_821 : mpow 205 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_821 (n : ℕ) : ¬ ((821:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 821 820 2 205 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 821 820 (by norm_num) ord_821) (dvd_of_mpow 205 (58*10) (by norm_num) per_821)
  exact chk_821 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_823 : ∀ j, j < 34 → mpow 823 2 64 ((mpow 411 2 64 (58*j+26)+2)%411) ≠ 820 := by decide

set_option maxRecDepth 100000 in
theorem ord_823 : mpow 823 2 64 411 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_823 : mpow 411 2 64 (58*34) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_823 (n : ℕ) : ¬ ((823:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 823 411 0 411 34 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 823 411 (by norm_num) ord_823) (dvd_of_mpow 411 (58*34) (by norm_num) per_823)
  exact chk_823 (n % 34) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_827 : ∀ j, j < 3 → mpow 827 2 64 ((mpow 826 2 64 (58*j+26)+2)%826) ≠ 824 := by decide

set_option maxRecDepth 100000 in
theorem ord_827 : mpow 827 2 64 826 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_827 : mpow 413 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_827 (n : ℕ) : ¬ ((827:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 827 826 1 413 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 827 826 (by norm_num) ord_827) (dvd_of_mpow 413 (58*3) (by norm_num) per_827)
  exact chk_827 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_829 : ∀ j, j < 33 → mpow 829 2 64 ((mpow 828 2 64 (58*j+26)+2)%828) ≠ 826 := by decide

set_option maxRecDepth 100000 in
theorem ord_829 : mpow 829 2 64 828 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_829 : mpow 207 2 64 (58*33) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_829 (n : ℕ) : ¬ ((829:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 829 828 2 207 33 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 829 828 (by norm_num) ord_829) (dvd_of_mpow 207 (58*33) (by norm_num) per_829)
  exact chk_829 (n % 33) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_839 : ∀ j, j < 209 → mpow 839 2 64 ((mpow 419 2 64 (58*j+26)+2)%419) ≠ 836 := by decide

set_option maxRecDepth 100000 in
theorem ord_839 : mpow 839 2 64 419 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_839 : mpow 419 2 64 (58*209) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_839 (n : ℕ) : ¬ ((839:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 839 419 0 419 209 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 839 419 (by norm_num) ord_839) (dvd_of_mpow 419 (58*209) (by norm_num) per_839)
  exact chk_839 (n % 209) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_853 : ∀ j, j < 35 → mpow 853 2 64 ((mpow 852 2 64 (58*j+26)+2)%852) ≠ 850 := by decide

set_option maxRecDepth 100000 in
theorem ord_853 : mpow 853 2 64 852 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_853 : mpow 213 2 64 (58*35) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_853 (n : ℕ) : ¬ ((853:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 853 852 2 213 35 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 853 852 (by norm_num) ord_853) (dvd_of_mpow 213 (58*35) (by norm_num) per_853)
  exact chk_853 (n % 35) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_857 : ∀ j, j < 53 → mpow 857 2 64 ((mpow 428 2 64 (58*j+26)+2)%428) ≠ 854 := by decide

set_option maxRecDepth 100000 in
theorem ord_857 : mpow 857 2 64 428 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_857 : mpow 107 2 64 (58*53) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_857 (n : ℕ) : ¬ ((857:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 857 428 2 107 53 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 857 428 (by norm_num) ord_857) (dvd_of_mpow 107 (58*53) (by norm_num) per_857)
  exact chk_857 (n % 53) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_859 : ∀ j, j < 30 → mpow 859 2 64 ((mpow 858 2 64 (58*j+26)+2)%858) ≠ 856 := by decide

set_option maxRecDepth 100000 in
theorem ord_859 : mpow 859 2 64 858 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_859 : mpow 429 2 64 (58*30) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_859 (n : ℕ) : ¬ ((859:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 859 858 1 429 30 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 859 858 (by norm_num) ord_859) (dvd_of_mpow 429 (58*30) (by norm_num) per_859)
  exact chk_859 (n % 30) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_863 : ∀ j, j < 43 → mpow 863 2 64 ((mpow 431 2 64 (58*j+26)+2)%431) ≠ 860 := by decide

set_option maxRecDepth 100000 in
theorem ord_863 : mpow 863 2 64 431 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_863 : mpow 431 2 64 (58*43) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_863 (n : ℕ) : ¬ ((863:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 863 431 0 431 43 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 863 431 (by norm_num) ord_863) (dvd_of_mpow 431 (58*43) (by norm_num) per_863)
  exact chk_863 (n % 43) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_877 : ∀ j, j < 9 → mpow 877 2 64 ((mpow 876 2 64 (58*j+26)+2)%876) ≠ 874 := by decide

set_option maxRecDepth 100000 in
theorem ord_877 : mpow 877 2 64 876 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_877 : mpow 219 2 64 (58*9) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_877 (n : ℕ) : ¬ ((877:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 877 876 2 219 9 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 877 876 (by norm_num) ord_877) (dvd_of_mpow 219 (58*9) (by norm_num) per_877)
  exact chk_877 (n % 9) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_881 : ∀ j, j < 10 → mpow 881 2 64 ((mpow 55 2 64 (58*j+26)+2)%55) ≠ 878 := by decide

set_option maxRecDepth 100000 in
theorem ord_881 : mpow 881 2 64 55 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_881 : mpow 55 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_881 (n : ℕ) : ¬ ((881:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 881 55 0 55 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 881 55 (by norm_num) ord_881) (dvd_of_mpow 55 (58*10) (by norm_num) per_881)
  exact chk_881 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_883 : ∀ j, j < 21 → mpow 883 2 64 ((mpow 882 2 64 (58*j+26)+2)%882) ≠ 880 := by decide

set_option maxRecDepth 100000 in
theorem ord_883 : mpow 883 2 64 882 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_883 : mpow 441 2 64 (58*21) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_883 (n : ℕ) : ¬ ((883:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 883 882 1 441 21 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 883 882 (by norm_num) ord_883) (dvd_of_mpow 441 (58*21) (by norm_num) per_883)
  exact chk_883 (n % 21) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_887 : ∀ j, j < 221 → mpow 887 2 64 ((mpow 443 2 64 (58*j+26)+2)%443) ≠ 884 := by decide

set_option maxRecDepth 100000 in
theorem ord_887 : mpow 887 2 64 443 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_887 : mpow 443 2 64 (58*221) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_887 (n : ℕ) : ¬ ((887:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 887 443 0 443 221 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 887 443 (by norm_num) ord_887) (dvd_of_mpow 443 (58*221) (by norm_num) per_887)
  exact chk_887 (n % 221) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_907 : ∀ j, j < 15 → mpow 907 2 64 ((mpow 906 2 64 (58*j+26)+2)%906) ≠ 904 := by decide

set_option maxRecDepth 100000 in
theorem ord_907 : mpow 907 2 64 906 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_907 : mpow 453 2 64 (58*15) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_907 (n : ℕ) : ¬ ((907:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 907 906 1 453 15 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 907 906 (by norm_num) ord_907) (dvd_of_mpow 453 (58*15) (by norm_num) per_907)
  exact chk_907 (n % 15) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_911 : ∀ j, j < 6 → mpow 911 2 64 ((mpow 91 2 64 (58*j+26)+2)%91) ≠ 908 := by decide

set_option maxRecDepth 100000 in
theorem ord_911 : mpow 911 2 64 91 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_911 : mpow 91 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_911 (n : ℕ) : ¬ ((911:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 911 91 0 91 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 911 91 (by norm_num) ord_911) (dvd_of_mpow 91 (58*6) (by norm_num) per_911)
  exact chk_911 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_919 : ∀ j, j < 12 → mpow 919 2 64 ((mpow 153 2 64 (58*j+26)+2)%153) ≠ 916 := by decide

set_option maxRecDepth 100000 in
theorem ord_919 : mpow 919 2 64 153 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_919 : mpow 153 2 64 (58*12) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_919 (n : ℕ) : ¬ ((919:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 919 153 0 153 12 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 919 153 (by norm_num) ord_919) (dvd_of_mpow 153 (58*12) (by norm_num) per_919)
  exact chk_919 (n % 12) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_929 : ∀ j, j < 14 → mpow 929 2 64 ((mpow 464 2 64 (58*j+26)+2)%464) ≠ 926 := by decide

set_option maxRecDepth 100000 in
theorem ord_929 : mpow 929 2 64 464 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_929 : mpow 29 2 64 (58*14) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_929 (n : ℕ) : ¬ ((929:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 929 464 4 29 14 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 929 464 (by norm_num) ord_929) (dvd_of_mpow 29 (58*14) (by norm_num) per_929)
  exact chk_929 (n % 14) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_937 : ∀ j, j < 6 → mpow 937 2 64 ((mpow 117 2 64 (58*j+26)+2)%117) ≠ 934 := by decide

set_option maxRecDepth 100000 in
theorem ord_937 : mpow 937 2 64 117 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_937 : mpow 117 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_937 (n : ℕ) : ¬ ((937:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 937 117 0 117 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 937 117 (by norm_num) ord_937) (dvd_of_mpow 117 (58*6) (by norm_num) per_937)
  exact chk_937 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_941 : ∀ j, j < 46 → mpow 941 2 64 ((mpow 940 2 64 (58*j+26)+2)%940) ≠ 938 := by decide

set_option maxRecDepth 100000 in
theorem ord_941 : mpow 941 2 64 940 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_941 : mpow 235 2 64 (58*46) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_941 (n : ℕ) : ¬ ((941:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 941 940 2 235 46 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 941 940 (by norm_num) ord_941) (dvd_of_mpow 235 (58*46) (by norm_num) per_941)
  exact chk_941 (n % 46) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_947 : ∀ j, j < 35 → mpow 947 2 64 ((mpow 946 2 64 (58*j+26)+2)%946) ≠ 944 := by decide

set_option maxRecDepth 100000 in
theorem ord_947 : mpow 947 2 64 946 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_947 : mpow 473 2 64 (58*35) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_947 (n : ℕ) : ¬ ((947:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 947 946 1 473 35 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 947 946 (by norm_num) ord_947) (dvd_of_mpow 473 (58*35) (by norm_num) per_947)
  exact chk_947 (n % 35) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_953 : ∀ j, j < 4 → mpow 953 2 64 ((mpow 68 2 64 (58*j+26)+2)%68) ≠ 950 := by decide

set_option maxRecDepth 100000 in
theorem ord_953 : mpow 953 2 64 68 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_953 : mpow 17 2 64 (58*4) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_953 (n : ℕ) : ¬ ((953:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 953 68 2 17 4 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 953 68 (by norm_num) ord_953) (dvd_of_mpow 17 (58*4) (by norm_num) per_953)
  exact chk_953 (n % 4) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_967 : ∀ j, j < 33 → mpow 967 2 64 ((mpow 483 2 64 (58*j+26)+2)%483) ≠ 964 := by decide

set_option maxRecDepth 100000 in
theorem ord_967 : mpow 967 2 64 483 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_967 : mpow 483 2 64 (58*33) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_967 (n : ℕ) : ¬ ((967:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 967 483 0 483 33 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 967 483 (by norm_num) ord_967) (dvd_of_mpow 483 (58*33) (by norm_num) per_967)
  exact chk_967 (n % 33) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_971 : ∀ j, j < 24 → mpow 971 2 64 ((mpow 194 2 64 (58*j+26)+2)%194) ≠ 968 := by decide

set_option maxRecDepth 100000 in
theorem ord_971 : mpow 971 2 64 194 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_971 : mpow 97 2 64 (58*24) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_971 (n : ℕ) : ¬ ((971:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 971 194 1 97 24 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 971 194 (by norm_num) ord_971) (dvd_of_mpow 97 (58*24) (by norm_num) per_971)
  exact chk_971 (n % 24) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_977 : ∀ j, j < 30 → mpow 977 2 64 ((mpow 488 2 64 (58*j+26)+2)%488) ≠ 974 := by decide

set_option maxRecDepth 100000 in
theorem ord_977 : mpow 977 2 64 488 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_977 : mpow 61 2 64 (58*30) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_977 (n : ℕ) : ¬ ((977:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 977 488 3 61 30 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 977 488 (by norm_num) ord_977) (dvd_of_mpow 61 (58*30) (by norm_num) per_977)
  exact chk_977 (n % 30) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_983 : ∀ j, j < 245 → mpow 983 2 64 ((mpow 491 2 64 (58*j+26)+2)%491) ≠ 980 := by decide

set_option maxRecDepth 100000 in
theorem ord_983 : mpow 983 2 64 491 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_983 : mpow 491 2 64 (58*245) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_983 (n : ℕ) : ¬ ((983:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 983 491 0 491 245 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 983 491 (by norm_num) ord_983) (dvd_of_mpow 491 (58*245) (by norm_num) per_983)
  exact chk_983 (n % 245) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_991 : ∀ j, j < 30 → mpow 991 2 64 ((mpow 495 2 64 (58*j+26)+2)%495) ≠ 988 := by decide

set_option maxRecDepth 100000 in
theorem ord_991 : mpow 991 2 64 495 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_991 : mpow 495 2 64 (58*30) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_991 (n : ℕ) : ¬ ((991:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 991 495 0 495 30 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 991 495 (by norm_num) ord_991) (dvd_of_mpow 495 (58*30) (by norm_num) per_991)
  exact chk_991 (n % 30) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_997 : ∀ j, j < 41 → mpow 997 2 64 ((mpow 332 2 64 (58*j+26)+2)%332) ≠ 994 := by decide

set_option maxRecDepth 100000 in
theorem ord_997 : mpow 997 2 64 332 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_997 : mpow 83 2 64 (58*41) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_997 (n : ℕ) : ¬ ((997:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 997 332 2 83 41 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 997 332 (by norm_num) ord_997) (dvd_of_mpow 83 (58*41) (by norm_num) per_997)
  exact chk_997 (n % 41) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1009 : ∀ j, j < 3 → mpow 1009 2 64 ((mpow 504 2 64 (58*j+26)+2)%504) ≠ 1006 := by decide

set_option maxRecDepth 100000 in
theorem ord_1009 : mpow 1009 2 64 504 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1009 : mpow 63 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1009 (n : ℕ) : ¬ ((1009:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1009 504 3 63 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1009 504 (by norm_num) ord_1009) (dvd_of_mpow 63 (58*3) (by norm_num) per_1009)
  exact chk_1009 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1013 : ∀ j, j < 11 → mpow 1013 2 64 ((mpow 92 2 64 (58*j+26)+2)%92) ≠ 1010 := by decide

set_option maxRecDepth 100000 in
theorem ord_1013 : mpow 1013 2 64 92 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1013 : mpow 23 2 64 (58*11) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1013 (n : ℕ) : ¬ ((1013:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1013 92 2 23 11 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1013 92 (by norm_num) ord_1013) (dvd_of_mpow 23 (58*11) (by norm_num) per_1013)
  exact chk_1013 (n % 11) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1019 : ∀ j, j < 254 → mpow 1019 2 64 ((mpow 1018 2 64 (58*j+26)+2)%1018) ≠ 1016 := by decide

set_option maxRecDepth 100000 in
theorem ord_1019 : mpow 1019 2 64 1018 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1019 : mpow 509 2 64 (58*254) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1019 (n : ℕ) : ¬ ((1019:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1019 1018 1 509 254 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1019 1018 (by norm_num) ord_1019) (dvd_of_mpow 509 (58*254) (by norm_num) per_1019)
  exact chk_1019 (n % 254) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1021 : ∀ j, j < 4 → mpow 1021 2 64 ((mpow 340 2 64 (58*j+26)+2)%340) ≠ 1018 := by decide

set_option maxRecDepth 100000 in
theorem ord_1021 : mpow 1021 2 64 340 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1021 : mpow 85 2 64 (58*4) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1021 (n : ℕ) : ¬ ((1021:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1021 340 2 85 4 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1021 340 (by norm_num) ord_1021) (dvd_of_mpow 85 (58*4) (by norm_num) per_1021)
  exact chk_1021 (n % 4) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1031 : ∀ j, j < 102 → mpow 1031 2 64 ((mpow 515 2 64 (58*j+26)+2)%515) ≠ 1028 := by decide

set_option maxRecDepth 100000 in
theorem ord_1031 : mpow 1031 2 64 515 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1031 : mpow 515 2 64 (58*102) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1031 (n : ℕ) : ¬ ((1031:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1031 515 0 515 102 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1031 515 (by norm_num) ord_1031) (dvd_of_mpow 515 (58*102) (by norm_num) per_1031)
  exact chk_1031 (n % 102) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1033 : ∀ j, j < 7 → mpow 1033 2 64 ((mpow 258 2 64 (58*j+26)+2)%258) ≠ 1030 := by decide

set_option maxRecDepth 100000 in
theorem ord_1033 : mpow 1033 2 64 258 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1033 : mpow 129 2 64 (58*7) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1033 (n : ℕ) : ¬ ((1033:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1033 258 1 129 7 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1033 258 (by norm_num) ord_1033) (dvd_of_mpow 129 (58*7) (by norm_num) per_1033)
  exact chk_1033 (n % 7) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1039 : ∀ j, j < 86 → mpow 1039 2 64 ((mpow 519 2 64 (58*j+26)+2)%519) ≠ 1036 := by decide

set_option maxRecDepth 100000 in
theorem ord_1039 : mpow 1039 2 64 519 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1039 : mpow 519 2 64 (58*86) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1039 (n : ℕ) : ¬ ((1039:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1039 519 0 519 86 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1039 519 (by norm_num) ord_1039) (dvd_of_mpow 519 (58*86) (by norm_num) per_1039)
  exact chk_1039 (n % 86) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1049 : ∀ j, j < 65 → mpow 1049 2 64 ((mpow 262 2 64 (58*j+26)+2)%262) ≠ 1046 := by decide

set_option maxRecDepth 100000 in
theorem ord_1049 : mpow 1049 2 64 262 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1049 : mpow 131 2 64 (58*65) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1049 (n : ℕ) : ¬ ((1049:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1049 262 1 131 65 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1049 262 (by norm_num) ord_1049) (dvd_of_mpow 131 (58*65) (by norm_num) per_1049)
  exact chk_1049 (n % 65) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1051 : ∀ j, j < 30 → mpow 1051 2 64 ((mpow 350 2 64 (58*j+26)+2)%350) ≠ 1048 := by decide

set_option maxRecDepth 100000 in
theorem ord_1051 : mpow 1051 2 64 350 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1051 : mpow 175 2 64 (58*30) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1051 (n : ℕ) : ¬ ((1051:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1051 350 1 175 30 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1051 350 (by norm_num) ord_1051) (dvd_of_mpow 175 (58*30) (by norm_num) per_1051)
  exact chk_1051 (n % 30) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1061 : ∀ j, j < 26 → mpow 1061 2 64 ((mpow 1060 2 64 (58*j+26)+2)%1060) ≠ 1058 := by decide

set_option maxRecDepth 100000 in
theorem ord_1061 : mpow 1061 2 64 1060 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1061 : mpow 265 2 64 (58*26) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1061 (n : ℕ) : ¬ ((1061:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1061 1060 2 265 26 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1061 1060 (by norm_num) ord_1061) (dvd_of_mpow 265 (58*26) (by norm_num) per_1061)
  exact chk_1061 (n % 26) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1063 : ∀ j, j < 3 → mpow 1063 2 64 ((mpow 531 2 64 (58*j+26)+2)%531) ≠ 1060 := by decide

set_option maxRecDepth 100000 in
theorem ord_1063 : mpow 1063 2 64 531 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1063 : mpow 531 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1063 (n : ℕ) : ¬ ((1063:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1063 531 0 531 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1063 531 (by norm_num) ord_1063) (dvd_of_mpow 531 (58*3) (by norm_num) per_1063)
  exact chk_1063 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1069 : ∀ j, j < 11 → mpow 1069 2 64 ((mpow 356 2 64 (58*j+26)+2)%356) ≠ 1066 := by decide

set_option maxRecDepth 100000 in
theorem ord_1069 : mpow 1069 2 64 356 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1069 : mpow 89 2 64 (58*11) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1069 (n : ℕ) : ¬ ((1069:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1069 356 2 89 11 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1069 356 (by norm_num) ord_1069) (dvd_of_mpow 89 (58*11) (by norm_num) per_1069)
  exact chk_1069 (n % 11) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1087 : ∀ j, j < 90 → mpow 1087 2 64 ((mpow 543 2 64 (58*j+26)+2)%543) ≠ 1084 := by decide

set_option maxRecDepth 100000 in
theorem ord_1087 : mpow 1087 2 64 543 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1087 : mpow 543 2 64 (58*90) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1087 (n : ℕ) : ¬ ((1087:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1087 543 0 543 90 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1087 543 (by norm_num) ord_1087) (dvd_of_mpow 543 (58*90) (by norm_num) per_1087)
  exact chk_1087 (n % 90) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1091 : ∀ j, j < 18 → mpow 1091 2 64 ((mpow 1090 2 64 (58*j+26)+2)%1090) ≠ 1088 := by decide

set_option maxRecDepth 100000 in
theorem ord_1091 : mpow 1091 2 64 1090 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1091 : mpow 545 2 64 (58*18) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1091 (n : ℕ) : ¬ ((1091:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1091 1090 1 545 18 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1091 1090 (by norm_num) ord_1091) (dvd_of_mpow 545 (58*18) (by norm_num) per_1091)
  exact chk_1091 (n % 18) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1093 : ∀ j, j < 6 → mpow 1093 2 64 ((mpow 364 2 64 (58*j+26)+2)%364) ≠ 1090 := by decide

set_option maxRecDepth 100000 in
theorem ord_1093 : mpow 1093 2 64 364 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1093 : mpow 91 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1093 (n : ℕ) : ¬ ((1093:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1093 364 2 91 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1093 364 (by norm_num) ord_1093) (dvd_of_mpow 91 (58*6) (by norm_num) per_1093)
  exact chk_1093 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1097 : ∀ j, j < 34 → mpow 1097 2 64 ((mpow 274 2 64 (58*j+26)+2)%274) ≠ 1094 := by decide

set_option maxRecDepth 100000 in
theorem ord_1097 : mpow 1097 2 64 274 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1097 : mpow 137 2 64 (58*34) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1097 (n : ℕ) : ¬ ((1097:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1097 274 1 137 34 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1097 274 (by norm_num) ord_1097) (dvd_of_mpow 137 (58*34) (by norm_num) per_1097)
  exact chk_1097 (n % 34) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1103 : ∀ j, j < 14 → mpow 1103 2 64 ((mpow 29 2 64 (58*j+26)+2)%29) ≠ 1100 := by decide

set_option maxRecDepth 100000 in
theorem ord_1103 : mpow 1103 2 64 29 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1103 : mpow 29 2 64 (58*14) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1103 (n : ℕ) : ¬ ((1103:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1103 29 0 29 14 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1103 29 (by norm_num) ord_1103) (dvd_of_mpow 29 (58*14) (by norm_num) per_1103)
  exact chk_1103 (n % 14) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1109 : ∀ j, j < 46 → mpow 1109 2 64 ((mpow 1108 2 64 (58*j+26)+2)%1108) ≠ 1106 := by decide

set_option maxRecDepth 100000 in
theorem ord_1109 : mpow 1109 2 64 1108 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1109 : mpow 277 2 64 (58*46) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1109 (n : ℕ) : ¬ ((1109:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1109 1108 2 277 46 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1109 1108 (by norm_num) ord_1109) (dvd_of_mpow 277 (58*46) (by norm_num) per_1109)
  exact chk_1109 (n % 46) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1117 : ∀ j, j < 15 → mpow 1117 2 64 ((mpow 1116 2 64 (58*j+26)+2)%1116) ≠ 1114 := by decide

set_option maxRecDepth 100000 in
theorem ord_1117 : mpow 1117 2 64 1116 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1117 : mpow 279 2 64 (58*15) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1117 (n : ℕ) : ¬ ((1117:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1117 1116 2 279 15 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1117 1116 (by norm_num) ord_1117) (dvd_of_mpow 279 (58*15) (by norm_num) per_1117)
  exact chk_1117 (n % 15) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1123 : ∀ j, j < 20 → mpow 1123 2 64 ((mpow 1122 2 64 (58*j+26)+2)%1122) ≠ 1120 := by decide

set_option maxRecDepth 100000 in
theorem ord_1123 : mpow 1123 2 64 1122 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1123 : mpow 561 2 64 (58*20) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1123 (n : ℕ) : ¬ ((1123:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1123 1122 1 561 20 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1123 1122 (by norm_num) ord_1123) (dvd_of_mpow 561 (58*20) (by norm_num) per_1123)
  exact chk_1123 (n % 20) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1129 : ∀ j, j < 23 → mpow 1129 2 64 ((mpow 564 2 64 (58*j+26)+2)%564) ≠ 1126 := by decide

set_option maxRecDepth 100000 in
theorem ord_1129 : mpow 1129 2 64 564 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1129 : mpow 141 2 64 (58*23) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1129 (n : ℕ) : ¬ ((1129:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1129 564 2 141 23 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1129 564 (by norm_num) ord_1129) (dvd_of_mpow 141 (58*23) (by norm_num) per_1129)
  exact chk_1129 (n % 23) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1151 : ∀ j, j < 110 → mpow 1151 2 64 ((mpow 575 2 64 (58*j+26)+2)%575) ≠ 1148 := by decide

set_option maxRecDepth 100000 in
theorem ord_1151 : mpow 1151 2 64 575 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1151 : mpow 575 2 64 (58*110) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1151 (n : ℕ) : ¬ ((1151:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1151 575 0 575 110 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1151 575 (by norm_num) ord_1151) (dvd_of_mpow 575 (58*110) (by norm_num) per_1151)
  exact chk_1151 (n % 110) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1153 : ∀ j, j < 3 → mpow 1153 2 64 ((mpow 288 2 64 (58*j+26)+2)%288) ≠ 1150 := by decide

set_option maxRecDepth 100000 in
theorem ord_1153 : mpow 1153 2 64 288 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1153 : mpow 9 2 64 (58*3) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1153 (n : ℕ) : ¬ ((1153:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1153 288 5 9 3 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1153 288 (by norm_num) ord_1153) (dvd_of_mpow 9 (58*3) (by norm_num) per_1153)
  exact chk_1153 (n % 3) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1163 : ∀ j, j < 41 → mpow 1163 2 64 ((mpow 166 2 64 (58*j+26)+2)%166) ≠ 1160 := by decide

set_option maxRecDepth 100000 in
theorem ord_1163 : mpow 1163 2 64 166 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1163 : mpow 83 2 64 (58*41) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1163 (n : ℕ) : ¬ ((1163:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1163 166 1 83 41 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1163 166 (by norm_num) ord_1163) (dvd_of_mpow 83 (58*41) (by norm_num) per_1163)
  exact chk_1163 (n % 41) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1171 : ∀ j, j < 6 → mpow 1171 2 64 ((mpow 1170 2 64 (58*j+26)+2)%1170) ≠ 1168 := by decide

set_option maxRecDepth 100000 in
theorem ord_1171 : mpow 1171 2 64 1170 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1171 : mpow 585 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1171 (n : ℕ) : ¬ ((1171:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1171 1170 1 585 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1171 1170 (by norm_num) ord_1171) (dvd_of_mpow 585 (58*6) (by norm_num) per_1171)
  exact chk_1171 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1181 : ∀ j, j < 1 → mpow 1181 2 64 ((mpow 236 2 64 (58*j+26)+2)%236) ≠ 1178 := by decide

set_option maxRecDepth 100000 in
theorem ord_1181 : mpow 1181 2 64 236 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1181 : mpow 59 2 64 (58*1) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1181 (n : ℕ) : ¬ ((1181:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1181 236 2 59 1 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1181 236 (by norm_num) ord_1181) (dvd_of_mpow 59 (58*1) (by norm_num) per_1181)
  exact chk_1181 (n % 1) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1187 : ∀ j, j < 74 → mpow 1187 2 64 ((mpow 1186 2 64 (58*j+26)+2)%1186) ≠ 1184 := by decide

set_option maxRecDepth 100000 in
theorem ord_1187 : mpow 1187 2 64 1186 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1187 : mpow 593 2 64 (58*74) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1187 (n : ℕ) : ¬ ((1187:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1187 1186 1 593 74 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1187 1186 (by norm_num) ord_1187) (dvd_of_mpow 593 (58*74) (by norm_num) per_1187)
  exact chk_1187 (n % 74) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1193 : ∀ j, j < 74 → mpow 1193 2 64 ((mpow 298 2 64 (58*j+26)+2)%298) ≠ 1190 := by decide

set_option maxRecDepth 100000 in
theorem ord_1193 : mpow 1193 2 64 298 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1193 : mpow 149 2 64 (58*74) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1193 (n : ℕ) : ¬ ((1193:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1193 298 1 149 74 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1193 298 (by norm_num) ord_1193) (dvd_of_mpow 149 (58*74) (by norm_num) per_1193)
  exact chk_1193 (n % 74) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1201 : ∀ j, j < 10 → mpow 1201 2 64 ((mpow 300 2 64 (58*j+26)+2)%300) ≠ 1198 := by decide

set_option maxRecDepth 100000 in
theorem ord_1201 : mpow 1201 2 64 300 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1201 : mpow 75 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1201 (n : ℕ) : ¬ ((1201:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1201 300 2 75 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1201 300 (by norm_num) ord_1201) (dvd_of_mpow 75 (58*10) (by norm_num) per_1201)
  exact chk_1201 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1213 : ∀ j, j < 50 → mpow 1213 2 64 ((mpow 1212 2 64 (58*j+26)+2)%1212) ≠ 1210 := by decide

set_option maxRecDepth 100000 in
theorem ord_1213 : mpow 1213 2 64 1212 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1213 : mpow 303 2 64 (58*50) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1213 (n : ℕ) : ¬ ((1213:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1213 1212 2 303 50 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1213 1212 (by norm_num) ord_1213) (dvd_of_mpow 303 (58*50) (by norm_num) per_1213)
  exact chk_1213 (n % 50) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1217 : ∀ j, j < 9 → mpow 1217 2 64 ((mpow 152 2 64 (58*j+26)+2)%152) ≠ 1214 := by decide

set_option maxRecDepth 100000 in
theorem ord_1217 : mpow 1217 2 64 152 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1217 : mpow 19 2 64 (58*9) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1217 (n : ℕ) : ¬ ((1217:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1217 152 3 19 9 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1217 152 (by norm_num) ord_1217) (dvd_of_mpow 19 (58*9) (by norm_num) per_1217)
  exact chk_1217 (n % 9) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1223 : ∀ j, j < 138 → mpow 1223 2 64 ((mpow 611 2 64 (58*j+26)+2)%611) ≠ 1220 := by decide

set_option maxRecDepth 100000 in
theorem ord_1223 : mpow 1223 2 64 611 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1223 : mpow 611 2 64 (58*138) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1223 (n : ℕ) : ¬ ((1223:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1223 611 0 611 138 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1223 611 (by norm_num) ord_1223) (dvd_of_mpow 611 (58*138) (by norm_num) per_1223)
  exact chk_1223 (n % 138) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1229 : ∀ j, j < 51 → mpow 1229 2 64 ((mpow 1228 2 64 (58*j+26)+2)%1228) ≠ 1226 := by decide

set_option maxRecDepth 100000 in
theorem ord_1229 : mpow 1229 2 64 1228 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1229 : mpow 307 2 64 (58*51) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1229 (n : ℕ) : ¬ ((1229:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1229 1228 2 307 51 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1229 1228 (by norm_num) ord_1229) (dvd_of_mpow 307 (58*51) (by norm_num) per_1229)
  exact chk_1229 (n % 51) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1231 : ∀ j, j < 10 → mpow 1231 2 64 ((mpow 615 2 64 (58*j+26)+2)%615) ≠ 1228 := by decide

set_option maxRecDepth 100000 in
theorem ord_1231 : mpow 1231 2 64 615 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1231 : mpow 615 2 64 (58*10) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1231 (n : ℕ) : ¬ ((1231:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1231 615 0 615 10 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1231 615 (by norm_num) ord_1231) (dvd_of_mpow 615 (58*10) (by norm_num) per_1231)
  exact chk_1231 (n % 10) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1237 : ∀ j, j < 51 → mpow 1237 2 64 ((mpow 1236 2 64 (58*j+26)+2)%1236) ≠ 1234 := by decide

set_option maxRecDepth 100000 in
theorem ord_1237 : mpow 1237 2 64 1236 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1237 : mpow 309 2 64 (58*51) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1237 (n : ℕ) : ¬ ((1237:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1237 1236 2 309 51 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1237 1236 (by norm_num) ord_1237) (dvd_of_mpow 309 (58*51) (by norm_num) per_1237)
  exact chk_1237 (n % 51) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1249 : ∀ j, j < 6 → mpow 1249 2 64 ((mpow 156 2 64 (58*j+26)+2)%156) ≠ 1246 := by decide

set_option maxRecDepth 100000 in
theorem ord_1249 : mpow 1249 2 64 156 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1249 : mpow 39 2 64 (58*6) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1249 (n : ℕ) : ¬ ((1249:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1249 156 2 39 6 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1249 156 (by norm_num) ord_1249) (dvd_of_mpow 39 (58*6) (by norm_num) per_1249)
  exact chk_1249 (n % 6) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1259 : ∀ j, j < 36 → mpow 1259 2 64 ((mpow 1258 2 64 (58*j+26)+2)%1258) ≠ 1256 := by decide

set_option maxRecDepth 100000 in
theorem ord_1259 : mpow 1259 2 64 1258 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1259 : mpow 629 2 64 (58*36) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1259 (n : ℕ) : ¬ ((1259:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1259 1258 1 629 36 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1259 1258 (by norm_num) ord_1259) (dvd_of_mpow 629 (58*36) (by norm_num) per_1259)
  exact chk_1259 (n % 36) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1277 : ∀ j, j < 70 → mpow 1277 2 64 ((mpow 1276 2 64 (58*j+26)+2)%1276) ≠ 1274 := by decide

set_option maxRecDepth 100000 in
theorem ord_1277 : mpow 1277 2 64 1276 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1277 : mpow 319 2 64 (58*70) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1277 (n : ℕ) : ¬ ((1277:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1277 1276 2 319 70 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1277 1276 (by norm_num) ord_1277) (dvd_of_mpow 319 (58*70) (by norm_num) per_1277)
  exact chk_1277 (n % 70) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1279 : ∀ j, j < 105 → mpow 1279 2 64 ((mpow 639 2 64 (58*j+26)+2)%639) ≠ 1276 := by decide

set_option maxRecDepth 100000 in
theorem ord_1279 : mpow 1279 2 64 639 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1279 : mpow 639 2 64 (58*105) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1279 (n : ℕ) : ¬ ((1279:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1279 639 0 639 105 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1279 639 (by norm_num) ord_1279) (dvd_of_mpow 639 (58*105) (by norm_num) per_1279)
  exact chk_1279 (n % 105) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1283 : ∀ j, j < 32 → mpow 1283 2 64 ((mpow 1282 2 64 (58*j+26)+2)%1282) ≠ 1280 := by decide

set_option maxRecDepth 100000 in
theorem ord_1283 : mpow 1283 2 64 1282 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1283 : mpow 641 2 64 (58*32) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1283 (n : ℕ) : ¬ ((1283:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1283 1282 1 641 32 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1283 1282 (by norm_num) ord_1283) (dvd_of_mpow 641 (58*32) (by norm_num) per_1283)
  exact chk_1283 (n % 32) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1289 : ∀ j, j < 33 → mpow 1289 2 64 ((mpow 161 2 64 (58*j+26)+2)%161) ≠ 1286 := by decide

set_option maxRecDepth 100000 in
theorem ord_1289 : mpow 1289 2 64 161 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1289 : mpow 161 2 64 (58*33) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1289 (n : ℕ) : ¬ ((1289:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1289 161 0 161 33 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1289 161 (by norm_num) ord_1289) (dvd_of_mpow 161 (58*33) (by norm_num) per_1289)
  exact chk_1289 (n % 33) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1291 : ∀ j, j < 14 → mpow 1291 2 64 ((mpow 1290 2 64 (58*j+26)+2)%1290) ≠ 1288 := by decide

set_option maxRecDepth 100000 in
theorem ord_1291 : mpow 1291 2 64 1290 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1291 : mpow 645 2 64 (58*14) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1291 (n : ℕ) : ¬ ((1291:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1291 1290 1 645 14 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1291 1290 (by norm_num) ord_1291) (dvd_of_mpow 645 (58*14) (by norm_num) per_1291)
  exact chk_1291 (n % 14) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1297 : ∀ j, j < 27 → mpow 1297 2 64 ((mpow 648 2 64 (58*j+26)+2)%648) ≠ 1294 := by decide

set_option maxRecDepth 100000 in
theorem ord_1297 : mpow 1297 2 64 648 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1297 : mpow 81 2 64 (58*27) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1297 (n : ℕ) : ¬ ((1297:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1297 648 3 81 27 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1297 648 (by norm_num) ord_1297) (dvd_of_mpow 81 (58*27) (by norm_num) per_1297)
  exact chk_1297 (n % 27) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1301 : ∀ j, j < 30 → mpow 1301 2 64 ((mpow 1300 2 64 (58*j+26)+2)%1300) ≠ 1298 := by decide

set_option maxRecDepth 100000 in
theorem ord_1301 : mpow 1301 2 64 1300 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1301 : mpow 325 2 64 (58*30) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1301 (n : ℕ) : ¬ ((1301:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1301 1300 2 325 30 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1301 1300 (by norm_num) ord_1301) (dvd_of_mpow 325 (58*30) (by norm_num) per_1301)
  exact chk_1301 (n % 30) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1303 : ∀ j, j < 15 → mpow 1303 2 64 ((mpow 651 2 64 (58*j+26)+2)%651) ≠ 1300 := by decide

set_option maxRecDepth 100000 in
theorem ord_1303 : mpow 1303 2 64 651 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1303 : mpow 651 2 64 (58*15) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1303 (n : ℕ) : ¬ ((1303:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1303 651 0 651 15 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1303 651 (by norm_num) ord_1303) (dvd_of_mpow 651 (58*15) (by norm_num) per_1303)
  exact chk_1303 (n % 15) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1307 : ∀ j, j < 326 → mpow 1307 2 64 ((mpow 1306 2 64 (58*j+26)+2)%1306) ≠ 1304 := by decide

set_option maxRecDepth 100000 in
theorem ord_1307 : mpow 1307 2 64 1306 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1307 : mpow 653 2 64 (58*326) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1307 (n : ℕ) : ¬ ((1307:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1307 1306 1 653 326 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1307 1306 (by norm_num) ord_1307) (dvd_of_mpow 653 (58*326) (by norm_num) per_1307)
  exact chk_1307 (n % 326) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1319 : ∀ j, j < 329 → mpow 1319 2 64 ((mpow 659 2 64 (58*j+26)+2)%659) ≠ 1316 := by decide

set_option maxRecDepth 100000 in
theorem ord_1319 : mpow 1319 2 64 659 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1319 : mpow 659 2 64 (58*329) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1319 (n : ℕ) : ¬ ((1319:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1319 659 0 659 329 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1319 659 (by norm_num) ord_1319) (dvd_of_mpow 659 (58*329) (by norm_num) per_1319)
  exact chk_1319 (n % 329) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1321 : ∀ j, j < 2 → mpow 1321 2 64 ((mpow 60 2 64 (58*j+26)+2)%60) ≠ 1318 := by decide

set_option maxRecDepth 100000 in
theorem ord_1321 : mpow 1321 2 64 60 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1321 : mpow 15 2 64 (58*2) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1321 (n : ℕ) : ¬ ((1321:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1321 60 2 15 2 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1321 60 (by norm_num) ord_1321) (dvd_of_mpow 15 (58*2) (by norm_num) per_1321)
  exact chk_1321 (n % 2) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1327 : ∀ j, j < 12 → mpow 1327 2 64 ((mpow 221 2 64 (58*j+26)+2)%221) ≠ 1324 := by decide

set_option maxRecDepth 100000 in
theorem ord_1327 : mpow 1327 2 64 221 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1327 : mpow 221 2 64 (58*12) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1327 (n : ℕ) : ¬ ((1327:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1327 221 0 221 12 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1327 221 (by norm_num) ord_1327) (dvd_of_mpow 221 (58*12) (by norm_num) per_1327)
  exact chk_1327 (n % 12) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1361 : ∀ j, j < 4 → mpow 1361 2 64 ((mpow 680 2 64 (58*j+26)+2)%680) ≠ 1358 := by decide

set_option maxRecDepth 100000 in
theorem ord_1361 : mpow 1361 2 64 680 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1361 : mpow 85 2 64 (58*4) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1361 (n : ℕ) : ¬ ((1361:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1361 680 3 85 4 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1361 680 (by norm_num) ord_1361) (dvd_of_mpow 85 (58*4) (by norm_num) per_1361)
  exact chk_1361 (n % 4) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1367 : ∀ j, j < 11 → mpow 1367 2 64 ((mpow 683 2 64 (58*j+26)+2)%683) ≠ 1364 := by decide

set_option maxRecDepth 100000 in
theorem ord_1367 : mpow 1367 2 64 683 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1367 : mpow 683 2 64 (58*11) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1367 (n : ℕ) : ¬ ((1367:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1367 683 0 683 11 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1367 683 (by norm_num) ord_1367) (dvd_of_mpow 683 (58*11) (by norm_num) per_1367)
  exact chk_1367 (n % 11) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1373 : ∀ j, j < 147 → mpow 1373 2 64 ((mpow 1372 2 64 (58*j+26)+2)%1372) ≠ 1370 := by decide

set_option maxRecDepth 100000 in
theorem ord_1373 : mpow 1373 2 64 1372 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1373 : mpow 343 2 64 (58*147) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1373 (n : ℕ) : ¬ ((1373:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1373 1372 2 343 147 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1373 1372 (by norm_num) ord_1373) (dvd_of_mpow 343 (58*147) (by norm_num) per_1373)
  exact chk_1373 (n % 147) (Nat.mod_lt _ (by norm_num))

set_option maxRecDepth 100000 in
theorem chk_1381 : ∀ j, j < 22 → mpow 1381 2 64 ((mpow 1380 2 64 (58*j+26)+2)%1380) ≠ 1378 := by decide

set_option maxRecDepth 100000 in
theorem ord_1381 : mpow 1381 2 64 1380 = 1 := by decide

set_option maxRecDepth 100000 in
theorem per_1381 : mpow 345 2 64 (58*22) = 1 := by decide

set_option maxRecDepth 100000 in
theorem ndp_1381 (n : ℕ) : ¬ ((1381:ℕ) ∣ 2^(2^(58*n+26)+2)+3) := by
  apply master 1381 1380 2 345 22 n (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide) (mod_of_mpow 1381 1380 (by norm_num) ord_1381) (dvd_of_mpow 345 (58*22) (by norm_num) per_1381)
  exact chk_1381 (n % 22) (Nat.mod_lt _ (by norm_num))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c0 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 2 ≤ q) (hhi : q < 34) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_2 n hqd
    | exact ndp_3 n hqd
    | exact ndp_5 n hqd
    | exact ndp_7 n hqd
    | exact ndp_11 n hqd
    | exact ndp_13 n hqd
    | exact ndp_17 n hqd
    | exact ndp_19 n hqd
    | exact ndp_23 n hqd
    | exact ndp_29 n hqd
    | exact ndp_31 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c1 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 34 ≤ q) (hhi : q < 66) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_37 n hqd
    | exact ndp_41 n hqd
    | exact ndp_43 n hqd
    | exact ndp_47 n hqd
    | exact ndp_53 n hqd
    | exact ndp_59 n hqd
    | exact ndp_61 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c2 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 66 ≤ q) (hhi : q < 98) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_67 n hr5 hqd
    | exact ndp_71 n hqd
    | exact ndp_73 n hqd
    | exact ndp_79 n hqd
    | exact ndp_83 n hqd
    | exact ndp_89 n hqd
    | exact ndp_97 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c3 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 98 ≤ q) (hhi : q < 130) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_101 n hqd
    | exact ndp_103 n hqd
    | exact ndp_107 n hqd
    | exact ndp_109 n hqd
    | exact ndp_113 n hqd
    | exact ndp_127 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c4 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 130 ≤ q) (hhi : q < 162) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_131 n hqd
    | exact ndp_137 n hqd
    | exact ndp_139 n hqd
    | exact ndp_149 n hqd
    | exact ndp_151 n hqd
    | exact ndp_157 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c5 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 162 ≤ q) (hhi : q < 194) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_163 n hqd
    | exact ndp_167 n hqd
    | exact ndp_173 n hqd
    | exact ndp_179 n hqd
    | exact ndp_181 n hqd
    | exact ndp_191 n hqd
    | exact ndp_193 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c6 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 194 ≤ q) (hhi : q < 226) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_197 n hqd
    | exact ndp_199 n hqd
    | exact ndp_211 n hqd
    | exact ndp_223 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c7 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 226 ≤ q) (hhi : q < 258) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_227 n hqd
    | exact ndp_229 n hqd
    | exact ndp_233 n hqd
    | exact ndp_239 n hqd
    | exact ndp_241 n hqd
    | exact ndp_251 n hqd
    | exact ndp_257 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c8 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 258 ≤ q) (hhi : q < 290) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_263 n hqd
    | exact ndp_269 n hqd
    | exact ndp_271 n hr18 hqd
    | exact ndp_277 n hqd
    | exact ndp_281 n hqd
    | exact ndp_283 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c9 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 290 ≤ q) (hhi : q < 322) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_293 n hqd
    | exact ndp_307 n hqd
    | exact ndp_311 n hqd
    | exact ndp_313 n hqd
    | exact ndp_317 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c10 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 322 ≤ q) (hhi : q < 354) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_331 n hqd
    | exact ndp_337 n hqd
    | exact ndp_347 n hqd
    | exact ndp_349 n hqd
    | exact ndp_353 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c11 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 354 ≤ q) (hhi : q < 386) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_359 n hqd
    | exact ndp_367 n hqd
    | exact ndp_373 n hqd
    | exact ndp_379 n hqd
    | exact ndp_383 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c12 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 386 ≤ q) (hhi : q < 418) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_389 n hqd
    | exact ndp_397 n hqd
    | exact ndp_401 n hqd
    | exact ndp_409 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c13 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 418 ≤ q) (hhi : q < 450) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_419 n hqd
    | exact ndp_421 n hqd
    | exact ndp_431 n hqd
    | exact ndp_433 n hqd
    | exact ndp_439 n hqd
    | exact ndp_443 n hqd
    | exact ndp_449 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c14 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 450 ≤ q) (hhi : q < 482) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_457 n hqd
    | exact ndp_461 n hqd
    | exact ndp_463 n hqd
    | exact ndp_467 n hqd
    | exact ndp_479 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c15 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 482 ≤ q) (hhi : q < 514) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_487 n hqd
    | exact ndp_491 n hqd
    | exact ndp_499 n hqd
    | exact ndp_503 n hqd
    | exact ndp_509 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c16 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 514 ≤ q) (hhi : q < 546) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_521 n hqd
    | exact ndp_523 n hr42 hqd
    | exact ndp_541 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c17 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 546 ≤ q) (hhi : q < 578) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_547 n hqd
    | exact ndp_557 n hqd
    | exact ndp_563 n hqd
    | exact ndp_569 n hqd
    | exact ndp_571 n hqd
    | exact ndp_577 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c18 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 578 ≤ q) (hhi : q < 610) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_587 n hqd
    | exact ndp_593 n hqd
    | exact ndp_599 n hqd
    | exact ndp_601 n hqd
    | exact ndp_607 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c19 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 610 ≤ q) (hhi : q < 642) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_613 n hqd
    | exact ndp_617 n hqd
    | exact ndp_619 n hqd
    | exact ndp_631 n hqd
    | exact ndp_641 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c20 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 642 ≤ q) (hhi : q < 674) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_643 n hqd
    | exact ndp_647 n hqd
    | exact ndp_653 n hqd
    | exact ndp_659 n hqd
    | exact ndp_661 n hqd
    | exact ndp_673 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c21 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 674 ≤ q) (hhi : q < 706) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_677 n hqd
    | exact ndp_683 n hqd
    | exact ndp_691 n hqd
    | exact ndp_701 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c22 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 706 ≤ q) (hhi : q < 738) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_709 n hqd
    | exact ndp_719 n hqd
    | exact ndp_727 n hqd
    | exact ndp_733 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c23 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 738 ≤ q) (hhi : q < 770) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_739 n hqd
    | exact ndp_743 n hqd
    | exact ndp_751 n hqd
    | exact ndp_757 n hqd
    | exact ndp_761 n hqd
    | exact ndp_769 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c24 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 770 ≤ q) (hhi : q < 802) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_773 n hqd
    | exact ndp_787 n hqd
    | exact ndp_797 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c25 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 802 ≤ q) (hhi : q < 834) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_809 n hqd
    | exact ndp_811 n hqd
    | exact ndp_821 n hqd
    | exact ndp_823 n hqd
    | exact ndp_827 n hqd
    | exact ndp_829 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c26 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 834 ≤ q) (hhi : q < 866) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_839 n hqd
    | exact ndp_853 n hqd
    | exact ndp_857 n hqd
    | exact ndp_859 n hqd
    | exact ndp_863 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c27 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 866 ≤ q) (hhi : q < 898) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_877 n hqd
    | exact ndp_881 n hqd
    | exact ndp_883 n hqd
    | exact ndp_887 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c28 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 898 ≤ q) (hhi : q < 930) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_907 n hqd
    | exact ndp_911 n hqd
    | exact ndp_919 n hqd
    | exact ndp_929 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c29 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 930 ≤ q) (hhi : q < 962) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_937 n hqd
    | exact ndp_941 n hqd
    | exact ndp_947 n hqd
    | exact ndp_953 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c30 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 962 ≤ q) (hhi : q < 994) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_967 n hqd
    | exact ndp_971 n hqd
    | exact ndp_977 n hqd
    | exact ndp_983 n hqd
    | exact ndp_991 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c31 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 994 ≤ q) (hhi : q < 1026) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_997 n hqd
    | exact ndp_1009 n hqd
    | exact ndp_1013 n hqd
    | exact ndp_1019 n hqd
    | exact ndp_1021 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c32 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1026 ≤ q) (hhi : q < 1058) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1031 n hqd
    | exact ndp_1033 n hqd
    | exact ndp_1039 n hqd
    | exact ndp_1049 n hqd
    | exact ndp_1051 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c33 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1058 ≤ q) (hhi : q < 1090) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1061 n hqd
    | exact ndp_1063 n hqd
    | exact ndp_1069 n hqd
    | exact ndp_1087 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c34 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1090 ≤ q) (hhi : q < 1122) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1091 n hqd
    | exact ndp_1093 n hqd
    | exact ndp_1097 n hqd
    | exact ndp_1103 n hqd
    | exact ndp_1109 n hqd
    | exact ndp_1117 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c35 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1122 ≤ q) (hhi : q < 1154) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1123 n hqd
    | exact ndp_1129 n hqd
    | exact ndp_1151 n hqd
    | exact ndp_1153 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c36 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1154 ≤ q) (hhi : q < 1186) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1163 n hqd
    | exact ndp_1171 n hqd
    | exact ndp_1181 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c37 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1186 ≤ q) (hhi : q < 1218) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1187 n hqd
    | exact ndp_1193 n hqd
    | exact ndp_1201 n hqd
    | exact ndp_1213 n hqd
    | exact ndp_1217 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c38 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1218 ≤ q) (hhi : q < 1250) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1223 n hqd
    | exact ndp_1229 n hqd
    | exact ndp_1231 n hqd
    | exact ndp_1237 n hqd
    | exact ndp_1249 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c39 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1250 ≤ q) (hhi : q < 1282) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1259 n hqd
    | exact ndp_1277 n hqd
    | exact ndp_1279 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c40 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1282 ≤ q) (hhi : q < 1314) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1283 n hqd
    | exact ndp_1289 n hqd
    | exact ndp_1291 n hqd
    | exact ndp_1297 n hqd
    | exact ndp_1301 n hqd
    | exact ndp_1303 n hqd
    | exact ndp_1307 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c41 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1314 ≤ q) (hhi : q < 1346) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1319 n hqd
    | exact ndp_1321 n hqd
    | exact ndp_1327 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c42 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1346 ≤ q) (hhi : q < 1378) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1361 n hqd
    | exact ndp_1367 n hqd
    | exact ndp_1373 n hqd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem no_small_c43 (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3)
    (hlo : 1378 ≤ q) (hhi : q < 1399) : False := by
  interval_cases q <;>
    first
    | exact absurd hq (by decide)
    | exact ndp_1381 n hqd

set_option maxHeartbeats 1000000 in
theorem no_small (n : ℕ) (hr5 : n % 5 ≠ 2) (hr18 : n % 18 ≠ 11) (hr42 : n % 42 ≠ 26)
    (q : ℕ) (hq : Nat.Prime q) (hqd : q ∣ 2^(2^(58*n+26)+2)+3) : 1399 ≤ q := by
  by_contra hlt
  push_neg at hlt
  have hb0 : 2 ≤ q := hq.two_le
  rcases lt_or_ge q 34 with h0 | hg0
  · exact no_small_c0 n hr5 hr18 hr42 q hq hqd hb0 h0
  rcases lt_or_ge q 66 with h1 | hg1
  · exact no_small_c1 n hr5 hr18 hr42 q hq hqd hg0 h1
  rcases lt_or_ge q 98 with h2 | hg2
  · exact no_small_c2 n hr5 hr18 hr42 q hq hqd hg1 h2
  rcases lt_or_ge q 130 with h3 | hg3
  · exact no_small_c3 n hr5 hr18 hr42 q hq hqd hg2 h3
  rcases lt_or_ge q 162 with h4 | hg4
  · exact no_small_c4 n hr5 hr18 hr42 q hq hqd hg3 h4
  rcases lt_or_ge q 194 with h5 | hg5
  · exact no_small_c5 n hr5 hr18 hr42 q hq hqd hg4 h5
  rcases lt_or_ge q 226 with h6 | hg6
  · exact no_small_c6 n hr5 hr18 hr42 q hq hqd hg5 h6
  rcases lt_or_ge q 258 with h7 | hg7
  · exact no_small_c7 n hr5 hr18 hr42 q hq hqd hg6 h7
  rcases lt_or_ge q 290 with h8 | hg8
  · exact no_small_c8 n hr5 hr18 hr42 q hq hqd hg7 h8
  rcases lt_or_ge q 322 with h9 | hg9
  · exact no_small_c9 n hr5 hr18 hr42 q hq hqd hg8 h9
  rcases lt_or_ge q 354 with h10 | hg10
  · exact no_small_c10 n hr5 hr18 hr42 q hq hqd hg9 h10
  rcases lt_or_ge q 386 with h11 | hg11
  · exact no_small_c11 n hr5 hr18 hr42 q hq hqd hg10 h11
  rcases lt_or_ge q 418 with h12 | hg12
  · exact no_small_c12 n hr5 hr18 hr42 q hq hqd hg11 h12
  rcases lt_or_ge q 450 with h13 | hg13
  · exact no_small_c13 n hr5 hr18 hr42 q hq hqd hg12 h13
  rcases lt_or_ge q 482 with h14 | hg14
  · exact no_small_c14 n hr5 hr18 hr42 q hq hqd hg13 h14
  rcases lt_or_ge q 514 with h15 | hg15
  · exact no_small_c15 n hr5 hr18 hr42 q hq hqd hg14 h15
  rcases lt_or_ge q 546 with h16 | hg16
  · exact no_small_c16 n hr5 hr18 hr42 q hq hqd hg15 h16
  rcases lt_or_ge q 578 with h17 | hg17
  · exact no_small_c17 n hr5 hr18 hr42 q hq hqd hg16 h17
  rcases lt_or_ge q 610 with h18 | hg18
  · exact no_small_c18 n hr5 hr18 hr42 q hq hqd hg17 h18
  rcases lt_or_ge q 642 with h19 | hg19
  · exact no_small_c19 n hr5 hr18 hr42 q hq hqd hg18 h19
  rcases lt_or_ge q 674 with h20 | hg20
  · exact no_small_c20 n hr5 hr18 hr42 q hq hqd hg19 h20
  rcases lt_or_ge q 706 with h21 | hg21
  · exact no_small_c21 n hr5 hr18 hr42 q hq hqd hg20 h21
  rcases lt_or_ge q 738 with h22 | hg22
  · exact no_small_c22 n hr5 hr18 hr42 q hq hqd hg21 h22
  rcases lt_or_ge q 770 with h23 | hg23
  · exact no_small_c23 n hr5 hr18 hr42 q hq hqd hg22 h23
  rcases lt_or_ge q 802 with h24 | hg24
  · exact no_small_c24 n hr5 hr18 hr42 q hq hqd hg23 h24
  rcases lt_or_ge q 834 with h25 | hg25
  · exact no_small_c25 n hr5 hr18 hr42 q hq hqd hg24 h25
  rcases lt_or_ge q 866 with h26 | hg26
  · exact no_small_c26 n hr5 hr18 hr42 q hq hqd hg25 h26
  rcases lt_or_ge q 898 with h27 | hg27
  · exact no_small_c27 n hr5 hr18 hr42 q hq hqd hg26 h27
  rcases lt_or_ge q 930 with h28 | hg28
  · exact no_small_c28 n hr5 hr18 hr42 q hq hqd hg27 h28
  rcases lt_or_ge q 962 with h29 | hg29
  · exact no_small_c29 n hr5 hr18 hr42 q hq hqd hg28 h29
  rcases lt_or_ge q 994 with h30 | hg30
  · exact no_small_c30 n hr5 hr18 hr42 q hq hqd hg29 h30
  rcases lt_or_ge q 1026 with h31 | hg31
  · exact no_small_c31 n hr5 hr18 hr42 q hq hqd hg30 h31
  rcases lt_or_ge q 1058 with h32 | hg32
  · exact no_small_c32 n hr5 hr18 hr42 q hq hqd hg31 h32
  rcases lt_or_ge q 1090 with h33 | hg33
  · exact no_small_c33 n hr5 hr18 hr42 q hq hqd hg32 h33
  rcases lt_or_ge q 1122 with h34 | hg34
  · exact no_small_c34 n hr5 hr18 hr42 q hq hqd hg33 h34
  rcases lt_or_ge q 1154 with h35 | hg35
  · exact no_small_c35 n hr5 hr18 hr42 q hq hqd hg34 h35
  rcases lt_or_ge q 1186 with h36 | hg36
  · exact no_small_c36 n hr5 hr18 hr42 q hq hqd hg35 h36
  rcases lt_or_ge q 1218 with h37 | hg37
  · exact no_small_c37 n hr5 hr18 hr42 q hq hqd hg36 h37
  rcases lt_or_ge q 1250 with h38 | hg38
  · exact no_small_c38 n hr5 hr18 hr42 q hq hqd hg37 h38
  rcases lt_or_ge q 1282 with h39 | hg39
  · exact no_small_c39 n hr5 hr18 hr42 q hq hqd hg38 h39
  rcases lt_or_ge q 1314 with h40 | hg40
  · exact no_small_c40 n hr5 hr18 hr42 q hq hqd hg39 h40
  rcases lt_or_ge q 1346 with h41 | hg41
  · exact no_small_c41 n hr5 hr18 hr42 q hq hqd hg40 h41
  rcases lt_or_ge q 1378 with h42 | hg42
  · exact no_small_c42 n hr5 hr18 hr42 q hq hqd hg41 h42
  exact no_small_c43 n hr5 hr18 hr42 q hq hqd hg42 hlt


/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

-- Helper definitions for the "covered" conditions based on the index k, where k = 58*n + 26.

/-- An index k is covered by Conjecture 1 if k = 10m + 2 for some m >= 0, predicting a(k)=67. -/
def covered_by_C1 (k : ℕ) : Prop := ∃ m : ℕ, k = 10 * m + 2

/-- An index k is covered by Conjecture 2 if k = 36m + 16 for some m >= 0, and m is not 1 mod 5, predicting a(k)=271. -/
def covered_by_C2 (k : ℕ) : Prop := ∃ m : ℕ, k = 36 * m + 16 ∧ m % 5 ≠ 1

/-- An index k is covered by Conjecture 3 if k = 84m + 22 for some m >= 0, and m is not 0 mod 5, predicting a(k)=523. -/
def covered_by_C3 (k : ℕ) : Prop := ∃ m : ℕ, k = 84 * m + 22 ∧ m % 5 ≠ 0

set_option maxHeartbeats 1000000

/--
A248802 Conjecture 4: a(58n+26) = 1399 for n >= 0 and when it is not covered by Conjectures 1-3.
-/
theorem oeis_248802_conjecture_4 (n : ℕ) :
  (¬ covered_by_C1 (58 * n + 26) ∧
   ¬ covered_by_C2 (58 * n + 26) ∧
   ¬ covered_by_C3 (58 * n + 26)) →
  a (58 * n + 26) = 1399 := by
  rintro ⟨h1, h2, h3⟩
  simp only [covered_by_C1, covered_by_C2, covered_by_C3] at h1 h2 h3
  obtain ⟨hr5, hr18, hr42⟩ := arith n h1 h2 h3
  show (2^(2^(58*n+26)+2)+3).minFac = 1399
  have hdvd : (1399:ℕ) ∣ 2^(2^(58*n+26)+2)+3 := dvd_1399 n
  have hle : (2^(2^(58*n+26)+2)+3).minFac ≤ 1399 := Nat.minFac_le_of_dvd (by norm_num) hdvd
  have hpos : 0 < 2^(2^(58*n+26)+2) := pow_pos (by norm_num) _
  have hne1 : 2^(2^(58*n+26)+2)+3 ≠ 1 := by omega
  have hge : 1399 ≤ (2^(2^(58*n+26)+2)+3).minFac := by
    rcases Nat.le_minFac.mpr (fun p hp hpd => no_small n hr5 hr18 hr42 p hp hpd) with h | h
    · exact absurd h hne1
    · exact h
  omega
