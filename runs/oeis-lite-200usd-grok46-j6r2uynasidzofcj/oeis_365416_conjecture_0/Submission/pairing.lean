import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

open Nat

/-! Pairing proof that `Y^2 = X^n + 2` is impossible for odd `n ≥ 3`. -/

lemma odd_add_one_dvd {x n : ℕ} (hn : Odd n) : x + 1 ∣ x ^ n + 1 :=
  Odd.nat_add_dvd_pow_add_pow hn x 1

lemma geom_mul {x n : ℕ} (hn : Odd n) :
    ((x ^ n + 1) / (x + 1)) * (x + 1) = x ^ n + 1 :=
  Nat.div_mul_cancel (odd_add_one_dvd hn)

lemma odd_pow_sub_one_mod_sq (d : ℤ) : ∀ k : ℕ,
    d ^ 2 ∣ (d - 1) ^ (2 * k + 1) + 1 - ((2 * k + 1 : ℕ) : ℤ) * d
  | 0 => by ring_nf; simp
  | k + 1 => by
    have ih := odd_pow_sub_one_mod_sq d k
    set n : ℕ := 2 * k + 1
    have hnat : 2 * (k + 1) + 1 = n + 2 := by simp [n]; omega
    rw [hnat]; push_cast
    have hn_odd : Odd n := ⟨k, rfl⟩
    have hd_dvd : d ∣ (d - 1) ^ n + 1 := by
      have := hn_odd.add_dvd_pow_add_pow (d - 1) (1 : ℤ)
      simpa using this
    have hdecomp :
        (d - 1) ^ (n + 2) + 1 - ((n : ℤ) + 2) * d =
          d ^ 2 * (d - 1) ^ n
            + ((d - 1) ^ n + 1 - (n : ℤ) * d)
            - 2 * d * ((d - 1) ^ n + 1) := by
      have : (d - 1) ^ (n + 2) = (d - 1) ^ n * (d - 1) ^ 2 := pow_add _ _ _
      have : (d - 1) ^ 2 = d ^ 2 - 2 * d + 1 := by ring
      rw [‹(d - 1) ^ (n + 2) = _›, this]; ring
    have h2 : d ^ 2 ∣ 2 * d * ((d - 1) ^ n + 1) := by
      obtain ⟨t, ht⟩ := hd_dvd
      rw [ht]; refine ⟨2 * t, by ring⟩
    have h1 : d ^ 2 ∣ d ^ 2 * (d - 1) ^ n := dvd_mul_right _ _
    have h3 : d ^ 2 ∣ (d - 1) ^ n + 1 - (n : ℤ) * d := ih
    rw [hdecomp]
    exact dvd_sub (dvd_add h1 h3) h2

lemma odd_pow_sub_one_mod_sq' {d : ℤ} {n : ℕ} (hn : Odd n) :
    d ^ 2 ∣ (d - 1) ^ n + 1 - (n : ℤ) * d := by
  obtain ⟨k, hk⟩ := hn; subst hk; exact odd_pow_sub_one_mod_sq d k

lemma geom_odd_mod {x n : ℕ} (hn : Odd n) :
    (x ^ n + 1) / (x + 1) ≡ n [MOD x + 1] := by
  set d : ℤ := ↑x + 1
  have hd0 : d ≠ 0 := by
    have : (0 : ℤ) < ↑x + 1 := by
      have : 0 < x + 1 := Nat.succ_pos _
      exact_mod_cast this
    exact ne_of_gt this
  have hx : (x : ℤ) = d - 1 := by simp [d]
  have hsq : d ^ 2 ∣ (d - 1) ^ n + 1 - (n : ℤ) * d := odd_pow_sub_one_mod_sq' hn
  have hmul : (x : ℤ) ^ n + 1 = d * ↑((x ^ n + 1) / (x + 1)) := by
    have h := geom_mul (x := x) hn
    have : ((x ^ n + 1 : ℕ) : ℤ) = ↑((x ^ n + 1) / (x + 1)) * ↑(x + 1) := by
      exact_mod_cast h.symm
    simp only [d, Nat.cast_add, Nat.cast_one, Nat.cast_pow] at this ⊢
    linarith
  have hdecomp : (x : ℤ) ^ n + 1 - (n : ℤ) * d =
      d * (↑((x ^ n + 1) / (x + 1)) - (n : ℤ)) := by
    rw [hmul]; ring
  have hdiv : d ∣ ↑((x ^ n + 1) / (x + 1)) - (n : ℤ) := by
    have h := hsq
    rw [← hx] at h
    rw [hdecomp] at h
    have : d * d ∣ d * (↑((x ^ n + 1) / (x + 1)) - (n : ℤ)) := by
      convert h using 1; ring
    exact (mul_dvd_mul_iff_left hd0).mp this
  rw [Nat.modEq_iff_dvd]
  have : d ∣ (n : ℤ) - ↑((x ^ n + 1) / (x + 1)) := by
    simpa [Int.dvd_neg, neg_sub] using hdiv.neg_right
  simpa [d] using this

lemma gcd_succ_geom {x n : ℕ} (hn : Odd n) :
    Nat.gcd (x + 1) ((x ^ n + 1) / (x + 1)) = Nat.gcd (x + 1) n := by
  have hmod := geom_odd_mod (x := x) hn
  apply Nat.dvd_antisymm
  · have hd := Nat.gcd_dvd_left (x + 1) ((x ^ n + 1) / (x + 1))
    have hg := Nat.gcd_dvd_right (x + 1) ((x ^ n + 1) / (x + 1))
    have hn' : Nat.gcd (x + 1) ((x ^ n + 1) / (x + 1)) ∣ n := by
      rw [Nat.modEq_iff_dvd] at hmod
      have hgZ : (Nat.gcd (x + 1) ((x ^ n + 1) / (x + 1)) : ℤ) ∣
          ((x ^ n + 1) / (x + 1) : ℤ) := by exact_mod_cast hg
      have hdZ : (Nat.gcd (x + 1) ((x ^ n + 1) / (x + 1)) : ℤ) ∣ (x + 1 : ℤ) := by
        exact_mod_cast hd
      have habs : (Nat.gcd (x + 1) ((x ^ n + 1) / (x + 1)) : ℤ) ∣
          (n : ℤ) - ((x ^ n + 1) / (x + 1) : ℤ) := hdZ.trans hmod
      have : (Nat.gcd (x + 1) ((x ^ n + 1) / (x + 1)) : ℤ) ∣ (n : ℤ) :=
        (Int.dvd_iff_dvd_of_dvd_sub habs).mpr hgZ
      exact_mod_cast this
    exact Nat.dvd_gcd hd hn'
  · have hd := Nat.gcd_dvd_left (x + 1) n
    have hn' := Nat.gcd_dvd_right (x + 1) n
    have hg : Nat.gcd (x + 1) n ∣ (x ^ n + 1) / (x + 1) := by
      rw [Nat.modEq_iff_dvd] at hmod
      have hdZ : (Nat.gcd (x + 1) n : ℤ) ∣ (x + 1 : ℤ) := by exact_mod_cast hd
      have hnZ : (Nat.gcd (x + 1) n : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn'
      have : (Nat.gcd (x + 1) n : ℤ) ∣
          (n : ℤ) - ((x ^ n + 1) / (x + 1) : ℤ) := hdZ.trans hmod
      have := (Int.dvd_iff_dvd_of_dvd_sub this).mp hnZ
      exact_mod_cast this
    exact Nat.dvd_gcd hd hg

lemma sq_mod_four_ne_two (n : ℕ) : n ^ 2 % 4 ≠ 2 := by
  have : n % 4 < 4 := Nat.mod_lt n (by decide)
  interval_cases n % 4 <;> norm_num

lemma X_odd_of_sq {X Y n : ℕ} (hn : 2 ≤ n) (h : Y ^ 2 = X ^ n + 2) : Odd X := by
  by_contra ho
  have hE : Even X := Nat.not_odd_iff_even.mp ho
  obtain ⟨k, hk⟩ := hE
  have h4 : 4 ∣ X ^ n := by
    have : X ^ 2 = 4 * k ^ 2 := by rw [hk]; ring
    have : 4 ∣ X ^ 2 := ⟨k ^ 2, this⟩
    exact Nat.dvd_trans this (pow_dvd_pow X hn)
  have : Y ^ 2 % 4 = 2 := by
    have : X ^ n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
    have := congrArg (· % 4) h
    simp [Nat.add_mod] at this
    omega
  exact sq_mod_four_ne_two Y this

lemma odd_sq_mod_eight {n : ℕ} (h : Odd n) : n ^ 2 % 8 = 1 := by
  have : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have : n % 2 = 1 := Nat.odd_iff.mp h
    have : n % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]

lemma odd_pow_mod_eight_self {a n : ℕ} (ha : Odd a) (hn : Odd n) :
    a ^ n % 8 = a % 8 := by
  have ha8 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
    have : a % 2 = 1 := Nat.odd_iff.mp ha
    have : a % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  obtain ⟨k, rfl⟩ := hn
  induction k with
  | zero => simp
  | succ k ih =>
    have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [this, pow_add, Nat.mul_mod, ih]
    rcases ha8 with h | h | h | h <;> simp [Nat.pow_mod, h]

lemma X_mod_eight {X Y n : ℕ} (hX : Odd X) (hn : Odd n) (h : Y ^ 2 = X ^ n + 2) :
    X % 8 = 7 := by
  have hY : Odd Y := by
    have hpn : Odd (X ^ n) := Odd.pow hX
    have : Odd (X ^ n + 2) := by rw [Nat.odd_add]; exact iff_of_true hpn even_two
    have : Odd (Y ^ 2) := by rwa [h]
    simpa [Nat.odd_pow_iff (by decide : (2 : ℕ) ≠ 0)] using this
  have hY8 : Y ^ 2 % 8 = 1 := odd_sq_mod_eight hY
  have hpn8 : X ^ n % 8 = X % 8 := odd_pow_mod_eight_self hX hn
  have : (X % 8 + 2) % 8 = 1 := by
    have : (X ^ n + 2) % 8 = 1 := by rw [← h, hY8]
    rwa [Nat.add_mod, hpn8] at this
  have hX8 : X % 8 = 1 ∨ X % 8 = 3 ∨ X % 8 = 5 ∨ X % 8 = 7 := by
    have : X % 2 = 1 := Nat.odd_iff.mp hX
    have : X % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  rcases hX8 with h8 | h8 | h8 | h8 <;> simp [h8] at this ⊢

lemma eight_dvd_succ {X Y n : ℕ} (hX : Odd X) (hn : Odd n) (h : Y ^ 2 = X ^ n + 2) :
    8 ∣ X + 1 :=
  Nat.dvd_iff_mod_eq_zero.mpr (by have := X_mod_eight hX hn h; omega)

lemma Y_odd_of_sq {X Y n : ℕ} (hX : Odd X) (h : Y ^ 2 = X ^ n + 2) : Odd Y := by
  have hpn : Odd (X ^ n) := Odd.pow hX
  have : Odd (X ^ n + 2) := by rw [Nat.odd_add]; exact iff_of_true hpn even_two
  have : Odd (Y ^ 2) := by rwa [h]
  simpa [Nat.odd_pow_iff (by decide : (2 : ℕ) ≠ 0)] using this

lemma Y_ge_two_of_sq {X Y n : ℕ} (hX : 1 ≤ X) (h : Y ^ 2 = X ^ n + 2) : 2 ≤ Y := by
  have : 3 ≤ Y ^ 2 := by
    have : 1 ≤ X ^ n := Nat.one_le_pow n X (by omega)
    omega
  match Y with
  | 0 => simp at this
  | 1 => simp at this
  | Y + 2 => omega

def Phi (X n : ℕ) : ℕ := (X ^ n + 1) / (X + 1)

lemma Phi_mul (X n : ℕ) (hn : Odd n) : Phi X n * (X + 1) = X ^ n + 1 :=
  geom_mul hn

lemma factor_Ym1 {X Y n : ℕ} (hn : Odd n) (h : Y ^ 2 = X ^ n + 2) :
    (Y - 1) * (Y + 1) = (X + 1) * Phi X n := by
  have hY : 1 ≤ Y := by
    have : 2 ≤ Y ^ 2 := by rw [h]; omega
    match Y with
    | 0 => simp at this
    | Y + 1 => omega
  have : Y ^ 2 - 1 = X ^ n + 1 := by omega
  have hfac : Y ^ 2 - 1 = (Y - 1) * (Y + 1) := by
    zify [hY]; ring
  have hPhi := Phi_mul X n hn
  omega

lemma Phi_odd {X n : ℕ} (hX : Odd X) (hn : Odd n) : Odd (Phi X n) := by
  have hmul := Phi_mul X n hn
  have hL : Odd (X ^ n + 1) := by
    have : Even (X ^ n + 1) := by
      have : Odd (X ^ n) := Odd.pow hX
      -- odd + 1 = even
      exact this.add_odd.even
    -- wait we need Phi odd, X+1 even, product = X^n+1 even. Doesn't force Phi odd.
    sorry
  sorry

-- X odd ⇒ X^n odd ⇒ X^n+1 even. X+1 even. Phi = even/even could be odd or even.
-- From even_eb, Phi is odd (geom_odd_odd). We'll prove it simply:
-- X ≡ 7 mod 8, X+1 ≡ 0 mod 8, v2(X^n+1)=v2(X+1) so v2(Phi)=0.

lemma four_mul_A {Y : ℕ} (hY : Odd Y) (hY2 : 2 ≤ Y) :
    (Y - 1) * (Y + 1) = 4 * ((Y - 1) / 2) * ((Y + 1) / 2) := by
  have h1 : Even (Y - 1) := by
    obtain ⟨k, hk⟩ := hY
    have : Y - 1 = 2 * k := by omega
    exact ⟨k, this⟩
  have h2 : Even (Y + 1) := by
    have : (Y + 1) % 2 = 0 := by
      have : Y % 2 = 1 := Nat.odd_iff.mp hY
      omega
    exact Nat.even_iff.mpr this
  have he1 : 2 * ((Y - 1) / 2) = Y - 1 := Nat.mul_div_cancel' (even_iff_two_dvd.mp h1)
  have he2 : 2 * ((Y + 1) / 2) = Y + 1 := Nat.mul_div_cancel' (even_iff_two_dvd.mp h2)
  calc
    (Y - 1) * (Y + 1) = (2 * ((Y - 1) / 2)) * (2 * ((Y + 1) / 2)) := by rw [he1, he2]
    _ = 4 * ((Y - 1) / 2) * ((Y + 1) / 2) := by ring

lemma A_succ {Y : ℕ} (hY : Odd Y) (hY2 : 2 ≤ Y) :
    (Y + 1) / 2 = (Y - 1) / 2 + 1 := by
  have : Y = 2 * ((Y - 1) / 2) + 1 := by
    obtain ⟨k, hk⟩ := hY
    have : Y - 1 = 2 * k := by omega
    have : (Y - 1) / 2 = k := by omega
    omega
  omega

/-- If `gcd(X+1, n) = 1` then `Y^2 = X^n + 2` is impossible for odd `n ≥ 3`. -/
lemma no_sq_pow_add_two_of_coprime {X Y n : ℕ}
    (hn3 : 3 ≤ n) (hnO : Odd n) (hX1 : 1 ≤ X)
    (h : Y ^ 2 = X ^ n + 2)
    (hg : Nat.gcd (X + 1) n = 1) : False := by
  have hn2 : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 3) hn3
  have hXo : Odd X := X_odd_of_sq hn2 h
  have hYo : Odd Y := Y_odd_of_sq hXo h
  have hY2 : 2 ≤ Y := Y_ge_two_of_sq hX1 h
  have h8 : 8 ∣ X + 1 := eight_dvd_succ hXo hnO h
  have hfac := factor_Ym1 hnO h
  have h4 : 4 ∣ X + 1 := dvd_trans (by decide : 4 ∣ 8) h8
  set A := (Y - 1) / 2
  have hAprod : A * (A + 1) = (X + 1) / 4 * Phi X n := by
    have hL : (Y - 1) * (Y + 1) = 4 * A * ((Y + 1) / 2) := four_mul_A hYo hY2
    have hAs : (Y + 1) / 2 = A + 1 := A_succ hYo hY2
    rw [hAs] at hL
    have hR : (X + 1) * Phi X n = 4 * ((X + 1) / 4) * Phi X n := by
      have : 4 * ((X + 1) / 4) = X + 1 := Nat.mul_div_cancel' h4
      rw [this]
    have : 4 * A * (A + 1) = 4 * ((X + 1) / 4 * Phi X n) := by
      have := hfac
      omega
    have hpos : 0 < (4 : ℕ) := by decide
    exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  have hgcdΦ : Nat.gcd (X + 1) (Phi X n) = 1 := by
    rw [gcd_succ_geom hnO, hg]
    rfl
  -- gcd((X+1)/4, Phi) = 1 because Phi is coprime to X+1
  have hcop : Nat.gcd ((X + 1) / 4) (Phi X n) = 1 := by
    have hd : Nat.gcd ((X + 1) / 4) (Phi X n) ∣ Phi X n := Nat.gcd_dvd_right _ _
    have hd' : Nat.gcd ((X + 1) / 4) (Phi X n) ∣ (X + 1) / 4 := Nat.gcd_dvd_left _ _
    have : Nat.gcd ((X + 1) / 4) (Phi X n) ∣ X + 1 := by
      have : (X + 1) / 4 ∣ X + 1 := Nat.div_dvd_of_dvd h4
      exact hd'.trans this
    have : Nat.gcd ((X + 1) / 4) (Phi X n) ∣ Nat.gcd (X + 1) (Phi X n) :=
      Nat.dvd_gcd this hd
    rwa [hgcdΦ, Nat.dvd_one] at this
  have hAcop : Nat.gcd A (A + 1) = 1 := Nat.gcd_succ A
  -- Two coprime factorizations of the same number: {A, A+1} = {(X+1)/4, Phi}
  have hcases : A = (X + 1) / 4 ∨ A = Phi X n := by
    -- A ∣ ((X+1)/4) * Phi and gcd(A, A+1)=1, gcd((X+1)/4, Phi)=1
    -- so A divides one of them, and then equality of products forces the pairing
    have hAdvd : A ∣ ((X + 1) / 4) * Phi X n := ⟨A + 1, hAprod.symm⟩
    have hA1dvd : A + 1 ∣ ((X + 1) / 4) * Phi X n := ⟨A, by rw [mul_comm, hAprod]⟩
    -- Use that if a coprime pair multiplies to a coprime pair, they match
    have : A ∣ (X + 1) / 4 ∨ A ∣ Phi X n :=
      (Nat.Coprime.dvd_mul_right hcop).mp ?_
    wait
    sorry
  sorry
