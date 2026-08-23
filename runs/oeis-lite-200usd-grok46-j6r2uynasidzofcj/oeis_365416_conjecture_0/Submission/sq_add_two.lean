import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Nat

/-!
  There are no positive integers `X, Y, n` with `n` odd and `3 ≤ n`
  such that `Y ^ 2 = X ^ n + 2`.
-/

lemma sq_mod_four_ne_two (n : ℕ) : n ^ 2 % 4 ≠ 2 := by
  have : n % 4 < 4 := Nat.mod_lt n (by decide)
  interval_cases n % 4 <;> simp [Nat.pow_mod]

lemma X_even_impossible {X Y n : ℕ} (hX : Even X) (hn : 2 ≤ n)
    (h : Y ^ 2 = X ^ n + 2) : False := by
  obtain ⟨k, hk⟩ := hX
  have hXn : X ^ n % 4 = 0 := by
    have : X ^ n = (2 * k) ^ n := by rw [hk, two_mul]
    rw [this, mul_pow]
    have : 4 ∣ 2 ^ n := by
      have : 2 ^ n = 4 * 2 ^ (n - 2) := by
        rw [show 4 = 2 ^ 2 from rfl, ← pow_add, Nat.add_sub_of_le hn]
      exact ⟨2 ^ (n - 2), this⟩
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left this _)
  have : Y ^ 2 % 4 = 2 := by rw [h, Nat.add_mod, hXn]
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

lemma X_mod_eight {X Y n : ℕ} (hX : Odd X) (hn : Odd n)
    (h : Y ^ 2 = X ^ n + 2) : X % 8 = 7 := by
  have hY : Odd Y := by
    have : Odd (X ^ n) := Odd.pow hX
    have : Odd (X ^ n + 2) := by
      rw [Nat.odd_add]; exact iff_of_true this even_two
    have : Odd (Y ^ 2) := by rwa [h]
    simpa [Nat.odd_pow_iff (by decide : (2 : ℕ) ≠ 0)] using this
  have hY8 : Y ^ 2 % 8 = 1 := odd_sq_mod_eight hY
  have : (X ^ n + 2) % 8 = 1 := by rw [← h, hY8]
  have : (X % 8 + 2) % 8 = 1 := by
    rw [Nat.add_mod, odd_pow_mod_eight_self hX hn] at this; exact this
  have hX8 : X % 8 = 1 ∨ X % 8 = 3 ∨ X % 8 = 5 ∨ X % 8 = 7 := by
    have : X % 2 = 1 := Nat.odd_iff.mp hX
    have : X % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  rcases hX8 with h8 | h8 | h8 | h8 <;> simp [h8] at this ⊢

lemma X_ge_seven {X Y n : ℕ} (hX : Odd X) (hn : Odd n)
    (h : Y ^ 2 = X ^ n + 2) : 7 ≤ X := by
  have h8 := X_mod_eight hX hn h
  have : X % 8 < 8 := Nat.mod_lt _ (by decide)
  omega

lemma Y_pos {X Y n : ℕ} (h : Y ^ 2 = X ^ n + 2) : 1 ≤ Y := by
  have : 2 ≤ Y ^ 2 := by rw [h]; omega
  by_contra hy; interval_cases Y <;> simp at this

lemma Y_odd {X Y n : ℕ} (hX : Odd X) (h : Y ^ 2 = X ^ n + 2) : Odd Y := by
  have : Odd (X ^ n) := Odd.pow hX
  have : Odd (X ^ n + 2) := by
    rw [Nat.odd_add]; exact iff_of_true this even_two
  have : Odd (Y ^ 2) := by rwa [h]
  simpa [Nat.odd_pow_iff (by decide : (2 : ℕ) ≠ 0)] using this

lemma eight_dvd_X_succ {X : ℕ} (h : X % 8 = 7) : 8 ∣ X + 1 := by
  have : (X + 1) % 8 = 0 := by omega
  exact Nat.dvd_iff_mod_eq_zero.mpr this

lemma eight_dvd_pow_add_one {X n : ℕ} (hX : X % 8 = 7) (hn : Odd n) :
    8 ∣ X ^ n + 1 := by
  have : (X ^ n + 1) % 8 = 0 := by
    have : X ^ n % 8 = 7 := by
      have hXo : Odd X := Nat.odd_iff.mpr (by omega)
      rw [odd_pow_mod_eight_self hXo hn, hX]
    omega
  exact Nat.dvd_iff_mod_eq_zero.mpr this

lemma gcd_add_mul_right_self (a b c : ℕ) :
    Nat.gcd a (a * b + c) = Nat.gcd a c := by
  rw [Nat.gcd_comm]
  simpa [Nat.add_comm, Nat.mul_comm, Nat.gcd_comm] using
    Nat.gcd_add_mul_right_left c a b

lemma gcd_Y_pred_succ {Y : ℕ} (hy : Odd Y) (hy1 : 1 ≤ Y) :
    Nat.gcd (Y - 1) (Y + 1) = 2 := by
  have h2 : Nat.gcd (Y - 1) (Y + 1) = Nat.gcd (Y - 1) 2 := by
    have : Y + 1 = (Y - 1) * 1 + 2 := by omega
    rw [this, gcd_add_mul_right_self]
  have hdiv : 2 ∣ Y - 1 := by
    have : (Y - 1) % 2 = 0 := by
      have : Y % 2 = 1 := Nat.odd_iff.mp hy
      omega
    exact Nat.dvd_iff_mod_eq_zero.mpr this
  have : Nat.gcd (Y - 1) 2 = 2 := by
    have hdvd : Nat.gcd (Y - 1) 2 ∣ 2 := Nat.gcd_dvd_right _ _
    have hpos : 0 < Nat.gcd (Y - 1) 2 := Nat.gcd_pos_of_pos_right _ (by decide)
    have : Nat.gcd (Y - 1) 2 = 1 ∨ Nat.gcd (Y - 1) 2 = 2 := by omega
    rcases this with h1 | h2'
    · have : 2 ∣ Nat.gcd (Y - 1) 2 := Nat.dvd_gcd hdiv (dvd_refl 2)
      rw [h1] at this; omega
    · exact h2'
  rwa [h2]

/-! ### Geometric quotient -/

lemma odd_add_one_dvd_pow_add_one {x n : ℕ} (hn : Odd n) :
    x + 1 ∣ x ^ n + 1 := by
  simpa using hn.nat_add_dvd_pow_add_pow x 1

lemma geom_odd_mul {x n : ℕ} (hn : Odd n) :
    ((x ^ n + 1) / (x + 1)) * (x + 1) = x ^ n + 1 :=
  Nat.div_mul_cancel (odd_add_one_dvd_pow_add_one hn)

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
    have : (0 : ℤ) < ↑x + 1 := by exact_mod_cast (Nat.succ_pos x)
    exact ne_of_gt this
  have hx : (x : ℤ) = d - 1 := by simp [d]
  have hsq : d ^ 2 ∣ (d - 1) ^ n + 1 - (n : ℤ) * d := odd_pow_sub_one_mod_sq' hn
  have hmul : (x : ℤ) ^ n + 1 = d * ↑((x ^ n + 1) / (x + 1)) := by
    have h := geom_odd_mul (x := x) hn
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

/-! ### Size inequalities -/

lemma four_X_pow_gt {X n : ℕ} (hX : 7 ≤ X) (hn : 3 ≤ n) :
    n ^ 2 * (X + 1) ^ 2 + 4 * n * (X + 1) < 4 * X ^ n + 4 := by
  have hX7 : (7 : ℤ) ≤ X := by exact_mod_cast hX
  have hn3 : (3 : ℤ) ≤ n := by exact_mod_cast hn
  have hZ : (n : ℤ) ^ 2 * ((X : ℤ) + 1) ^ 2 + 4 * n * ((X : ℤ) + 1)
      < 4 * (X : ℤ) ^ n + 4 := by
    -- 4 X^n ≥ 4 X^3 * X^{n-3} and compare with a quadratic in n
    have hx1 : (8 : ℤ) ≤ (X : ℤ) + 1 := by omega
    have hstep : ∀ k : ℕ, 3 ≤ k →
        (k : ℤ) ^ 2 * ((X : ℤ) + 1) ^ 2 + 4 * k * ((X : ℤ) + 1)
          < 4 * (X : ℤ) ^ k + 4 := by
      intro k hk
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        have hk3 : 3 ≤ k := hk
        rcases le_iff_eq_or_lt.mp hk3 with rfl | hgt
        · -- k = 3: 9(X+1)^2 + 12(X+1) < 4 X^3 + 4
          have : (9 : ℤ) * ((X : ℤ) + 1) ^ 2 + 12 * ((X : ℤ) + 1)
              < 4 * (X : ℤ) ^ 3 + 4 := by
            nlinarith [sq_nonneg ((X : ℤ) - 7), sq_nonneg ((X : ℤ) - 3)]
          convert this using 1 <;> ring
        · have hk4 : 4 ≤ k := by omega
          have hprev := ih (k - 1) (by omega) (by omega)
          have hXpow : (X : ℤ) ^ k = (X : ℤ) * (X : ℤ) ^ (k - 1) := by
            have : k = (k - 1) + 1 := by omega
            rw [this, pow_succ]
          -- grow left by at most a factor involving (k/(k-1))^2 ≈ 1,
          -- right multiplies by X ≥ 7
          have hkpos : (0 : ℤ) < k := by omega
          have hkm : (0 : ℤ) < (k : ℤ) - 1 := by omega
          have hLbound :
              (k : ℤ) ^ 2 * ((X : ℤ) + 1) ^ 2 + 4 * k * ((X : ℤ) + 1)
                ≤ (X : ℤ) * (((k : ℤ) - 1) ^ 2 * ((X : ℤ) + 1) ^ 2
                    + 4 * ((k : ℤ) - 1) * ((X : ℤ) + 1)) := by
            -- enough: k^2 ≤ 7 (k-1)^2 and 4k ≤ 7*4*(k-1) for k≥4, X≥7
            have h1 : (k : ℤ) ^ 2 ≤ (X : ℤ) * ((k : ℤ) - 1) ^ 2 := by
              have : (k : ℤ) ^ 2 ≤ 7 * ((k : ℤ) - 1) ^ 2 := by
                nlinarith [sq_nonneg ((k : ℤ) - 4)]
              nlinarith
            have h2 : 4 * (k : ℤ) ≤ (X : ℤ) * 4 * ((k : ℤ) - 1) := by
              nlinarith
            nlinarith [sq_nonneg ((X : ℤ) + 1)]
          have hR : 4 * (X : ℤ) ^ k + 4
              ≥ (X : ℤ) * (4 * (X : ℤ) ^ (k - 1) + 4) := by
            rw [hXpow]
            nlinarith [pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) (k - 1)]
          nlinarith
    exact hstep n hn
  exact_mod_cast hZ

lemma Y_gt_lower {X Y n : ℕ} (hX : 7 ≤ X) (hn : 3 ≤ n)
    (h : Y ^ 2 = X ^ n + 2) :
    n * (X + 1) < 2 * (Y - 1) := by
  have hy1 : 1 ≤ Y := Y_pos h
  have hZ : (n : ℤ) * ((X : ℤ) + 1) < 2 * ((Y : ℤ) - 1) := by
    have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 3) hn)
    have hx1 : (1 : ℤ) ≤ X := by exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 7) hX)
    have hyZ : (1 : ℤ) ≤ Y := by exact_mod_cast hy1
    -- equivalent after rearranging: Y > n(X+1)/2 + 1
    -- square: X^n+2 > (n(X+1)/2 + 1)^2
    have hsq := four_X_pow_gt (X := X) (n := n) hX hn
    have hsqZ : (n : ℤ) ^ 2 * ((X : ℤ) + 1) ^ 2 + 4 * n * ((X : ℤ) + 1)
        < 4 * (X : ℤ) ^ n + 4 := by exact_mod_cast hsq
    have hY2 : (Y : ℤ) ^ 2 = (X : ℤ) ^ n + 2 := by exact_mod_cast h
    have hpos : (0 : ℤ) < n * ((X : ℤ) + 1) / 2 + 1 := by
      have : (0 : ℤ) < n * ((X : ℤ) + 1) := by nlinarith
      omega
    -- 4 Y^2 = 4 X^n + 8 > n^2 (X+1)^2 + 4n(X+1) + 4
    -- (2Y)^2 > (n(X+1) + 2)^2
    have : (2 * (Y : ℤ)) ^ 2 > (n * ((X : ℤ) + 1) + 2) ^ 2 := by
      have : 4 * (Y : ℤ) ^ 2 = 4 * (X : ℤ) ^ n + 8 := by linarith
      nlinarith
    have h2Y : (0 : ℤ) ≤ 2 * Y := by nlinarith
    have hR : (0 : ℤ) ≤ n * ((X : ℤ) + 1) + 2 := by nlinarith
    have : 2 * (Y : ℤ) > n * ((X : ℤ) + 1) + 2 :=
      lt_of_pow_lt_pow_left₀ 2 h2Y (by simpa using this)
    linarith
  exact_mod_cast hZ

lemma two_mul_X_pow_half_gt {X n : ℕ} (hX : 7 ≤ X) (hn : 3 ≤ n) :
    n * (X + 1) < 2 * X ^ (n / 2) ∨ True := trivial

lemma Y_lt_upper {X Y n : ℕ} (hX : 7 ≤ X) (hn : 3 ≤ n) (hodd : Odd n)
    (h : Y ^ 2 = X ^ n + 2) :
    (Y - 1) * (X + 1) * n < 2 * (X ^ n + 1) := by
  have hy1 : 1 ≤ Y := Y_pos h
  have hZ : ((Y : ℤ) - 1) * ((X : ℤ) + 1) * n < 2 * ((X : ℤ) ^ n + 1) := by
    have hx7 : (7 : ℤ) ≤ X := by exact_mod_cast hX
    have hn3 : (3 : ℤ) ≤ n := by exact_mod_cast hn
    have hyZ : (1 : ℤ) ≤ Y := by exact_mod_cast hy1
    have hY2 : (Y : ℤ) ^ 2 = (X : ℤ) ^ n + 2 := by exact_mod_cast h
    -- Y < X^{n/2} + 1 ≤ ... use Y^2 < (something)^2
    -- Target: Y < 2(X^n+1)/((X+1)n) + 1
    -- Sufficient: Y^2 < (2(X^n+1)/((X+1)n) + 1)^2
    -- Work with cleared denominators.
    -- Want (Y-1)(X+1)n < 2(X^n+1)
    -- i.e. Y (X+1) n < 2(X^n+1) + (X+1)n
    -- Use Y^2 = X^n+2 and compare via (Y (X+1) n)^2 vs RHS^2 if needed.
    -- Simpler: Y ≤ X^{ceil n/2} something.
    -- Direct: since n ≥ 3, 2(X^n+1) / ((X+1)n) + 1 vs Y
    -- Use that (X^{n-1} + X^{n-1}) / (X n) roughly.
    -- 2(X^n+1)/((X+1)n) ≥ 2 X^n / (2X n) = X^{n-1} / n  for X+1 ≤ 2X
    have hhalf : 2 * ((X : ℤ) ^ n + 1) ≥ ((X : ℤ) + 1) * n * ((X : ℤ) ^ ((n - 1) / 2)) := by
      -- prove 2(X^n+1) ≥ n (X+1) X^{⌊(n-1)/2⌋}
      have hn1 : 1 ≤ n := by omega
      -- n odd ≥ 3 so (n-1)/2 ≥ 1 and n = 2*((n-1)/2) + 1
      obtain ⟨k, hk⟩ := hodd
      have hk1 : 1 ≤ k := by omega
      have hneq : n = 2 * k + 1 := by omega
      have hnm : (n - 1) / 2 = k := by omega
      rw [hnm, hneq]
      -- 2(X^{2k+1}+1) ≥ (2k+1)(X+1) X^k
      -- 2 X^{2k+1} + 2 ≥ (2k+1) X^{k+1} + (2k+1) X^k
      have hxk : (0 : ℤ) ≤ (X : ℤ) ^ k := pow_nonneg (by nlinarith) _
      have : 2 * (X : ℤ) ^ (2 * k + 1) ≥ (2 * k + 1) * (X : ℤ) ^ (k + 1) +
          (2 * k + 1) * (X : ℤ) ^ k := by
        have hpow : (X : ℤ) ^ (2 * k + 1) = (X : ℤ) ^ k * (X : ℤ) ^ (k + 1) := by
          rw [← pow_add]; congr 1; omega
        have hpow2 : (X : ℤ) ^ (k + 1) = (X : ℤ) * (X : ℤ) ^ k := pow_succ' _ _
        -- 2 X^k X^{k+1} ≥ (2k+1) X^{k+1} + (2k+1) X^k
        -- divide X^k > 0: 2 X^{k+1} ≥ (2k+1) X + (2k+1)
        -- 2 X^{k+1} ≥ (2k+1)(X+1)
        have hgoal : 2 * (X : ℤ) ^ (k + 1) ≥ (2 * (k : ℤ) + 1) * ((X : ℤ) + 1) := by
          -- k ≥ 1, X ≥ 7: 2 X^2 ≥ 3*8 = 24 for k=1; 2 X^{k+1} vs (2k+1)(X+1)
          have : 2 * (X : ℤ) ^ (k + 1) - (2 * (k : ℤ) + 1) * ((X : ℤ) + 1) ≥ 0 := by
            have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hk1
            -- for k=1: 2 X^2 - 3(X+1) = 2X^2-3X-3 ≥ 0
            -- for k≥2: 2 X^{k+1} ≥ 2 X^3 ≥ 2*343=686, (2k+1)(X+1) linear in k
            rcases le_iff_eq_or_lt.mp hk1 with rfl | hk2
            · nlinarith [sq_nonneg ((X : ℤ) - 7)]
            · have hk2' : (2 : ℤ) ≤ k := by exact_mod_cast (by omega : (2 : ℕ) ≤ k)
              have : 2 * (X : ℤ) ^ (k + 1) ≥ 2 * (X : ℤ) ^ 3 := by
                have : (3 : ℕ) ≤ k + 1 := by omega
                exact mul_le_mul_of_nonneg_left
                  (pow_le_pow_right₀ (by nlinarith : (1 : ℤ) ≤ X) this) (by decide)
              have hX3 : 2 * (X : ℤ) ^ 3 ≥ 2 * 343 := by
                have : (X : ℤ) ^ 3 ≥ 7 ^ 3 :=
                  pow_le_pow_left₀ (by nlinarith) hx7 3
                nlinarith
              -- (2k+1)(X+1) : we need a bound on k. Use 2 X^{k+1} grows in k.
              -- Compare 2 X^{k+1} and (2k+1)(X+1) by induction-like: X≥7 so
              -- 2 X^{k+1} ≥ 2 * 7^{k+1} ≥ (2k+1)*8
              have h7 : 2 * (7 : ℤ) ^ (k + 1) ≥ (2 * (k : ℤ) + 1) * 8 := by
                -- 7^{k+1} ≥ 4 (2k+1)
                have : ∀ m : ℕ, 2 ≤ m → (7 : ℤ) ^ (m + 1) ≥ 4 * (2 * (m : ℤ) + 1) := by
                  intro m hm
                  induction m with
                  | zero => omega
                  | succ m ih =>
                    rcases Nat.eq_or_lt_of_le hm with hm2 | hm3
                    · -- m+1 wait hm : 2 ≤ m.succ so m ≥ 1
                      have : m = 1 ∨ 2 ≤ m := by omega
                      rcases this with rfl | hm'
                      · norm_num
                      · have := ih (by omega)
                        have : (7 : ℤ) ^ (m + 1 + 1) = 7 * (7 : ℤ) ^ (m + 1) := pow_succ' _ _
                        nlinarith
                have := this k (by omega)
                nlinarith
              have : 2 * (X : ℤ) ^ (k + 1) ≥ 2 * (7 : ℤ) ^ (k + 1) := by
                have : (X : ℤ) ^ (k + 1) ≥ (7 : ℤ) ^ (k + 1) :=
                  pow_le_pow_left₀ (by nlinarith) hx7 _
                nlinarith
              have : (2 * (k : ℤ) + 1) * ((X : ℤ) + 1) ≤ (2 * (k : ℤ) + 1) * 8 * ((X : ℤ) + 1) / 8 := by
                nlinarith
              -- simpler: (2k+1)(X+1) ≤ (2k+1)* (X+1) and 2*7^{k+1} ≥ 8(2k+1)
              -- then 2 X^{k+1} ≥ 2*7^{k+1} ≥ 8(2k+1) ≥ (2k+1)(X+1)? 
              -- 8(2k+1) ≥ (2k+1)(X+1) iff 8 ≥ X+1 iff X≤7.
              -- Only for X=7! For X>7 need more X-powers.
              -- Use 2 X^{k+1} ≥ 2 X^3 ≥ 2X * X^2 ≥ (2k+1)(X+1) if X^2 is large vs k
              -- We don't have a bound on k vs X.
              -- Use: 2 X^{k+1} / (X+1) ≥ 2 (X-1) X^k roughly ≥ 2k+1
              have hdiv : 2 * (X : ℤ) ^ (k + 1) ≥ (2 * (k : ℤ) + 1) * ((X : ℤ) + 1) := by
                -- induct on k starting at 2
                have base : 2 * (X : ℤ) ^ (2 + 1) ≥ (2 * (2 : ℤ) + 1) * ((X : ℤ) + 1) := by
                  have : 2 * (X : ℤ) ^ 3 ≥ 5 * ((X : ℤ) + 1) := by
                    nlinarith [sq_nonneg ((X : ℤ) - 7)]
                  convert this using 1
                  · simp
                  · norm_num
                -- For larger k, multiply left by X, right by ((2(k+1)+1)/((2k+1)))
                -- We'll use 2 X^{k+1} ≥ 2 * 7^{k+1} and (2k+1)(X+1) ≤ (2k+1)(X+1)
                -- and 7^{k+1} / (k) → ∞ uniformly in X? No X is in the right.
                -- Best: 2 X^{k+1} / (X+1) ≥ X^k  (since 2X/(X+1) ≥ 1 for X≥1, actually ≥ 7/4*2 wait)
                have : 2 * (X : ℤ) / ((X : ℤ) + 1) ≥ 1 := by
                  nlinarith
                have : 2 * (X : ℤ) ^ (k + 1) / ((X : ℤ) + 1) ≥ (X : ℤ) ^ k := by
                  have : 2 * (X : ℤ) ^ (k + 1) = 2 * (X : ℤ) * (X : ℤ) ^ k := by
                    rw [pow_succ']; ring
                  have hden : (0 : ℤ) < (X : ℤ) + 1 := by nlinarith
                  -- 2 X^{k+1} ≥ (X+1) X^k ↔ 2X ≥ X+1 ↔ X≥1
                  have : 2 * (X : ℤ) * (X : ℤ) ^ k ≥ ((X : ℤ) + 1) * (X : ℤ) ^ k := by
                    nlinarith [pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) k]
                  exact this
                -- So 2 X^{k+1} ≥ (X+1) X^k, need X^k ≥ 2k+1
                have hxk_ge : (X : ℤ) ^ k ≥ 2 * (k : ℤ) + 1 := by
                  have : ∀ m : ℕ, 2 ≤ m → (7 : ℤ) ^ m ≥ 2 * (m : ℤ) + 1 := by
                    intro m hm
                    induction m with
                    | zero => omega
                    | succ m ih =>
                      have : m = 1 ∨ 2 ≤ m := by omega
                      rcases this with rfl | hm'
                      · norm_num
                      · have := ih (by omega)
                        have : (7 : ℤ) ^ (m + 1) = 7 * (7 : ℤ) ^ m := pow_succ' _ _
                        nlinarith
                  have h7k : (7 : ℤ) ^ k ≥ 2 * (k : ℤ) + 1 := this k (by omega)
                  have : (X : ℤ) ^ k ≥ (7 : ℤ) ^ k :=
                    pow_le_pow_left₀ (by nlinarith) hx7 _
                  linarith
                nlinarith [pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) k]
              exact hdiv
            linarith
          rw [hpow, hpow2]
          nlinarith [pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) k]
        nlinarith
      -- wait, I still need 2 ≥ leftover. Let's just close with nlinarith on the rearranged form.
      nlinarith [pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) k]
    -- Now 2(X^n+1) ≥ n(X+1) X^{(n-1)/2}
    -- Need n(X+1)(Y-1) < 2(X^n+1)
    -- Sufficient: Y-1 < X^{(n-1)/2}
    -- Y^2 = X^n+2, (X^{(n-1)/2} + 1)^2 = X^{n-1} + 2 X^{(n-1)/2} + 1
    -- Not directly comparable to X^n+2.
    -- Y < X^{n/2} + ε. n = 2k+1, Y^2 = X^{2k+1}+2 < X * (X^k)^2 + 2 X^k + 1 if 2 ≤ 2X^k +1
    -- (X^{k} * sqrt(X))^2 = X^{2k+1}. Y < X^k * sqrt(X) + 1
    -- We need Y-1 < 2(X^n+1)/((X+1)n)
    -- Use Y^2 < [2(X^n+1)/((X+1)n) + 1]^2
    have hdenpos : (0 : ℤ) < ((X : ℤ) + 1) * n := by
      nlinarith
    -- Compare  (Y-1)^2 (X+1)^2 n^2  <  4 (X^n+1)^2
    -- i.e. prove the squared form, then take positive roots.
    have hy_le : (Y : ℤ) ^ 2 ≤ (X : ℤ) ^ n + (X : ℤ) ^ n := by
      have : (2 : ℤ) ≤ (X : ℤ) ^ n := by
        have : (2 : ℤ) ≤ 7 ^ 3 := by decide
        have : (7 : ℤ) ^ 3 ≤ (X : ℤ) ^ n := by
          calc
            (7 : ℤ) ^ 3 ≤ (X : ℤ) ^ 3 := pow_le_pow_left₀ (by nlinarith) hx7 3
            _ ≤ (X : ℤ) ^ n := pow_le_pow_right₀ (by nlinarith) hn3
        linarith
      linarith
    -- A cruder bound: Y - 1 < Y ≤ X^{n}  (since Y^2 = X^n+2 < (X^n)^2 for X^n ≥ 3)
    have hYlt : (Y : ℤ) < (X : ℤ) ^ n := by
      have : (Y : ℤ) ^ 2 < ((X : ℤ) ^ n) ^ 2 := by
        have hXn : (3 : ℤ) ≤ (X : ℤ) ^ n := by
          have : (7 : ℤ) ^ 3 ≤ (X : ℤ) ^ n := by
            calc
              (7 : ℤ) ^ 3 ≤ (X : ℤ) ^ 3 := pow_le_pow_left₀ (by nlinarith) hx7 3
              _ ≤ (X : ℤ) ^ n := pow_le_pow_right₀ (by nlinarith) hn3
          linarith
        have : (X : ℤ) ^ n + 2 < ((X : ℤ) ^ n) ^ 2 := by
          nlinarith [sq_nonneg ((X : ℤ) ^ n - 3)]
        rwa [hY2]
      exact lt_of_pow_lt_pow_left₀ 2 (by nlinarith) this
    -- Then (Y-1)(X+1)n < X^n * (X+1) * n
    -- Need X^n (X+1) n < 2(X^n+1)
    -- This is FALSE for large X,n (left is ~ n X^{n+1}, right 2 X^n). Too crude!
    -- Must use the better bound Y ≈ X^{n/2}.
    -- n = 2k+1, Y^2 = X^{2k+1}+2 < (X^k * 3)^2 = 9 X^{2k} for X≥7, k≥1:
    -- X^{2k+1}+2 < 9 X^{2k} ↔ X + 2/X^{2k} < 9. Yes X≥7? 7<9 yes. X=7 OK. X=11>9 FAIL.
    -- Y < X^{k} * sqrt(X) + 1. Bound sqrt(X) ≤ X/2 for X≥4? X/2 vs sqrt(X): X≥4.
    -- Y < X^k * X / 2 + 1 = X^{k+1}/2 + 1  for X≥4? sqrt(X) ≤ X/2 for X≥4 yes.
    -- Then Y-1 < X^{k+1}/2
    -- (Y-1)(X+1)n < X^{k+1}/2 * (X+1) * (2k+1)
    -- 2(X^n+1) > 2 X^{2k+1}
    -- Need (2k+1)(X+1) X^{k+1} / 2 < 2 X^{2k+1}
    -- (2k+1)(X+1) X^{k+1} < 4 X^{2k+1}
    -- (2k+1)(X+1) < 4 X^{k}
    -- For k=1 (n=3): 3(X+1) < 4X, 3X+3<4X, 3<X OK (X≥7).
    -- For k=2 (n=5): 5(X+1)<4 X^2, OK.
    -- For large k: 2k X vs 4 X^k, OK.
    obtain ⟨k, hk⟩ := hodd
    have hk1 : 1 ≤ k := by omega
    have hneq : n = 2 * k + 1 := by omega
    have hY2' : (Y : ℤ) ^ 2 = (X : ℤ) ^ (2 * k + 1) + 2 := by
      rwa [hneq] at hY2
    have hYlt2 : (Y : ℤ) - 1 < (X : ℤ) ^ (k + 1) / 2 + 1 := by
      -- prove Y < X^{k+1}/2 + 2, enough
      have hsqrt : (Y : ℤ) < (X : ℤ) ^ k * (X : ℤ) / 2 + 1 := by
        have hcmp : (Y : ℤ) ^ 2 < ((X : ℤ) ^ k * (X : ℤ) / 2 + 1) ^ 2 := by
          -- (X^{k+1}/2 + 1)^2 = X^{2k+2}/4 + X^{k+1} + 1
          -- vs X^{2k+1}+2
          -- X^{2k+2}/4 = X^{2k+1} * X / 4 ≥ X^{2k+1} * 7/4 > X^{2k+1}+2
          have hxk : (0 : ℤ) ≤ (X : ℤ) ^ k := pow_nonneg (by nlinarith) _
          have : ((X : ℤ) ^ (k + 1) / 2 + 1) ^ 2
              = (X : ℤ) ^ (2 * (k + 1)) / 4 + (X : ℤ) ^ (k + 1) + 1 ∨ True := by
            trivial
          -- Use 2Y ≤ X^{k+1} + 2 or avoid division
          trivial
        trivial
      trivial
    -- Let's redo more carefully without integer division.
    -- Prove 2(Y-1) < X^{k+1}  i.e. Y-1 < X^{k+1}/2, or 2Y < X^{k+1} + 2
    have h2Y : 2 * (Y : ℤ) < (X : ℤ) ^ (k + 1) + 2 := by
      have : (2 * (Y : ℤ)) ^ 2 < ((X : ℤ) ^ (k + 1) + 2) ^ 2 := by
        have hL : (2 * (Y : ℤ)) ^ 2 = 4 * ((X : ℤ) ^ (2 * k + 1) + 2) := by
          nlinarith
        have hR : ((X : ℤ) ^ (k + 1) + 2) ^ 2 =
            (X : ℤ) ^ (2 * k + 2) + 4 * (X : ℤ) ^ (k + 1) + 4 := by
          have : (X : ℤ) ^ (k + 1) * (X : ℤ) ^ (k + 1) = (X : ℤ) ^ (2 * k + 2) := by
            rw [← pow_add]; congr 1; omega
          nlinarith
        have hpowX : (X : ℤ) ^ (2 * k + 2) = (X : ℤ) * (X : ℤ) ^ (2 * k + 1) := by
          have : 2 * k + 2 = (2 * k + 1) + 1 := by omega
          rw [this, pow_succ]
        -- 4 X^{2k+1} + 8 < X * X^{2k+1} + 4 X^{k+1} + 4
        -- (X-4) X^{2k+1} + 4 X^{k+1} - 4 > 0
        have : (0 : ℤ) < ((X : ℤ) - 4) * (X : ℤ) ^ (2 * k + 1)
            + 4 * (X : ℤ) ^ (k + 1) - 4 := by
          have : (0 : ℤ) < (X : ℤ) - 4 := by nlinarith
          have : (0 : ℤ) < (X : ℤ) ^ (2 * k + 1) :=
            pow_pos (by nlinarith) _
          nlinarith [pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) (k + 1)]
        nlinarith
      have hposL : (0 : ℤ) ≤ 2 * Y := by nlinarith
      have hposR : (0 : ℤ) ≤ (X : ℤ) ^ (k + 1) + 2 := by
        nlinarith [pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) (k + 1)]
      exact lt_of_pow_lt_pow_left₀ 2 hposL this
    -- 2(Y-1) < X^{k+1}
    have hYm : 2 * ((Y : ℤ) - 1) < (X : ℤ) ^ (k + 1) := by linarith
    -- (Y-1)(X+1)n = (Y-1)(X+1)(2k+1)
    -- < X^{k+1}/2 * (X+1)(2k+1)
    -- 2(X^n+1) > 2 X^{2k+1}
    -- Need (2k+1)(X+1) X^{k+1} < 4 X^{2k+1}  i.e. (2k+1)(X+1) < 4 X^k
    have hkey : (2 * (k : ℤ) + 1) * ((X : ℤ) + 1) < 4 * (X : ℤ) ^ k := by
      have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hk1
      rcases le_iff_eq_or_lt.mp hk1 with rfl | hkgt
      · -- k=1: 3(X+1) < 4X
        nlinarith
      · have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast (by omega : (2 : ℕ) ≤ k)
        --  (2k+1)(X+1) < 4 X^k, X^k ≥ X^2 ≥ 49, 2k+1 vs 4 X^k / (X+1) ≥ 4 X^{k-1} * X/(X+1) ≥ 3 X^{k-1}
        have hXk : 4 * (X : ℤ) ^ k ≥ 4 * (X : ℤ) ^ 2 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by nlinarith) hk2) (by decide)
        -- Need a bound relating k and X. Use 4*7^k ≥ (2k+1)(X+1) is false if X huge.
        -- Must keep X: 4 X^k ≥ 4 X^2, (2k+1)(X+1) linear in X, 4X^2 vs (2k+1)X
        -- 4 X^k vs (2k+1)(X+1). For k≥2, 4 X^2 vs (2k+1)(X+1).
        -- If k is huge and X=7, 4*7^k vs (2k+1)*8, fine.
        -- If k is huge and X huge, 4 X^k even better.
        -- The only issue is large k, small X — still 7^k beats k.
        have : 4 * (X : ℤ) ^ k - (2 * (k : ℤ) + 1) * ((X : ℤ) + 1) > 0 := by
          have h7 : ∀ m : ℕ, 2 ≤ m →
              4 * (7 : ℤ) ^ m ≥ (2 * (m : ℤ) + 1) * 8 := by
            intro m hm
            induction m with
            | zero => omega
            | succ m ih =>
              have : m = 1 ∨ 2 ≤ m := by omega
              rcases this with rfl | hm'
              · norm_num
              · have := ih (by omega)
                have : (7 : ℤ) ^ (m + 1) = 7 * (7 : ℤ) ^ m := pow_succ' _ _
                nlinarith
          -- 4 X^k ≥ 4 * 7^k ≥ (2k+1)*8, and (2k+1)(X+1) vs (2k+1)*8: only X=7.
          -- General X: 4 X^k / (X+1) ≥ 4 (X-1) X^{k-1} * X/(X(X+1)) wait
          -- 4 X^k ≥ (2k+1)(X+1) ↔ 4 X^k / (X+1) ≥ 2k+1
          -- 4 X^k / (X+1) ≥ 4 (X-1) X^{k-1} / X * X^2/(X+1) ...
          -- Simply: 4 X^k ≥ 4 X * X^{k-1} = 4 X^k, and X+1 ≤ 2X for X≥1,
          -- 4 X^k / (X+1) ≥ 4 X^k / (2X) = 2 X^{k-1} ≥ 2 * 7^{k-1} ≥ 2k+1
          have : 4 * (X : ℤ) ^ k ≥ (2 * (k : ℤ) + 1) * ((X : ℤ) + 1) := by
            have hden : (X : ℤ) + 1 ≤ 2 * (X : ℤ) := by nlinarith
            have hfrac : 2 * (X : ℤ) ^ (k - 1) ≥ 2 * (k : ℤ) + 1 := by
              have : k = (k - 1) + 1 := by omega
              have hkm : 1 ≤ k - 1 := by omega
              have : ∀ m : ℕ, 1 ≤ m → 2 * (7 : ℤ) ^ m ≥ 2 * ((m : ℤ) + 1) + 1 := by
                intro m hm
                induction m with
                | zero => omega
                | succ m ih =>
                  cases m with
                  | zero => norm_num
                  | succ m =>
                    have := ih (by omega)
                    have : (7 : ℤ) ^ (m + 1 + 1) = 7 * (7 : ℤ) ^ (m + 1) := pow_succ' _ _
                    nlinarith
              -- 2 X^{k-1} ≥ 2 * 7^{k-1} ≥ 2k+1 = 2((k-1)+1)+1
              have : 2 * (7 : ℤ) ^ (k - 1) ≥ 2 * ((k - 1 : ℕ) : ℤ) + 2 + 1 := by
                have := this (k - 1) (by omega)
                -- 2*7^m ≥ 2(m+1)+1 = 2m+3, and we need 2k+1 = 2(m+1)+1=2m+3. Yes!
                convert this using 1
                · rfl
                · have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
                    rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
                  linarith
              have : 2 * (X : ℤ) ^ (k - 1) ≥ 2 * (7 : ℤ) ^ (k - 1) := by
                have : (X : ℤ) ^ (k - 1) ≥ (7 : ℤ) ^ (k - 1) :=
                  pow_le_pow_left₀ (by nlinarith) hx7 _
                nlinarith
              linarith
            -- 4 X^k = 4 X * X^{k-1} ≥ 2X * 2 X^{k-1} ≥ (X+1) * (2k+1)
            have : 4 * (X : ℤ) ^ k = 4 * (X : ℤ) * (X : ℤ) ^ (k - 1) := by
              have : k = (k - 1) + 1 := by omega
              conv_lhs => rw [this, pow_succ']
              ring
            nlinarith [pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) (k - 1)]
          exact this
        linarith
      -- k=1 done, k≥2 done
    -- Finish: (Y-1)(X+1)n < X^{k+1}/2 * (X+1)(2k+1) < 2 X^{2k+1} ≤ 2(X^n+1)
    -- From 2(Y-1) < X^{k+1} and (2k+1)(X+1) < 4 X^k:
    -- (Y-1)(X+1)(2k+1) < X^{k+1}/2 * (X+1)(2k+1) < X^{k+1}/2 * 4 X^k
    --   = 2 X^{2k+1} ≤ 2(X^{2k+1}+1)
    have : ((Y : ℤ) - 1) * ((X : ℤ) + 1) * (2 * (k : ℤ) + 1)
        < 2 * ((X : ℤ) ^ (2 * k + 1) + 1) := by
      have hxk1 : (0 : ℤ) < (X : ℤ) ^ (k + 1) := pow_pos (by nlinarith) _
      have hposY : (0 : ℤ) ≤ (Y : ℤ) - 1 := by omega
      have hpos2 : (0 : ℤ) ≤ ((X : ℤ) + 1) * (2 * (k : ℤ) + 1) := by nlinarith
      -- (Y-1) * rhs_factor < X^{k+1}/2 * rhs_factor
      have : ((Y : ℤ) - 1) * ((X : ℤ) + 1) * (2 * (k : ℤ) + 1)
          ≤ ((X : ℤ) ^ (k + 1) - 1) / 2 * ((X : ℤ) + 1) * (2 * (k : ℤ) + 1) := by
        -- use 2(Y-1) ≤ X^{k+1} - 1 (since 2(Y-1) < X^{k+1} and both sides integer)
        have : 2 * ((Y : ℤ) - 1) ≤ (X : ℤ) ^ (k + 1) - 1 := by
          have : 2 * ((Y : ℤ) - 1) + 1 ≤ (X : ℤ) ^ (k + 1) := by
            have hlt := hYm
            have : 2 * ((Y : ℤ) - 1) + 1 ≤ (X : ℤ) ^ (k + 1) := by
              omega
            exact this
          linarith
        -- avoid division: 2(Y-1)(X+1)(2k+1) ≤ (X^{k+1}-1)(X+1)(2k+1)
        nlinarith
      -- switch to doubled inequality
      have hdoubled :
          2 * (((Y : ℤ) - 1) * ((X : ℤ) + 1) * (2 * (k : ℤ) + 1))
            ≤ ((X : ℤ) ^ (k + 1)) * ((X : ℤ) + 1) * (2 * (k : ℤ) + 1) := by
        have := hYm
        nlinarith
      have hdoubled2 :
          ((X : ℤ) ^ (k + 1)) * ((X : ℤ) + 1) * (2 * (k : ℤ) + 1)
            < 4 * (X : ℤ) ^ (2 * k + 1) := by
        have : (X : ℤ) ^ (k + 1) * (X : ℤ) ^ k = (X : ℤ) ^ (2 * k + 1) := by
          rw [← pow_add]; congr 1; omega
        nlinarith [pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) (k + 1),
          pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) k]
      nlinarith [pow_nonneg (by nlinarith : (0 : ℤ) ≤ X) (2 * k + 1)]
    rw [hneq]
    convert this using 1
    · push_cast; ring
    · push_cast; rfl
  exact_mod_cast hZ

/-! ### Main argument for prime exponents -/

lemma four_dvd_pow_add_one {X n : ℕ} (h8 : 8 ∣ X ^ n + 1) : 4 ∣ X ^ n + 1 :=
  dvd_trans (by decide : (4 : ℕ) ∣ 8) h8

lemma A_mul_succ {X Y n : ℕ} (hXo : Odd X) (hn : Odd n)
    (h : Y ^ 2 = X ^ n + 2) :
    ((Y - 1) / 2) * ((Y + 1) / 2) = (X ^ n + 1) / 4 := by
  have hy := Y_odd hXo h
  have hy1 := Y_pos h
  have h8X := X_mod_eight hXo hn h
  have he1 : 2 ∣ Y - 1 := by
    have : (Y - 1) % 2 = 0 := by
      have : Y % 2 = 1 := Nat.odd_iff.mp hy; omega
    exact Nat.dvd_iff_mod_eq_zero.mpr this
  have he2 : 2 ∣ Y + 1 := by
    have : (Y + 1) % 2 = 0 := by
      have : Y % 2 = 1 := Nat.odd_iff.mp hy; omega
    exact Nat.dvd_iff_mod_eq_zero.mpr this
  have h4 : 4 ∣ X ^ n + 1 := four_dvd_pow_add_one (eight_dvd_pow_add_one h8X hn)
  have hL : (Y - 1) * (Y + 1) = 4 * (((Y - 1) / 2) * ((Y + 1) / 2)) := by
    have ha : Y - 1 = 2 * ((Y - 1) / 2) := (Nat.mul_div_cancel' he1).symm
    have hb : Y + 1 = 2 * ((Y + 1) / 2) := (Nat.mul_div_cancel' he2).symm
    rw [ha, hb]; ring
  have hR : X ^ n + 1 = 4 * ((X ^ n + 1) / 4) := (Nat.mul_div_cancel' h4).symm
  have : (Y - 1) * (Y + 1) = Y ^ 2 - 1 := by
    have := Nat.sq_sub_sq Y 1
    simpa [Nat.mul_comm, one_pow] using this.symm
  have : Y ^ 2 - 1 = X ^ n + 1 := by omega
  omega

lemma Phi_mul (X n : ℕ) (hn : Odd n) :
    ((X ^ n + 1) / (X + 1)) * (X + 1) = X ^ n + 1 :=
  geom_odd_mul hn

lemma no_sq_eq_prime_pow_add_two {X Y n : ℕ}
    (hnP : Nat.Prime n) (hodd : Odd n) (hX : 7 ≤ X)
    (hXo : Odd X) (h8 : X % 8 = 7)
    (h : Y ^ 2 = X ^ n + 2) : False := by
  have hn3 : 3 ≤ n := Nat.Prime.one_lt hnP ▸ (by
    have : 2 ≤ n := hnP.two_le
    have : n ≠ 2 := by
      intro h2; subst h2
      exact (by decide : ¬ Odd 2) hodd
    omega)
  have hy := Y_odd hXo h
  have hy1 := Y_pos h
  set A := (Y - 1) / 2
  set B := (Y + 1) / 2
  have hAB : A * B = (X ^ n + 1) / 4 := A_mul_succ hXo hodd h
  have hBA : B = A + 1 := by
    have he1 : 2 ∣ Y - 1 := by
      have : (Y - 1) % 2 = 0 := by
        have : Y % 2 = 1 := Nat.odd_iff.mp hy; omega
      exact Nat.dvd_iff_mod_eq_zero.mpr this
    have he2 : 2 ∣ Y + 1 := by
      have : (Y + 1) % 2 = 0 := by
        have : Y % 2 = 1 := Nat.odd_iff.mp hy; omega
      exact Nat.dvd_iff_mod_eq_zero.mpr this
    have : Y + 1 = (Y - 1) + 2 := by omega
    have : (Y + 1) / 2 = (Y - 1) / 2 + 1 := by
      have h1 : Y + 1 = 2 * ((Y + 1) / 2) := (Nat.mul_div_cancel' he2).symm
      have h2 : Y - 1 = 2 * ((Y - 1) / 2) := (Nat.mul_div_cancel' he1).symm
      omega
    simpa [A, B] using this
  have hAprod : A * (A + 1) = (X ^ n + 1) / 4 := by rwa [← hBA]
  set Φ := (X ^ n + 1) / (X + 1)
  have hΦ : Φ * (X + 1) = X ^ n + 1 := Phi_mul X n hodd
  have h4 : 4 ∣ X ^ n + 1 := four_dvd_pow_add_one (eight_dvd_pow_add_one h8 hodd)
  have h8succ : 8 ∣ X + 1 := eight_dvd_X_succ h8
  have hg : Nat.gcd (X + 1) Φ = Nat.gcd (X + 1) n := gcd_succ_geom hodd
  have hd : Nat.gcd (X + 1) n = 1 ∨ Nat.gcd (X + 1) n = n := by
    have hdvd : Nat.gcd (X + 1) n ∣ n := Nat.gcd_dvd_right _ _
    rcases hnP.eq_one_or_self_of_dvd hdvd with h1 | hn
    · exact Or.inl h1
    · exact Or.inr hn
  have hAlower : n * (X + 1) < 2 * (Y - 1) := Y_gt_lower hX hn3 h
  have hAupper : (Y - 1) * (X + 1) * n < 2 * (X ^ n + 1) :=
    Y_lt_upper hX hn3 hodd h
  have he1 : 2 ∣ Y - 1 := by
    have : (Y - 1) % 2 = 0 := by
      have : Y % 2 = 1 := Nat.odd_iff.mp hy; omega
    exact Nat.dvd_iff_mod_eq_zero.mpr this
  have hAeq : 2 * A = Y - 1 := Nat.mul_div_cancel' he1
  -- n(X+1)/4 < A  because 4 | n(X+1) (n odd, 8|X+1)
  have h4nX : 4 ∣ n * (X + 1) := by
    have : 4 ∣ X + 1 := dvd_trans (by decide : (4 : ℕ) ∣ 8) h8succ
    exact dvd_mul_of_dvd_right this _
  have hA_gt : n * (X + 1) / 4 < A := by
    have : n * (X + 1) < 2 * (Y - 1) := hAlower
    have : n * (X + 1) < 4 * A := by
      have : 2 * (Y - 1) = 4 * A := by omega
      omega
    have ha : n * (X + 1) = 4 * (n * (X + 1) / 4) :=
      (Nat.mul_div_cancel' h4nX).symm
    omega
  rcases hd with hd1 | hdn
  · -- gcd(X+1, n) = 1 ⇒ gcd(X+1, Φ) = 1
    have hcop : Nat.gcd (X + 1) Φ = 1 := by rwa [hg]
    have hcop4 : Nat.gcd ((X + 1) / 4) Φ = 1 := by
      have h4X : 4 ∣ X + 1 := dvd_trans (by decide : (4 : ℕ) ∣ 8) h8succ
      have : Nat.gcd (X + 1) Φ = 1 := hcop
      have hdvd : Nat.gcd ((X + 1) / 4) Φ ∣ Nat.gcd (X + 1) Φ := by
        refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
        have : (X + 1) / 4 ∣ X + 1 := Nat.div_dvd_of_dvd h4X
        exact this.trans (Nat.gcd_dvd_left _ _)
      rwa [this] at hdvd
    -- Φ is odd
    have hΦodd : Odd Φ := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      -- 8 | X^n+1 and 8 | X+1 so v2(Φ)=v2(X^n+1)-v2(X+1)≥3-3, need =0
      -- From X≡7 mod 8, n odd: X^n ≡7 mod 8, X^n+1≡0 mod 8 but not necessarily higher.
      -- Φ = (X^n+1)/(X+1), both divisible by 8, quotient could be even.
      -- Use: X=8t-1, ( (8t-1)^n + 1 ) / (8t) 
      -- (8t-1)^n = ∑ binom(n,k) (8t)^k (-1)^{n-k}, k=0 term (-1)^n = -1 (n odd)
      -- so (8t-1)^n + 1 = ∑_{k≥1} binom(n,k) (8t)^k (-1)^{n-k}
      -- = 8t * (n (-1)^{n-1} + multiples of 8t)
      -- n odd so (-1)^{n-1}=1, Φ = n + multiple of 8t, n odd ⇒ Φ odd.
      obtain ⟨t, ht⟩ : 8 ∣ X + 1 := h8succ
      have hXeq : X = 8 * t - 1 := by
        have : X + 1 = 8 * t := ht.symm
        omega
      have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Odd.pos hodd)
      -- Use binomial via integers
      have hΦmod : Φ % 2 = 1 := by
        have : (X ^ n + 1) / (X + 1) % 2 = n % 2 := by
          have := geom_odd_mod (x := X) hodd
          -- Φ ≡ n [MOD X+1], X+1 even, so Φ ≡ n [MOD 2]
          have hmod := this
          have : Φ ≡ n [MOD X + 1] := by simpa [Φ] using hmod
          have : 2 ∣ X + 1 := dvd_trans (by decide : (2 : ℕ) ∣ 8) h8succ
          have : Φ ≡ n [MOD 2] := this.of_dvd ‹2 ∣ X + 1›
          simpa [Nat.ModEq] using this
        have : n % 2 = 1 := Nat.odd_iff.mp hodd
        omega
      exact Nat.odd_iff.mpr hΦmod
    -- A(A+1) = (X+1)Φ/4
    have hprod : A * (A + 1) = ((X + 1) / 4) * Φ := by
      have h4X : 4 ∣ X + 1 := dvd_trans (by decide : (4 : ℕ) ∣ 8) h8succ
      have : (X ^ n + 1) / 4 = ((X + 1) / 4) * Φ := by
        have : X ^ n + 1 = (X + 1) * Φ := hΦ.symm
        have : (X + 1) * Φ / 4 = ((X + 1) / 4) * Φ := by
          have : (X + 1) * Φ = 4 * (((X + 1) / 4) * Φ) := by
            have : X + 1 = 4 * ((X + 1) / 4) := (Nat.mul_div_cancel' h4X).symm
            rw [this]; ring
          omega
        omega
      rwa [this] at hAprod
    have hcopA : Nat.gcd Φ A = 1 ∨ Φ ∣ A := by
      -- Φ divides A(A+1), so Φ's primes go to A or A+1
      have : Φ ∣ A * (A + 1) := ⟨(X + 1) / 4, hprod.symm⟩
      exact Or.inr (by
        -- we'll use the coprimeness to decide
        trivial) ∨ True |> fun _ => Or.inl (by
          -- placeholder, replaced below
          trivial)
    -- Cleaner: since gcd(Φ, (X+1)/4)=1, and A(A+1)=((X+1)/4)Φ,
    -- Φ | A or Φ | A+1 because gcd(A, A+1)=1
    have hgcdA : Nat.gcd A (A + 1) = 1 := Nat.gcd_succ A
    have hΦ_div : Φ ∣ A ∨ Φ ∣ A + 1 := by
      have hdiv : Φ ∣ A * (A + 1) := ⟨(X + 1) / 4, by rw [hprod]⟩
      exact (Nat.Prime.dvd_mul ?_).mp ?_ |> fun _ =>
        -- Φ may be composite. Use coprimeness of A, A+1:
        -- gcd(Φ, A) * gcd(Φ, A+1) = Φ  (because Φ | A(A+1) and gcd(A,A+1)=1)
        False.elim (by
          -- implement via: let d = gcd(Φ, A), then Φ/d | A+1 (since Φ/d coprime to A)
          trivial)
    -- Implement properly:
    have hΦ_div : Φ ∣ A ∨ Φ ∣ A + 1 := by
      set d := Nat.gcd Φ A
      have hdA : d ∣ A := Nat.gcd_dvd_right _ _
      have hdΦ : d ∣ Φ := Nat.gcd_dvd_left _ _
      obtain ⟨Φ', hΦ'⟩ := hdΦ
      obtain ⟨A', hA'⟩ := hdA
      have hcop' : Nat.gcd Φ' A' = 1 := by
        have : d * Nat.gcd Φ' A' = d := by
          have := Nat.gcd_mul_left d Φ' A'
          rw [← hΦ', ← hA'] at this
          simpa [d] using this
        have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ (by
          have : 0 < Φ := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _)
            (odd_add_one_dvd_pow_add_one hodd)) (Nat.succ_pos _)
          omega)
        omega
      have hdiv : Φ ∣ A * (A + 1) := ⟨(X + 1) / 4, by rw [hprod]⟩
      have : Φ' ∣ A' * (A + 1) := by
        -- d Φ' | d A' * (A+1), cancel d
        obtain ⟨t, ht⟩ := hdiv
        have : d * Φ' * t = d * A' * (A + 1) := by
          rw [← hΦ', ← hA'] at ht; linarith
        have hdpos : d ≠ 0 := by
          have : 0 < d := Nat.gcd_pos_of_pos_left _ (by
            have : 0 < Φ := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _)
              (odd_add_one_dvd_pow_add_one hodd)) (Nat.succ_pos _)
            omega)
          omega
        exact ⟨t, by
          have := Nat.mul_left_cancel (Nat.pos_of_ne_zero hdpos) (by
            convert this using 1 <;> ring)
          linarith⟩
      have : Φ' ∣ A + 1 := by
        have : Φ' ∣ A' * (A + 1) := this
        exact Coprime.dvd_of_dvd_mul_left hcop'.symm this
      rcases eq_or_ne Φ' 1 with h1 | hne
      · left
        -- Φ = d * 1, d | A so Φ | A
        rw [hΦ', h1, mul_one]
        exact hdA
      · right
        -- Φ' > 1, Φ' | A+1. Need all of Φ | A+1.
        -- Since gcd(A, A+1)=1 and d | A, gcd(d, A+1)=1, so d doesn't divide A+1
        -- unless d=1, in which case Φ=Φ' | A+1.
        have hdcop : Nat.gcd d (A + 1) = 1 := by
          have : Nat.gcd d (A + 1) ∣ Nat.gcd A (A + 1) := by
            exact Nat.dvd_gcd hdA (dvd_refl _)
          rwa [hgcdA] at this
        -- Φ = d * Φ', Φ' | A+1, need d | A+1 or d=1
        have : d = 1 := by
          -- d | Φ and Φ | A(A+1), d | A already. OK any d.
          -- We want Φ | A+1 i.e. d Φ' | A+1. Φ' | A+1, need d | A+1, so d=1.
          -- NOT necessarily: we might have Φ | A instead if Φ'=1, already handled.
          -- If Φ'>1 and d>1, Φ splits! Then neither Φ|A nor Φ|A+1.
          -- THIS IS THE SPLITTING PROBLEM.
          trivial
        rw [this, hΦ', one_mul]
        exact this
    sorry
  · sorry

theorem no_sq_eq_odd_pow_add_two {X Y n : ℕ}
    (hn : 3 ≤ n) (hodd : Odd n) (hXpos : 1 ≤ X)
    (h : Y ^ 2 = X ^ n + 2) : False := by
  have hn2 : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 3) hn
  by_cases hXE : Even X
  · exact X_even_impossible hXE hn2 h
  · have hXo : Odd X := Nat.not_even_iff_odd.mp hXE
    have h8 := X_mod_eight hXo hodd h
    have hX7 := X_ge_seven hXo hodd h
    obtain ⟨r, hrP, hrdvd⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have hrO : Odd r := by
      have : r ≠ 2 := by
        intro h2; subst h2
        have : 2 ∣ n := hrdvd
        have : Even n := even_iff_two_dvd.mpr this
        exact (Nat.not_even_iff_odd.mpr hodd) this
      exact hrP.eq_two_or_odd'.resolve_left this
    obtain ⟨m, hm⟩ := hrdvd
    have hmeq : X ^ n = (X ^ m) ^ r := by
      rw [hm, mul_comm, pow_mul]
    have h' : Y ^ 2 = (X ^ m) ^ r + 2 := by rw [← hmeq]; exact h
    have hXm : 7 ≤ X ^ m := by
      have : 1 ≤ m := by
        have : 0 < r * m := by
          have : 0 < n := by omega
          rwa [← hm]
        have : 0 < r := Nat.Prime.pos hrP
        omega
      calc
        7 ≤ X := hX7
        _ = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ m := Nat.pow_le_pow_right (by omega) this
    have hXmo : Odd (X ^ m) := Odd.pow hXo
    have h8m : (X ^ m) % 8 = 7 := by
      have : Odd m := by
        -- n = r * m both odd
        have : Odd (r * m) := by rwa [← hm]
        exact (Nat.odd_mul.mp this).2
      have := odd_pow_mod_eight_self hXo this
      rwa [h8] at this
    exact no_sq_eq_prime_pow_add_two hrP hrO hXm hXmo h8m h'
