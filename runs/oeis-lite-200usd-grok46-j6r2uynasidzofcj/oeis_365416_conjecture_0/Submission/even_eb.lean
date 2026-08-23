import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

open Nat

/-!
  There are no positive integers `X, Y, n` with `n` odd, `3 ≤ n`, `1 < Y`
  such that `X ^ 2 = Y ^ n + 2`.
-/

/-! ### Geometric quotient for odd exponents -/

lemma odd_add_one_dvd_pow_add_one {x n : ℕ} (hn : Odd n) :
    x + 1 ∣ x ^ n + 1 := by
  simpa using hn.nat_add_dvd_pow_add_pow x 1

lemma geom_odd_mul {x n : ℕ} (hn : Odd n) :
    ((x ^ n + 1) / (x + 1)) * (x + 1) = x ^ n + 1 :=
  Nat.div_mul_cancel (odd_add_one_dvd_pow_add_one hn)

lemma odd_pow_sub_one_mod_sq (d : ℤ) : ∀ k : ℕ,
    d ^ 2 ∣ (d - 1) ^ (2 * k + 1) + 1 - ((2 * k + 1 : ℕ) : ℤ) * d
  | 0 => by
    ring_nf
    simp
  | k + 1 => by
    have ih := odd_pow_sub_one_mod_sq d k
    set n : ℕ := 2 * k + 1
    have hnat : 2 * (k + 1) + 1 = n + 2 := by
      simp [n]; omega
    rw [hnat]
    push_cast
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
      rw [‹(d - 1) ^ (n + 2) = _›, this]
      ring
    have h2 : d ^ 2 ∣ 2 * d * ((d - 1) ^ n + 1) := by
      obtain ⟨t, ht⟩ := hd_dvd
      rw [ht]
      refine ⟨2 * t, by ring⟩
    have h1 : d ^ 2 ∣ d ^ 2 * (d - 1) ^ n := dvd_mul_right _ _
    have h3 : d ^ 2 ∣ (d - 1) ^ n + 1 - (n : ℤ) * d := ih
    rw [hdecomp]
    exact dvd_sub (dvd_add h1 h3) h2

lemma odd_pow_sub_one_mod_sq' {d : ℤ} {n : ℕ} (hn : Odd n) :
    d ^ 2 ∣ (d - 1) ^ n + 1 - (n : ℤ) * d := by
  obtain ⟨k, hk⟩ := hn
  subst hk
  exact odd_pow_sub_one_mod_sq d k

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
      convert h using 1
      ring
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

/-! ### Parity and 2-adic data -/

lemma sq_sub_two_X_odd {X Y n : ℕ} (hY : Odd Y) (h : X ^ 2 = Y ^ n + 2) : Odd X := by
  have hYn : Odd (Y ^ n) := Odd.pow hY
  have hodd : Odd (Y ^ n + 2) := by
    rw [Nat.odd_iff] at hYn ⊢
    omega
  have : Odd (X ^ 2) := by simpa [h] using hodd
  simpa [Nat.odd_pow_iff (by decide : (2 : ℕ) ≠ 0)] using this

lemma sq_mod_four_ne_two (n : ℕ) : n ^ 2 % 4 ≠ 2 := by
  have : n % 4 < 4 := Nat.mod_lt n (by decide)
  have heq : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  rw [heq]
  interval_cases n % 4 <;> norm_num

lemma Y_even_impossible {X Y n : ℕ} (hY : Even Y) (hn : 2 ≤ n)
    (h : X ^ 2 = Y ^ n + 2) : False := by
  obtain ⟨k, hk⟩ := hY
  have hYn : Y ^ n % 4 = 0 := by
    have : Y ^ n = (2 * k) ^ n := by rw [hk, two_mul]
    rw [this, mul_pow]
    have hn2 : 2 ≤ n := hn
    have : 4 ∣ 2 ^ n := by
      have : 2 ^ n = 2 ^ 2 * 2 ^ (n - 2) := by
        rw [← pow_add, Nat.add_sub_of_le hn2]
      exact ⟨2 ^ (n - 2), by simpa using this⟩
    have : 4 ∣ 2 ^ n * k ^ n := dvd_mul_of_dvd_left this _
    exact Nat.dvd_iff_mod_eq_zero.mp this
  have hx2 : X ^ 2 % 4 = 2 := by
    rw [h, Nat.add_mod, hYn]
  exact sq_mod_four_ne_two X hx2

lemma odd_sq_mod_eight {X : ℕ} (hX : Odd X) : X ^ 2 % 8 = 1 := by
  have : X % 8 = 1 ∨ X % 8 = 3 ∨ X % 8 = 5 ∨ X % 8 = 7 := by
    have : X % 2 = 1 := Nat.odd_iff.mp hX
    have : X % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]

lemma odd_pow_mod_eight {a n : ℕ} (ha : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7)
    (hn : Odd n) : a ^ n % 8 = a % 8 := by
  obtain ⟨k, rfl⟩ := hn
  induction k with
  | zero => simp
  | succ k ih =>
    have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [this, pow_add, Nat.mul_mod, ih]
    rcases ha with h | h | h | h <;> simp [Nat.pow_mod, h]

lemma Y_mod_eight_of_sq_sub_two {X Y n : ℕ} (hY : Odd Y) (hn : Odd n)
    (h : X ^ 2 = Y ^ n + 2) : Y % 8 = 7 := by
  have hX : Odd X := sq_sub_two_X_odd hY h
  have hx8 : X ^ 2 % 8 = 1 := odd_sq_mod_eight hX
  have : (Y ^ n + 2) % 8 = 1 := by rw [← h, hx8]
  have : (Y ^ n % 8 + 2) % 8 = 1 := by rwa [Nat.add_mod] at this
  have hYn : Y ^ n % 8 = 7 := by omega
  have hY8 : Y % 8 = 1 ∨ Y % 8 = 3 ∨ Y % 8 = 5 ∨ Y % 8 = 7 := by
    have : Y % 2 = 1 := Nat.odd_iff.mp hY
    have : Y % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  have : Y ^ n % 8 = Y % 8 := odd_pow_mod_eight hY8 hn
  omega

lemma two_lt_of_Y_mod_eight {Y : ℕ} (h : Y % 8 = 7) : 3 ≤ padicValNat 2 (Y + 1) := by
  have h8 : 2 ^ 3 ∣ Y + 1 := by
    have hmod : (Y + 1) % 8 = 0 := by omega
    exact Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hne : Y + 1 ≠ 0 := Nat.succ_ne_zero Y
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (padicValNat_dvd_iff_le hne).mp h8

lemma Y_ge_seven {X Y n : ℕ} (hY : Odd Y) (hn : Odd n) (hY1 : 1 < Y)
    (h : X ^ 2 = Y ^ n + 2) : 7 ≤ Y := by
  have h8 : Y % 8 = 7 := Y_mod_eight_of_sq_sub_two hY hn h
  have : Y % 8 < 8 := Nat.mod_lt _ (by decide)
  omega
lemma odd_of_not_two_dvd {s : ℕ} (h : ¬ 2 ∣ s) : Odd s :=
  Nat.not_even_iff_odd.mp (fun he => h (even_iff_two_dvd.mp he))

lemma odd_part_of_val2 (Y : ℕ) :
    Odd ((Y + 1) / 2 ^ padicValNat 2 (Y + 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY1ne : Y + 1 ≠ 0 := Nat.succ_ne_zero _
  set α := padicValNat 2 (Y + 1)
  have hdiv : 2 ^ α ∣ Y + 1 := pow_padicValNat_dvd
  set s := (Y + 1) / 2 ^ α
  have hs : Y + 1 = 2 ^ α * s := (Nat.mul_div_cancel' hdiv).symm
  have : ¬ 2 ∣ s := by
    intro h2s
    have : 2 ^ (α + 1) ∣ Y + 1 := by
      rw [hs, pow_succ]
      exact mul_dvd_mul_left _ h2s
    have : α + 1 ≤ α := (padicValNat_dvd_iff_le hY1ne).mp this
    omega
  exact odd_of_not_two_dvd this


lemma add_pow_mod_sq_dvd {a b : ℤ} {N : ℕ} (hN : (N : ℤ) ∣ b ^ 2) :
    ∀ n : ℕ, 1 ≤ n →
      (a + b) ^ n ≡ a ^ n + (n : ℤ) * a ^ (n - 1) * b [ZMOD N]
  | 1, _ => by
    simp [pow_one]
  | n + 2, _ => by
    have ihn : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have ih := add_pow_mod_sq_dvd (a := a) (b := b) (N := N) hN (n + 1) ihn
    have hsucc : (a + b) ^ (n + 2) = (a + b) * (a + b) ^ (n + 1) := pow_succ' _ _
    have hmul : (a + b) ^ (n + 2) ≡
        (a + b) * (a ^ (n + 1) + (↑n + 1) * a ^ n * b) [ZMOD N] := by
      rw [hsucc]
      have : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by simp
      have ih' : (a + b) ^ (n + 1) ≡
          a ^ (n + 1) + (↑n + 1) * a ^ n * b [ZMOD N] := by
        convert ih
      exact (Int.ModEq.refl (a + b)).mul ih'
    have n1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by simp
    have n2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by simp
    have hexpand :
        (a + b) * (a ^ (n + 1) + (↑n + 1) * a ^ n * b) =
          a ^ (n + 2) + (↑n + 2) * a ^ (n + 1) * b
            + (↑n + 1) * a ^ n * b ^ 2 := by
      ring
    have hy : (↑n + 1) * a ^ n * b ^ 2 ≡ 0 [ZMOD N] := by
      rw [Int.modEq_zero_iff_dvd]
      exact dvd_mul_of_dvd_right hN _
    have hdrop :
        a ^ (n + 2) + (↑n + 2) * a ^ (n + 1) * b + (↑n + 1) * a ^ n * b ^ 2 ≡
          a ^ (n + 2) + (↑n + 2) * a ^ (n + 1) * b [ZMOD N] := by
      simpa using (Int.ModEq.refl (a ^ (n + 2) + (↑n + 2) * a ^ (n + 1) * b)).add hy
    have hright :
        (a + b) * (a ^ (n + 1) + (↑n + 1) * a ^ n * b) ≡
          a ^ (n + 2) + (↑n + 2) * a ^ (n + 1) * b [ZMOD N] := by
      rwa [hexpand]
    have hmain : (a + b) ^ (n + 2) ≡
        a ^ (n + 2) + (↑n + 2) * a ^ (n + 1) * b [ZMOD N] :=
      hmul.trans hright
    simpa [Nat.add_sub_cancel, n2] using hmain


/-- For odd `Y` and odd `n`, `v₂(Y ^ n + 1) = v₂(Y + 1)`. -/
lemma val2_pow_add_one_of_odd {Y n : ℕ} (hY : Odd Y) (hn : Odd n) :
    padicValNat 2 (Y ^ n + 1) = padicValNat 2 (Y + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY1ne : Y + 1 ≠ 0 := Nat.succ_ne_zero _
  have hYn1ne : Y ^ n + 1 ≠ 0 := Nat.succ_ne_zero _
  set α := padicValNat 2 (Y + 1)
  have hαpos : 1 ≤ α := by
    have : 2 ∣ Y + 1 := by
      have hYmod : Y % 2 = 1 := Nat.odd_iff.mp hY
      have : (Y + 1) % 2 = 0 := by omega
      exact Nat.dvd_iff_mod_eq_zero.mpr this
    exact (padicValNat_dvd_iff_le hY1ne).mp this
  have hdiv : 2 ^ α ∣ Y + 1 := pow_padicValNat_dvd
  set s := (Y + 1) / 2 ^ α
  have hs : Y + 1 = 2 ^ α * s := (Nat.mul_div_cancel' hdiv).symm
  have hsodd : Odd s := by
    simpa [s] using odd_part_of_val2 Y
  have hYeq : (Y : ℤ) = (2 : ℤ) ^ α * s - 1 := by
    have : ((Y + 1 : ℕ) : ℤ) = ((2 ^ α * s : ℕ) : ℤ) := by
      exact_mod_cast hs
    push_cast at this
    linarith
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Odd.pos hn)
  have hN : ((2 ^ (α + 1) : ℕ) : ℤ) ∣ ((2 : ℤ) ^ α * s) ^ 2 := by
    have : α + 1 ≤ 2 * α := by omega
    have hpow : (2 : ℤ) ^ (α + 1) ∣ (2 : ℤ) ^ (2 * α) :=
      pow_dvd_pow (2 : ℤ) this
    have : ((2 ^ (α + 1) : ℕ) : ℤ) = (2 : ℤ) ^ (α + 1) := by
      simp [Nat.cast_pow]
    rw [this, mul_pow, ← pow_mul, mul_comm α 2]
    exact dvd_mul_of_dvd_left hpow _
  -- Y = -1 + 2^α s, so Y^n ≡ (-1)^n + n (-1)^{n-1} 2^α s [ZMOD 2^{α+1}]
  have hcong :=
    add_pow_mod_sq_dvd (a := (-1 : ℤ)) (b := (2 : ℤ) ^ α * s) (N := 2 ^ (α + 1))
      hN n hn1
  have hYab : (Y : ℤ) = (-1 : ℤ) + (2 : ℤ) ^ α * s := by linarith [hYeq]
  have hpow : (Y : ℤ) ^ n ≡
      (-1 : ℤ) ^ n + (n : ℤ) * (-1 : ℤ) ^ (n - 1) * ((2 : ℤ) ^ α * s)
        [ZMOD 2 ^ (α + 1)] := by
    rwa [hYab]
  have hsign1 : (-1 : ℤ) ^ n = -1 := Odd.neg_one_pow hn
  have hsign2 : (-1 : ℤ) ^ (n - 1) = 1 := by
    have : Even (n - 1) := by
      obtain ⟨k, hk⟩ := hn
      refine ⟨k, by omega⟩
    exact Even.neg_one_pow this
  have hpow' : (Y : ℤ) ^ n ≡
      -1 + (n : ℤ) * ((2 : ℤ) ^ α * s) [ZMOD 2 ^ (α + 1)] := by
    simpa [hsign1, hsign2] using hpow
  have hYn : (Y : ℤ) ^ n + 1 ≡ (n : ℤ) * ((2 : ℤ) ^ α * s) [ZMOD 2 ^ (α + 1)] := by
    simpa [add_comm, add_left_comm] using hpow'.add (Int.ModEq.refl (1 : ℤ))
  -- n * s is odd, so n * 2^α * s ≡ 2^α [ZMOD 2^{α+1}]
  have hns : Odd ((n : ℤ) * s) := by
    have hnZ : Odd (n : ℤ) := by
      obtain ⟨k, hk⟩ := hn
      refine ⟨k, by exact_mod_cast hk⟩
    have hsZ : Odd (s : ℤ) := by
      obtain ⟨k, hk⟩ := hsodd
      refine ⟨k, by exact_mod_cast hk⟩
    exact hnZ.mul hsZ
  have hns2 : ¬ (2 : ℤ) ∣ (n : ℤ) * s := by
    intro h2
    exact Int.not_even_iff_odd.mpr hns (even_iff_two_dvd.mpr h2)
  have hmod : (n : ℤ) * ((2 : ℤ) ^ α * s) ≡ (2 : ℤ) ^ α [ZMOD 2 ^ (α + 1)] := by
    -- n*s = 2t+1 ⇒ n*2^α*s = 2^{α+1} t + 2^α
    obtain ⟨t, ht⟩ := hns
    have : (n : ℤ) * s = 2 * t + 1 := ht
    have : (n : ℤ) * ((2 : ℤ) ^ α * s) = (2 : ℤ) ^ (α + 1) * t + (2 : ℤ) ^ α := by
      calc
        (n : ℤ) * ((2 : ℤ) ^ α * s) = ((n : ℤ) * s) * (2 : ℤ) ^ α := by ring
        _ = (2 * t + 1) * (2 : ℤ) ^ α := by rw [this]
        _ = 2 * t * (2 : ℤ) ^ α + (2 : ℤ) ^ α := by ring
        _ = (2 : ℤ) ^ (α + 1) * t + (2 : ℤ) ^ α := by
          rw [pow_succ]; ring
    rw [Int.modEq_iff_dvd, this]
    simp [add_comm]
  have hfinal : (Y : ℤ) ^ n + 1 ≡ (2 : ℤ) ^ α [ZMOD 2 ^ (α + 1)] :=
    hYn.trans hmod
  -- Hence 2^α ∣ Y^n+1 but not 2^{α+1}
  have hdvdα : 2 ^ α ∣ Y ^ n + 1 := by
    have hsub : (2 : ℤ) ^ (α + 1) ∣ (2 : ℤ) ^ α - ((Y : ℤ) ^ n + 1) := by
      have h := hfinal
      rw [Int.modEq_iff_dvd] at h
      simpa [Nat.cast_pow] using h
    have hα : (2 : ℤ) ^ α ∣ (2 : ℤ) ^ α - ((Y : ℤ) ^ n + 1) :=
      dvd_trans (pow_dvd_pow (2 : ℤ) (Nat.le_succ α)) hsub
    have : (2 : ℤ) ^ α ∣ (Y : ℤ) ^ n + 1 := by
      have := dvd_sub (dvd_refl ((2 : ℤ) ^ α)) hα
      simpa using this
    exact_mod_cast this
  have hnot : ¬ 2 ^ (α + 1) ∣ Y ^ n + 1 := by
    intro hdiv'
    have hc : (2 : ℤ) ^ (α + 1) ∣ (Y : ℤ) ^ n + 1 := by
      exact_mod_cast hdiv'
    have hsub : (2 : ℤ) ^ (α + 1) ∣ (2 : ℤ) ^ α - ((Y : ℤ) ^ n + 1) := by
      have h := hfinal
      rw [Int.modEq_iff_dvd] at h
      simpa [Nat.cast_pow] using h
    have : (2 : ℤ) ^ (α + 1) ∣ (2 : ℤ) ^ α :=
      (Int.dvd_iff_dvd_of_dvd_sub hsub).mpr hc
    have hnat : (2 : ℕ) ^ (α + 1) ∣ 2 ^ α := by exact_mod_cast this
    have : α + 1 ≤ α :=
      (pow_dvd_pow_iff_le_right (by decide : (1 : ℕ) < 2)).mp hnat
    omega
  have hle : α ≤ padicValNat 2 (Y ^ n + 1) :=
    (padicValNat_dvd_iff_le hYn1ne).mp hdvdα
  have hnle : ¬ α + 1 ≤ padicValNat 2 (Y ^ n + 1) :=
    mt (padicValNat_dvd_iff_le hYn1ne).mpr hnot
  omega

lemma geom_odd_odd {Y n : ℕ} (hY : Odd Y) (hn : Odd n) :
    Odd ((Y ^ n + 1) / (Y + 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := geom_odd_mul (x := Y) hn
  have hY1ne : Y + 1 ≠ 0 := Nat.succ_ne_zero _
  have hYn1ne : Y ^ n + 1 ≠ 0 := Nat.succ_ne_zero _
  have hval := val2_pow_add_one_of_odd hY hn
  have hΦne : (Y ^ n + 1) / (Y + 1) ≠ 0 := by
    have : 0 < (Y ^ n + 1) / (Y + 1) :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos _)
        (odd_add_one_dvd_pow_add_one hn)) (Nat.succ_pos _)
    omega
  have : padicValNat 2 ((Y ^ n + 1) / (Y + 1)) = 0 := by
    have : padicValNat 2 (Y ^ n + 1) =
        padicValNat 2 (((Y ^ n + 1) / (Y + 1)) * (Y + 1)) := by
      rw [hmul]
    rw [padicValNat.mul hΦne hY1ne, hval] at this
    omega
  exact odd_of_not_two_dvd (by
    intro h2
    have : 1 ≤ padicValNat 2 ((Y ^ n + 1) / (Y + 1)) :=
      (padicValNat_dvd_iff_le hΦne).mp h2
    omega)



/-! ### 2-adic data for `X^2 - 1` -/

lemma val2_X_sq_sub_one {X Y n : ℕ} (hY : Odd Y) (hn : Odd n)
    (h : X ^ 2 = Y ^ n + 2) :
    padicValNat 2 (X ^ 2 - 1) = padicValNat 2 (Y + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : Odd X := sq_sub_two_X_odd hY h
  have hpos : 1 ≤ X := Odd.pos hX
  have hsub : X ^ 2 - 1 = Y ^ n + 1 := by
    have : 1 ≤ X ^ 2 := Nat.one_le_pow 2 X hpos
    omega
  rw [hsub]
  exact val2_pow_add_one_of_odd hY hn

lemma val2_one_of_odd_pred {X : ℕ} (hX : Odd X) (hXpos : 0 < X) :
    padicValNat 2 (X - 1) = 1 ∨ padicValNat 2 (X + 1) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : 2 ∣ X - 1 := by
    have : (X - 1) % 2 = 0 := by
      have : X % 2 = 1 := Nat.odd_iff.mp hX
      omega
    exact Nat.dvd_iff_mod_eq_zero.mpr this
  have h2 : 2 ∣ X + 1 := by
    have : (X + 1) % 2 = 0 := by
      have : X % 2 = 1 := Nat.odd_iff.mp hX
      omega
    exact Nat.dvd_iff_mod_eq_zero.mpr this
  have hne1 : X - 1 ≠ 0 ∨ X + 1 ≠ 0 := by omega
  -- among two consecutive even numbers, exactly one is divisible by 4
  have hmod4 : X % 4 = 1 ∨ X % 4 = 3 := by
    have : X % 2 = 1 := Nat.odd_iff.mp hX
    have : X % 4 < 4 := Nat.mod_lt _ (by decide)
    omega
  rcases hmod4 with h1' | h3
  · -- X ≡ 1 [MOD 4], so 4 ∣ X-1 and X+1 ≡ 2 [MOD 4], so v2(X+1)=1
    right
    have hne : X + 1 ≠ 0 := Nat.succ_ne_zero _
    have hdvd : 2 ∣ X + 1 := h2
    have hnot : ¬ 4 ∣ X + 1 := by
      intro hd
      have : (X + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
      omega
    have hle : 1 ≤ padicValNat 2 (X + 1) := (padicValNat_dvd_iff_le hne).mp hdvd
    have hnle : ¬ 2 ≤ padicValNat 2 (X + 1) := by
      intro h2le
      have : 2 ^ 2 ∣ X + 1 := (padicValNat_dvd_iff_le hne).mpr h2le
      exact hnot this
    omega
  · -- X ≡ 3 [MOD 4], so v2(X-1)=1
    left
    have hne : X - 1 ≠ 0 := by
      intro hz
      have : X = 1 := by omega
      subst this
      omega
    have hdvd : 2 ∣ X - 1 := h1
    have hnot : ¬ 4 ∣ X - 1 := by
      intro hd
      have : (X - 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
      omega
    have hle : 1 ≤ padicValNat 2 (X - 1) := (padicValNat_dvd_iff_le hne).mp hdvd
    have hnle : ¬ 2 ≤ padicValNat 2 (X - 1) := by
      intro h2le
      have : 2 ^ 2 ∣ X - 1 := (padicValNat_dvd_iff_le hne).mpr h2le
      exact hnot this
    omega

lemma val2_mul_pred_succ {X : ℕ} (hX : 2 ≤ X) :
    padicValNat 2 ((X - 1) * (X + 1)) =
      padicValNat 2 (X - 1) + padicValNat 2 (X + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne1 : X - 1 ≠ 0 := by omega
  have hne2 : X + 1 ≠ 0 := Nat.succ_ne_zero _
  exact padicValNat.mul hne1 hne2

lemma X_ge_two {X Y n : ℕ} (h : X ^ 2 = Y ^ n + 2) : 2 ≤ X := by
  have h2 : 2 ≤ X ^ 2 := by rw [h]; omega
  match X with
  | 0 => simp at h2
  | 1 => simp at h
  | X + 2 => omega

/-! ### Coprime odd parts multiply to `s * Φ` -/
