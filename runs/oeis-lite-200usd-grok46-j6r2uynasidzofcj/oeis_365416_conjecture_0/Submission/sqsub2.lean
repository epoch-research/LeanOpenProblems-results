import Mathlib

set_option linter.unusedVariables false

open Nat

/-! ### Geometric quotient for odd exponents -/

lemma odd_add_one_dvd_pow_add_one {x n : ℕ} (hn : Odd n) :
    x + 1 ∣ x ^ n + 1 := by
  simpa using hn.nat_add_dvd_pow_add_pow x 1

lemma geom_odd_mul {x n : ℕ} (hn : Odd n) :
    ((x ^ n + 1) / (x + 1)) * (x + 1) = x ^ n + 1 :=
  Nat.div_mul_cancel (odd_add_one_dvd_pow_add_one hn)

/-- For odd `n = 2k+1`, `d^2` divides `(d-1)^n + 1 - n d`. -/
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

/-- For odd `n`, `(x ^ n + 1) / (x + 1) ≡ n [MOD x + 1]`. -/
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


/-! ### Parity and 2-adic data for `X ^ 2 = Y ^ n + 2` -/

lemma sq_sub_two_X_odd {X Y n : ℕ} (hY : Odd Y) (h : X ^ 2 = Y ^ n + 2) : Odd X := by
  have hYn : Odd (Y ^ n) := Odd.pow hY
  have hodd : Odd (Y ^ n + 2) := by
    rw [Nat.odd_iff] at hYn ⊢
    omega
  have : Odd (X ^ 2) := by simpa [h] using hodd
  simpa [Nat.odd_pow_iff (by decide : (2 : ℕ) ≠ 0)] using this

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


/-! ### Size lemmas -/

lemma Y_ge_seven_of_sq_sub_two {X Y n : ℕ} (hY : Odd Y) (hn : Odd n)
    (hY1 : 1 < Y) (h : X ^ 2 = Y ^ n + 2) : 7 ≤ Y := by
  have h8 : Y % 8 = 7 := Y_mod_eight_of_sq_sub_two hY hn h
  have : Y % 8 < 8 := Nat.mod_lt _ (by decide)
  omega


lemma geom_quot_ge {Y n : ℕ} (hY : 2 ≤ Y) (hn : 3 ≤ n) (hodd : Odd n) :
    3 ≤ (Y ^ n + 1) / (Y + 1) := by
  have hdiv := odd_add_one_dvd_pow_add_one (x := Y) hodd
  have hpos : 0 < Y + 1 := Nat.succ_pos _
  have hYn : Y ^ 3 ≤ Y ^ n := Nat.pow_le_pow_right (by omega) hn
  have h3 : (Y + 1) * 3 ≤ Y ^ 3 + 1 := by
    have : (Y : ℤ) ^ 3 + 1 - 3 * ((Y : ℤ) + 1) = (Y : ℤ) ^ 3 - 3 * Y - 2 := by ring
    have : (0 : ℤ) ≤ (Y : ℤ) ^ 3 - 3 * Y - 2 := by
      nlinarith [sq_nonneg ((Y : ℤ) - 2), sq_nonneg (Y : ℤ)]
    have hcast : ((Y + 1) * 3 : ℤ) ≤ (Y ^ 3 + 1 : ℤ) := by
      have : (Y : ℤ) ^ 3 + 1 - 3 * ((Y : ℤ) + 1) ≥ 0 := by
        nlinarith [sq_nonneg ((Y : ℤ) - 1)]
      linarith
    exact_mod_cast hcast
  have : 3 * (Y + 1) ≤ Y ^ n + 1 := by
    rw [mul_comm]
    exact le_trans h3 (Nat.add_le_add_right hYn 1)
  exact (Nat.le_div_iff_mul_le hpos).mpr this

lemma four_s_succ_lt_cube {s : ℕ} (hs : 1 ≤ s) :
    4 * s * (s + 1) - 1 < (8 * s - 1) ^ 3 := by
  have hs8 : 1 ≤ 8 * s := by omega
  have hpos : 1 ≤ 4 * s * (s + 1) := by nlinarith
  have hL : ((4 * s * (s + 1) - 1 : ℕ) : ℤ) = 4 * (s : ℤ) * ((s : ℤ) + 1) - 1 := by
    rw [Nat.cast_sub hpos]; push_cast; rfl
  have hR : ((8 * s - 1 : ℕ) : ℤ) = 8 * (s : ℤ) - 1 := by
    rw [Nat.cast_sub hs8]; push_cast; rfl
  have hZ : ((4 * s * (s + 1) - 1 : ℕ) : ℤ) < ((8 * s - 1 : ℕ) : ℤ) ^ 3 := by
    rw [hL, hR]
    have hexp : (8 * (s : ℤ) - 1) ^ 3 =
        512 * (s : ℤ) ^ 3 - 192 * (s : ℤ) ^ 2 + 24 * (s : ℤ) - 1 := by ring
    have hr : 4 * (s : ℤ) * ((s : ℤ) + 1) - 1 =
        4 * (s : ℤ) ^ 2 + 4 * (s : ℤ) - 1 := by ring
    rw [hexp, hr]
    nlinarith [sq_nonneg (s : ℤ)]
  exact_mod_cast hZ


lemma four_s_pred_lt_cube {s : ℕ} (hs : 3 ≤ s) :
    4 * s * (s - 1) - 1 < (8 * s - 1) ^ 3 :=
  lt_of_le_of_lt (by
    have : s - 1 ≤ s + 1 := by omega
    have : 4 * s * (s - 1) ≤ 4 * s * (s + 1) := Nat.mul_le_mul_left _ this
    omega) (four_s_succ_lt_cube (by omega))


lemma two_pow_nat_cube_gt {α : ℕ} (hα : 3 ≤ α) :
    2 ^ (2 * α - 2) + 2 ^ α < (2 ^ α - 1) ^ 3 := by
  have h8 : 8 ≤ 2 ^ α := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ α := Nat.pow_le_pow_right (by decide) hα
  have hposR : 1 ≤ 2 ^ α := Nat.one_le_pow _ _ (by decide)
  have hL : ((2 ^ (2 * α - 2) + 2 ^ α : ℕ) : ℤ) =
      (2 : ℤ) ^ (2 * α - 2) + (2 : ℤ) ^ α := by push_cast; rfl
  have hR : ((2 ^ α - 1 : ℕ) : ℤ) = (2 : ℤ) ^ α - 1 := by
    rw [Nat.cast_sub hposR]; simp [Nat.cast_pow]
  have hZ : ((2 ^ (2 * α - 2) + 2 ^ α : ℕ) : ℤ) < ((2 ^ α - 1 : ℕ) : ℤ) ^ 3 := by
    rw [hL, hR]
    set t := (2 : ℤ) ^ α with ht
    have ht8 : (8 : ℤ) ≤ t := by
      have : (8 : ℤ) ≤ (2 : ℤ) ^ α := by
        exact_mod_cast h8
      simpa [t] using this
    have h4L : 4 * ((2 : ℤ) ^ (2 * α - 2) + t) = t ^ 2 + 4 * t := by
      have hsum : 4 * ((2 : ℤ) ^ (2 * α - 2) + t) =
          4 * (2 : ℤ) ^ (2 * α - 2) + 4 * t := by ring
      have hpow : 4 * (2 : ℤ) ^ (2 * α - 2) = (2 : ℤ) ^ (2 * α) := by
        have heq : (2 * α - 2) + 2 = 2 * α := by omega
        calc
          4 * (2 : ℤ) ^ (2 * α - 2)
              = (2 : ℤ) ^ 2 * (2 : ℤ) ^ (2 * α - 2) := by norm_num
          _ = (2 : ℤ) ^ (2 + (2 * α - 2)) := (pow_add (2 : ℤ) 2 (2 * α - 2)).symm
          _ = (2 : ℤ) ^ ((2 * α - 2) + 2) := by rw [add_comm]
          _ = (2 : ℤ) ^ (2 * α) := by rw [heq]
      have ht2 : (2 : ℤ) ^ (2 * α) = t ^ 2 := by
        rw [ht, ← pow_mul, mul_comm]
      rw [hsum, hpow, ht2]
    have hexp : 4 * (t - 1) ^ 3 = 4 * t ^ 3 - 12 * t ^ 2 + 12 * t - 4 := by ring
    have hdiff : (0 : ℤ) < 4 * (t - 1) ^ 3 - (t ^ 2 + 4 * t) := by
      have : 4 * (t - 1) ^ 3 - (t ^ 2 + 4 * t) = 4 * t ^ 3 - 13 * t ^ 2 + 8 * t - 4 := by
        ring
      rw [this]
      have : 4 * t ^ 3 - 13 * t ^ 2 + 8 * t - 4 ≥ 19 * t ^ 2 + 8 * t - 4 := by
        nlinarith
      nlinarith [sq_nonneg t]
    have : 4 * ((2 : ℤ) ^ (2 * α - 2) + t) < 4 * (t - 1) ^ 3 := by
      linarith
    have h4 : (0 : ℤ) < 4 := by decide
    exact lt_of_mul_lt_mul_left this h4.le
  exact_mod_cast hZ



/-! ### 2-adic splitting of `X ± 1` -/

lemma padicValNat_two_mul_odd {k : ℕ} (hk : k ≠ 0) (hodd : Odd k) :
    padicValNat 2 (2 * k) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ 2 ∣ k := mt even_iff_two_dvd.mpr (Nat.not_even_iff_odd.mpr hodd)
  rw [padicValNat.mul (by decide : (2 : ℕ) ≠ 0) hk, padicValNat_self,
    padicValNat.eq_zero_of_not_dvd hnot]

lemma val2_one_of_odd_pred_or_succ {X : ℕ} (hX : Odd X) (hXpos : 0 < X) :
    padicValNat 2 (X - 1) = 1 ∨ padicValNat 2 (X + 1) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hX
  have hX1 : X - 1 = 2 * k := by omega
  have hX2 : X + 1 = 2 * (k + 1) := by omega
  rcases Nat.mod_two_eq_zero_or_one k with hke | hko
  · right
    have hodd : Odd (k + 1) := by rw [Nat.odd_iff]; omega
    have hk1 : k + 1 ≠ 0 := Nat.succ_ne_zero _
    rw [hX2, padicValNat_two_mul_odd hk1 hodd]
  · left
    have hodd : Odd k := by rw [Nat.odd_iff]; exact hko
    have hk0 : k ≠ 0 := by intro hz; subst hz; omega
    rw [hX1, padicValNat_two_mul_odd hk0 hodd]

lemma val2_mul_Xsq_sub_one {X : ℕ} (hX : 2 ≤ X) :
    padicValNat 2 (X ^ 2 - 1) =
      padicValNat 2 (X - 1) + padicValNat 2 (X + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : X ^ 2 - 1 = (X - 1) * (X + 1) := by
    have h1 : X ^ 2 - 1 ^ 2 = (X + 1) * (X - 1) := Nat.sq_sub_sq X 1
    simpa [mul_comm] using h1
  have h1 : X - 1 ≠ 0 := by omega
  have h2 : X + 1 ≠ 0 := Nat.succ_ne_zero _
  rw [hfac, padicValNat.mul h1 h2]

lemma Y_eq_two_pow_mul_s (Y : ℕ) :
    Y + 1 = 2 ^ padicValNat 2 (Y + 1) * ((Y + 1) / 2 ^ padicValNat 2 (Y + 1)) :=
  (Nat.mul_div_cancel' pow_padicValNat_dvd).symm


lemma two_pow_s_cube_gt {α s : ℕ} (hα : 3 ≤ α) (hs : 1 ≤ s) :
    2 ^ (2 * α - 2) * s ^ 2 + 2 ^ α * s < (2 ^ α * s - 1) ^ 3 := by
  have h8 : 8 ≤ 2 ^ α := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ α := Nat.pow_le_pow_right (by decide) hα
  have hpos : 1 ≤ 2 ^ α * s := by
    have : 1 ≤ 2 ^ α := Nat.one_le_pow _ _ (by decide)
    nlinarith
  have hL : ((2 ^ (2 * α - 2) * s ^ 2 + 2 ^ α * s : ℕ) : ℤ) =
      (2 : ℤ) ^ (2 * α - 2) * (s : ℤ) ^ 2 + (2 : ℤ) ^ α * s := by
    push_cast; rfl
  have hR : ((2 ^ α * s - 1 : ℕ) : ℤ) = (2 : ℤ) ^ α * s - 1 := by
    rw [Nat.cast_sub hpos]; push_cast; rfl
  have hZ : ((2 ^ (2 * α - 2) * s ^ 2 + 2 ^ α * s : ℕ) : ℤ) <
      ((2 ^ α * s - 1 : ℕ) : ℤ) ^ 3 := by
    rw [hL, hR]
    set t := (2 : ℤ) ^ α
    set u := (s : ℤ)
    have ht8 : (8 : ℤ) ≤ t := by
      have : (8 : ℤ) ≤ (2 : ℤ) ^ α := by exact_mod_cast h8
      simpa [t] using this
    have hu : (1 : ℤ) ≤ u := by
      have : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
      simpa [u] using this
    have hpow : 4 * (2 : ℤ) ^ (2 * α - 2) = t ^ 2 := by
      have heq : (2 * α - 2) + 2 = 2 * α := by omega
      have ht2 : (2 : ℤ) ^ (2 * α) = t ^ 2 := by
        simp [t, ← pow_mul, mul_comm]
      calc
        4 * (2 : ℤ) ^ (2 * α - 2)
            = (2 : ℤ) ^ 2 * (2 : ℤ) ^ (2 * α - 2) := by norm_num
        _ = (2 : ℤ) ^ (2 + (2 * α - 2)) := (pow_add (2 : ℤ) 2 (2 * α - 2)).symm
        _ = (2 : ℤ) ^ ((2 * α - 2) + 2) := by rw [add_comm]
        _ = (2 : ℤ) ^ (2 * α) := by rw [heq]
        _ = t ^ 2 := ht2
    have hcmp : 4 * ((2 : ℤ) ^ (2 * α - 2) * u ^ 2 + t * u) < 4 * (t * u - 1) ^ 3 := by
      have lhs : 4 * ((2 : ℤ) ^ (2 * α - 2) * u ^ 2 + t * u) =
          t ^ 2 * u ^ 2 + 4 * t * u := by
        calc
          4 * ((2 : ℤ) ^ (2 * α - 2) * u ^ 2 + t * u)
              = 4 * (2 : ℤ) ^ (2 * α - 2) * u ^ 2 + 4 * t * u := by ring
          _ = t ^ 2 * u ^ 2 + 4 * t * u := by rw [hpow]
      rw [lhs]
      have hexp : 4 * (t * u - 1) ^ 3 =
          4 * t ^ 3 * u ^ 3 - 12 * t ^ 2 * u ^ 2 + 12 * t * u - 4 := by ring
      rw [hexp]
      have hge : 4 * t ^ 3 * u ^ 3 - 12 * t ^ 2 * u ^ 2 + 12 * t * u - 4 -
          (t ^ 2 * u ^ 2 + 4 * t * u) ≥ 19 * t ^ 2 * u ^ 2 + 8 * t * u - 4 := by
        have ht3 : t ^ 3 ≥ 8 * t ^ 2 := by
          nlinarith [sq_nonneg t]
        have hu3 : u ^ 3 ≥ u ^ 2 := by
          nlinarith [sq_nonneg u]
        have : 4 * t ^ 3 * u ^ 3 ≥ 32 * t ^ 2 * u ^ 2 := by
          nlinarith
        nlinarith
      nlinarith [sq_nonneg t, sq_nonneg u]
    have h4 : (0 : ℤ) < 4 := by decide
    exact lt_of_mul_lt_mul_left hcmp h4.le
  exact_mod_cast hZ



/-! ### The ring ℤ√2 -/

open Zsqrtd Int

abbrev Zsqrt2 := ℤ√(2 : ℤ)

namespace Zsqrt2

lemma two_not_sq : ∀ n : ℤ, (2 : ℤ) ≠ n * n := by
  intro n h
  have hsq : n ^ 2 = 2 := by rw [sq]; exact h.symm
  have habs : |n| ≤ 1 := by
    have : n ^ 2 < (2 : ℤ) ^ 2 := by nlinarith
    have : |n| < 2 := lt_of_pow_lt_pow_left₀ 2 (by decide : (0 : ℤ) ≤ 2) (by rwa [sq_abs])
    have : 0 ≤ |n| := abs_nonneg _
    omega
  have : |n| = 0 ∨ |n| = 1 := by
    have : 0 ≤ |n| := abs_nonneg _
    omega
  rcases this with h0 | h1
  · rw [abs_eq_zero] at h0; subst h0; norm_num at hsq
  · rcases eq_or_eq_neg_of_abs_eq h1 with rfl | rfl <;> norm_num at hsq

lemma norm_eq (z : Zsqrt2) : z.norm = z.re ^ 2 - 2 * z.im ^ 2 := by
  rw [norm_def]; ring

lemma norm_eq_zero_iff' (z : Zsqrt2) : z.norm = 0 ↔ z = 0 :=
  Zsqrtd.norm_eq_zero two_not_sq z

lemma int_abs_sub_mul_round (a N : ℤ) (hN : N ≠ 0) :
    |a - round ((a : ℚ) / N) * N| * 2 ≤ |N| := by
  have hNq : (N : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hN
  set q := round ((a : ℚ) / N)
  have hle : |((a : ℚ) / N) - (q : ℚ)| ≤ 1 / 2 := abs_sub_round _
  have habs : |((a : ℚ) / N) - (q : ℚ)| * |(N : ℚ)| = |(a : ℚ) - (q : ℚ) * N| := by
    calc
      |((a : ℚ) / N) - (q : ℚ)| * |(N : ℚ)|
        = |(((a : ℚ) / N) - (q : ℚ)) * N| := (abs_mul _ _).symm
      _ = |(a : ℚ) - (q : ℚ) * N| := by
            rw [sub_mul, div_mul_cancel₀ _ hNq]
  have hbound : |(a : ℚ) - (q : ℚ) * N| ≤ |(N : ℚ)| / 2 := by
    rw [← habs]
    have := mul_le_mul_of_nonneg_right hle (abs_nonneg (N : ℚ))
    linarith
  have hcast : ((a - q * N : ℤ) : ℚ) = (a : ℚ) - (q : ℚ) * N := by push_cast; rfl
  have : ((|a - q * N| * 2 : ℤ) : ℚ) ≤ ((|N| : ℤ) : ℚ) := by
    rw [Int.cast_mul, Int.cast_abs, Int.cast_two, hcast, Int.cast_abs]
    linarith
  exact_mod_cast this

noncomputable instance : Div Zsqrt2 :=
  ⟨fun x y =>
    ⟨round ((x * star y).re / (y.norm : ℚ)),
     round ((x * star y).im / (y.norm : ℚ))⟩⟩

lemma div_def (x y : Zsqrt2) :
    x / y = ⟨round (((x * star y).re : ℚ) / (y.norm : ℚ)),
             round (((x * star y).im : ℚ) / (y.norm : ℚ))⟩ := rfl

noncomputable instance : Mod Zsqrt2 := ⟨fun x y => x - y * (x / y)⟩

lemma mod_def (x y : Zsqrt2) : x % y = x - y * (x / y) := rfl

lemma rem_mul_star (x y : Zsqrt2) :
    (x % y) * star y = x * star y - (x / y) * (y.norm : Zsqrt2) := by
  rw [mod_def, sub_mul, norm_eq_mul_conj]
  ring

lemma rem_norm_mul (x y : Zsqrt2) :
    (x % y).norm * y.norm = (x * star y - (x / y) * (y.norm : Zsqrt2)).norm := by
  have := rem_mul_star x y
  rw [← this, Zsqrtd.norm_mul, Zsqrtd.norm_conj]

lemma mul_intCast_re (z : Zsqrt2) (n : ℤ) :
    (z * (n : Zsqrt2)).re = z.re * n := by
  simp [Zsqrtd.re_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast]

lemma mul_intCast_im (z : Zsqrt2) (n : ℤ) :
    (z * (n : Zsqrt2)).im = z.im * n := by
  simp [Zsqrtd.im_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast]

lemma rem_norm_expand (x y : Zsqrt2) :
    (x * star y - (x / y) * (y.norm : Zsqrt2)).norm =
      ((x * star y).re - (x / y).re * y.norm) ^ 2 -
      2 * ((x * star y).im - (x / y).im * y.norm) ^ 2 := by
  rw [norm_eq, re_sub, im_sub, mul_intCast_re, mul_intCast_im]

lemma four_mul_abs_form {A B N : ℤ} (hA : |A| * 2 ≤ |N|) (hB : |B| * 2 ≤ |N|) :
    4 * |A ^ 2 - 2 * B ^ 2| ≤ 3 * N ^ 2 := by
  have hA4 : 4 * A ^ 2 ≤ N ^ 2 := by
    have : |2 * A| ≤ |N| := by
      rw [abs_mul, abs_two, mul_comm]
      exact hA
    have : (2 * A) ^ 2 ≤ N ^ 2 := sq_le_sq.mpr this
    nlinarith
  have hB4 : 4 * B ^ 2 ≤ N ^ 2 := by
    have : |2 * B| ≤ |N| := by
      rw [abs_mul, abs_two, mul_comm]
      exact hB
    have : (2 * B) ^ 2 ≤ N ^ 2 := sq_le_sq.mpr this
    nlinarith
  have hsum : 4 * (A ^ 2 + 2 * B ^ 2) ≤ 3 * N ^ 2 := by nlinarith
  have hle : |A ^ 2 - 2 * B ^ 2| ≤ A ^ 2 + 2 * B ^ 2 :=
    abs_sub_le_iff.mpr ⟨by nlinarith [sq_nonneg A, sq_nonneg B],
      by nlinarith [sq_nonneg A, sq_nonneg B]⟩
  nlinarith

lemma abs_norm_mod_lt (x : Zsqrt2) {y : Zsqrt2} (hy : y ≠ 0) :
    |(x % y).norm| < |y.norm| := by
  have hNne : y.norm ≠ 0 := by
    intro h0
    exact hy ((norm_eq_zero_iff' y).mp h0)
  set N := y.norm
  set α := x * star y
  set q := x / y
  have hre : |α.re - q.re * N| * 2 ≤ |N| := by
    change |α.re - round ((α.re : ℚ) / N) * N| * 2 ≤ |N|
    exact int_abs_sub_mul_round α.re N hNne
  have him : |α.im - q.im * N| * 2 ≤ |N| := by
    change |α.im - round ((α.im : ℚ) / N) * N| * 2 ≤ |N|
    exact int_abs_sub_mul_round α.im N hNne
  have h4 : 4 * |(α.re - q.re * N) ^ 2 - 2 * (α.im - q.im * N) ^ 2| ≤ 3 * N ^ 2 :=
    four_mul_abs_form hre him
  have hmul : (x % y).norm * N = (α - q * (N : Zsqrt2)).norm := rem_norm_mul x y
  have hexp : (α - q * (N : Zsqrt2)).norm =
      (α.re - q.re * N) ^ 2 - 2 * (α.im - q.im * N) ^ 2 := rem_norm_expand x y
  have : 4 * |(x % y).norm * N| ≤ 3 * N ^ 2 := by
    rw [hmul, hexp]; exact h4
  have hassoc : 4 * |(x % y).norm * N| = 4 * |(x % y).norm| * |N| := by
    rw [abs_mul, mul_assoc]
  rw [hassoc] at this
  have hNabs : 0 < |N| := abs_pos.mpr hNne
  have hNsq : N ^ 2 = |N| * |N| := by rw [← sq_abs, sq]
  have hle : 4 * |(x % y).norm| ≤ 3 * |N| := by
    have hmul' : 4 * |(x % y).norm| * |N| ≤ 3 * (|N| * |N|) := by
      rwa [hNsq] at this
    have hmul'' : 4 * |(x % y).norm| * |N| ≤ (3 * |N|) * |N| := by
      convert hmul' using 1; ring
    exact _root_.le_of_mul_le_mul_right hmul'' hNabs
  nlinarith

lemma natAbs_norm_mod_lt (x : Zsqrt2) {y : Zsqrt2} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have h := abs_norm_mod_lt x hy
  have e1 : ((x % y).norm.natAbs : ℤ) = |(x % y).norm| := Int.natCast_natAbs _
  have e2 : (y.norm.natAbs : ℤ) = |y.norm| := Int.natCast_natAbs _
  have : ((x % y).norm.natAbs : ℤ) < (y.norm.natAbs : ℤ) := by
    rwa [e1, e2]
  exact_mod_cast this

lemma natAbs_norm_mul_left (x : Zsqrt2) {y : Zsqrt2} (hy : y ≠ 0) :
    x.norm.natAbs ≤ (x * y).norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have : 1 ≤ y.norm.natAbs := by
    have : y.norm ≠ 0 := by
      intro h0
      exact hy ((norm_eq_zero_iff' y).mp h0)
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr this)
  exact Nat.le_mul_of_pos_right _ this

noncomputable instance : EuclideanDomain Zsqrt2 :=
  { inferInstanceAs (CommRing Zsqrt2),
    inferInstanceAs (Nontrivial Zsqrt2) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      simp [div_def, Zsqrtd.norm_zero]
      rfl
    quotient_mul_add_remainder_eq := fun _ _ => by
      simp [mod_def]
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge (natAbs_norm_mul_left a hb0) }

def eps : Zsqrt2 := ⟨1, 1⟩

lemma eps_norm : (eps : Zsqrt2).norm = -1 := by
  simp [eps, norm_eq]

lemma eps_mul_conj : eps * ⟨-1, 1⟩ = 1 := by
  ext <;> simp [eps]

lemma isUnit_eps : IsUnit (eps : Zsqrt2) :=
  ⟨⟨eps, ⟨-1, 1⟩, eps_mul_conj, by ext <;> simp [eps]⟩, rfl⟩

def epsInv : Zsqrt2 := ⟨-1, 1⟩

lemma eps_mul_epsInv : eps * epsInv = 1 := eps_mul_conj

lemma epsInv_mul_eps : epsInv * eps = 1 := by
  rw [mul_comm]; exact eps_mul_epsInv

lemma eps_sq : (eps : Zsqrt2) ^ 2 = ⟨3, 2⟩ := by
  ext <;> simp [eps, pow_two]

lemma two_not_isSquare : ¬ IsSquare (2 : ℤ) := by
  rintro ⟨k, hk⟩
  exact two_not_sq k hk

def fund : Pell.Solution₁ 2 := Pell.Solution₁.mk 3 2 (by norm_num)

lemma fund_x : fund.x = 3 := Pell.Solution₁.x_mk 3 2 (by norm_num)
lemma fund_y : fund.y = 2 := Pell.Solution₁.y_mk 3 2 (by norm_num)

lemma fund_isFundamental : Pell.IsFundamental fund := by
  refine ⟨?hx, ?hy, ?min⟩
  · rw [fund_x]; norm_num
  · rw [fund_y]; norm_num
  · intro b hb
    have hprop := b.prop
    have hx2 : (2 : ℤ) ≤ b.x := by linarith
    have hb3 : (3 : ℤ) ≤ b.x := by
      by_contra h
      have hxeq : b.x = 2 := by omega
      rw [hxeq] at hprop
      have : (2 : ℤ) * b.y ^ 2 = 3 := by linarith
      have hy0 : b.y ^ 2 = 0 ∨ b.y ^ 2 = 1 ∨ (4 : ℤ) ≤ b.y ^ 2 := by
        have : 0 ≤ b.y ^ 2 := sq_nonneg _
        have : b.y ^ 2 ≤ 1 ∨ 4 ≤ b.y ^ 2 := by
          have habs : |b.y| ≤ 1 ∨ 2 ≤ |b.y| := by omega
          rcases habs with h1 | h2
          · left; have := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1); simpa using this
          · right
            have : (2 : ℤ) ^ 2 ≤ |b.y| ^ 2 := pow_le_pow_left₀ (by omega) h2 2
            simpa [sq_abs] using this
        omega
      rcases hy0 with h0 | h1 | h4 <;> linarith
    simpa [fund_x] using hb3

lemma fund_coe : (fund : Zsqrt2) = ⟨3, 2⟩ := by
  simp [fund, Pell.Solution₁.coe_mk]

lemma fund_eq_eps_sq : (fund : Zsqrt2) = eps ^ 2 :=
  fund_coe.trans eps_sq.symm

lemma isUnit_of_natAbs_norm_one (z : Zsqrt2) (h : z.norm.natAbs = 1) : IsUnit z :=
  Zsqrtd.norm_eq_one_iff.mp h

lemma natAbs_norm_eq_one_of_isUnit {z : Zsqrt2} (h : IsUnit z) : z.norm.natAbs = 1 :=
  Zsqrtd.norm_eq_one_iff.mpr h

lemma norm_eq_one_or_neg_one_of_isUnit {z : Zsqrt2} (h : IsUnit z) :
    z.norm = 1 ∨ z.norm = -1 :=
  Int.natAbs_eq_iff.mp (natAbs_norm_eq_one_of_isUnit h)

lemma eq_fund_zpow_of_norm_one {z : Zsqrt2} (h : z.norm = 1) :
    ∃ k : ℤ, z = ((fund ^ k : Pell.Solution₁ 2) : Zsqrt2) ∨
      z = -((fund ^ k : Pell.Solution₁ 2) : Zsqrt2) := by
  let a : Pell.Solution₁ 2 :=
    Pell.Solution₁.mk z.re z.im (by
      have : z.re ^ 2 - 2 * z.im ^ 2 = 1 := by rw [← norm_eq, h]
      exact this)
  have ha : (a : Zsqrt2) = z := by
    ext <;> simp [a, Pell.Solution₁.coe_mk]
  obtain ⟨k, hk⟩ := fund_isFundamental.eq_zpow_or_neg_zpow a
  refine ⟨k, ?_⟩
  rcases hk with hk | hk
  · left; rw [← ha, hk]
  · right; rw [← ha, hk]; rfl

lemma epsInv_sq : (epsInv : Zsqrt2) ^ 2 = ⟨3, -2⟩ := by
  ext <;> simp [epsInv, pow_two]

def ω : Zsqrt2 := ⟨0, 1⟩

lemma ω_sq : (ω * ω : Zsqrt2) = (2 : Zsqrt2) := by
  ext <;> simp [ω]

lemma norm_ω : ω.norm = -2 := by simp [ω, norm_eq]

def plus (y : ℤ) : Zsqrt2 := ⟨y, 1⟩
def minus (y : ℤ) : Zsqrt2 := ⟨y, -1⟩

lemma plus_mul_minus (y : ℤ) : plus y * minus y = ⟨y ^ 2 - 2, 0⟩ := by
  ext
  · simp [plus, minus]; ring
  · simp [plus, minus]

lemma intCast_mk (n : ℤ) : (n : Zsqrt2) = ⟨n, 0⟩ := by
  ext <;> simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]

lemma plus_mul_minus' (y : ℤ) : plus y * minus y = (y ^ 2 - 2 : ℤ) := by
  rw [plus_mul_minus, intCast_mk]

lemma plus_sub_minus (y : ℤ) : plus y - minus y = ⟨0, 2⟩ := by
  ext <;> simp [plus, minus]

lemma two_mul_ω : (2 : Zsqrt2) * ω = ⟨0, 2⟩ := by
  ext <;> simp [ω]

lemma plus_sub_minus' (y : ℤ) : plus y - minus y = (2 : Zsqrt2) * ω := by
  rw [plus_sub_minus, two_mul_ω]

lemma star_plus (y : ℤ) : star (plus y) = minus y := by
  ext <;> simp [plus, minus]

lemma norm_plus (y : ℤ) : (plus y).norm = y ^ 2 - 2 := by
  simp [plus, norm_eq]

lemma plus_ne_zero {y : ℤ} (h : y ^ 2 ≠ 2) : plus y ≠ 0 := by
  intro hz
  have : (plus y).norm = 0 := by rw [hz]; simp [norm_def]
  rw [norm_plus] at this
  exact h (by linarith)

lemma omega_dvd_plus_iff (y : ℤ) : ω ∣ plus y ↔ Even y := by
  constructor
  · intro ⟨z, hz⟩
    have hre : (plus y).re = (ω * z).re := congrArg Zsqrtd.re hz
    have : y = 2 * z.im := by
      simp [plus, ω] at hre
      linarith
    refine ⟨z.im, ?_⟩
    rw [this, two_mul]
  · intro ⟨k, hk⟩
    refine ⟨⟨1, k⟩, ?_⟩
    ext
    · simp [plus, ω, hk]; ring
    · simp [plus, ω]

lemma odd_not_omega_dvd_plus {y : ℤ} (hy : Odd y) : ¬ ω ∣ plus y := by
  rw [omega_dvd_plus_iff]
  exact Int.not_even_iff_odd.mpr hy

lemma not_isUnit_ω : ¬ IsUnit ω := by
  intro hu
  have : ω.norm.natAbs = 1 := natAbs_norm_eq_one_of_isUnit hu
  rw [norm_ω] at this
  norm_num at this

lemma omega_irreducible : Irreducible ω := by
  refine ⟨not_isUnit_ω, ?_⟩
  intro a b hab
  have hn : (a * b).norm = -2 := by rw [← hab, norm_ω]
  rw [Zsqrtd.norm_mul] at hn
  have hdiv : a.norm ∣ 2 := ⟨-b.norm, by linarith⟩
  have habs : a.norm.natAbs ∣ 2 := Int.natAbs_dvd_natAbs.mpr hdiv
  have : a.norm.natAbs = 1 ∨ a.norm.natAbs = 2 := by
    have := Nat.le_of_dvd (by decide : (0 : ℕ) < 2) habs
    interval_cases a.norm.natAbs <;> tauto
  rcases this with h | h
  · left; exact isUnit_of_natAbs_norm_one a h
  · right
    have : b.norm.natAbs = 1 := by
      have : (a.norm * b.norm).natAbs = 2 := by rw [hn]; norm_num
      rw [Int.natAbs_mul, h] at this
      omega
    exact isUnit_of_natAbs_norm_one b this

lemma omega_prime : Prime ω := Irreducible.prime omega_irreducible

lemma two_eq_omega_sq : (2 : Zsqrt2) = ω * ω := ω_sq.symm

lemma isCoprime_plus_minus {y : ℤ} (hy : Odd y) (hne : y ^ 2 ≠ 2) :
    IsCoprime (plus y) (minus y) := by
  refine isCoprime_of_irreducible_dvd ?_ ?_
  · exact not_and_of_not_left _ (plus_ne_zero hne)
  · intro π hπ hπplus hπminus
    have hdiff : π ∣ plus y - minus y := dvd_sub hπplus hπminus
    rw [plus_sub_minus'] at hdiff
    have hω3 : π ∣ ω ^ 3 := by
      have : (2 : Zsqrt2) * ω = ω ^ 3 := by
        rw [two_eq_omega_sq, pow_three]; ring
      rwa [this] at hdiff
    have hπω : π ∣ ω :=
      (Irreducible.prime hπ).dvd_of_dvd_pow (n := 3) hω3
    have : Associated π ω :=
      (Irreducible.dvd_irreducible_iff_associated hπ omega_irreducible).mp hπω
    exact odd_not_omega_dvd_plus hy (this.symm.dvd.trans hπplus)

lemma plus_associated_pow {y : ℤ} {p n : ℕ} (hy : Odd y)
    (h : (y ^ 2 - 2 : ℤ) = (p : ℤ) ^ n) :
    ∃ d : Zsqrt2, Associated (d ^ n) (plus y) := by
  have hne : y ^ 2 ≠ 2 := by
    intro hf
    have : (p : ℤ) ^ n = 0 := by linarith
    cases n with
    | zero => norm_num at this
    | succ n =>
      have : (p : ℤ) = 0 := pow_eq_zero this
      exact two_not_sq y (by rw [← sq]; exact hf.symm)
  have hab : IsCoprime (plus y) (minus y) := isCoprime_plus_minus hy hne
  have hmul : plus y * minus y = ((p : ℤ) : Zsqrt2) ^ n := by
    rw [plus_mul_minus', h, Int.cast_pow]
  exact exists_associated_pow_of_mul_eq_pow' hab hmul

lemma s_dvd_im_pow (r s : ℤ) : ∀ n : ℕ, s ∣ ((⟨r, s⟩ : Zsqrt2) ^ n).im
  | 0 => by simp
  | n + 1 => by
    have ih := s_dvd_im_pow r s n
    have : ((⟨r, s⟩ : Zsqrt2) ^ (n + 1)).im =
        r * ((⟨r, s⟩ : Zsqrt2) ^ n).im + s * ((⟨r, s⟩ : Zsqrt2) ^ n).re := by
      rw [pow_succ, im_mul]; simp; ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_right _ _)

lemma norm_pow (z : Zsqrt2) : ∀ n : ℕ, (z ^ n).norm = z.norm ^ n
  | 0 => by simp [norm_def]
  | n + 1 => by rw [pow_succ, pow_succ, Zsqrtd.norm_mul, norm_pow]

lemma s_dvd_one_of_plus_eq_pow {y r s : ℤ} {n : ℕ}
    (h : plus y = (⟨r, s⟩ : Zsqrt2) ^ n ∨ plus y = -((⟨r, s⟩ : Zsqrt2) ^ n)) :
    s ∣ 1 := by
  have him : (plus y).im = 1 := rfl
  have hs := s_dvd_im_pow r s n
  rcases h with h | h
  · rw [h] at him; rwa [← him]
  · have : (-((⟨r, s⟩ : Zsqrt2) ^ n)).im = -((⟨r, s⟩ : Zsqrt2) ^ n).im := by simp
    rw [h, this] at him
    have : s ∣ -((⟨r, s⟩ : Zsqrt2) ^ n).im := hs.neg_right
    rwa [him] at this

end Zsqrt2

namespace Zsqrt2


def UV2 (a : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let u := (UV2 a n).1
    let v := (UV2 a n).2
    (a * u + 2 * v, u + a * v)

def U2 (a : ℤ) (n : ℕ) : ℤ := (UV2 a n).1
def V2 (a : ℤ) (n : ℕ) : ℤ := (UV2 a n).2

lemma U2_zero (a : ℤ) : U2 a 0 = 1 := rfl
lemma V2_zero (a : ℤ) : V2 a 0 = 0 := rfl
lemma U2_succ (a : ℤ) (n : ℕ) : U2 a (n + 1) = a * U2 a n + 2 * V2 a n := rfl
lemma V2_succ (a : ℤ) (n : ℕ) : V2 a (n + 1) = U2 a n + a * V2 a n := rfl

lemma pow_eq_U2_V2 (a : ℤ) : ∀ n : ℕ,
    (⟨a, 1⟩ : Zsqrt2) ^ n = ⟨U2 a n, V2 a n⟩
  | 0 => by
    ext
    · simp [U2_zero]
    · simp [V2_zero]
  | n + 1 => by
    rw [pow_succ, pow_eq_U2_V2 a n, U2_succ, V2_succ]
    ext
    · simp; ring
    · simp; ring

lemma V2_one (a : ℤ) : V2 a 1 = 1 := by simp [V2_succ, U2_zero, V2_zero]
lemma U2_one (a : ℤ) : U2 a 1 = a := by simp [U2_succ, U2_zero, V2_zero]
lemma V2_two (a : ℤ) : V2 a 2 = 2 * a := by
  rw [V2_succ, U2_one, V2_one]; ring
lemma U2_two (a : ℤ) : U2 a 2 = a ^ 2 + 2 := by
  rw [U2_succ, U2_one, V2_one]; ring
lemma V2_three (a : ℤ) : V2 a 3 = 3 * a ^ 2 + 2 := by
  rw [V2_succ, U2_two, V2_two]; ring

lemma V2_succ2 (a : ℤ) (n : ℕ) :
    V2 a (n + 2) = 2 * a * V2 a (n + 1) - (a ^ 2 - 2) * V2 a n := by
  rw [V2_succ, U2_succ, V2_succ]
  ring

lemma U2_V2_norm (a : ℤ) : ∀ n : ℕ,
    U2 a n ^ 2 - 2 * V2 a n ^ 2 = (a ^ 2 - 2) ^ n
  | 0 => by simp [U2_zero, V2_zero]
  | n + 1 => by
    have ih := U2_V2_norm a n
    calc
      U2 a (n + 1) ^ 2 - 2 * V2 a (n + 1) ^ 2
        = (a * U2 a n + 2 * V2 a n) ^ 2 - 2 * (U2 a n + a * V2 a n) ^ 2 := by
          rw [U2_succ, V2_succ]
      _ = (a ^ 2 - 2) * (U2 a n ^ 2 - 2 * V2 a n ^ 2) := by ring
      _ = (a ^ 2 - 2) * (a ^ 2 - 2) ^ n := by rw [ih]
      _ = (a ^ 2 - 2) ^ (n + 1) := (pow_succ' _ _).symm

lemma V2_zero_of_a (n : ℕ) : V2 0 n = if Even n then 0 else (2 : ℤ) ^ (n / 2) := by
  sorry

lemma V2_ne_one_of_abs_ge_two {a : ℤ} (ha : 2 ≤ |a|) :
    ∀ n : ℕ, 2 ≤ n → |V2 a n| ≠ 1 := by
  intro n hn
  have h2 : |V2 a 2| = 2 * |a| := by
    rw [V2_two, abs_mul, abs_two]
  have h2gt : 2 < |V2 a 2| := by
    have : 4 ≤ 2 * |a| := by nlinarith
    omega
  match n with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | n + 3 =>
    have h3 : |V2 a 3| = 3 * a ^ 2 + 2 := by
      rw [V2_three, abs_of_nonneg]
      nlinarith [sq_nonneg a]
    have h3gt : 2 < |V2 a 3| := by
      rw [h3]; nlinarith [sq_nonneg a]
    -- grow via |V_{m+2}| ≥ 2|a| |V_{m+1}| - |a^2-2| |V_m|
    -- For a conservative bound: |V_3|≥14, and the sequence is increasing in abs
    have habs : ∀ m, 3 ≤ m → 2 < |V2 a m| := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact h3gt
      | succ m hm ih =>
        have hr := V2_succ2 a (m - 1)
        have hm1 : m - 1 + 2 = m + 1 := by omega
        have hm0 : m - 1 + 1 = m := by omega
        sorry
    have := habs (n + 3) (by omega)
    omega

lemma V2_ne_one_of_a_zero {n : ℕ} (hn : 3 ≤ n) : |V2 0 n| ≠ 1 := by
  -- V2 0 1 = 1, V2 0 2 = 0, V2 0 3 = 2, V2 0 4 = 0, V2 0 5 = 4, ...
  have h1 : V2 0 1 = 1 := V2_one 0
  have h2 : V2 0 2 = 0 := by rw [V2_two]; simp
  have h3 : V2 0 3 = 2 := by rw [V2_three]; simp
  have hrec : ∀ m, V2 0 (m + 2) = 2 * V2 0 m := by
    intro m
    rw [V2_succ2]
    simp
  -- For odd n=2k+1 ≥ 3, V = 2^k ≥ 2
  have : ∀ k, V2 0 (2 * k + 1) = (2 : ℤ) ^ k := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      rw [this, hrec, ih, pow_succ]
      ring
  obtain ⟨k, hk⟩ := Nat.even_or_odd' n |>.resolve_left (fun he => by
    -- even n ≥ 4: V2 0 even = 0
    have : ∀ k, V2 0 (2 * k) = 0 := by
      intro k
      induction k with
      | zero => simp [V2_zero]
      | succ k ih =>
        have : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [this, hrec, ih, mul_zero]
    obtain ⟨k, rfl⟩ := he
    have : 2 ≤ k := by omega
    rw [this 0] at *
    sorry)
  sorry

lemma no_V2_eq_one {a : ℤ} {n : ℕ} (hn : 3 ≤ n) (hY : 1 < (a ^ 2 - 2).natAbs) :
    |V2 a n| ≠ 1 := by
  have ha : a = 0 ∨ 1 ≤ |a| := by omega
  rcases ha with rfl | ha
  · -- a=0: a^2-2 = -2, natAbs=2, hY : 1<2, OK. V2 0 n ≠ ±1 for n≥3
    sorry
  · have ha1 : |a| = 1 ∨ 2 ≤ |a| := by omega
    rcases ha1 with ha1 | ha2
    · -- |a|=1: a^2-2=-1, natAbs=1, contradicts hY
      have : (a ^ 2 - 2).natAbs = 1 := by
        have : a ^ 2 = 1 := sq_abs a ▸ (by simp [ha1])
        rw [this]; norm_num
      omega
    · exact V2_ne_one_of_abs_ge_two ha2 n (by omega)

end Zsqrt2

