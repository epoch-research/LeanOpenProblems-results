import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

open Int

def g (k b : ℤ) : ℤ := k ^ 3 + 3 * k * b ^ 2 - 2 * b ^ 3

lemma g_even_of_odd_b {k b : ℤ} (hb : Odd b) : Even (g k b) := by
  have hmod : g k b ≡ k ^ 3 + k * b ^ 2 [ZMOD 2] := by
    refine Int.modEq_iff_dvd.mpr ⟨b ^ 3 - k * b ^ 2, ?_⟩
    simp only [g]; ring
  have hb2 : (b ^ 2 : ℤ) ≡ 1 [ZMOD 2] := by
    have : Odd (b ^ 2) := Odd.pow hb
    exact Int.odd_iff.mp this
  have hkb : k * b ^ 2 ≡ k * 1 [ZMOD 2] := Int.ModEq.mul_left k hb2
  have hkb' : k * b ^ 2 ≡ k [ZMOD 2] := by simpa using hkb
  have hsum0 : k ^ 3 + k * b ^ 2 ≡ k ^ 3 + k [ZMOD 2] :=
    Int.ModEq.add_left _ hkb'
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by
    have : k % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
    have : 0 ≤ k % 2 := Int.emod_nonneg _ (by decide)
    omega
  have hsum : k ^ 3 + k ≡ 0 [ZMOD 2] := by
    rcases hk with hk | hk
    · have hk0 : k ≡ 0 [ZMOD 2] := hk
      have hk3 : k ^ 3 ≡ 0 [ZMOD 2] := by simpa using Int.ModEq.pow (n := 2) 3 hk0
      exact hk3.add hk0
    · have hk1 : k ≡ 1 [ZMOD 2] := hk
      have hk3 : k ^ 3 ≡ 1 [ZMOD 2] := by simpa using Int.ModEq.pow (n := 2) 3 hk1
      exact (hk3.add hk1).trans (by decide : (1 + 1 : ℤ) ≡ 0 [ZMOD 2])
  have : g k b ≡ 0 [ZMOD 2] := hmod.trans (hsum0.trans hsum)
  exact Int.even_iff.mpr this

lemma b_even_of_g_eq_pm_one {k b : ℤ} (h : g k b = 1 ∨ g k b = -1) : Even b := by
  by_contra hb
  have he : Even (g k b) := g_even_of_odd_b (Int.not_even_iff_odd.mp hb)
  rcases h with h | h <;> (rw [h] at he; revert he; decide)

lemma g_modEq (k b : ℤ) :
    g k b ≡ (k % 9) ^ 3 + 3 * (k % 9) * (b % 9) ^ 2 - 2 * (b % 9) ^ 3 [ZMOD 9] := by
  have hk : k ≡ k % 9 [ZMOD 9] := (Int.mod_modEq k 9).symm
  have hb : b ≡ b % 9 [ZMOD 9] := (Int.mod_modEq b 9).symm
  have hk3 : k ^ 3 ≡ (k % 9) ^ 3 [ZMOD 9] := Int.ModEq.pow 3 hk
  have hb2 : b ^ 2 ≡ (b % 9) ^ 2 [ZMOD 9] := Int.ModEq.pow 2 hb
  have hb3 : b ^ 3 ≡ (b % 9) ^ 3 [ZMOD 9] := Int.ModEq.pow 3 hb
  have h3 : 3 * k * b ^ 2 ≡ 3 * (k % 9) * (b % 9) ^ 2 [ZMOD 9] := by
    have h1 : 3 * k ≡ 3 * (k % 9) [ZMOD 9] := Int.ModEq.mul_left 3 hk
    exact h1.mul hb2
  have h2 : 2 * b ^ 3 ≡ 2 * (b % 9) ^ 3 [ZMOD 9] := Int.ModEq.mul_left 2 hb3
  simpa [g] using (hk3.add h3).sub h2

lemma three_dvd_b_of_g_pm_one {k b : ℤ} (h : g k b = 1 ∨ g k b = -1) : (3 : ℤ) ∣ b := by
  have hg : g k b % 9 = 1 ∨ g k b % 9 = 8 := by
    rcases h with h | h <;> simp [h]
  have hr : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
    have : b % 3 < 3 := Int.emod_lt_of_pos b (by decide)
    have : 0 ≤ b % 3 := Int.emod_nonneg b (by decide)
    omega
  rcases hr with h0 | h1 | h2
  · exact Int.dvd_iff_emod_eq_zero.mpr h0
  · have hb9 : b % 9 = 1 ∨ b % 9 = 4 ∨ b % 9 = 7 := by
      have : b % 9 < 9 := Int.emod_lt_of_pos b (by decide)
      have : 0 ≤ b % 9 := Int.emod_nonneg b (by decide)
      have e : b % 3 = (b % 9) % 3 :=
        (Int.emod_emod_of_dvd b (by decide : (3 : ℤ) ∣ 9)).symm
      omega
    have hk9 : k % 9 = 0 ∨ k % 9 = 1 ∨ k % 9 = 2 ∨ k % 9 = 3 ∨ k % 9 = 4 ∨
        k % 9 = 5 ∨ k % 9 = 6 ∨ k % 9 = 7 ∨ k % 9 = 8 := by
      have : k % 9 < 9 := Int.emod_lt_of_pos k (by decide)
      have : 0 ≤ k % 9 := Int.emod_nonneg k (by decide)
      omega
    have hg' := g_modEq k b
    have hgeq : g k b % 9 =
        ((k % 9) ^ 3 + 3 * (k % 9) * (b % 9) ^ 2 - 2 * (b % 9) ^ 3) % 9 :=
      Int.ModEq.eq hg'
    rw [hgeq] at hg
    rcases hb9 with hb9 | hb9 | hb9 <;>
      rcases hk9 with hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9
    all_goals (rw [hk9, hb9] at hg; norm_num at hg)
  · have hb9 : b % 9 = 2 ∨ b % 9 = 5 ∨ b % 9 = 8 := by
      have : b % 9 < 9 := Int.emod_lt_of_pos b (by decide)
      have : 0 ≤ b % 9 := Int.emod_nonneg b (by decide)
      have e : b % 3 = (b % 9) % 3 :=
        (Int.emod_emod_of_dvd b (by decide : (3 : ℤ) ∣ 9)).symm
      omega
    have hk9 : k % 9 = 0 ∨ k % 9 = 1 ∨ k % 9 = 2 ∨ k % 9 = 3 ∨ k % 9 = 4 ∨
        k % 9 = 5 ∨ k % 9 = 6 ∨ k % 9 = 7 ∨ k % 9 = 8 := by
      have : k % 9 < 9 := Int.emod_lt_of_pos k (by decide)
      have : 0 ≤ k % 9 := Int.emod_nonneg k (by decide)
      omega
    have hgeq : g k b % 9 =
        ((k % 9) ^ 3 + 3 * (k % 9) * (b % 9) ^ 2 - 2 * (b % 9) ^ 3) % 9 :=
      Int.ModEq.eq (g_modEq k b)
    rw [hgeq] at hg
    rcases hb9 with hb9 | hb9 | hb9 <;>
      rcases hk9 with hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9
    all_goals (rw [hk9, hb9] at hg; norm_num at hg)

lemma six_dvd_b_of_g_pm_one {k b : ℤ} (h : g k b = 1 ∨ g k b = -1) : (6 : ℤ) ∣ b := by
  have h2 : (2 : ℤ) ∣ b := even_iff_two_dvd.mp (b_even_of_g_eq_pm_one h)
  have h3 : (3 : ℤ) ∣ b := three_dvd_b_of_g_pm_one h
  have h2m : b % 2 = 0 := Int.emod_eq_zero_of_dvd h2
  have h3m : b % 3 = 0 := Int.emod_eq_zero_of_dvd h3
  have h6 : b % 6 = 0 := by
    have : b % 6 < 6 := Int.emod_lt_of_pos b (by decide)
    have : 0 ≤ b % 6 := Int.emod_nonneg b (by decide)
    have e2 : b % 2 = (b % 6) % 2 :=
      (Int.emod_emod_of_dvd b (by decide : (2 : ℤ) ∣ 6)).symm
    have e3 : b % 3 = (b % 6) % 3 :=
      (Int.emod_emod_of_dvd b (by decide : (3 : ℤ) ∣ 6)).symm
    omega
  exact Int.dvd_iff_emod_eq_zero.mpr h6

lemma gcd_k_b_eq_one {k b : ℤ} (h : g k b = 1 ∨ g k b = -1) :
    Int.gcd k b = 1 := by
  have hd : (Int.gcd k b : ℤ) ∣ g k b := by
    have hk : (Int.gcd k b : ℤ) ∣ k := Int.gcd_dvd_left k b
    have hb : (Int.gcd k b : ℤ) ∣ b := Int.gcd_dvd_right k b
    have hk3 : (Int.gcd k b : ℤ) ∣ k ^ 3 := dvd_pow hk (by decide)
    have hb2 : (Int.gcd k b : ℤ) ∣ b ^ 2 := dvd_pow hb (by decide)
    have hb3 : (Int.gcd k b : ℤ) ∣ b ^ 3 := dvd_pow hb (by decide)
    have h3 : (Int.gcd k b : ℤ) ∣ 3 * k * b ^ 2 :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hk _) _
    have h2 : (Int.gcd k b : ℤ) ∣ 2 * b ^ 3 := dvd_mul_of_dvd_right hb3 _
    simpa [g] using (hk3.add h3).sub h2
  have hg1 : (Int.gcd k b : ℤ) ∣ 1 := by
    rcases h with h | h
    · rwa [h] at hd
    · have : (Int.gcd k b : ℤ) ∣ -1 := by rwa [h] at hd
      simpa using this
  have : Int.gcd k b ∣ 1 := by exact_mod_cast hg1
  exact Nat.dvd_one.mp this

lemma g_of_six_mul (k c : ℤ) :
    g k (6 * c) = k ^ 3 + 108 * k * c ^ 2 - 432 * c ^ 3 := by
  simp [g]; ring

lemma g_eq_one_factor {k c : ℤ} (h : g k (6 * c) = 1) :
    (k - 1) * (k ^ 2 + k + 1) = 108 * c ^ 2 * (4 * c - k) := by
  have := g_of_six_mul k c
  rw [this] at h
  have : k ^ 3 - 1 = 432 * c ^ 3 - 108 * k * c ^ 2 := by linarith
  have hL : k ^ 3 - 1 = (k - 1) * (k ^ 2 + k + 1) := by ring
  have hR : 432 * c ^ 3 - 108 * k * c ^ 2 = 108 * c ^ 2 * (4 * c - k) := by ring
  rw [hL, hR] at this
  exact this

lemma g_eq_neg_one_factor {k c : ℤ} (h : g k (6 * c) = -1) :
    (k + 1) * (k ^ 2 - k + 1) = 108 * c ^ 2 * (4 * c - k) := by
  have := g_of_six_mul k c
  rw [this] at h
  have : k ^ 3 + 1 = 432 * c ^ 3 - 108 * k * c ^ 2 := by linarith
  have hL : k ^ 3 + 1 = (k + 1) * (k ^ 2 - k + 1) := by ring
  have hR : 432 * c ^ 3 - 108 * k * c ^ 2 = 108 * c ^ 2 * (4 * c - k) := by ring
  rw [hL, hR] at this
  exact this

lemma gcd_k_sub_one_c {k c : ℤ} (hcop : Int.gcd k (6 * c) = 1) :
    Int.gcd (k - 1) c = 1 := by
  have h : Int.gcd (k - 1) c ∣ Int.gcd k (6 * c) := by
    -- gcd(k-1,c) | c and gcd(k-1,c) | k  (since it divides (k-1)+1)
    have hc : (Int.gcd (k - 1) c : ℤ) ∣ c := Int.gcd_dvd_right _ _
    have hk1 : (Int.gcd (k - 1) c : ℤ) ∣ k - 1 := Int.gcd_dvd_left _ _
    have hk : (Int.gcd (k - 1) c : ℤ) ∣ k := by
      have : (Int.gcd (k - 1) c : ℤ) ∣ (k - 1) + 1 :=
        hk1.add (dvd_refl 1) |>.trans ?_
      -- gcd | 1? No: gcd | (k-1) so gcd | ((k-1)+1) only if gcd | 1
      -- Wait: d | (k-1) does NOT imply d | k.
      -- d | (k-1) and d | c. We need d | k? Only if d | 1.
      -- Actually gcd(k-1, c) | c, and gcd(k, 6c)=1 so gcd(k,c)=1,
      -- thus gcd(k-1,c) and k are... 
      sorry
    sorry
  sorry
