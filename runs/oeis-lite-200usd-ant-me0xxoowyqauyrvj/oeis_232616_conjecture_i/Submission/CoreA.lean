import Submission.PartA
open PartA
namespace PartADev
set_option maxRecDepth 10000

theorem chk_a1 : chk 19 1 6052 = true := by decide +kernel
theorem chk_a2 : chk 19 6053 6052 = true := by decide +kernel

-- cancellation of a common factor 34
theorem cancel34 (x y m : ℕ) (h : 34*x ≡ 34*y [MOD 34*m]) : x ≡ y [MOD m] := by
  have h2 : 34*(x%m) = 34*(y%m) := by
    rw [← Nat.mul_mod_mul_left, ← Nat.mul_mod_mul_left]; exact h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

-- 416891 ∣ 2^12104 - 1
theorem dvd_pow_sub_one : (416891 : ℕ) ∣ 2^12104 - 1 := by
  have hz : (2 : ZMod 416891)^12104 = 1 := by
    rw [show (12104:ℕ) = 8*17*89 by norm_num, pow_mul, pow_mul]; decide +kernel
  rw [← ZMod.natCast_eq_zero_iff]
  rw [Nat.cast_sub (Nat.one_le_pow 12104 2 (by norm_num))]
  push_cast
  rw [hz]; ring

-- N ∣ 2^a * (2^12104 - 1) for a ≥ 1
theorem N_dvd (a : ℕ) (ha : 1 ≤ a) : (833782 : ℕ) ∣ 2^a * (2^12104 - 1) := by
  have h2 : (2:ℕ) ∣ 2^a := dvd_pow_self 2 (by omega)
  have hco : Nat.Coprime 2 416891 := by decide
  have : (833782 : ℕ) = 2 * 416891 := by norm_num
  rw [this]
  exact hco.mul_dvd_of_dvd_of_dvd (Dvd.dvd.mul_right h2 _)
    (Dvd.dvd.mul_left dvd_pow_sub_one _)

-- quasiperiod
theorem qp (a : ℕ) (ha : 1 ≤ a) : 2^(a+12104) ≡ 2^a [MOD 833782] := by
  have hle : 2^a ≤ 2^(a+12104) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have he : 2^(a+12104) - 2^a = 2^a * (2^12104 - 1) := by
    rw [pow_add, Nat.mul_sub, mul_one]
  exact ((Nat.modEq_iff_dvd' hle).2 (by rw [he]; exact N_dvd a ha)).symm

theorem qpj (a : ℕ) (ha : 1 ≤ a) (j : ℕ) : 2^(a + j*12104) ≡ 2^a [MOD 833782] := by
  induction j with
  | zero => simpa using Nat.ModEq.refl (2^a)
  | succ j ih =>
    have he : a + (j+1)*12104 = (a + j*12104) + 12104 := by ring
    rw [he]
    exact (qp (a+j*12104) (by omega)).trans ih

-- forward solving lemma
theorem FWD (j c : ℕ) (h : j * 12104 ≡ c [MOD 833782]) :
    34 ∣ c ∧ j % 24523 = (11366 * (c/34)) % 24523 := by
  -- 34 ∣ c
  have h34 : 34 ∣ c := by
    have hm : j*12104 ≡ c [MOD 34] := h.of_dvd (by norm_num)
    have h0 : j*12104 ≡ 0 [MOD 34] := by
      have : j*12104 = 34*(j*356) := by ring
      rw [this]; exact (Nat.modEq_zero_iff_dvd).2 ⟨j*356, rfl⟩
    have : c ≡ 0 [MOD 34] := hm.symm.trans h0
    exact (Nat.modEq_zero_iff_dvd).1 this
  refine ⟨h34, ?_⟩
  set cp := c/34 with hcp
  have hccp : (34:ℕ) * cp = c := Nat.mul_div_cancel' h34
  -- cancel 34
  have e1 : j*356 ≡ cp [MOD 24523] := by
    apply cancel34
    have h1 : 34*(j*356) = j*12104 := by ring
    have h3 : (34:ℕ)*24523 = 833782 := by norm_num
    rw [h1, hccp, h3]; exact h
  have e3 : 356*11366 ≡ 1 [MOD 24523] := by decide
  have e4 : j*(356*11366) ≡ j [MOD 24523] := by
    calc j*(356*11366) ≡ j*1 [MOD 24523] := Nat.ModEq.mul_left j e3
      _ = j := mul_one j
  have e2 : j*356*11366 ≡ cp*11366 [MOD 24523] := e1.mul_right 11366
  have e5 : j ≡ cp*11366 [MOD 24523] := by
    have hassoc : j*356*11366 = j*(356*11366) := by ring
    rw [hassoc] at e2
    exact e4.symm.trans e2
  have : j % 24523 = (cp*11366) % 24523 := e5
  rw [this, Nat.mul_comm cp 11366]

end PartADev

namespace PartADev2
open PartADev
set_option maxRecDepth 10000

theorem core (k : ℕ) (hk : 1 ≤ k) (hf : (2^k - k) % 833782 = 270024) : 27621329 ≤ k := by
  set k0 := (k-1) % 12104 + 1 with hk0def
  set j := (k-1) / 12104 with hjdef
  have hk0_lb : 1 ≤ k0 := by omega
  have hk0_ub : k0 ≤ 12104 := by
    have := Nat.mod_lt (k-1) (show 0 < 12104 by norm_num); omega
  have hkeq : k = k0 + j * 12104 := by
    have hmd := Nat.mod_add_div (k-1) 12104
    omega
  have hkle : k ≤ 2^k := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hc1 : 2^k - k ≡ 270024 [MOD 833782] := by
    show (2^k - k) % 833782 = 270024 % 833782
    rw [hf]
  have hc2 : 2^k ≡ 270024 + k [MOD 833782] := by
    have := hc1.add_right k
    rwa [Nat.sub_add_cancel hkle] at this
  have hc3 : 2^k ≡ 2^k0 [MOD 833782] := by
    conv_lhs => rw [hkeq]
    exact qpj k0 hk0_lb j
  have hc4 : 2^k0 ≡ 270024 + k [MOD 833782] := hc3.symm.trans hc2
  set P0 := mpow 20 2 833782 k0 with hP0def
  have hP0eq : P0 = 2^k0 % 833782 :=
    mpow_correct 20 2 833782 k0 (lt_of_le_of_lt hk0_ub (by norm_num))
  set c := (P0 + 833782 - (270024 + k0)) % 833782 with hcdef
  have hPlt : P0 < 833782 := by rw [hP0eq]; exact Nat.mod_lt _ (by norm_num)
  have hcadd : c + (270024 + k0) ≡ 2^k0 [MOD 833782] := by
    have hsub : P0 + 833782 - (270024+k0) + (270024+k0) = P0 + 833782 := by omega
    calc c + (270024+k0)
        ≡ (P0 + 833782 - (270024+k0)) + (270024+k0) [MOD 833782] :=
          Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
      _ = P0 + 833782 := hsub
      _ ≡ P0 + 0 [MOD 833782] := Nat.ModEq.add_left P0 (by decide)
      _ = P0 := by rw [Nat.add_zero]
      _ ≡ 2^k0 [MOD 833782] := by rw [hP0eq]; exact Nat.mod_modEq _ _
  have hcomb : c + (270024+k0) ≡ (270024 + k0) + j*12104 [MOD 833782] := by
    have h1 : c + (270024+k0) ≡ 270024 + k [MOD 833782] := hcadd.trans hc4
    have h2 : 270024 + k = (270024+k0) + j*12104 := by omega
    rwa [h2] at h1
  have hcong : c ≡ j*12104 [MOD 833782] := by
    have h := hcomb
    rw [Nat.add_comm c (270024+k0)] at h
    exact Nat.ModEq.add_left_cancel' (270024+k0) h
  obtain ⟨h34, hjeq⟩ := FWD j c hcong.symm
  have hpass : passes k0 = true := by
    rcases lt_or_ge k0 6053 with hsplit | hsplit
    · exact chk_spec 19 1 6052 chk_a1 k0 hk0_lb (by omega)
    · exact chk_spec 19 6053 6052 chk_a2 k0 (by omega) (by omega)
  rw [passes, ← hP0def, ← hcdef] at hpass
  have hc34 : c % 34 = 0 := by obtain ⟨t, ht⟩ := h34; omega
  rw [hc34] at hpass
  simp only [bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at hpass
  by_contra hcon
  push_neg at hcon
  have hjlt : j < 2282 := by omega
  have hjmod : j % 24523 = j := Nat.mod_eq_of_lt (by omega)
  rw [hjmod] at hjeq
  omega

end PartADev2

namespace PartADev3
open PartADev
set_option maxRecDepth 10000

-- backward solving: the explicit j works
theorem BWD (c : ℕ) (h34 : 34 ∣ c) :
    ((11366*(c/34))%24523) * 12104 ≡ c [MOD 833782] := by
  set j := (11366*(c/34))%24523 with hjdef
  set cp := c/34 with hcpdef
  have hccp : 34 * cp = c := Nat.mul_div_cancel' h34
  have hj1 : j ≡ 11366*cp [MOD 24523] := by rw [hjdef]; exact Nat.mod_modEq _ _
  have e3 : 356*11366 ≡ 1 [MOD 24523] := by decide
  have hj2 : j*356 ≡ cp [MOD 24523] := by
    calc j*356 ≡ (11366*cp)*356 [MOD 24523] := hj1.mul_right 356
      _ = cp*(356*11366) := by ring
      _ ≡ cp*1 [MOD 24523] := Nat.ModEq.mul_left cp e3
      _ = cp := mul_one cp
  have hlift : 34*(j*356) ≡ 34*cp [MOD 34*24523] := Nat.ModEq.mul_left' 34 hj2
  have e1 : 34*(j*356) = j*12104 := by ring
  have e2 : (34:ℕ)*24523 = 833782 := by norm_num
  rw [e1, hccp, e2] at hlift
  exact hlift

def vv (k0 : ℕ) : ℕ := (mpow 20 2 34 k0 + 170 - k0) % 34

theorem vv_eq (k0 : ℕ) (h : k0 ≤ 136) : (2^k0 - k0) % 34 = vv k0 := by
  rw [vv, mpow_correct 20 2 34 k0 (lt_of_le_of_lt h (by norm_num))]
  have hk : k0 ≤ 2^k0 := Nat.le_of_lt Nat.lt_two_pow_self
  have h1 : (2^k0 - k0) + k0 = 2^k0 := Nat.sub_add_cancel hk
  have h2 : (2^k0 % 34 + 170 - k0) + k0 = 2^k0 % 34 + 170 := by omega
  have h3 : 2^k0 ≡ 2^k0 % 34 + 170 [MOD 34] := by
    calc 2^k0 ≡ 2^k0 % 34 [MOD 34] := (Nat.mod_modEq _ _).symm
      _ = 2^k0 % 34 + 0 := (Nat.add_zero _).symm
      _ ≡ 2^k0 % 34 + 170 [MOD 34] := Nat.ModEq.add_left _ (by decide)
  have hg : (2^k0-k0)+k0 ≡ (2^k0%34+170-k0)+k0 [MOD 34] := by rw [h1, h2]; exact h3
  exact Nat.ModEq.add_right_cancel' k0 hg

theorem surj34 : ∀ s, s < 34 → ∃ k0 < 137, 1 ≤ k0 ∧ vv k0 = s := by decide +kernel

theorem hit (r : ℕ) (hr : r < 833782) :
    ∃ k, 1 ≤ k ∧ k ≤ 296814424 ∧ (2^k - k) % 833782 = r := by
  obtain ⟨k0, hk0lt, hk0_1, hvv⟩ := surj34 (r%34) (Nat.mod_lt r (by norm_num))
  have hk0le : k0 ≤ 136 := by omega
  have hmod34 : (2^k0 - k0) % 34 = r % 34 := by rw [vv_eq k0 hk0le, hvv]
  set A0 := (2^k0 - k0) % 833782 with hA0def
  have hAlt : A0 < 833782 := Nat.mod_lt _ (by norm_num)
  set c := (A0 + 833782 - r) % 833782 with hcdef
  -- c + r ≡ A0 [MOD N]
  have hcrA0 : c + r ≡ A0 [MOD 833782] := by
    have hsub : A0 + 833782 - r + r = A0 + 833782 := by omega
    calc c + r ≡ (A0 + 833782 - r) + r [MOD 833782] :=
            Nat.ModEq.add_right r (Nat.mod_modEq _ _)
      _ = A0 + 833782 := hsub
      _ ≡ A0 + 0 [MOD 833782] := Nat.ModEq.add_left A0 (by decide)
      _ = A0 := Nat.add_zero A0
  -- A0 ≡ r [MOD 34]
  have hA0r34 : A0 ≡ r [MOD 34] := by
    have hA0e : A0 ≡ 2^k0 - k0 [MOD 34] := (Nat.mod_modEq _ _).of_dvd (by norm_num)
    have hre : (2^k0 - k0) ≡ r [MOD 34] := hmod34
    exact hA0e.trans hre
  -- 34 ∣ c
  have h34c : 34 ∣ c := by
    have hcr34 : c + r ≡ A0 [MOD 34] := hcrA0.of_dvd (by norm_num)
    have : c + r ≡ r [MOD 34] := hcr34.trans hA0r34
    have hc0 : c ≡ 0 [MOD 34] :=
      Nat.ModEq.add_right_cancel' r (by rw [Nat.zero_add]; exact this)
    exact (Nat.modEq_zero_iff_dvd).1 hc0
  set j := (11366*(c/34))%24523 with hjdef
  have hjlt : j < 24523 := Nat.mod_lt _ (by norm_num)
  have hjd : j*12104 ≡ c [MOD 833782] := BWD c h34c
  clear_value j
  clear hjdef
  have hjb : j * 12104 ≤ 296814288 := by
    have hj : j ≤ 24522 := by omega
    calc j * 12104 ≤ 24522 * 12104 := by gcongr
      _ = 296814288 := by norm_num
  refine ⟨k0 + j*12104, by omega, by omega, ?_⟩
  set K := k0 + j*12104 with hKdef
  have hKle : K ≤ 2^K := Nat.le_of_lt Nat.lt_two_pow_self
  have h2K : 2^K ≡ 2^k0 [MOD 833782] := by rw [hKdef]; exact qpj k0 hk0_1 j
  have hA0k0 : A0 + k0 ≡ 2^k0 [MOD 833782] := by
    have he : (2^k0 - k0) + k0 = 2^k0 := Nat.sub_add_cancel (Nat.le_of_lt Nat.lt_two_pow_self)
    calc A0 + k0 ≡ (2^k0 - k0) + k0 [MOD 833782] := Nat.ModEq.add_right k0 (Nat.mod_modEq _ _)
      _ = 2^k0 := he
  have h2k0 : 2^k0 ≡ r + k0 + j*12104 [MOD 833782] := by
    calc 2^k0 ≡ A0 + k0 [MOD 833782] := hA0k0.symm
      _ ≡ (c + r) + k0 [MOD 833782] := Nat.ModEq.add_right k0 hcrA0.symm
      _ ≡ (j*12104 + r) + k0 [MOD 833782] :=
            Nat.ModEq.add_right k0 (Nat.ModEq.add_right r hjd.symm)
      _ = r + k0 + j*12104 := by ring
  have h2Kfin : 2^K ≡ r + K [MOD 833782] := by
    calc 2^K ≡ 2^k0 [MOD 833782] := h2K
      _ ≡ r + k0 + j*12104 [MOD 833782] := h2k0
      _ = r + K := by rw [hKdef]; ring
  have hfin : (2^K - K) % 833782 = r % 833782 := by
    have e : (2^K - K) + K = 2^K := Nat.sub_add_cancel hKle
    have h : (2^K - K) + K ≡ r + K [MOD 833782] := by rw [e]; exact h2Kfin
    exact Nat.ModEq.add_right_cancel' K h
  rw [hfin, Nat.mod_eq_of_lt hr]

end PartADev3
