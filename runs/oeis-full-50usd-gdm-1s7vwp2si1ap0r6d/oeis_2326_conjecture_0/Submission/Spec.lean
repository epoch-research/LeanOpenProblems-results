import FormalConjectures.Util.ProblemImports

open Nat

/--
A002326: Multiplicative order of 2 mod 2n+1.
In other words, least $m > 0$ such that $2n+1$ divides $2^m-1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  orderOf (2 : ZMod (2 * n + 1))

lemma helper (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) : 2 * ((p^3 - 1) / 2) + 1 = p^3 := by
  have hp_two_le : 2 ≤ p := hp_prime.two_le
  have hp_gt_two : 2 < p := lt_of_le_of_ne hp_two_le hp_odd.symm
  have hp_odd' : Odd p := hp_prime.odd_of_ne_two hp_odd
  have h_odd_pow : Odd (p^3) := hp_odd'.pow
  rcases h_odd_pow with ⟨k, hk⟩
  have h_sub : p^3 - 1 = 2 * k := by omega
  rw [h_sub]
  rw [Nat.mul_div_cancel_left _ (by decide)]
  omega

lemma helper2 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) : 2 * ((p^2 - 1) / 2) + 1 = p^2 := by
  have hp_two_le : 2 ≤ p := hp_prime.two_le
  have hp_gt_two : 2 < p := lt_of_le_of_ne hp_two_le hp_odd.symm
  have hp_odd' : Odd p := hp_prime.odd_of_ne_two hp_odd
  have h_odd_pow : Odd (p^2) := hp_odd'.pow
  rcases h_odd_pow with ⟨k, hk⟩
  have h_sub : p^2 - 1 = 2 * k := by omega
  rw [h_sub]
  rw [Nat.mul_div_cancel_left _ (by decide)]
  omega

lemma coprime_two_pow_two (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) : Nat.Coprime 2 (p^2) := by
  have hp_two_le : 2 ≤ p := hp_prime.two_le
  have hp_gt_two : 2 < p := lt_of_le_of_ne hp_two_le hp_odd.symm
  have hp_odd' : Odd p := hp_prime.odd_of_ne_two hp_odd
  have h_odd_pow : Odd (p^2) := hp_odd'.pow
  rcases h_odd_pow with ⟨k, hk⟩
  unfold Nat.Coprime
  rw [hk]
  have h_eq : 2 * k + 1 = 1 + k * 2 := by omega
  rw [h_eq]
  rw [Nat.gcd_comm]
  rw [Nat.gcd_add_mul_right_left]
  rfl

lemma orderOf_two_pos (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  0 < orderOf (2 : ZMod (p^2)) := by
  have h_coprime := coprime_two_pow_two p hp_prime hp_odd
  let u : Units (ZMod (p^2)) := ZMod.unitOfCoprime 2 h_coprime
  have h_coe : (u : ZMod (p^2)) = 2 := ZMod.coe_unitOfCoprime 2 h_coprime
  have h_order_eq : orderOf (u : ZMod (p^2)) = orderOf u := orderOf_units
  rw [h_coe] at h_order_eq
  rw [h_order_eq]
  exact orderOf_pos u

lemma order_dvd (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  orderOf (2 : ZMod (p^2)) ∣ orderOf (2 : ZMod (p^3)) := by
  have hp_two_le : 2 ≤ p := hp_prime.two_le
  have hp_pos : 0 < p := by omega
  have hp2_pos : p^2 ≠ 0 := by positivity
  have hp3_pos : p^3 ≠ 0 := by positivity
  have : NeZero (p^2) := ⟨hp2_pos⟩
  have : NeZero (p^3) := ⟨hp3_pos⟩
  have h_dvd : p^2 ∣ p^3 := by
    use p
    ring
  let f : ZMod (p^3) →+* ZMod (p^2) := ZMod.castHom h_dvd (ZMod (p^2))
  have h_map : f.toMonoidHom 2 = 2 := map_ofNat f 2
  have h_pow : (2 : ZMod (p^3)) ^ (orderOf (2 : ZMod (p^3))) = 1 := pow_orderOf_eq_one (2 : ZMod (p^3))
  have h_map_pow : f ((2 : ZMod (p^3)) ^ (orderOf (2 : ZMod (p^3)))) = f 1 := by rw [h_pow]
  rw [map_one f] at h_map_pow
  rw [map_pow f] at h_map_pow
  rw [show f 2 = 2 from h_map] at h_map_pow
  exact orderOf_dvd_of_pow_eq_one h_map_pow

lemma order_dvd3 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) (a : ZMod (p^3)) :
  (1 + (p^2 : ZMod (p^3)) * a) ^ p = 1 := by
  have hp3 : 3 ≤ p := by
    have h_ge_2 : 2 ≤ p := hp_prime.two_le
    omega
  let u : ZMod (p^3) := p^2
  let v : ZMod (p^3) := p
  have hvu : v ∣ u := by
    use p
    simp [u, v]
    ring
  have hp_cube : (p : ZMod (p^3)) ^ 3 = 0 := by
    have h : (p : ZMod (p^3)) ^ 3 = ((p^3 : ℕ) : ZMod (p^3)) := by
      push_cast
      rfl
    rw [h]
    exact ZMod.natCast_self (p^3)
  have hpuv : (p : ZMod (p^3)) * u * v ∣ u ^ p := by
    have h_zero : (p : ZMod (p^3)) * u * v = 0 := by
      calc
        (p : ZMod (p^3)) * u * v = p^4 := by
          simp [u, v]
          ring
        _ = (p : ZMod (p^3))^3 * p := by ring
        _ = 0 * p := by rw [hp_cube]
        _ = 0 := by ring
    rw [h_zero]
    have hu_pow : u ^ p = 0 := by
      have h_u : u ^ p = (p : ZMod (p^3)) ^ (2 * p) := by
        simp [u]
        rw [← pow_mul]
      have h_pow_eq : u ^ p = (p : ZMod (p^3))^3 * (p^(2 * p - 3) : ZMod (p^3)) := by
        rw [h_u]
        have h_cast : (p : ZMod (p^3)) ^ (2 * p) = (p : ZMod (p^3)) ^ (3 + (2 * p - 3)) := by
          congr 1
          omega
        rw [h_cast]
        ring
      rw [h_pow_eq]
      rw [hp_cube]
      ring
    rw [hu_pow]
  have h_inst := ZMod.exists_one_add_mul_pow_prime_pow_eq hp_prime hvu hpuv a 1
  obtain ⟨y, hy⟩ := h_inst
  calc
    (1 + (p^2 : ZMod (p^3)) * a) ^ p = (1 + u * a) ^ (p ^ 1) := by
      simp [u]
    _ = 1 + (p : ZMod (p^3)) ^ 1 * u * (a + v * y) := hy
    _ = 1 + p^3 * (a + v * y) := by
      congr 1
      simp [u]
      ring
    _ = 1 + 0 * (a + v * y) := by
      congr 1
      rw [hp_cube]
    _ = 1 := by ring

lemma castHom_eq_one_iff (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) (x : ZMod (p^3))
  (h_dvd : p^2 ∣ p^3) (h : ZMod.castHom h_dvd (ZMod (p^2)) x = 1) :
  ∃ a : ZMod (p^3), x = 1 + (p^2 : ZMod (p^3)) * a := by
  have hp3 : 3 ≤ p := by
    have h_ge_2 : 2 ≤ p := hp_prime.two_le
    omega
  have hp_pos : 0 < p := by omega
  have hp2_pos : p^2 ≠ 0 := by positivity
  have hp3_pos : p^3 ≠ 0 := by positivity
  have : NeZero (p^2) := ⟨hp2_pos⟩
  have : NeZero (p^3) := ⟨hp3_pos⟩
  have h_val : ZMod.castHom h_dvd (ZMod (p^2)) x = (x.val : ZMod (p^2)) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [h_val] at h
  have h_eq : x.val ≡ 1 [MOD p^2] := by
    have h' : (1 : ZMod (p^2)) = ((1 : ℕ) : ZMod (p^2)) := by
      push_cast
      rfl
    rw [h'] at h
    rwa [ZMod.natCast_eq_natCast_iff] at h
  have hp2_gt_one : 1 < p^2 := by
    calc
      1 < 3^2 := by decide
      _ ≤ p^2 := Nat.pow_le_pow_left hp3 2
  have h_mod : x.val % p^2 = 1 := by
    have h_mod' : x.val % p^2 = 1 % p^2 := h_eq
    rw [Nat.mod_eq_of_lt hp2_gt_one] at h_mod'
    exact h_mod'
  have h_div_eq : x.val = 1 + p^2 * (x.val / p^2) := by
    nth_rw 1 [← Nat.div_add_mod x.val (p^2)]
    rw [h_mod, add_comm]
  use (x.val / p^2 : ℕ)
  have h_cast : x = ((x.val : ℕ) : ZMod (p^3)) := by
    rw [ZMod.natCast_zmod_val]
  nth_rw 1 [h_cast]
  nth_rw 1 [h_div_eq]
  push_cast
  ring

lemma order_dvd_rev (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  orderOf (2 : ZMod (p^3)) ∣ p * orderOf (2 : ZMod (p^2)) := by
  have hp3 : 3 ≤ p := by
    have h_ge_2 : 2 ≤ p := hp_prime.two_le
    omega
  have hp_pos : 0 < p := by omega
  have hp2_pos : p^2 ≠ 0 := by positivity
  have hp3_pos : p^3 ≠ 0 := by positivity
  have : NeZero (p^2) := ⟨hp2_pos⟩
  have : NeZero (p^3) := ⟨hp3_pos⟩
  have h_dvd : p^2 ∣ p^3 := by
    use p
    ring
  let f : ZMod (p^3) →+* ZMod (p^2) := ZMod.castHom h_dvd (ZMod (p^2))
  have h_map : f.toMonoidHom 2 = 2 := map_ofNat f 2
  let e_2 := orderOf (2 : ZMod (p^2))
  have h_pow : f ((2 : ZMod (p^3))^e_2) = 1 := by
    calc
      f ((2 : ZMod (p^3))^e_2) = (f 2)^e_2 := map_pow f 2 e_2
      _ = (2 : ZMod (p^2))^e_2 := by
        rw [show f 2 = 2 from h_map]
      _ = 1 := by
        exact pow_orderOf_eq_one (2 : ZMod (p^2))
  have h_one : ∃ a : ZMod (p^3), (2 : ZMod (p^3))^e_2 = 1 + (p^2 : ZMod (p^3)) * a := by
    exact castHom_eq_one_iff p hp_prime hp_odd ((2 : ZMod (p^3))^e_2) h_dvd h_pow
  obtain ⟨a, ha⟩ := h_one
  have h_pow_p : ((2 : ZMod (p^3))^e_2)^p = 1 := by
    rw [ha]
    exact order_dvd3 p hp_prime hp_odd a
  have h_pow_p2 : (2 : ZMod (p^3))^(p * e_2) = 1 := by
    rw [mul_comm]
    rw [pow_mul]
    exact h_pow_p
  exact orderOf_dvd_of_pow_eq_one h_pow_p2

lemma eq_or_eq (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  orderOf (2 : ZMod (p^3)) = orderOf (2 : ZMod (p^2)) ∨
  orderOf (2 : ZMod (p^3)) = p * orderOf (2 : ZMod (p^2)) := by
  have hdvd1 := order_dvd p hp_prime hp_odd
  have hdvd2 := order_dvd_rev p hp_prime hp_odd
  obtain ⟨k, hk⟩ := hdvd1
  have h_dvd : orderOf (2 : ZMod (p^2)) * k ∣ orderOf (2 : ZMod (p^2)) * p := by
    rw [mul_comm (orderOf (2 : ZMod (p^2))) p]
    rw [← hk]
    exact hdvd2
  have hA_pos : 0 < orderOf (2 : ZMod (p^2)) := orderOf_two_pos p hp_prime hp_odd
  have hk_dvd : k ∣ p := (mul_dvd_mul_iff_left hA_pos.ne').mp h_dvd
  obtain hk1 | hk2 := hp_prime.eq_one_or_self_of_dvd k hk_dvd
  · left
    rw [hk, hk1, mul_one]
  · right
    rw [hk, hk2, mul_comm]


lemma orderOf_two_p_pos (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  0 < orderOf (2 : ZMod p) := by
  have hp_two_le : 2 ≤ p := hp_prime.two_le
  have hp_gt_two : 2 < p := lt_of_le_of_ne hp_two_le hp_odd.symm
  have h_coprime : Nat.Coprime 2 p := by
    unfold Nat.Coprime
    rw [Nat.gcd_comm]
    exact hp_prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp_gt_two)
  let u : Units (ZMod p) := ZMod.unitOfCoprime 2 h_coprime
  have h_coe : (u : ZMod p) = 2 := ZMod.coe_unitOfCoprime 2 h_coprime
  have h_order_eq : orderOf (u : ZMod p) = orderOf u := orderOf_units
  rw [h_coe] at h_order_eq
  rw [h_order_eq]
  exact orderOf_pos u

lemma order_dvd_1_2 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  orderOf (2 : ZMod p) ∣ orderOf (2 : ZMod (p^2)) := by
  have hp_two_le : 2 ≤ p := hp_prime.two_le
  have hp_pos : 0 < p := by omega
  have hp2_pos : p^2 ≠ 0 := by positivity
  have : NeZero p := ⟨hp_prime.ne_zero⟩
  have : NeZero (p^2) := ⟨hp2_pos⟩
  have h_dvd : p ∣ p^2 := by
    use p
    ring
  let f : ZMod (p^2) →+* ZMod p := ZMod.castHom h_dvd (ZMod p)
  have h_map : f.toMonoidHom 2 = 2 := map_ofNat f 2
  have h_pow : (2 : ZMod (p^2)) ^ (orderOf (2 : ZMod (p^2))) = 1 := pow_orderOf_eq_one (2 : ZMod (p^2))
  have h_map_pow : f ((2 : ZMod (p^2)) ^ (orderOf (2 : ZMod (p^2)))) = f 1 := by rw [h_pow]
  rw [map_one f] at h_map_pow
  rw [map_pow f] at h_map_pow
  rw [show f 2 = 2 from h_map] at h_map_pow
  exact orderOf_dvd_of_pow_eq_one h_map_pow

lemma order_dvd2 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) (a : ZMod (p^2)) :
  (1 + (p : ZMod (p^2)) * a) ^ p = 1 := by
  have hp3 : 3 ≤ p := by
    have h_ge_2 : 2 ≤ p := hp_prime.two_le
    omega
  let u : ZMod (p^2) := p
  let v : ZMod (p^2) := p
  have hvu : v ∣ u := by rfl
  have hp_sq : (p : ZMod (p^2)) ^ 2 = 0 := by
    have h : (p : ZMod (p^2)) ^ 2 = ((p^2 : ℕ) : ZMod (p^2)) := by
      push_cast
      rfl
    rw [h]
    exact ZMod.natCast_self (p^2)
  have hpuv : (p : ZMod (p^2)) * u * v ∣ u ^ p := by
    have h_zero : (p : ZMod (p^2)) * u * v = 0 := by
      calc
        (p : ZMod (p^2)) * u * v = p^3 := by
          simp [u, v]
          ring
        _ = (p : ZMod (p^2))^2 * p := by ring
        _ = 0 * p := by rw [hp_sq]
        _ = 0 := by ring
    rw [h_zero]
    have hu_pow : u ^ p = 0 := by
      have h_u : u ^ p = (p : ZMod (p^2)) ^ p := by simp [u]
      have h_pow_eq : u ^ p = (p : ZMod (p^2))^2 * (p^(p - 2) : ZMod (p^2)) := by
        rw [h_u]
        have h_cast : (p : ZMod (p^2)) ^ p = (p : ZMod (p^2)) ^ (2 + (p - 2)) := by
          congr 1
          omega
        rw [h_cast]
        ring
      rw [h_pow_eq]
      rw [hp_sq]
      ring
    rw [hu_pow]
  have h_inst := ZMod.exists_one_add_mul_pow_prime_pow_eq hp_prime hvu hpuv a 1
  obtain ⟨y, hy⟩ := h_inst
  calc
    (1 + (p : ZMod (p^2)) * a) ^ p = (1 + u * a) ^ (p ^ 1) := by
      simp [u]
    _ = 1 + (p : ZMod (p^2)) ^ 1 * u * (a + v * y) := hy
    _ = 1 + p^2 * (a + v * y) := by
      congr 1
      simp [u]
      ring
    _ = 1 + 0 * (a + v * y) := by
      congr 1
      rw [hp_sq]
    _ = 1 := by ring

lemma castHom_eq_one_iff2 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) (x : ZMod (p^2))
  (h_dvd : p ∣ p^2) (h : ZMod.castHom h_dvd (ZMod p) x = 1) :
  ∃ a : ZMod (p^2), x = 1 + (p : ZMod (p^2)) * a := by
  have hp3 : 3 ≤ p := by
    have h_ge_2 : 2 ≤ p := hp_prime.two_le
    omega
  have hp_pos : 0 < p := by omega
  have hp2_pos : p^2 ≠ 0 := by positivity
  have : NeZero p := ⟨hp_prime.ne_zero⟩
  have : NeZero (p^2) := ⟨hp2_pos⟩
  have h_val : ZMod.castHom h_dvd (ZMod p) x = (x.val : ZMod p) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [h_val] at h
  have h_eq : x.val ≡ 1 [MOD p] := by
    have h' : (1 : ZMod p) = ((1 : ℕ) : ZMod p) := by
      push_cast
      rfl
    rw [h'] at h
    rwa [ZMod.natCast_eq_natCast_iff] at h
  have hp_gt_one : 1 < p := by omega
  have h_mod : x.val % p = 1 := by
    have h_mod' : x.val % p = 1 % p := h_eq
    rw [Nat.mod_eq_of_lt hp_gt_one] at h_mod'
    exact h_mod'
  have h_div_eq : x.val = 1 + p * (x.val / p) := by
    nth_rw 1 [← Nat.div_add_mod x.val p]
    rw [h_mod, add_comm]
  use (x.val / p : ℕ)
  have h_cast : x = ((x.val : ℕ) : ZMod (p^2)) := by
    rw [ZMod.natCast_zmod_val]
  nth_rw 1 [h_cast]
  nth_rw 1 [h_div_eq]
  push_cast
  ring

lemma order_dvd_rev_1_2 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  orderOf (2 : ZMod (p^2)) ∣ p * orderOf (2 : ZMod p) := by
  have hp3 : 3 ≤ p := by
    have h_ge_2 : 2 ≤ p := hp_prime.two_le
    omega
  have hp_pos : 0 < p := by omega
  have hp2_pos : p^2 ≠ 0 := by positivity
  have : NeZero p := ⟨hp_prime.ne_zero⟩
  have : NeZero (p^2) := ⟨hp2_pos⟩
  have h_dvd : p ∣ p^2 := by
    use p
    ring
  let f : ZMod (p^2) →+* ZMod p := ZMod.castHom h_dvd (ZMod p)
  have h_map : f.toMonoidHom 2 = 2 := map_ofNat f 2
  let e_1 := orderOf (2 : ZMod p)
  have h_pow : f ((2 : ZMod (p^2))^e_1) = 1 := by
    calc
      f ((2 : ZMod (p^2))^e_1) = (f 2)^e_1 := map_pow f 2 e_1
      _ = (2 : ZMod p)^e_1 := by
        rw [show f 2 = 2 from h_map]
      _ = 1 := by
        exact pow_orderOf_eq_one (2 : ZMod p)
  have h_one : ∃ a : ZMod (p^2), (2 : ZMod (p^2))^e_1 = 1 + (p : ZMod (p^2)) * a := by
    exact castHom_eq_one_iff2 p hp_prime hp_odd ((2 : ZMod (p^2))^e_1) h_dvd h_pow
  obtain ⟨a, ha⟩ := h_one
  have h_pow_p : ((2 : ZMod (p^2))^e_1)^p = 1 := by
    rw [ha]
    exact order_dvd2 p hp_prime hp_odd a
  have h_pow_p2 : (2 : ZMod (p^2))^(p * e_1) = 1 := by
    rw [mul_comm]
    rw [pow_mul]
    exact h_pow_p
  exact orderOf_dvd_of_pow_eq_one h_pow_p2

lemma eq_or_eq_1_2 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  orderOf (2 : ZMod (p^2)) = orderOf (2 : ZMod p) ∨
  orderOf (2 : ZMod (p^2)) = p * orderOf (2 : ZMod p) := by
  have hdvd1 := order_dvd_1_2 p hp_prime hp_odd
  have hdvd2 := order_dvd_rev_1_2 p hp_prime hp_odd
  obtain ⟨k, hk⟩ := hdvd1
  have h_dvd : orderOf (2 : ZMod p) * k ∣ orderOf (2 : ZMod p) * p := by
    rw [mul_comm (orderOf (2 : ZMod p)) p]
    rw [← hk]
    exact hdvd2
  have hA_pos : 0 < orderOf (2 : ZMod p) := orderOf_two_p_pos p hp_prime hp_odd
  have hk_dvd : k ∣ p := (mul_dvd_mul_iff_left hA_pos.ne').mp h_dvd
  obtain hk1 | hk2 := hp_prime.eq_one_or_self_of_dvd k hk_dvd
  · left
    rw [hk, hk1, mul_one]
  · right
    rw [hk, hk2, mul_comm]

lemma padicValNat_orderOf_two_p1 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) (h_eq : orderOf (2 : ZMod (p^2)) = p * orderOf (2 : ZMod p)) :
  padicValNat p (2^(orderOf (2 : ZMod p)) - 1) = 1 := by
  let e_1 := orderOf (2 : ZMod p)
  let e_2 := orderOf (2 : ZMod (p^2))
  have h_e2_eq : e_2 = p * e_1 := h_eq
  have h_e1_pos : 0 < e_1 := orderOf_two_p_pos p hp_prime hp_odd
  have h_e2_pos : 0 < e_2 := orderOf_two_pos p hp_prime hp_odd
  have hp3 : 3 ≤ p := by
    have h_ge_2 : 2 ≤ p := hp_prime.two_le
    omega
  have hp_odd' : Odd p := hp_prime.odd_of_ne_two hp_odd
  have h_dvd : p ∣ 2^e_1 - 1 := by
    have h_pow : (2 : ZMod p)^e_1 = 1 := pow_orderOf_eq_one (2 : ZMod p)
    have h_cast : (2 : ZMod p)^e_1 = ((2^e_1 : ℕ) : ZMod p) := by push_cast; rfl
    rw [h_cast] at h_pow
    have h_eq : ((2^e_1 : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [h_pow]
      push_cast
      rfl
    rw [ZMod.natCast_eq_natCast_iff] at h_eq
    have h_gt : 1 < p := by omega
    have h_mod : (2^e_1) % p = 1 % p := h_eq
    rw [Nat.mod_eq_of_lt h_gt] at h_mod
    have h_div : 2^e_1 = p * (2^e_1 / p) + 1 := by
      have := Nat.div_add_mod (2^e_1) p
      omega
    have h_sub : 2^e_1 - 1 = p * (2^e_1 / p) := by omega
    use 2^e_1 / p
  have h_ne : 2^e_1 - 1 ≠ 0 := by
    have : 2^1 ≤ 2^e_1 := Nat.pow_le_pow_right (by decide) h_e1_pos
    omega
  have h_fact : Fact p.Prime := ⟨hp_prime⟩
  have h1 : 1 ≤ padicValNat p (2^e_1 - 1) := one_le_padicValNat_of_dvd h_ne h_dvd
  have h2 : padicValNat p (2^e_1 - 1) < 2 := by
    by_contra hc
    have h_ge : 2 ≤ padicValNat p (2^e_1 - 1) := by omega
    have h_dvd_p2 : p^2 ∣ 2^e_1 - 1 := (padicValNat_dvd_iff_le h_ne).mpr h_ge
    obtain ⟨c, hc_eq⟩ := h_dvd_p2
    have h_eq2 : 2^e_1 = p^2 * c + 1 := Nat.eq_add_of_sub_eq (by omega) hc_eq
    have h_zmod : (2 : ZMod (p^2))^e_1 = 1 := by
      have h_cast : (2 : ZMod (p^2))^e_1 = ((2^e_1 : ℕ) : ZMod (p^2)) := by push_cast; rfl
      rw [h_cast, h_eq2]
      push_cast
      have hp2_zero : (p : ZMod (p^2)) ^ 2 = 0 := by
        have h : (p : ZMod (p^2)) ^ 2 = ((p^2 : ℕ) : ZMod (p^2)) := by push_cast; rfl
        rw [h]
        exact ZMod.natCast_self (p^2)
      rw [show (p^2 : ZMod (p^2)) = (p : ZMod (p^2))^2 by push_cast; rfl]
      rw [hp2_zero]
      ring
    have h_dvd_e1 : e_2 ∣ e_1 := orderOf_dvd_of_pow_eq_one h_zmod
    rw [h_e2_eq] at h_dvd_e1
    have h_p_dvd : p ∣ 1 := by
      rcases h_dvd_e1 with ⟨k, hk⟩
      have hk2 : e_1 * 1 = e_1 * (p * k) := by
        calc
          e_1 * 1 = e_1 := mul_one e_1
          _ = p * e_1 * k := hk
          _ = e_1 * (p * k) := by ring
      have hpk : 1 = p * k := (mul_right_inj' h_e1_pos.ne').mp hk2
      use k
    have hp1 : p = 1 := Nat.eq_one_of_dvd_one h_p_dvd
    exact hp_prime.ne_one hp1
  change padicValNat p (2^e_1 - 1) = 1
  omega

lemma orderOf_two_p3_eq_p_p2_of_eq (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) (h_eq : orderOf (2 : ZMod (p^2)) = p * orderOf (2 : ZMod p)) :
  orderOf (2 : ZMod (p^3)) = p * orderOf (2 : ZMod (p^2)) := by
  let e_1 := orderOf (2 : ZMod p)
  let e_2 := orderOf (2 : ZMod (p^2))
  let e_3 := orderOf (2 : ZMod (p^3))
  have h_e2_eq : e_2 = p * e_1 := h_eq
  have h_val : padicValNat p (2^e_2 - 1) = 2 := by
    have hp_odd' : Odd p := hp_prime.odd_of_ne_two hp_odd
    have h_fact : Fact p.Prime := ⟨hp_prime⟩
    have h_e1_pos : 0 < e_1 := orderOf_two_p_pos p hp_prime hp_odd
    have h_ne : 2^e_1 - 1 ≠ 0 := by
      have : 2^1 ≤ 2^e_1 := Nat.pow_le_pow_right (by decide) h_e1_pos
      omega
    have h_dvd : p ∣ 2^e_1 - 1 := by
      have h1 := padicValNat_orderOf_two_p1 p hp_prime hp_odd h_eq
      have h2 : 1 ≤ padicValNat p (2^e_1 - 1) := h1.symm.le
      have h_pow_dvd := (padicValNat_dvd_iff_le h_ne).mpr h2
      rwa [pow_one] at h_pow_dvd
    have h_pow_sub := padicValNat.pow_sub_pow (p := p) hp_odd' (x := 2^e_1) (y := 1) (n := p)
      (hyx := by
        have : 2^1 ≤ 2^e_1 := Nat.pow_le_pow_right (by decide) h_e1_pos
        omega
      )
      (hxy := h_dvd)
      (hx := by
        intro h_dvd2
        have h_p_dvd_one : p ∣ 1 := by
          have h_sub_eq : 2^e_1 - (2^e_1 - 1) = 1 := by omega
          have h_iff := Nat.dvd_sub_iff_left (k := 2^e_1 - 1) (n := 2^e_1) (hkn := by omega) (h := h_dvd)
          rw [h_sub_eq] at h_iff
          exact h_iff.mpr h_dvd2
        have hp1 : p = 1 := Nat.eq_one_of_dvd_one h_p_dvd_one
        exact hp_prime.ne_one hp1
      ) hp_prime.ne_zero
    have h_pow_eq : (2^e_1)^p - 1^p = 2^e_2 - 1 := by
      rw [one_pow]
      congr 1
      rw [← pow_mul, mul_comm, h_e2_eq]
    rw [h_pow_eq] at h_pow_sub
    rw [h_pow_sub]
    have h_p1 := padicValNat_orderOf_two_p1 p hp_prime hp_odd h_eq
    have hp_val : padicValNat p p = 1 := padicValNat_self
    dsimp only [e_1, e_2, e_3] at *
    omega
  rcases eq_or_eq p hp_prime hp_odd with h | h
  · exfalso
    have hp3 : 3 ≤ p := by
      have h_ge_2 : 2 ≤ p := hp_prime.two_le
      omega
    have h_e2_pos : 0 < e_2 := orderOf_two_pos p hp_prime hp_odd
    have h_pow_eq : (2 : ZMod (p^3))^e_2 = 1 := by
      change (2 : ZMod (p^3)) ^ (orderOf (2 : ZMod (p^2))) = 1
      rw [← h]
      exact pow_orderOf_eq_one (2 : ZMod (p^3))
    have h_cast : (2 : ZMod (p^3))^e_2 = ((2^e_2 : ℕ) : ZMod (p^3)) := by push_cast; rfl
    rw [h_cast] at h_pow_eq
    have h_eq : ((2^e_2 : ℕ) : ZMod (p^3)) = ((1 : ℕ) : ZMod (p^3)) := by
      rw [h_pow_eq]
      push_cast
      rfl
    rw [ZMod.natCast_eq_natCast_iff] at h_eq
    have h_gt : 1 < p^3 := by
      have : 3^3 ≤ p^3 := Nat.pow_le_pow_left hp3 3
      omega
    have h_mod : (2^e_2) % p^3 = 1 % p^3 := h_eq
    rw [Nat.mod_eq_of_lt h_gt] at h_mod
    have h_div : 2^e_2 = p^3 * (2^e_2 / p^3) + 1 := by
      have := Nat.div_add_mod (2^e_2) (p^3)
      omega
    have h_sub : 2^e_2 - 1 = p^3 * (2^e_2 / p^3) := by omega
    have h_dvd_p3 : p^3 ∣ 2^e_2 - 1 := by
      use 2^e_2 / p^3
    have h_ne2 : 2^e_2 - 1 ≠ 0 := by
      have : 2^1 ≤ 2^e_2 := Nat.pow_le_pow_right (by decide) h_e2_pos
      omega
    have h_fact : Fact p.Prime := ⟨hp_prime⟩
    have h_le := (padicValNat_dvd_iff_le h_ne2).mp h_dvd_p3
    omega
  · exact h

lemma orderOf_two_p3_eq_p_p2_of_padic_eq_two (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) (h_val : padicValNat p (2^(orderOf (2 : ZMod (p^2))) - 1) = 2) :
  orderOf (2 : ZMod (p^3)) = p * orderOf (2 : ZMod (p^2)) := by
  let e_2 := orderOf (2 : ZMod (p^2))
  have h_val' : padicValNat p (2^e_2 - 1) = 2 := h_val
  rcases eq_or_eq p hp_prime hp_odd with h | h
  · exfalso
    have hp3 : 3 ≤ p := by
      have h_ge_2 : 2 ≤ p := hp_prime.two_le
      omega
    have h_e2_pos : 0 < e_2 := orderOf_two_pos p hp_prime hp_odd
    have h_pow_eq : (2 : ZMod (p^3))^e_2 = 1 := by
      change (2 : ZMod (p^3)) ^ (orderOf (2 : ZMod (p^2))) = 1
      rw [← h]
      exact pow_orderOf_eq_one (2 : ZMod (p^3))
    have h_cast : (2 : ZMod (p^3))^e_2 = ((2^e_2 : ℕ) : ZMod (p^3)) := by push_cast; rfl
    rw [h_cast] at h_pow_eq
    have h_eq : ((2^e_2 : ℕ) : ZMod (p^3)) = ((1 : ℕ) : ZMod (p^3)) := by
      rw [h_pow_eq]
      push_cast
      rfl
    rw [ZMod.natCast_eq_natCast_iff] at h_eq
    have h_gt : 1 < p^3 := by
      have : 3^3 ≤ p^3 := Nat.pow_le_pow_left hp3 3
      omega
    have h_mod : (2^e_2) % p^3 = 1 % p^3 := h_eq
    rw [Nat.mod_eq_of_lt h_gt] at h_mod
    have h_sub : 2^e_2 - 1 = p^3 * (2^e_2 / p^3) := by
      have := Nat.div_add_mod (2^e_2) (p^3)
      omega
    have h_dvd_p3 : p^3 ∣ 2^e_2 - 1 := by
      use 2^e_2 / p^3
    have h_ne2 : 2^e_2 - 1 ≠ 0 := by
      have : 2^1 ≤ 2^e_2 := Nat.pow_le_pow_right (by decide) h_e2_pos
      omega
    have h_fact : Fact p.Prime := ⟨hp_prime⟩
    have h_le := (padicValNat_dvd_iff_le h_ne2).mp h_dvd_p3
    omega
  · exact h


set_option maxRecDepth 1000000
set_option exponentiation.threshold 2000

lemma prime_factors_364 (p : ℕ) (hp : p.Prime) (hdvd : p ∣ 364) : p = 2 ∨ p = 7 ∨ p = 13 := by
  have : p ≤ 364 := Nat.le_of_dvd (by decide) hdvd
  have h_decide : ∀ x < 365, Nat.Prime x ∧ x ∣ 364 → x = 2 ∨ x = 7 ∨ x = 13 := by decide
  exact h_decide p (by omega) ⟨hp, hdvd⟩

lemma order_1093 : orderOf (2 : ZMod (1093^2)) = 364 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · decide
  · intro p hp hdvd
    have h_or := prime_factors_364 p hp hdvd
    rcases h_or with rfl | rfl | rfl
    · decide
    · decide
    · decide

lemma prime_factors_1755 (p : ℕ) (hp : p.Prime) (hdvd : p ∣ 1755) : p = 3 ∨ p = 5 ∨ p = 13 := by
  have : p ≤ 1755 := Nat.le_of_dvd (by decide) hdvd
  have h_decide : ∀ x < 1756, x ∣ 1755 ∧ Nat.Prime x → x = 3 ∨ x = 5 ∨ x = 13 := by decide
  exact h_decide p (by omega) ⟨hdvd, hp⟩

lemma order_3511 : orderOf (2 : ZMod (3511^2)) = 1755 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · decide
  · intro p hp hdvd
    have h_or := prime_factors_1755 p hp hdvd
    rcases h_or with rfl | rfl | rfl
    · decide
    · decide
    · decide

lemma dvd_of_zmod_pow_eq_one (m e : ℕ) (hm : 1 < m) (h : (2 : ZMod m) ^ e = 1) : m ∣ 2^e - 1 := by
  have h_cast : (2 : ZMod m)^e = ((2^e : ℕ) : ZMod m) := by push_cast; rfl
  rw [h_cast] at h
  have h_eq : ((2^e : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
    rw [h]
    push_cast
    rfl
  rw [ZMod.natCast_eq_natCast_iff] at h_eq
  have h_mod : (2^e) % m = 1 % m := h_eq
  rw [Nat.mod_eq_of_lt hm] at h_mod
  have h_div : 2^e = m * (2^e / m) + 1 := by
    have := Nat.div_add_mod (2^e) m
    omega
  have h_sub : 2^e - 1 = m * (2^e / m) := by omega
  use (2^e / m)

lemma not_dvd_of_zmod_pow_ne_one (m e : ℕ) (he : 0 < e) (hm : 1 < m) (h : (2 : ZMod m) ^ e ≠ 1) : ¬ m ∣ 2^e - 1 := by
  intro hdvd
  obtain ⟨k, hk⟩ := hdvd
  have h_two_pow_pos : 1 ≤ 2^e := by
    have : 2^1 ≤ 2^e := Nat.pow_le_pow_right (by decide) he
    omega
  have h_eq : 2^e = m * k + 1 := Nat.eq_add_of_sub_eq h_two_pow_pos hk
  have h_cast : ((2^e : ℕ) : ZMod m) = ((m * k + 1 : ℕ) : ZMod m) := by rw [h_eq]
  have h_cast2 : (2 : ZMod m)^e = ((2^e : ℕ) : ZMod m) := by push_cast; rfl
  rw [← h_cast2] at h_cast
  push_cast at h_cast
  have hm0 : (m : ZMod m) = 0 := ZMod.natCast_self m
  rw [hm0] at h_cast
  simp only [zero_mul, zero_add] at h_cast
  exact h h_cast

lemma padic_1093_decide (hp_prime : Nat.Prime 1093) : padicValNat 1093 (2^364 - 1) = 2 := by
  have h_fact : Fact (Nat.Prime 1093) := ⟨hp_prime⟩
  have h_ne : 2^364 - 1 ≠ 0 := by decide
  have h_dvd : 1093^2 ∣ 2^364 - 1 := by
    apply dvd_of_zmod_pow_eq_one (1093^2) 364 (by decide) (by decide)
  have h_not_dvd : ¬ 1093^3 ∣ 2^364 - 1 := by
    apply not_dvd_of_zmod_pow_ne_one (1093^3) 364 (by decide) (by decide) (by decide)
  have h_le : 2 ≤ padicValNat 1093 (2^364 - 1) := (padicValNat_dvd_iff_le h_ne).mp h_dvd
  have h_not_le : ¬ 3 ≤ padicValNat 1093 (2^364 - 1) := by
    intro h_le3
    have h_dvd3 := (padicValNat_dvd_iff_le h_ne).mpr h_le3
    exact h_not_dvd h_dvd3
  generalize padicValNat 1093 (2^364 - 1) = V at h_le h_not_le ⊢
  omega

lemma padic_3511_decide (hp_prime : Nat.Prime 3511) : padicValNat 3511 (2^1755 - 1) = 2 := by
  have h_fact : Fact (Nat.Prime 3511) := ⟨hp_prime⟩
  have h_ne : 2^1755 - 1 ≠ 0 := by decide
  have h_dvd : 3511^2 ∣ 2^1755 - 1 := by
    apply dvd_of_zmod_pow_eq_one (3511^2) 1755 (by decide) (by decide)
  have h_not_dvd : ¬ 3511^3 ∣ 2^1755 - 1 := by
    apply not_dvd_of_zmod_pow_ne_one (3511^3) 1755 (by decide) (by decide) (by decide)
  have h_le : 2 ≤ padicValNat 3511 (2^1755 - 1) := (padicValNat_dvd_iff_le h_ne).mp h_dvd
  have h_not_le : ¬ 3 ≤ padicValNat 3511 (2^1755 - 1) := by
    intro h_le3
    have h_dvd3 := (padicValNat_dvd_iff_le h_ne).mpr h_le3
    exact h_not_dvd h_dvd3
  generalize padicValNat 3511 (2^1755 - 1) = V at h_le h_not_le ⊢
  omega



lemma wief_le_3511_bool :
  ((List.range 3512).filter (fun p => Nat.Prime p ∧ p ≠ 2 ∧ orderOf (2 : ZMod (p^2)) = orderOf (2 : ZMod p))).all (fun p => p = 1093 ∨ p = 3511) = true := by decide

lemma wief_le_3511 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) (h_wief : orderOf (2 : ZMod (p^2)) = orderOf (2 : ZMod p)) :
  p = 1093 ∨ p = 3511 ∨ 3512 ≤ p := by
  by_cases hp_lt : p < 3512
  · left; left
    have h_all : ∀ x ∈ ((List.range 3512).filter (fun p => Nat.Prime p ∧ p ≠ 2 ∧ orderOf (2 : ZMod (p^2)) = orderOf (2 : ZMod p))), x = 1093 ∨ x = 3511 := by
      have h_bool := wief_le_3511_bool
      rw [List.all_eq_true] at h_bool
      exact h_bool
    have h_mem : p ∈ ((List.range 3512).filter (fun p => Nat.Prime p ∧ p ≠ 2 ∧ orderOf (2 : ZMod (p^2)) = orderOf (2 : ZMod p))) := by
      rw [List.mem_filter]
      refine ⟨?_, hp_prime, hp_odd, h_wief⟩
      rwa [List.mem_range]
    exact h_all p h_mem
  · right; right
    omega


theorem oeis_2326_conjecture_0 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  a ((p^3 - 1) / 2) = p * a ((p^2 - 1) / 2) := by
  have h1 : 2 * ((p^3 - 1) / 2) + 1 = p^3 := helper p hp_prime hp_odd
  have h2 : 2 * ((p^2 - 1) / 2) + 1 = p^2 := helper2 p hp_prime hp_odd
  unfold a
  rw [h1, h2]
  rcases eq_or_eq_1_2 p hp_prime hp_odd with h_wief | h_nonwief
  · by_cases hp_1093 : p = 1093
    · subst hp_1093
      have h_pad : padicValNat 1093 (2^(orderOf (2 : ZMod (1093^2))) - 1) = 2 := by
        rw [order_1093]
        exact padic_1093_decide hp_prime
      exact orderOf_two_p3_eq_p_p2_of_padic_eq_two 1093 hp_prime hp_odd h_pad
    · by_cases hp_3511 : p = 3511
      · subst hp_3511
        have h_pad : padicValNat 3511 (2^(orderOf (2 : ZMod (3511^2))) - 1) = 2 := by
          rw [order_3511]
          exact padic_3511_decide hp_prime
        exact orderOf_two_p3_eq_p_p2_of_padic_eq_two 3511 hp_prime hp_odd h_pad
      · by_cases h_pad : padicValNat p (2^(orderOf (2 : ZMod (p^2))) - 1) = 2
        · exact orderOf_two_p3_eq_p_p2_of_padic_eq_two p hp_prime hp_odd h_pad
        · sorry
  · exact orderOf_two_p3_eq_p_p2_of_eq p hp_prime hp_odd h_nonwief

