import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma dvd_of_factorization_le {D N : ℕ} (hD : D ≠ 0) (hN : N ≠ 0)
  (h : ∀ p : ℕ, p.Prime → padicValNat p D ≤ padicValNat p N) : D ∣ N := by
  rw [← Nat.factorization_le_iff_dvd hD hN]
  intro p
  by_cases hp : p.Prime
  · have h1 : D.factorization p = padicValNat p D := Nat.factorization_def D hp
    have h2 : N.factorization p = padicValNat p N := Nat.factorization_def N hp
    rw [h1, h2]
    exact h p hp
  · have h1 : D.factorization p = 0 := Nat.factorization_eq_zero_of_not_prime D hp
    rw [h1]
    exact Nat.zero_le _

lemma padic_108_2 : padicValNat 2 108 = 2 := by
  have : 108 = 2^2 * 27 := by decide
  rw [this]
  have fact_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by decide) (by decide)]
  have h1 : padicValNat 2 (2^2) = 2 := by
    rw [padicValNat.pow 2 (by decide)]
    rw [padicValNat.self (by decide)]
  have h2 : padicValNat 2 27 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    decide
  rw [h1, h2]

lemma padic_108_3 : padicValNat 3 108 = 3 := by
  have : 108 = 3^3 * 4 := by decide
  rw [this]
  have fact_three : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [padicValNat.mul (by decide) (by decide)]
  have h1 : padicValNat 3 (3^3) = 3 := by
    rw [padicValNat.pow 3 (by decide)]
    rw [padicValNat.self (by decide)]
  have h2 : padicValNat 3 4 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    decide
  rw [h1, h2]

lemma padic_108_p {p : ℕ} (hp : p.Prime) (hp_gt : 3 < p) : padicValNat p 108 = 0 := by
  have fact_p : Fact p.Prime := ⟨hp⟩
  apply padicValNat.eq_zero_of_not_dvd
  intro h_dvd
  have h1 : p ∣ 2^2 * 3^3 := by
    have : 108 = 2^2 * 3^3 := by decide
    rwa [← this]
  have h2 : p ∣ 2^2 ∨ p ∣ 3^3 := Nat.Prime.dvd_mul hp |>.mp h1
  rcases h2 with h2 | h2
  · have h3 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp h2
    have h4 : p ≤ 2 := Nat.le_of_dvd (by decide) h3
    omega
  · have h3 : p ∣ 3 := Nat.Prime.dvd_of_dvd_pow hp h2
    have h4 : p ≤ 3 := Nat.le_of_dvd (by decide) h3
    omega

lemma div_add_div_le_div (r1 r2 q : ℕ) (hq : 0 < q) (hr1 : r1 < q) (hr2 : r2 < q) :
  2 * ((r1 + r2) / q) ≤ (3 * r1) / q + (3 * r2) / q := by
  by_cases h : r1 + r2 < q
  · have : (r1 + r2) / q = 0 := Nat.div_eq_of_lt h
    rw [this]
    exact Nat.zero_le _
  · have : (r1 + r2) / q = 1 := by
      have hq1 : r1 + r2 < 2 * q := by omega
      have hq2 : 1 * q ≤ r1 + r2 := by omega
      exact Nat.div_eq_of_lt_le hq2 hq1
    rw [this]
    have h1 : 3 * r1 = q * ((3 * r1) / q) + (3 * r1) % q := (Nat.div_add_mod (3 * r1) q).symm
    have hm1 : (3 * r1) % q < q := Nat.mod_lt _ hq

    have h2 : 3 * r2 = q * ((3 * r2) / q) + (3 * r2) % q := (Nat.div_add_mod (3 * r2) q).symm
    have hm2 : (3 * r2) % q < q := Nat.mod_lt _ hq

    generalize hd1 : (3 * r1) / q = d1 at h1 ⊢
    generalize hd2 : (3 * r2) / q = d2 at h2 ⊢
    generalize hm1_eq : (3 * r1) % q = m1 at hm1 h1 ⊢
    generalize hm2_eq : (3 * r2) % q = m2 at hm2 h2 ⊢

    have h_sum1 : 3 * q ≤ 3 * r1 + 3 * r2 := by omega
    have h_sum2 : 3 * r1 + 3 * r2 = q * d1 + q * d2 + m1 + m2 := by omega
    have h_sum3 : 3 * q ≤ q * d1 + q * d2 + m1 + m2 := by omega
    have h_m : m1 + m2 < 2 * q := by omega
    have h_d : 1 * q < q * d1 + q * d2 := by omega
    have h_d2 : q * 1 < q * (d1 + d2) := by
      calc q * 1 = 1 * q := by ring
           _     < q * d1 + q * d2 := h_d
           _     = q * (d1 + d2) := by ring
    have h_d_le : 1 < d1 + d2 := Nat.lt_of_mul_lt_mul_left h_d2
    omega

lemma div_ineq (c e q : ℕ) (hq : 0 < q) :
  2 * ((c + e) / q) + c / q + e / q ≤ (3 * c) / q + (3 * e) / q := by
  have hc : c = q * (c / q) + c % q := (Nat.div_add_mod c q).symm
  have hr1 : c % q < q := Nat.mod_lt c hq

  have he : e = q * (e / q) + e % q := (Nat.div_add_mod e q).symm
  have hr2 : e % q < q := Nat.mod_lt e hq

  generalize hd1 : c / q = d1 at hc ⊢
  generalize hd2 : e / q = d2 at he ⊢
  generalize hr1_eq : c % q = r1 at hr1 hc ⊢
  generalize hr2_eq : e % q = r2 at hr2 he ⊢

  have h_ce : c + e = q * (d1 + d2) + (r1 + r2) := by
    calc c + e = (q * d1 + r1) + (q * d2 + r2) := by rw [hc, he]
         _     = q * d1 + q * d2 + r1 + r2 := by ring
         _     = q * (d1 + d2) + (r1 + r2) := by ring
  have h_3c : 3 * c = q * (3 * d1) + 3 * r1 := by
    calc 3 * c = 3 * (q * d1 + r1) := by rw [hc]
         _     = 3 * q * d1 + 3 * r1 := by ring
         _     = q * (3 * d1) + 3 * r1 := by ring
  have h_3e : 3 * e = q * (3 * d2) + 3 * r2 := by
    calc 3 * e = 3 * (q * d2 + r2) := by rw [he]
         _     = 3 * q * d2 + 3 * r2 := by ring
         _     = q * (3 * d2) + 3 * r2 := by ring

  have H1 : (c + e) / q = d1 + d2 + (r1 + r2) / q := by
    calc (c + e) / q = (q * (d1 + d2) + (r1 + r2)) / q := by rw [h_ce]
         _           = (r1 + r2 + q * (d1 + d2)) / q := by rw [Nat.add_comm (q * (d1 + d2))]
         _           = (r1 + r2) / q + (d1 + d2) := by rw [Nat.add_mul_div_left _ _ hq]
         _           = d1 + d2 + (r1 + r2) / q := by omega
  have H2 : (3 * c) / q = 3 * d1 + (3 * r1) / q := by
    calc (3 * c) / q = (q * (3 * d1) + 3 * r1) / q := by rw [h_3c]
         _           = (3 * r1 + q * (3 * d1)) / q := by rw [Nat.add_comm (q * (3 * d1))]
         _           = (3 * r1) / q + 3 * d1 := by rw [Nat.add_mul_div_left _ _ hq]
         _           = 3 * d1 + (3 * r1) / q := by omega
  have H3 : (3 * e) / q = 3 * d2 + (3 * r2) / q := by
    calc (3 * e) / q = (q * (3 * d2) + 3 * r2) / q := by rw [h_3e]
         _           = (3 * r2 + q * (3 * d2)) / q := by rw [Nat.add_comm (q * (3 * d2))]
         _           = (3 * r2) / q + 3 * d2 := by rw [Nat.add_mul_div_left _ _ hq]
         _           = 3 * d2 + (3 * r2) / q := by omega

  rw [H1, H2, H3]

  have H_rem := div_add_div_le_div r1 r2 q hq hr1 hr2
  omega

lemma sum_ineq (N_i D_i : ℕ → ℕ) (b : ℕ) (hb : 3 ≤ b)
  (h1 : D_i 1 + 1 ≤ N_i 1)
  (h2 : D_i 2 + 1 ≤ N_i 2)
  (h_le : ∀ i, 1 ≤ i → i < b → D_i i ≤ N_i i) :
  ∑ i ∈ Ico 1 b, D_i i + 2 ≤ ∑ i ∈ Ico 1 b, N_i i := by
  have H : ∑ i ∈ Ico 1 3, D_i i + ∑ i ∈ Ico 3 b, D_i i = ∑ i ∈ Ico 1 b, D_i i := sum_Ico_consecutive (fun i => D_i i) (by decide) hb
  have H' : ∑ i ∈ Ico 1 3, N_i i + ∑ i ∈ Ico 3 b, N_i i = ∑ i ∈ Ico 1 b, N_i i := sum_Ico_consecutive (fun i => N_i i) (by decide) hb
  have H_13 : ∑ i ∈ Ico 1 3, D_i i + 2 ≤ ∑ i ∈ Ico 1 3, N_i i := by
    have hd : ∑ i ∈ Ico 1 3, D_i i = D_i 1 + D_i 2 := by rfl
    have hn : ∑ i ∈ Ico 1 3, N_i i = N_i 1 + N_i 2 := by rfl
    omega
  have H_rest : ∑ i ∈ Ico 3 b, D_i i ≤ ∑ i ∈ Ico 3 b, N_i i := by
    apply sum_le_sum
    intro i hi
    rw [mem_Ico] at hi
    apply h_le i (by omega) hi.2
  omega

lemma padic_N_ge_padic_D_two (n : ℕ) :
  padicValNat 2 ((4 * n + 2).factorial * (2 * n + 3).factorial * ((6 * n + 5).factorial)^2) + 2
    ≤ padicValNat 2 ((12 * n + 6).factorial * (6 * n + 9).factorial) := by
  have fact_2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let b := 12 * n + 10
  have hb1 : Nat.log 2 (12 * n + 6) < b := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self _ _)
    omega
  have hb2 : Nat.log 2 (6 * n + 9) < b := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self _ _)
    omega
  have hb3 : Nat.log 2 (4 * n + 2) < b := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self _ _)
    omega
  have hb4 : Nat.log 2 (2 * n + 3) < b := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self _ _)
    omega
  have hb5 : Nat.log 2 (6 * n + 5) < b := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self _ _)
    omega

  have hn0 : (12 * n + 6).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn1 : (6 * n + 9).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn2 : (4 * n + 2).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn3 : (2 * n + 3).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn4 : (6 * n + 5).factorial ≠ 0 := Nat.factorial_ne_zero _

  have hN : padicValNat 2 ((12 * n + 6).factorial * (6 * n + 9).factorial) =
      padicValNat 2 (12 * n + 6).factorial + padicValNat 2 (6 * n + 9).factorial := padicValNat.mul hn0 hn1

  have hD : padicValNat 2 ((4 * n + 2).factorial * (2 * n + 3).factorial * ((6 * n + 5).factorial)^2) =
      padicValNat 2 (4 * n + 2).factorial + padicValNat 2 (2 * n + 3).factorial + 2 * padicValNat 2 (6 * n + 5).factorial := by
    have H : padicValNat 2 ((4 * n + 2).factorial * (2 * n + 3).factorial) =
      padicValNat 2 (4 * n + 2).factorial + padicValNat 2 (2 * n + 3).factorial := padicValNat.mul hn2 hn3
    have H2 : padicValNat 2 (((6 * n + 5).factorial)^2) = 2 * padicValNat 2 (6 * n + 5).factorial := padicValNat.pow 2 hn4
    rw [padicValNat.mul (mul_ne_zero hn2 hn3) (pow_ne_zero 2 hn4), H, H2]

  rw [hN, hD]
  rw [padicValNat_factorial hb1, padicValNat_factorial hb2]
  rw [padicValNat_factorial hb3, padicValNat_factorial hb4, padicValNat_factorial hb5]
  rw [← sum_add_distrib]
  have H2 : 2 * ∑ i ∈ Ico 1 b, (6 * n + 5) / 2 ^ i = ∑ i ∈ Ico 1 b, 2 * ((6 * n + 5) / 2 ^ i) := by rw [mul_sum]
  rw [H2, ← sum_add_distrib, ← sum_add_distrib]
  
  let D_i := fun i => (4 * n + 2) / 2 ^ i + (2 * n + 3) / 2 ^ i + 2 * ((6 * n + 5) / 2 ^ i)
  let N_i := fun i => (12 * n + 6) / 2 ^ i + (6 * n + 9) / 2 ^ i

  have H_le : ∑ i ∈ Ico 1 b, D_i i + 2 ≤ ∑ i ∈ Ico 1 b, N_i i := by
    apply sum_ineq N_i D_i b (by omega)
    · -- i = 1
      dsimp [D_i, N_i]
      omega
    · -- i = 2
      dsimp [D_i, N_i]
      have : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases this with h | h
      · have ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
        subst hk
        omega
      · have ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
        subst hk
        omega
    · -- general i
      intro i hi1 hib
      dsimp [D_i, N_i]
      have hq : 0 < 2 ^ i := by positivity
      have H_ineq := div_ineq (4 * n + 2) (2 * n + 3) (2 ^ i) hq
      have h_3c : 3 * (4 * n + 2) = 12 * n + 6 := by omega
      have h_3e : 3 * (2 * n + 3) = 6 * n + 9 := by omega
      have h_ce : (4 * n + 2) + (2 * n + 3) = 6 * n + 5 := by omega
      rw [h_3c, h_3e, h_ce] at H_ineq
      omega
  
  exact H_le

lemma sum_digits_mul (p x : ℕ) (hp : 1 < p) (hx : 0 < x) :
  (Nat.digits p (p * x)).sum = (Nat.digits p x).sum := by
  rw [Nat.digits_base_mul hp hx]
  simp

lemma sub_one_mul_padic_three (x : ℕ) : 2 * padicValNat 3 x.factorial = x - (Nat.digits 3 x).sum := by
  have fact_three : Fact (Nat.Prime 3) := ⟨by decide⟩
  have := sub_one_mul_padicValNat_factorial (p := 3) x
  exact this

lemma sum_digits_three (n : ℕ) : 3 ≤ (Nat.digits 3 (6 * n + 5)).sum := by
  have hp : 1 < 3 := by decide
  have h0 : 0 < 6 * n + 5 := by omega
  rw [Nat.digits_def' hp h0]
  have h1 : (6 * n + 5) % 3 = 2 := by omega
  have h2 : (6 * n + 5) / 3 = 2 * n + 1 := by omega
  rw [h1, h2]
  simp only [List.sum_cons]
  have h3 : 2 * n + 1 ≠ 0 := by omega
  have h4 : Nat.digits 3 (2 * n + 1) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr h3
  have h5 : 1 ≤ (Nat.digits 3 (2 * n + 1)).sum := by
    apply Nat.sum_pos_iff_exists_pos.mpr
    have h_last := Nat.getLast_digit_ne_zero 3 h3
    refine ⟨_, List.getLast_mem h4, Nat.pos_of_ne_zero h_last⟩
  omega

lemma padic_N_ge_padic_D_three (n : ℕ) :
  padicValNat 3 ((4 * n + 2).factorial * (2 * n + 3).factorial * ((6 * n + 5).factorial)^2) + 3
    ≤ padicValNat 3 ((12 * n + 6).factorial * (6 * n + 9).factorial) := by
  have fact_three : Fact (Nat.Prime 3) := ⟨by decide⟩

  have hn0 : (12 * n + 6).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn1 : (6 * n + 9).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn2 : (4 * n + 2).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn3 : (2 * n + 3).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn4 : (6 * n + 5).factorial ≠ 0 := Nat.factorial_ne_zero _

  have hN : padicValNat 3 ((12 * n + 6).factorial * (6 * n + 9).factorial) =
      padicValNat 3 (12 * n + 6).factorial + padicValNat 3 (6 * n + 9).factorial := padicValNat.mul hn0 hn1

  have hD : padicValNat 3 ((4 * n + 2).factorial * (2 * n + 3).factorial * ((6 * n + 5).factorial)^2) =
      padicValNat 3 (4 * n + 2).factorial + padicValNat 3 (2 * n + 3).factorial + 2 * padicValNat 3 (6 * n + 5).factorial := by
    have H : padicValNat 3 ((4 * n + 2).factorial * (2 * n + 3).factorial) =
      padicValNat 3 (4 * n + 2).factorial + padicValNat 3 (2 * n + 3).factorial := padicValNat.mul hn2 hn3
    have H2 : padicValNat 3 (((6 * n + 5).factorial)^2) = 2 * padicValNat 3 (6 * n + 5).factorial := padicValNat.pow 2 hn4
    rw [padicValNat.mul (mul_ne_zero hn2 hn3) (pow_ne_zero 2 hn4), H, H2]

  have H_N2 : 2 * padicValNat 3 ((12 * n + 6).factorial * (6 * n + 9).factorial) =
    (12 * n + 6 - (Nat.digits 3 (12 * n + 6)).sum) + (6 * n + 9 - (Nat.digits 3 (6 * n + 9)).sum) := by
    rw [hN, mul_add, sub_one_mul_padic_three, sub_one_mul_padic_three]
  
  have H_D2 : 2 * padicValNat 3 ((4 * n + 2).factorial * (2 * n + 3).factorial * ((6 * n + 5).factorial)^2) =
    (4 * n + 2 - (Nat.digits 3 (4 * n + 2)).sum) + (2 * n + 3 - (Nat.digits 3 (2 * n + 3)).sum)
    + 2 * (6 * n + 5 - (Nat.digits 3 (6 * n + 5)).sum) := by
    rw [hD, mul_add, mul_add, sub_one_mul_padic_three, sub_one_mul_padic_three]
    have : 2 * (2 * padicValNat 3 (6 * n + 5).factorial) = 2 * (6 * n + 5 - (Nat.digits 3 (6 * n + 5)).sum) := by
      rw [← mul_assoc, mul_comm 2 2, mul_assoc]
      have h_sub : 2 * padicValNat 3 (6 * n + 5).factorial = 6 * n + 5 - (Nat.digits 3 (6 * n + 5)).sum := sub_one_mul_padic_three _
      rw [h_sub]
    rw [this]

  have H_dig1 : (Nat.digits 3 (12 * n + 6)).sum = (Nat.digits 3 (4 * n + 2)).sum := by
    have : 12 * n + 6 = 3 * (4 * n + 2) := by omega
    rw [this]
    apply sum_digits_mul 3 _ (by decide) (by omega)
  have H_dig2 : (Nat.digits 3 (6 * n + 9)).sum = (Nat.digits 3 (2 * n + 3)).sum := by
    have : 6 * n + 9 = 3 * (2 * n + 3) := by omega
    rw [this]
    apply sum_digits_mul 3 _ (by decide) (by omega)
  
  have H_sum_le := sum_digits_three n

  have hd1 : (Nat.digits 3 (4 * n + 2)).sum ≤ 4 * n + 2 := Nat.digit_sum_le 3 _
  have hd2 : (Nat.digits 3 (2 * n + 3)).sum ≤ 2 * n + 3 := Nat.digit_sum_le 3 _
  have hd3 : (Nat.digits 3 (6 * n + 5)).sum ≤ 6 * n + 5 := Nat.digit_sum_le 3 _
  
  omega

lemma padic_N_ge_padic_D_prime (n p : ℕ) (hp : p.Prime) :
  padicValNat p ((4 * n + 2).factorial * (2 * n + 3).factorial * ((6 * n + 5).factorial)^2)
    ≤ padicValNat p ((12 * n + 6).factorial * (6 * n + 9).factorial) := by
  have fact_p : Fact p.Prime := ⟨hp⟩
  have hp_pos : 0 < p := Nat.Prime.pos hp
  have hp_ge2 : 2 ≤ p := Nat.Prime.two_le hp
  let b := 12 * n + 10
  have hb1 : Nat.log p (12 * n + 6) < b := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self _ _)
    omega
  have hb2 : Nat.log p (6 * n + 9) < b := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self _ _)
    omega
  have hb3 : Nat.log p (4 * n + 2) < b := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self _ _)
    omega
  have hb4 : Nat.log p (2 * n + 3) < b := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self _ _)
    omega
  have hb5 : Nat.log p (6 * n + 5) < b := by
    apply Nat.lt_of_le_of_lt (Nat.log_le_self _ _)
    omega

  have hn0 : (12 * n + 6).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn1 : (6 * n + 9).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn2 : (4 * n + 2).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn3 : (2 * n + 3).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hn4 : (6 * n + 5).factorial ≠ 0 := Nat.factorial_ne_zero _

  have hN : padicValNat p ((12 * n + 6).factorial * (6 * n + 9).factorial) =
      padicValNat p (12 * n + 6).factorial + padicValNat p (6 * n + 9).factorial := padicValNat.mul hn0 hn1

  have hD : padicValNat p ((4 * n + 2).factorial * (2 * n + 3).factorial * ((6 * n + 5).factorial)^2) =
      padicValNat p (4 * n + 2).factorial + padicValNat p (2 * n + 3).factorial + 2 * padicValNat p (6 * n + 5).factorial := by
    have H : padicValNat p ((4 * n + 2).factorial * (2 * n + 3).factorial) =
      padicValNat p (4 * n + 2).factorial + padicValNat p (2 * n + 3).factorial := padicValNat.mul hn2 hn3
    have H2 : padicValNat p (((6 * n + 5).factorial)^2) = 2 * padicValNat p (6 * n + 5).factorial := padicValNat.pow 2 hn4
    rw [padicValNat.mul (mul_ne_zero hn2 hn3) (pow_ne_zero 2 hn4), H, H2]

  rw [hN, hD]
  rw [padicValNat_factorial hb1, padicValNat_factorial hb2]
  rw [padicValNat_factorial hb3, padicValNat_factorial hb4, padicValNat_factorial hb5]
  rw [← sum_add_distrib]
  have H2 : 2 * ∑ i ∈ Ico 1 b, (6 * n + 5) / p ^ i = ∑ i ∈ Ico 1 b, 2 * ((6 * n + 5) / p ^ i) := by rw [mul_sum]
  rw [H2, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  have hq : 0 < p ^ i := by positivity
  have H_ineq := div_ineq (4 * n + 2) (2 * n + 3) (p ^ i) hq
  have h_3c : 3 * (4 * n + 2) = 12 * n + 6 := by omega
  have h_3e : 3 * (2 * n + 3) = 6 * n + 9 := by omega
  have h_ce : (4 * n + 2) + (2 * n + 3) = 6 * n + 5 := by omega
  rw [h_3c, h_3e, h_ce] at H_ineq
  omega

/--
A368692:
$$a(n) = \frac{(12n + 6)! \cdot (6n + 9)!}{108 \cdot (4n + 2)! \cdot (2n + 3)! \cdot ((6n + 5)!)^2}$$
It is conjectured that $a(n)$ are integers.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := (12 * n + 6)! * (6 * n + 9)!
  let den_base : ℕ := (4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2
  num / (108 * den_base)

/--
Conjecture from OEIS A368692: $a(n)$ is an integer for all $n \in \mathbb{N}$.
According to A. Adolphson and S. Sperber, "On the integrality of hypergeometric series
whose coefficients are factorial ratios", ArXiv: 2001.03296, s.page 14, first equation
after Eq.(7.4): for any two integers K, L, the ratios $(3K)!(3L)!/(K!L!((K+L)!)^2)$
are proven to be integers. $108 \cdot a(n)$ results from $K = 4n+2$ and $L = 2n+3$, $n \ge 0$.
It is conjectured here that $a(n)$ are integers.
This is equivalent to the denominator dividing the numerator exactly in the definition
of $a(n)$.
-/
theorem oeis_a368692_conjecture_integrality (n : ℕ) :
  108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2) ∣ (12 * n + 6)! * (6 * n + 9)! := by
  let D' := (4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2
  let D := 108 * D'
  let N := (12 * n + 6)! * (6 * n + 9)!
  
  have hD' : D' ≠ 0 := mul_ne_zero (mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)) (pow_ne_zero 2 (factorial_ne_zero _))
  have hD : D ≠ 0 := mul_ne_zero (by decide) hD'
  have hN : N ≠ 0 := mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
  
  apply dvd_of_factorization_le hD hN
  intro p hp
  have fact_p : Fact p.Prime := ⟨hp⟩
  have h_mul : padicValNat p D = padicValNat p 108 + padicValNat p D' := padicValNat.mul (by decide) hD'
  rw [h_mul]

  have hp2 : 2 ≤ p := Nat.Prime.two_le hp
  rcases eq_or_lt_of_le hp2 with rfl | hp3
  · -- p = 2
    have H1 := padic_108_2
    have H2 := padic_N_ge_padic_D_two n
    dsimp [D', N] at *
    omega
  · rcases eq_or_lt_of_le (show 3 ≤ p by omega) with rfl | hp4
    · -- p = 3
      have H1 := padic_108_3
      have H2 := padic_N_ge_padic_D_three n
      dsimp [D', N] at *
      omega
    · -- p > 3
      have H1 := padic_108_p hp hp4
      have H2 := padic_N_ge_padic_D_prime n p hp
      dsimp [D', N] at *
      omega

theorem oeis_a368692_conjecture_integrality.disproof : ¬ (type_of% @oeis_a368692_conjecture_integrality) := sorry
