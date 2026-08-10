import FormalConjectures.Util.ProblemImports
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

open Nat Set

lemma prime_sq_sol (p : ℕ) (hp : p.Prime) : (p^2 - 1) % Nat.totient (p^2) = p - 1 := by
  have h1 : 0 < 2 := by decide
  rw [Nat.totient_prime_pow hp h1]
  have h2 : 2 - 1 = 1 := by rfl
  rw [h2, pow_one]
  have hp_ge : p ≥ 2 := hp.two_le
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp_ge
  -- Now p = 2 + q.
  have h_sub : 2 + q - 1 = 1 + q := by omega
  rw [h_sub]
  rw [pow_two]
  have h_add : (2 + q) * (2 + q) = (2 + q) * (1 + q) + (1 + q) + 1 := by ring
  have h3 : (2 + q) * (2 + q) - 1 = (2 + q) * (1 + q) + (1 + q) := by omega
  rw [h3]
  rw [Nat.add_mod_left]
  apply Nat.mod_eq_of_lt
  have h4 : 1 < 2 + q := by omega
  exact lt_mul_of_one_lt_left (by omega) h4


lemma prime_pow_sol (p : ℕ) (hp : p.Prime) (c : ℕ) (hc : c ≥ 1) :
    (p^(c+1) - 1) % (p^c * (p - 1)) = p^c - 1 := by
  have hp_ge : p ≥ 2 := hp.two_le
  have h_eq : p^(c+1) - 1 = p^c * (p - 1) + (p^c - 1) := by
    rw [pow_succ]
    have : p^c * p - 1 = p^c * (p - 1) + p^c - 1 := by
      rw [mul_tsub, mul_one]
      rw [tsub_add_cancel_of_le]
      apply Nat.le_mul_of_pos_right
      positivity
    rw [this]
    rw [Nat.add_sub_assoc]
    have : 0 < p^c := by positivity
    exact this
  rw [h_eq]
  have h_mod : (p^c * (p - 1) + (p^c - 1)) % (p^c * (p - 1)) = (p^c - 1) % (p^c * (p - 1)) := by
    rw [add_comm]
    rw [Nat.add_mod_right]
  rw [h_mod]
  apply Nat.mod_eq_of_lt
  have : p^c - 1 < p^c := Nat.sub_lt (by positivity) (by decide)
  have : p^c ≤ p^c * (p - 1) := by
    nth_rw 1 [← mul_one (p^c)]
    apply Nat.mul_le_mul_left
    omega
  omega

lemma even_one_odd_prime_sol (a : ℕ) (ha : a ≥ 1) (q : ℕ) (hq : q.Prime) (hq_odd : q ≠ 2) (c : ℕ)  :
    (2^a * q^(c+1) - 1) % (2^(a-1) * q^c * (q-1)) = 2^a * q^c - 1 := by
  have hq_ge : q ≥ 3 := by
    have : q ≥ 2 := hq.two_le
    omega
  have h2a : 2^a = 2 * 2^(a-1) := by
    have h_a : a = a - 1 + 1 := by omega
    nth_rw 1 [h_a]
    rw [pow_succ, mul_comm]
  have h_eq : 2^a * q^(c+1) - 1 = 2 * (2^(a-1) * q^c * (q-1)) + (2^a * q^c - 1) := by
    rw [h2a]
    have : 2 * 2^(a-1) * q^(c+1) - 1 = 2 * (2^(a-1) * q^c * (q-1)) + 2 * 2^(a-1) * q^c - 1 := by
      rw [pow_succ q]
      have h_mul1 : 2 * 2^(a-1) * (q^c * q) = 2 * 2^(a-1) * q^c * q := by ring
      rw [h_mul1]
      have h_mul2 : 2 * (2^(a-1) * q^c * (q-1)) + 2 * 2^(a-1) * q^c = 2 * 2^(a-1) * q^c * (q-1) + 2 * 2^(a-1) * q^c := by ring
      rw [h_mul2]
      rw [mul_tsub, mul_one]
      rw [tsub_add_cancel_of_le]
      apply Nat.le_mul_of_pos_right
      omega
    rw [this]
    rw [Nat.add_sub_assoc]
    have : 0 < 2 * 2^(a-1) * q^c := by positivity
    exact this
  rw [h_eq]
  have h_mod : (2 * (2^(a-1) * q^c * (q-1)) + (2^a * q^c - 1)) % (2^(a-1) * q^c * (q-1)) = (2^a * q^c - 1) % (2^(a-1) * q^c * (q-1)) := by
    rw [add_comm]
    have : 2 * (2^(a-1) * q^c * (q-1)) = (2^(a-1) * q^c * (q-1)) * 2 := by ring
    rw [this]
    rw [Nat.add_mul_mod_self_left]
  rw [h_mod]
  apply Nat.mod_eq_of_lt
  have : 2^a * q^c - 1 < 2^a * q^c := Nat.sub_lt (by positivity) (by decide)
  have : 2^a * q^c ≤ 2^(a-1) * q^c * (q-1) := by
    rw [h2a]
    have : 2 * 2^(a-1) * q^c = 2^(a-1) * q^c * 2 := by ring
    rw [this]
    apply Nat.mul_le_mul_left
    omega
  omega

lemma totient_divisor_sol_general (d : ℕ) (q : ℕ) (hq : q.Prime) 
    (c : ℕ) (w : ℕ) (k : ℕ) (hk : k ≥ 1) (h_dk : d ≥ k) (h_eq_w : w - d = k * (q - 1)) 
    (h_div : d.totient ∣ d - k) (h_ineq : d.totient * (q - 1) ≥ w) :
    (d * q^(c+1) - 1) % (d.totient * q^c * (q - 1)) = w * q^c - 1 := by
  have hd_pos : d > 0 := by omega
  have hq_pos : q > 0 := by
    have : q ≥ 2 := hq.two_le
    omega
  have h_qc_pos : q^c > 0 := by positivity
  have h_d_qc_pos : d * q^c > 0 := Nat.mul_pos hd_pos h_qc_pos
  have hq_ge : q ≥ 2 := hq.two_le
  have hq1 : q - 1 ≥ 1 := by omega
  have hkq1 : k * (q - 1) ≥ 1 := by
    calc k * (q - 1)
      _ ≥ 1 * 1 := Nat.mul_le_mul hk hq1
      _ = 1 := by rfl
  have hw : w = d + k * (q - 1) := by omega
  have hw_pos : w > 0 := by omega
  have hw_qc_pos : w * q^c > 0 := Nat.mul_pos hw_pos h_qc_pos
  have hd_q : d * q = (d - k) * (q - 1) + w := by
    rw [hw]
    set X := d - k
    set Y := q - 1
    have h1 : X * Y + (d + k * Y) = (X + k) * Y + d := by ring
    rw [h1]
    rw [Nat.sub_add_cancel h_dk]
    rw [mul_tsub, mul_one]
    rw [Nat.sub_add_cancel]
    apply Nat.le_mul_of_pos_right
    exact hq_pos
  obtain ⟨m, hm⟩ := h_div
  have h_eq : d * q^(c+1) - 1 = m * (d.totient * q^c * (q - 1)) + (w * q^c - 1) := by
    rw [pow_succ q c]
    have h1 : d * (q^c * q) = q^c * (d * q) := by ring
    rw [h1]
    rw [hd_q, hm]
    have h_sub : q^c * (d.totient * m * (q - 1) + w) - 1 = m * (d.totient * q^c * (q - 1)) + w * q^c - 1 := by
      set Y := q - 1
      have : q^c * (d.totient * m * Y + w) = m * (d.totient * q^c * Y) + w * q^c := by ring
      rw [this]
    rw [h_sub]
    rw [Nat.add_sub_assoc hw_qc_pos]
  rw [h_eq]
  have h_mod : (m * (d.totient * q^c * (q - 1)) + (w * q^c - 1)) % (d.totient * q^c * (q - 1)) = (w * q^c - 1) % (d.totient * q^c * (q - 1)) := by
    rw [add_comm]
    set Y := d.totient * q^c * (q - 1)
    have h_comm : m * Y = Y * m := mul_comm m Y
    rw [h_comm]
    rw [Nat.add_mul_mod_self_left]
  rw [h_mod]
  apply Nat.mod_eq_of_lt
  have : w * q^c - 1 < w * q^c := Nat.sub_lt hw_qc_pos (by decide)
  have : w * q^c ≤ d.totient * q^c * (q - 1) := by
    have h_mul_ineq : d.totient * (q - 1) * q^c ≥ w * q^c := Nat.mul_le_mul_right (q^c) h_ineq
    set Y := q - 1
    have : d.totient * q^c * Y = d.totient * Y * q^c := by ring
    rw [this]
    exact h_mul_ineq
  omega




/--
A268597: Smallest x such that (x-1) % totient(x) = n, or sInf empty if no such x exists.
-/
noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

/--
A268597 Conjecture: a(n) > 0 for all n.
-/
theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by
  have h_nonempty : { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }.Nonempty := by
    by_cases hn : n < 150
    · interval_cases n
      · use 1; decide
      · use 4; decide
      · use 9; decide
      · use 8; decide
      · use 25; decide
      · use 18; decide
      · use 15; decide
      · use 16; decide
      · use 21; decide
      · use 50; decide
      · use 35; decide
      · use 36; decide
      · use 33; decide
      · use 98; decide
      · use 39; decide
      · use 32; decide
      · use 65; decide
      · use 54; decide
      · use 51; decide
      · use 100; decide
      · use 45; decide
      · use 70; decide
      · use 95; decide
      · use 72; decide
      · use 69; decide
      · use 338; decide
      · use 63; decide
      · use 196; decide
      · use 161; decide
      · use 110; decide
      · use 87; decide
      · use 64; decide
      · use 93; decide
      · use 130; decide
      · use 75; decide
      · use 108; decide
      · use 217; decide
      · use 182; decide
      · use 99; decide
      · use 200; decide
      · use 185; decide
      · use 170; decide
      · use 123; decide
      · use 140; decide
      · use 117; decide
      · use 190; decide
      · use 215; decide
      · use 144; decide
      · use 141; decide
      · use 250; decide
      · use 235; decide
      · use 676; decide
      · use 329; decide
      · use 162; decide
      · use 159; decide
      · use 392; decide
      · use 153; decide
      · use 322; decide
      · use 371; decide
      · use 220; decide
      · use 177; decide
      · use 494; decide
      · use 135; decide
      · use 128; decide
      · use 305; decide
      · use 290; decide
      · use 427; decide
      · use 260; decide
      · use 201; decide
      · use 310; decide
      · use 335; decide
      · use 216; decide
      · use 213; decide
      · use 434; decide
      · use 207; decide
      · use 364; decide
      · use 245; decide
      · use 638; decide
      · use 511; decide
      · use 400; decide
      · use 189; decide
      · use 370; decide
      · use 395; decide
      · use 340; decide
      · use 249; decide
      · use 518; decide
      · use 415; decide
      · use 280; decide
      · use 581; decide
      · use 410; decide
      · use 267; decide
      · use 380; decide
      · use 261; decide
      · use 430; decide
      · use 623; decide
      · use 288; decide
      · use 1501; decide
      · use 602; decide
      · use 279; decide
      · use 500; decide
      · use 485; decide
      · use 462; decide
      · use 303; decide
      · use 1352; decide
      · use 225; decide
      · use 658; decide
      · use 515; decide
      · use 324; decide
      · use 321; decide
      · use 350; decide
      · use 231; decide
      · use 784; decide
      · use 545; decide
      · use 530; decide
      · use 339; decide
      · use 644; decide
      · use 297; decide
      · use 742; decide
      · use 539; decide
      · use 440; decide
      · use 1331; decide
      · use 1634; decide
      · use 1243; decide
      · use 988; decide
      · use 625; decide
      · use 510; decide
      · use 255; decide
      · use 256; decide
      · use 273; decide
      · use 610; decide
      · use 635; decide
      · use 580; decide
      · use 393; decide
      · use 854; decide
      · use 351; decide
      · use 520; decide
      · use 917; decide
      · use 570; decide
      · use 411; decide
      · use 620; decide
      · use 285; decide
      · use 670; decide
      · use 363; decide
      · use 432; decide
      · use 385; decide
      · use 938; decide
      · use 423; decide
      · use 868; decide
      · use 1529; decide
      · use 550; decide
    · by_cases hn2 : n < 300
      · have h_shift : n - 150 < 150 := by omega
        set m := n - 150 with hm
        rw [show n = m + 150 by omega]
        interval_cases m
        · use 447; decide
        · use 728; decide
        · use 453; decide
        · use 490; decide
        · use 755; decide
        · use 1276; decide
        · use 1057; decide
        · use 1022; decide
        · use 471; decide
        · use 800; decide
        · use 785; decide
        · use 486; decide
        · use 1099; decide
        · use 740; decide
        · use 357; decide
        · use 790; decide
        · use 455; decide
        · use 680; decide
        · use 345; decide
        · use 650; decide
        · use 459; decide
        · use 1036; decide
        · use 1169; decide
        · use 830; decide
        · use 375; decide
        · use 560; decide
        · use 865; decide
        · use 1162; decide
        · use 1211; decide
        · use 820; decide
        · use 537; decide
        · use 2054; decide
        · use 399; decide
        · use 760; decide
        · use 905; decide
        · use 890; decide
        · use 847; decide
        · use 860; decide
        · use 405; decide
        · use 1246; decide
        · use 1991; decide
        · use 576; decide
        · use 573; decide
        · use 3002; decide
        · use 507; decide
        · use 1204; decide
        · use 965; decide
        · use 870; decide
        · use 591; decide
        · use 1000; decide
        · use 597; decide
        · use 970; decide
        · use 995; decide
        · use 924; decide
        · use 925; decide
        · use 1358; decide
        · use 603; decide
        · use 2704; decide
        · use 2189; decide
        · use 850; decide
        · use 435; decide
        · use 1316; decide
        · use 633; decide
        · use 1030; decide
        · use 1055; decide
        · use 648; decide
        · use 1477; decide
        · use 1442; decide
        · use 483; decide
        · use 700; decide
        · use 845; decide
        · use 1070; decide
        · use 2743; decide
        · use 1568; decide
        · use 465; decide
        · use 1090; decide
        · use 1115; decide
        · use 1060; decide
        · use 681; decide
        · use 950; decide
        · use 687; decide
        · use 1288; decide
        · use 665; decide
        · use 1130; decide
        · use 699; decide
        · use 1484; decide
        · use 1165; decide
        · use 1078; decide
        · use 1631; decide
        · use 880; decide
        · use 561; decide
        · use 2662; decide
        · use 567; decide
        · use 3268; decide
        · use 1205; decide
        · use 1110; decide
        · use 1183; decide
        · use 1976; decide
        · use 1785; decide
        · use 1250; decide
        · use 2651; decide
        · use 1020; decide
        · use 753; decide
        · use 4142; decide
        · use 747; decide
        · use 512; decide
        · use 1757; decide
        · use 1554; decide
        · use 771; decide
        · use 1220; decide
        · use 1285; decide
        · use 1270; decide
        · use 1799; decide
        · use 1160; decide
        · use 789; decide
        · use 1274; decide
        · use 555; decide
        · use 1708; decide
        · use 1841; decide
        · use 1150; decide
        · use 807; decide
        · use 1040; decide
        · use 609; decide
        · use 1834; decide
        · use 875; decide
        · use 1140; decide
        · use 805; decide
        · use 3302; decide
        · use 663; decide
        · use 1240; decide
        · use 1001; decide
        · use 1290; decide
        · use 843; decide
        · use 1340; decide
        · use 849; decide
        · use 1390; decide
        · use 1415; decide
        · use 864; decide
        · use 1981; decide
        · use 1946; decide
        · use 651; decide
        · use 1876; decide
        · use 3113; decide
        · use 1806; decide
        · use 615; decide
        · use 1736; decide
        · use 837; decide
        · use 3058; decide
        · use 1859; decide
        · use 1100; decide
      · by_cases hp : (n+1).Prime
        · use (n+1)^2
          constructor
          · positivity
          · exact prime_sq_sol (n+1) hp
        · by_cases h_pow : IsPrimePow (n+1)
          · have h_nat : ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p ^ k = n + 1 := (isPrimePow_nat_iff (n+1)).mp h_pow
            obtain ⟨p, k, hp, hk, h_eq⟩ := h_nat
            obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
            use p^(c+2)
            constructor
            · have : p ≥ 2 := hp.two_le; positivity
            · have h_tot : Nat.totient (p^(c+2)) = p^(c+1) * (p - 1) := by
                have : c + 2 = (c + 1) + 1 := by omega
                rw [this]
                rw [Nat.totient_prime_pow hp (by omega)]
                have h_sub : c + 1 + 1 - 1 = c + 1 := by omega
                rw [h_sub]
              rw [h_tot]
              have h_sol := prime_pow_sol p hp (c+1) (by omega)
              rw [h_eq] at h_sol
              rw [h_eq]
              exact h_sol
          · sorry
  have h_mem := Nat.sInf_mem h_nonempty
  exact h_mem.1
