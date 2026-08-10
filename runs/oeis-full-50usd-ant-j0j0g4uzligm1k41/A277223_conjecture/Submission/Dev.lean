import FormalConjectures.Util.ProblemImports

open Nat Set

private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

noncomputable def A277223 (n : ℕ) : ℕ :=
  let valid_multipliers : Set ℕ := { k | k = sum_digits_10 (k * n) }
  sSup valid_multipliers

-- digit sum is at most 9 * length
theorem dsum_le (m : ℕ) : sum_digits_10 m ≤ 9 * (Nat.digits 10 m).length := by
  have : ∀ d ∈ Nat.digits 10 m, d ≤ 9 := by
    intro d hd
    have := Nat.digits_lt_base (by norm_num) hd
    omega
  calc sum_digits_10 m ≤ (Nat.digits 10 m).length * 9 := by
        exact List.sum_le_card_nsmul _ 9 (by simpa using this)
    _ = 9 * (Nat.digits 10 m).length := by ring

-- length of digits = log + 1 for m ≠ 0
-- For BddAbove: any valid k satisfies k ≤ 9 * (length of k*n).
-- We bound the length. Let me find an explicit bound on k.

-- Key: if k = sum_digits_10 (k*n) and n ≥ 1, then k*n < 10^(length), and
-- length = log10(k*n)+1. We get k ≤ 9*(log10(k*n)+1).
-- Let me prove a bound B(n) on the valid set.

-- 18m ≤ 10^m for m ≥ 2
theorem h18 (m : ℕ) (hm : 2 ≤ m) : 18 * m ≤ 10 ^ m := by
  induction m with
  | zero => omega
  | succ i ih =>
    rcases Nat.lt_or_ge i 2 with h | h
    · interval_cases i <;> first | omega | norm_num
    · have hb := ih h
      have : (18:ℕ) ≤ 10^i := by
        calc (18:ℕ) ≤ 10^2 := by norm_num
          _ ≤ 10^i := Nat.pow_le_pow_right (by norm_num) h
      calc 18 * (i+1) = 18*i + 18 := by ring
        _ ≤ 10^i + 10^i := by omega
        _ ≤ 10^(i+1) := by rw [pow_succ]; omega

-- 18 * log10 k ≤ k for k ≥ 18
theorem log_bound (k : ℕ) (hk : 18 ≤ k) : 18 * Nat.log 10 k ≤ k := by
  set m := Nat.log 10 k with hm
  have hkpos : k ≠ 0 := by omega
  have hpow : 10 ^ m ≤ k := Nat.pow_log_le_self 10 hkpos
  rcases Nat.lt_or_ge m 2 with h | h
  · interval_cases m
    · omega
    · -- m = 1: 18*1 = 18 ≤ k
      omega
  · calc 18 * m ≤ 10 ^ m := h18 m h
      _ ≤ k := hpow

-- log of product: log10 (a*b) ≤ log10 a + log10 b + 1  (for a,b ≥ 1)
theorem log_mul_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.log 10 (a * b) ≤ Nat.log 10 a + Nat.log 10 b + 1 := by
  have ha' : a < 10 ^ (Nat.log 10 a + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
  have hb' : b < 10 ^ (Nat.log 10 b + 1) := Nat.lt_pow_succ_log_self (by norm_num) b
  have hab : a * b < 10 ^ (Nat.log 10 a + Nat.log 10 b + 2) := by
    calc a * b < 10 ^ (Nat.log 10 a + 1) * 10 ^ (Nat.log 10 b + 1) :=
          Nat.mul_lt_mul'' ha' hb'
      _ = 10 ^ (Nat.log 10 a + Nat.log 10 b + 2) := by rw [← pow_add]; ring_nf
  have := Nat.log_lt_of_lt_pow (Nat.mul_ne_zero ha hb) hab
  omega

-- The valid set is bounded: every fixed point k ≤ 18*log10 n + 36.
theorem valid_bound (n k : ℕ) (hn : 1 ≤ n) (hk : k = sum_digits_10 (k * n)) :
    k ≤ 18 * Nat.log 10 n + 36 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · omega
  · have hkn : k * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have hlen : (Nat.digits 10 (k * n)).length = Nat.log 10 (k * n) + 1 :=
      Nat.digits_len 10 (k * n) (by norm_num) hkn
    have h1 : k ≤ 9 * (Nat.log 10 (k * n) + 1) := by
      calc k = sum_digits_10 (k * n) := hk
        _ ≤ 9 * (Nat.digits 10 (k * n)).length := dsum_le _
        _ = 9 * (Nat.log 10 (k * n) + 1) := by rw [hlen]
    have h2 : Nat.log 10 (k * n) ≤ Nat.log 10 k + Nat.log 10 n + 1 :=
      log_mul_le k n (by omega) (by omega)
    rcases Nat.lt_or_ge k 18 with hlt | hge
    · omega
    · have hb := log_bound k hge
      omega

-- Membership and bddAbove for the valid set
theorem zero_mem_valid (n : ℕ) : (0 : ℕ) = sum_digits_10 (0 * n) := by
  simp [sum_digits_10]

theorem valid_bddAbove (n : ℕ) (hn : 1 ≤ n) :
    BddAbove {k | k = sum_digits_10 (k * n)} := by
  refine ⟨18 * Nat.log 10 n + 36, ?_⟩
  intro k hk
  exact valid_bound n k hn hk

-- A277223 n is itself a fixed point (an element of the valid set)
theorem A_mem (n : ℕ) (hn : 1 ≤ n) : A277223 n = sum_digits_10 (A277223 n * n) := by
  have hne : {k | k = sum_digits_10 (k * n)}.Nonempty := ⟨0, zero_mem_valid n⟩
  have hbdd := valid_bddAbove n hn
  have := Nat.sSup_mem hne hbdd
  simpa [A277223] using this

-- A277223 n is the maximum: any fixed point ≤ A277223 n
theorem A_max (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k = sum_digits_10 (k * n)) :
    k ≤ A277223 n := by
  have hbdd := valid_bddAbove n hn
  exact le_csSup hbdd hk

-- mod 9: any fixed point M satisfies 9 ∣ M*(n-1)
theorem fixed_mod9 (n M : ℕ) (hn : 1 ≤ n) (hM : M = sum_digits_10 (M * n)) :
    (9 : ℕ) ∣ M * (n - 1) := by
  have h := Nat.modEq_nine_digits_sum (M * n)
  have hM' : (Nat.digits 10 (M * n)).sum = M := hM.symm
  rw [hM'] at h            -- h : M * n ≡ M [MOD 9]
  have hle : M ≤ M * n := Nat.le_mul_of_pos_right M hn
  have hdvd : (9 : ℕ) ∣ M * n - M := (Nat.modEq_iff_dvd' hle).mp h.symm
  have heq : M * n - M = M * (n - 1) := by
    rw [Nat.mul_sub, Nat.mul_one]
  rwa [heq] at hdvd

-- g=1 case: if 3 ∤ (n-1) then 9 ∣ M
theorem g1_case (n M : ℕ) (hn : 1 ≤ n) (hM : M = sum_digits_10 (M * n))
    (h3 : ¬ (3 ∣ (n - 1))) : (9 : ℕ) ∣ M := by
  have hdvd := fixed_mod9 n M hn hM
  have hcop3 : Nat.Coprime 3 (n - 1) := (Nat.prime_three.coprime_iff_not_dvd).mpr h3
  have hcop9 : Nat.Coprime 9 (n - 1) := by
    have : Nat.Coprime (3 ^ 2) (n - 1) := hcop3.pow_left 2
    simpa using this
  exact hcop9.dvd_of_dvd_mul_right hdvd

-- digits of x + 10*y when x < 10 and x+10y > 0
theorem digits_low (x y : ℕ) (hx : x < 10) (hpos : 0 < x + 10 * y) :
    Nat.digits 10 (x + 10 * y) = x :: Nat.digits 10 y := by
  rw [Nat.digits_def' (b := 10) (by norm_num) hpos]
  congr 1
  · omega
  · congr 1; omega

-- No-carry multiplication for digit sums
theorem sum_mul_nocarry (c m : ℕ)
    (h : ∀ d ∈ Nat.digits 10 m, c * d < 10) :
    sum_digits_10 (c * m) = c * sum_digits_10 m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp [sum_digits_10]
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc; simp [sum_digits_10]
    have hm0 : m ≠ 0 := by omega
    have hdigm : Nat.digits 10 m = m % 10 :: Nat.digits 10 (m / 10) :=
      Nat.digits_def' (b := 10) (by norm_num) hm
    have hcd : c * (m % 10) < 10 := by
      apply h; rw [hdigm]; exact List.mem_cons_self
    have hdm := Nat.div_add_mod m 10
    have hdec : c * m = c * (m % 10) + 10 * (c * (m / 10)) := by
      conv_lhs => rw [← hdm]
      ring
    have hpos : 0 < c * (m % 10) + 10 * (c * (m / 10)) := by
      have : 0 < c * m := Nat.mul_pos hc hm
      omega
    have htail : ∀ d ∈ Nat.digits 10 (m / 10), c * d < 10 := by
      intro d hd; apply h; rw [hdigm]; exact List.mem_cons_of_mem _ hd
    have ihq := ih (m / 10) (Nat.div_lt_self hm (by norm_num)) htail
    have hL : sum_digits_10 (c * m) = c * (m % 10) + sum_digits_10 (c * (m / 10)) := by
      unfold sum_digits_10
      rw [hdec, digits_low _ _ hcd hpos, List.sum_cons]
    rw [hL, ihq]
    unfold sum_digits_10
    rw [hdigm, List.sum_cons, Nat.mul_add]

-- every digit of M*n is ≤ M (since digit sum = M)
theorem digbound (n M c : ℕ) (hMfix : M = sum_digits_10 (M * n)) (hcb : c * M ≤ 9) :
    ∀ d ∈ Nat.digits 10 (M * n), c * d < 10 := by
  intro d hd
  have hdle : d ≤ sum_digits_10 (M * n) := by
    unfold sum_digits_10
    exact List.single_le_sum (fun x _ => Nat.zero_le x) d hd
  rw [← hMfix] at hdle
  calc c * d ≤ c * M := Nat.mul_le_mul (le_refl c) hdle
    _ ≤ 9 := hcb
    _ < 10 := by norm_num

-- If M is the maximum and is small, doubling/scaling yields a larger fixed point: contradiction.
theorem kill (n M c : ℕ) (hn : 1 ≤ n) (hM1 : 1 ≤ M) (hMmax : A277223 n = M)
    (hMfix : M = sum_digits_10 (M * n)) (hc2 : 2 ≤ c) (hcb : c * M ≤ 9) : False := by
  have hdig := digbound n M c hMfix hcb
  have hfix2 : c * M = sum_digits_10 ((c * M) * n) := by
    have h1 : (c * M) * n = c * (M * n) := by ring
    rw [h1, sum_mul_nocarry c (M * n) hdig, ← hMfix]
  have hle := A_max n hn (c * M) hfix2
  rw [hMmax] at hle
  have h2M : 2 * M ≤ c * M := Nat.mul_le_mul hc2 (le_refl M)
  omega

-- digit sum invariant under multiplying by a power of 10
theorem ds_pow_mul (k m : ℕ) : sum_digits_10 (10 ^ k * m) = sum_digits_10 m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [sum_digits_10]
  · unfold sum_digits_10
    rw [Nat.digits_base_pow_mul (by norm_num) hm, List.sum_append]
    simp

-- Generalized kill: takes the digit hypothesis directly (no need cM ≤ 9)
theorem kill2 (n M c : ℕ) (hn : 1 ≤ n) (hMmax : A277223 n = M)
    (hMfix : M = sum_digits_10 (M * n)) (hc2 : 2 ≤ c)
    (hdig : ∀ d ∈ Nat.digits 10 (M * n), c * d < 10) (hM1 : 1 ≤ M) : False := by
  have hfix2 : c * M = sum_digits_10 ((c * M) * n) := by
    have h1 : (c * M) * n = c * (M * n) := by ring
    rw [h1, sum_mul_nocarry c (M * n) hdig, ← hMfix]
  have hle := A_max n hn (c * M) hfix2
  rw [hMmax] at hle
  have h2M : 2 * M ≤ c * M := Nat.mul_le_mul hc2 (le_refl M)
  omega

-- digit sum 0 implies the number is 0
theorem ds_zero (m : ℕ) (h : sum_digits_10 m = 0) : m = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exact hm
    · exfalso
      have hdig : Nat.digits 10 m = m % 10 :: Nat.digits 10 (m / 10) :=
        Nat.digits_def' (b := 10) (by norm_num) hm
      have : sum_digits_10 m = m % 10 + sum_digits_10 (m / 10) := by
        unfold sum_digits_10; rw [hdig, List.sum_cons]
      have htail : sum_digits_10 (m / 10) = 0 := by omega
      have hq0 : m / 10 = 0 := ih (m / 10) (Nat.div_lt_self hm (by norm_num)) htail
      have hmod0 : m % 10 = 0 := by omega
      omega

-- if the digit sum of m equals d ≥ 1 and d is itself a digit, then m = d * 10^j
theorem single_digit (m d : ℕ) (hd : 1 ≤ d) (hsum : sum_digits_10 m = d)
    (hmem : d ∈ Nat.digits 10 m) : ∃ j, m = d * 10 ^ j := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hm0 : m ≠ 0 := by
      rintro h; subst h; simp [sum_digits_10] at hsum; omega
    have hm : 0 < m := Nat.pos_of_ne_zero hm0
    have hdig : Nat.digits 10 m = m % 10 :: Nat.digits 10 (m / 10) :=
      Nat.digits_def' (b := 10) (by norm_num) hm
    have hsum' : m % 10 + sum_digits_10 (m / 10) = d := by
      have : sum_digits_10 m = m % 10 + sum_digits_10 (m / 10) := by
        unfold sum_digits_10; rw [hdig, List.sum_cons]
      omega
    rw [hdig] at hmem
    rcases List.mem_cons.mp hmem with hcase | hcase
    · -- d = m % 10, so tail sums to 0 ⟹ m/10 = 0
      have htail0 : sum_digits_10 (m / 10) = 0 := by omega
      have hq0 : m / 10 = 0 := ds_zero _ htail0
      refine ⟨0, ?_⟩
      have : m = m % 10 := by omega
      rw [this]; omega
    · -- d ∈ digits (m/10): then d ≤ sum tail, so m%10 = 0, tail sum = d
      have hge : d ≤ sum_digits_10 (m / 10) := by
        unfold sum_digits_10
        exact List.single_le_sum (fun y _ => Nat.zero_le y) d hcase
      have hmod0 : m % 10 = 0 := by omega
      have htail : sum_digits_10 (m / 10) = d := by omega
      have hq : 0 < m / 10 := by
        rcases Nat.eq_zero_or_pos (m/10) with h | h
        · rw [h] at htail; simp [sum_digits_10] at htail; omega
        · exact h
      obtain ⟨j, hj⟩ := ih (m / 10) (Nat.div_lt_self hm (by norm_num)) htail hcase
      refine ⟨j + 1, ?_⟩
      have : m = 10 * (m / 10) := by omega
      rw [this, hj]; ring

-- appending Y after the 3 digits of 125
theorem ds_125_append (Y : ℕ) :
    sum_digits_10 (125 + 1000 * Y) = 8 + sum_digits_10 Y := by
  have h1000 : (1000 : ℕ) = 10 ^ ((Nat.digits 10 125).length) := by
    have h3 : (Nat.digits 10 125).length = 3 := by simp
    rw [h3]; norm_num
  unfold sum_digits_10
  rw [h1000, ← Nat.digits_append_digits (by norm_num : (0:ℕ) < 10), List.sum_append]
  norm_num [sum_digits_10]

-- appending Z after the 2 digits of 25
theorem ds_25_append (Z : ℕ) :
    sum_digits_10 (25 + 100 * Z) = 7 + sum_digits_10 Z := by
  have h100 : (100 : ℕ) = 10 ^ ((Nat.digits 10 25).length) := by
    have h2 : (Nat.digits 10 25).length = 2 := by simp
    rw [h2]; norm_num
  unfold sum_digits_10
  rw [h100, ← Nat.digits_append_digits (by norm_num : (0:ℕ) < 10), List.sum_append]
  norm_num [sum_digits_10]

-- the key digit-sum identity: 125·10^p + 25·10^q has digit sum 15 for p ≠ q
theorem ds15 (p q : ℕ) (hpq : p ≠ q) :
    sum_digits_10 (125 * 10 ^ p + 25 * 10 ^ q) = 15 := by
  rcases Nat.lt_or_ge p q with hlt | hge
  · -- p < q
    obtain ⟨g, hg⟩ : ∃ g, q = p + g := ⟨q - p, by omega⟩
    have hgpos : 1 ≤ g := by omega
    have hfac : 125 * 10 ^ p + 25 * 10 ^ q = 10 ^ p * (125 + 25 * 10 ^ g) := by
      rw [hg]; ring
    rw [hfac, ds_pow_mul]
    rcases Nat.lt_or_ge g 3 with hg3 | hg3
    · interval_cases g
      · norm_num [sum_digits_10]
      · norm_num [sum_digits_10]
    · have hrw : 125 + 25 * 10 ^ g = 125 + 1000 * (25 * 10 ^ (g - 3)) := by
        have : (1000 : ℕ) * (25 * 10 ^ (g - 3)) = 25 * 10 ^ g := by
          rw [show (1000:ℕ) = 10 ^ 3 by norm_num, mul_comm (10^3) (25 * 10^(g-3)),
            mul_assoc, ← pow_add]
          congr 2; omega
        rw [this]
      rw [hrw, ds_125_append, show 25 * 10 ^ (g - 3) = 10 ^ (g - 3) * 25 by ring, ds_pow_mul]
      norm_num [sum_digits_10]
  · -- p > q
    have hpq' : q < p := by omega
    obtain ⟨g, hg⟩ : ∃ g, p = q + g := ⟨p - q, by omega⟩
    have hgpos : 1 ≤ g := by omega
    have hfac : 125 * 10 ^ p + 25 * 10 ^ q = 10 ^ q * (125 * 10 ^ g + 25) := by
      rw [hg]; ring
    rw [hfac, ds_pow_mul]
    rcases Nat.lt_or_ge g 2 with hg2 | hg2
    · interval_cases g
      · norm_num [sum_digits_10]
    · have hrw : 125 * 10 ^ g + 25 = 25 + 100 * (125 * 10 ^ (g - 2)) := by
        have : (100 : ℕ) * (125 * 10 ^ (g - 2)) = 125 * 10 ^ g := by
          rw [show (100:ℕ) = 10 ^ 2 by norm_num, mul_comm (10^2) (125 * 10^(g-2)),
            mul_assoc, ← pow_add]
          congr 2; omega
        rw [this]; ring
      rw [hrw, ds_25_append, show 125 * 10 ^ (g - 2) = 10 ^ (g - 2) * 125 by ring, ds_pow_mul]
      norm_num [sum_digits_10]

-- two-digit extraction: digit sum 6 with a 5 present ⟹ shape 5·10^a + 10^b
theorem two_digit (m : ℕ) (h5 : 5 ∈ Nat.digits 10 m) (hsum : sum_digits_10 m = 6) :
    ∃ a b, a ≠ b ∧ m = 5 * 10 ^ a + 10 ^ b := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hm0 : m ≠ 0 := by rintro h; subst h; simp [sum_digits_10] at hsum
    have hm : 0 < m := Nat.pos_of_ne_zero hm0
    have hdig : Nat.digits 10 m = m % 10 :: Nat.digits 10 (m / 10) :=
      Nat.digits_def' (b := 10) (by norm_num) hm
    have hsum' : m % 10 + sum_digits_10 (m / 10) = 6 := by
      have : sum_digits_10 m = m % 10 + sum_digits_10 (m / 10) := by
        unfold sum_digits_10; rw [hdig, List.sum_cons]
      omega
    rw [hdig] at h5
    rcases List.mem_cons.mp h5 with h50 | h5tail
    · -- 5 is the lowest digit: m % 10 = 5, so tail sums to 1
      have htail1 : sum_digits_10 (m / 10) = 1 := by omega
      -- tail has a digit 1 (single_digit)
      have h1mem : (1 : ℕ) ∈ Nat.digits 10 (m / 10) := by
        rcases Nat.eq_zero_or_pos (m / 10) with hq | hq
        · rw [hq] at htail1; simp [sum_digits_10] at htail1
        · -- positive, ds = 1, so it has a nonzero digit which must be 1
          by_contra hno
          have hall : ∀ x ∈ Nat.digits 10 (m / 10), x = 0 := by
            intro x hx
            rcases Nat.lt_or_ge x 1 with h | h
            · omega
            · rcases Nat.lt_or_ge x 2 with h2 | h2
              · exfalso; apply hno; have : x = 1 := by omega
                rwa [this] at hx
              · exfalso
                have hle : x ≤ sum_digits_10 (m / 10) := by
                  unfold sum_digits_10
                  exact List.single_le_sum (fun y _ => Nat.zero_le y) x hx
                omega
          have : m / 10 = 0 := ds_zero _ (by
            unfold sum_digits_10
            exact List.sum_eq_zero hall)
          omega
      obtain ⟨c, hc⟩ := single_digit (m / 10) 1 (by norm_num) htail1 h1mem
      refine ⟨0, c + 1, by omega, ?_⟩
      have hmrec : m = m % 10 + 10 * (m / 10) := by omega
      rw [hmrec, h50, hc]; ring
    · -- 5 is in the tail
      have htail5 : (5 : ℕ) ≤ sum_digits_10 (m / 10) := by
        unfold sum_digits_10
        exact List.single_le_sum (fun y _ => Nat.zero_le y) 5 h5tail
      have hmod_le : m % 10 ≤ 1 := by omega
      interval_cases hmod : (m % 10)
      · -- m % 10 = 0, recurse
        have htail6 : sum_digits_10 (m / 10) = 6 := by omega
        have hq : 0 < m / 10 := by
          rcases Nat.eq_zero_or_pos (m / 10) with h | h
          · rw [h] at htail6; simp [sum_digits_10] at htail6
          · exact h
        obtain ⟨a, b, hab, hrec⟩ :=
          ih (m / 10) (Nat.div_lt_self hm (by norm_num)) h5tail htail6
        refine ⟨a + 1, b + 1, by omega, ?_⟩
        have hmrec : m = 10 * (m / 10) := by omega
        rw [hmrec, hrec]; ring
      · -- m % 10 = 1: tail has digit sum 5 with a 5 → 5·10^c
        have htail5' : sum_digits_10 (m / 10) = 5 := by omega
        obtain ⟨c, hc⟩ := single_digit (m / 10) 5 (by norm_num) htail5' h5tail
        refine ⟨c + 1, 0, by omega, ?_⟩
        have hmrec : m = m % 10 + 10 * (m / 10) := by omega
        rw [hmrec, hmod, hc]; ring

theorem A277223_conjecture (n : ℕ) :
    n > 0 → (A277223 n < 12 → A277223 n = 0 ∨ A277223 n = 9) := by
  intro hn hlt
  have hMfix : A277223 n = sum_digits_10 (A277223 n * n) := A_mem n hn
  by_cases h3 : 3 ∣ (n - 1)
  · -- hard case: M = A277223 n < 12. Rule out small values.
    set M := A277223 n with hMdef
    clear_value M
    interval_cases M
    · left; rfl
    · exact absurd (kill n 1 9 hn (by norm_num) hMdef.symm hMfix (by norm_num) (by norm_num)) id
    · exact absurd (kill n 2 4 hn (by norm_num) hMdef.symm hMfix (by norm_num) (by norm_num)) id
    · exact absurd (kill n 3 3 hn (by norm_num) hMdef.symm hMfix (by norm_num) (by norm_num)) id
    · exact absurd (kill n 4 2 hn (by norm_num) hMdef.symm hMfix (by norm_num) (by norm_num)) id
    · -- M = 5
      exfalso
      by_cases hcase : ∀ d ∈ Nat.digits 10 (5 * n), d ≤ 4
      · exact kill2 n 5 2 hn hMdef.symm hMfix (by norm_num)
          (fun d hd => by have := hcase d hd; omega) (by norm_num)
      · push_neg at hcase
        obtain ⟨d, hd_mem, hd_gt⟩ := hcase
        have hd_le : d ≤ sum_digits_10 (5 * n) := by
          unfold sum_digits_10
          exact List.single_le_sum (fun y _ => Nat.zero_le y) d hd_mem
        have hd5 : d = 5 := by omega
        subst hd5
        obtain ⟨j, hj⟩ := single_digit (5 * n) 5 (by norm_num) hMfix.symm hd_mem
        have hn10 : n = 10 ^ j := Nat.eq_of_mul_eq_mul_left (by norm_num) hj
        have h9fix : (9 : ℕ) = sum_digits_10 (9 * n) := by
          rw [hn10]
          have h9p : 9 * 10 ^ j = 10 ^ j * 9 := by ring
          rw [h9p, ds_pow_mul]; simp [sum_digits_10]
        have hle := A_max n hn 9 h9fix
        rw [← hMdef] at hle
        omega
    · -- M = 6
      exfalso
      by_cases hcase : ∀ d ∈ Nat.digits 10 (6 * n), d ≤ 4
      · exact kill2 n 6 2 hn hMdef.symm hMfix (by norm_num)
          (fun d hd => by have := hcase d hd; omega) (by norm_num)
      · push_neg at hcase
        obtain ⟨d, hd_mem, hd_gt⟩ := hcase
        have hd_le : d ≤ sum_digits_10 (6 * n) := by
          unfold sum_digits_10
          exact List.single_le_sum (fun y _ => Nat.zero_le y) d hd_mem
        -- d ∈ {5, 6}
        have hd_le6 : d ≤ 6 := by omega
        interval_cases d
        · -- d = 5: structure {5,1}
          obtain ⟨a, b, hab, hm6⟩ := two_digit (6 * n) hd_mem hMfix.symm
          have heven : (2:ℕ) ∣ 6 * n := ⟨3 * n, by ring⟩
          have key : (2:ℕ) ∣ 5 * 10 ^ a + 10 ^ b := by rw [← hm6]; exact heven
          have ha1 : 1 ≤ a := by
            by_contra h
            have ha0 : a = 0 := by omega
            rw [ha0] at key
            have hb1 : 1 ≤ b := by omega
            have hdb : (2:ℕ) ∣ 10 ^ b := dvd_trans (by norm_num) (dvd_pow_self 10 (by omega))
            simp only [pow_zero, mul_one] at key
            omega
          have hb1 : 1 ≤ b := by
            by_contra h
            have hb0 : b = 0 := by omega
            rw [hb0] at key
            have hda : (2:ℕ) ∣ 10 ^ a := dvd_trans (by norm_num) (dvd_pow_self 10 (by omega))
            have hda5 : (2:ℕ) ∣ 5 * 10 ^ a := hda.mul_left 5
            simp only [pow_zero, mul_one] at key
            omega
          obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          obtain ⟨b', hb'⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
          have hab' : a' ≠ b' := by omega
          have h15n : 15 * n = 125 * 10 ^ a' + 25 * 10 ^ b' := by
            apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
            have lhs : 2 * (15 * n) = 5 * (6 * n) := by ring
            rw [lhs, hm6, ha', hb']; ring
          have h15fix : (15 : ℕ) = sum_digits_10 (15 * n) := by
            rw [h15n, ds15 a' b' hab']
          have hle := A_max n hn 15 h15fix
          rw [← hMdef] at hle
          omega
        · -- d = 6: single big digit
          obtain ⟨j, hj⟩ := single_digit (6 * n) 6 (by norm_num) hMfix.symm hd_mem
          have hn10 : n = 10 ^ j := Nat.eq_of_mul_eq_mul_left (by norm_num) hj
          have h9fix : (9 : ℕ) = sum_digits_10 (9 * n) := by
            rw [hn10]
            have h9p : 9 * 10 ^ j = 10 ^ j * 9 := by ring
            rw [h9p, ds_pow_mul]; simp [sum_digits_10]
          have hle := A_max n hn 9 h9fix
          rw [← hMdef] at hle
          omega
    · sorry  -- M = 7  (OPEN)
    · sorry  -- M = 8  (OPEN)
    · right; rfl
    · sorry  -- M = 10 (OPEN)
    · sorry  -- M = 11 (OPEN)
  · have h9 : (9 : ℕ) ∣ A277223 n := g1_case n (A277223 n) hn hMfix h3
    obtain ⟨c, hc⟩ := h9
    omega
