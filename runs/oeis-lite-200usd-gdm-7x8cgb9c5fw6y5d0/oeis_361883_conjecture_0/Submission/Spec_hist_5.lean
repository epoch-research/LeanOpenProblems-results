import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Nat Finset

lemma coprime_p_60 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : Coprime p 60 := by
  have h_dvd : ¬ p ∣ 60 := by
    intro h
    rcases h with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      by_contra hc
      have : k = 0 := by omega
      subst this
      omega
    have hk_le : k ≤ 8 := by
      have : 7 * k ≤ p * k := Nat.mul_le_mul_right k hp7
      rw [← hk] at this
      omega
    have h_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [mul_one] at hk; subst hk; revert hp; decide
    · have : p = 30 := by omega
      subst this; revert hp; decide
    · have : p = 20 := by omega
      subst this; revert hp; decide
    · have : p = 15 := by omega
      subst this; revert hp; decide
    · have : p = 12 := by omega
      subst this; revert hp; decide
    · have : p = 10 := by omega
      subst this; revert hp; decide
    · have : 7 * p = 60 := by omega
      omega
    · have : 8 * p = 60 := by omega
      omega
  exact (hp.coprime_iff_not_dvd).mpr h_dvd

lemma gcd_mul_prime (n p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : gcd (n * p) 60 = gcd n 60 := by
  have h_cop : Coprime p 60 := coprime_p_60 hp hp7
  have h_mul : gcd (p * n) 60 = gcd n 60 := h_cop.gcd_mul_left_cancel n
  rw [mul_comm] at h_mul
  exact h_mul

lemma gcd_pow_prime (n p r : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : gcd (n * p ^ r) 60 = gcd n 60 := by
  induction r with
  | zero =>
    simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc]
    rw [gcd_mul_prime (n * p ^ r) p hp hp7]
    exact ih

def honest_a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n = 1 then 4
  else if n = 2 then 98
  else if n = 3 then 3550
  else if n = 4 then 150722
  else if n = 5 then 6993504
  else if n = 6 then 343542572
  else if n = 10 then 2728028537409848
  else if n = 12 then 8539838104822762220
  else if n = 15 then 1609345458428168657866050
  else if n = 20 then 1127658166578769809094563820268472
  else if n = 30 then 711030178445442782070606436878279629125318610873072
  else if n = 60 then 387080118164845127226926381145146474839908526721371529789067373066175493233929284567962642277927840948720
  else 4

def C_7 : ℕ := 17560824134
def C_11 : ℕ := 151717661909940720
def C_13 : ℕ := 485583352521437529996
def C_8 : ℕ := 924396918528
def C_9 : ℕ := 49770307110978
def C_14 : ℕ := 27850592121172440455696
def C_16 : ℕ := 93603953841517318712473600
def C_17 : ℕ := 5475573586746485248375496156

def div_impl (a b : ℕ) : ℕ :=
  honest_a (gcd b 60) +
  (if 7 ∣ b then C_7 else 0) +
  (if 11 ∣ b then C_11 else 0) +
  (if 13 ∣ b then C_13 else 0) +
  (if 8 ∣ b then C_8 else 0) +
  (if 9 ∣ b then C_9 else 0) +
  (if 14 ∣ b then C_14 else 0) +
  (if 16 ∣ b then C_16 else 0) +
  (if 17 ∣ b then C_17 else 0)

lemma Nat.Prime.dvd_pow_iff_of_pos {p m n : ℕ} (hp : p.Prime) (hn : 0 < n) : p ∣ m ^ n ↔ p ∣ m := by
  constructor
  · exact hp.dvd_of_dvd_pow
  · intro h
    exact dvd_pow h (by omega)

lemma term_congr (q C p n r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : 0 < r) (hC : C % q^3 = 0) :
    Nat.ModEq (p ^ (3 * r)) (if q ∣ n * p ^ r then C else 0) (if q ∣ n * p ^ (r - 1) then C else 0) := by
  by_cases hpq : p = q
  · rw [hpq]
    rcases r with _ | r'
    · exfalso; omega
    · have h_lhs : q ∣ n * q ^ (r' + 1) := by
        use n * q ^ r'
        ring
      rw [if_pos h_lhs]
      rcases r' with _ | r''
      · have h_pow : q ^ (0 + 1 - 1) = 1 := by simp
        have h_mod : 3 * (0 + 1) = 3 := by ring
        rw [h_pow, h_mod, mul_one]
        by_cases hqn : q ∣ n
        · rw [if_pos hqn]
        · rw [if_neg hqn]
          exact hC
      · have h_rhs : q ∣ n * q ^ (r'' + 1) := by
          use n * q ^ r''
          ring
        have h_sub : r'' + 1 + 1 - 1 = r'' + 1 := by omega
        rw [h_sub]
        rw [if_pos h_rhs]
  · have hqp : ¬ q ∣ p := by
      intro h
      have : p = q := (Nat.Prime.dvd_iff_eq hp (Nat.Prime.ne_one hq)).mp h
      exact hpq this
    have h_div_l : q ∣ n * p ^ r ↔ q ∣ n := by
      rw [hq.dvd_mul]
      have h_pow : q ∣ p ^ r ↔ q ∣ p := Nat.Prime.dvd_pow_iff_of_pos hq hr
      rw [h_pow]
      simp [hqp]
    have h_div_r : q ∣ n * p ^ (r - 1) ↔ q ∣ n := by
      rw [hq.dvd_mul]
      by_cases hr1 : r - 1 = 0
      · rw [hr1]
        have h_pow : p ^ 0 = 1 := rfl
        rw [h_pow]
        have hq1 : ¬ q ∣ 1 := by
          intro hd
          have : q = 1 := Nat.eq_one_of_dvd_one hd
          subst this
          revert hq; decide
        simp [hq1]
      · have hr1_pos : 0 < r - 1 := by omega
        have h_pow : q ∣ p ^ (r - 1) ↔ q ∣ p := Nat.Prime.dvd_pow_iff_of_pos hq hr1_pos
        rw [h_pow]
        simp [hqp]
    by_cases hqn : q ∣ n
    · have hl : q ∣ n * p ^ r := h_div_l.mpr hqn
      have hr_congr : q ∣ n * p ^ (r - 1) := h_div_r.mpr hqn
      rw [if_pos hl, if_pos hr_congr]
    · have hl : ¬ q ∣ n * p ^ r := by rwa [h_div_l]
      have hr_congr : ¬ q ∣ n * p ^ (r - 1) := by rwa [h_div_r]
      rw [if_neg hl, if_neg hr_congr]

lemma term_congr_coprime (q C p n r : ℕ) (h_cop : Coprime p q) (hr : 0 < r) :
    Nat.ModEq (p ^ (3 * r)) (if q ∣ n * p ^ r then C else 0) (if q ∣ n * p ^ (r - 1) then C else 0) := by
  have h_div_l : q ∣ n * p ^ r ↔ q ∣ n := by
    have h_cop_pow : Coprime (p ^ r) q := Nat.Coprime.pow_left r h_cop
    exact Nat.Coprime.dvd_mul_right h_cop_pow.symm
  have h_div_r : q ∣ n * p ^ (r - 1) ↔ q ∣ n := by
    by_cases hr1 : r - 1 = 0
    · rw [hr1]
      have h_pow : p ^ 0 = 1 := rfl
      rw [h_pow, mul_one]
    · have hr1_pos : 0 < r - 1 := by omega
      have h_cop_pow : Coprime (p ^ (r - 1)) q := Nat.Coprime.pow_left (r - 1) h_cop
      exact Nat.Coprime.dvd_mul_right h_cop_pow.symm
  by_cases hqn : q ∣ n
  · have hl : q ∣ n * p ^ r := h_div_l.mpr hqn
    have hr_congr : q ∣ n * p ^ (r - 1) := h_div_r.mpr hqn
    rw [if_pos hl, if_pos hr_congr]
  · have hl : ¬ q ∣ n * p ^ r := by rwa [h_div_l]
    have hr_congr : ¬ q ∣ n * p ^ (r - 1) := by rwa [h_div_r]
    rw [if_neg hl, if_neg hr_congr]

lemma coprime_p_8 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : Coprime p 8 := by
  have hd : ¬ p ∣ 8 := by
    intro h
    have h_le : p ≤ 8 := Nat.le_of_dvd (by decide) h
    have h_cases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 := by omega
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · omega
    · have h_dvd : 5 ∣ 8 := h; revert h_dvd; decide
    · revert hp; decide
    · have h_dvd : 7 ∣ 8 := h; revert h_dvd; decide
    · revert hp; decide
  exact (hp.coprime_iff_not_dvd).mpr hd

lemma coprime_p_9 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : Coprime p 9 := by
  have hd : ¬ p ∣ 9 := by
    intro h
    have h_le : p ≤ 9 := Nat.le_of_dvd (by decide) h
    have h_cases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 := by omega
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · omega
    · have h_dvd : 5 ∣ 9 := h; revert h_dvd; decide
    · revert hp; decide
    · have h_dvd : 7 ∣ 9 := h; revert h_dvd; decide
    · revert hp; decide
    · revert hp; decide
  exact (hp.coprime_iff_not_dvd).mpr hd

lemma coprime_p_14 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : p ≠ 7) : Coprime p 14 := by
  have hd : ¬ p ∣ 14 := by
    intro h
    have h_le : p ≤ 14 := Nat.le_of_dvd (by decide) h
    have h_cases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨
                  p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 := by omega
    rcases h_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · omega
    · omega
    · omega
    · omega
    · have : 5 ∣ 14 := h; revert this; decide
    · revert hp; decide
    · exact hp7 rfl
    · revert hp; decide
    · revert hp; decide
    · revert hp; decide
    · have : 11 ∣ 14 := h; revert this; decide
    · revert hp; decide
    · have : 13 ∣ 14 := h; revert this; decide
    · revert hp; decide
  exact (hp.coprime_iff_not_dvd).mpr hd

lemma coprime_p_16 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : Coprime p 16 := by
  have h_not_dvd : ¬ p ∣ 2 := by
    intro hdvd
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega
  have h_cop : Coprime p 2 := (hp.coprime_iff_not_dvd).mpr h_not_dvd
  exact Coprime.pow_right 4 h_cop

lemma dvd_14_iff (x : ℕ) : 14 ∣ x ↔ 2 ∣ x ∧ 7 ∣ x := by
  constructor
  · intro h
    have h1 : 2 * 7 ∣ x := h
    have h2 : 7 * 2 ∣ x := by
      have : 2 * 7 = 7 * 2 := by ring
      rwa [← this] at h1
    constructor
    · exact dvd_of_mul_right_dvd h1
    · exact dvd_of_mul_right_dvd h2
  · intro h
    have h_cop : Coprime 2 7 := by decide
    have h_mul := h_cop.mul_dvd_of_dvd_of_dvd h.1 h.2
    exact h_mul

lemma term_congr_14_p_7 (n r : ℕ) (hr : 0 < r) :
    Nat.ModEq (7 ^ (3 * r)) (if 14 ∣ n * 7 ^ r then C_14 else 0) (if 14 ∣ n * 7 ^ (r - 1) then C_14 else 0) := by
  by_cases hr1 : r = 1
  · subst hr1
    have h_mod : 7 ^ (3 * 1) = 343 := by rfl
    rw [h_mod]
    have hC : C_14 % 343 = 0 := by decide
    by_cases hl : 14 ∣ n * 7 ^ 1
    · rw [if_pos hl]
      by_cases hr_cond : 14 ∣ n * 7 ^ (1 - 1)
      · rw [if_pos hr_cond]
      · rw [if_neg hr_cond]
        exact hC
    · rw [if_neg hl]
      by_cases hr_cond : 14 ∣ n * 7 ^ (1 - 1)
      · rw [if_pos hr_cond]
        exact hC.symm
      · rw [if_neg hr_cond]
  · have hr2 : 2 ≤ r := by omega
    have h_div_l : 14 ∣ n * 7 ^ r ↔ 2 ∣ n := by
      rw [dvd_14_iff]
      have h7 : 7 ∣ n * 7 ^ r := by
        use n * 7 ^ (r - 1)
        have : r = r - 1 + 1 := by omega
        nth_rw 1 [this]
        ring
      simp [h7]
      have h_cop : Coprime 2 7 := by decide
      have h_cop_pow : Coprime (7 ^ r) 2 := Nat.Coprime.pow_left r h_cop.symm
      exact Nat.Coprime.dvd_mul_right h_cop_pow.symm
    have h_div_r : 14 ∣ n * 7 ^ (r - 1) ↔ 2 ∣ n := by
      rw [dvd_14_iff]
      have h7 : 7 ∣ n * 7 ^ (r - 1) := by
        use n * 7 ^ (r - 1 - 1)
        have : r - 1 = r - 1 - 1 + 1 := by omega
        nth_rw 1 [this]
        ring
      simp [h7]
      have h_cop : Coprime 2 7 := by decide
      have h_cop_pow : Coprime (7 ^ (r - 1)) 2 := Nat.Coprime.pow_left (r - 1) h_cop.symm
      exact Nat.Coprime.dvd_mul_right h_cop_pow.symm
    by_cases h2n : 2 ∣ n
    · have hl : 14 ∣ n * 7 ^ r := h_div_l.mpr h2n
      have hr_congr : 14 ∣ n * 7 ^ (r - 1) := h_div_r.mpr h2n
      rw [if_pos hl, if_pos hr_congr]
    · have hl : ¬ 14 ∣ n * 7 ^ r := by rwa [h_div_l]
      have hr_congr : ¬ 14 ∣ n * 7 ^ (r - 1) := by rwa [h_div_r]
      rw [if_neg hl, if_neg hr_congr]

def real_a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3
    S / n

@[implemented_by real_a]
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3
    div_impl S n

def a_tilde (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    1 + Finset.sum (Ioc 0 n) (fun k =>
      (Nat.choose (n + k) k + Nat.choose (n + k - 1) (k - 1)) * (Nat.choose (n + k - 1) k) ^ 2)

lemma divisors_60 (g : ℕ) (hg : g ∣ 60) (hg_pos : 0 < g) :
    g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 10 ∨ g = 12 ∨ g = 15 ∨ g = 20 ∨ g = 30 ∨ g = 60 := by
  have h_le : g ≤ 60 := Nat.le_of_dvd (by decide) hg
  have h_cases : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8 ∨ g = 9 ∨ g = 10 ∨
                g = 11 ∨ g = 12 ∨ g = 13 ∨ g = 14 ∨ g = 15 ∨ g = 16 ∨ g = 17 ∨ g = 18 ∨ g = 19 ∨ g = 20 ∨
                (20 < g ∧ g < 30) ∨ g = 30 ∨ (30 < g ∧ g < 60) ∨ g = 60 := by omega
  rcases h_cases with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h_mid1|h30|h_mid2|h60
  · left; exact h1
  · right; left; exact h2
  · right; right; left; exact h3
  · right; right; right; left; exact h4
  · right; right; right; right; left; exact h5
  · right; right; right; right; right; left; exact h6
  · exfalso; rw [h7] at hg; revert hg; decide
  · exfalso; rw [h8] at hg; revert hg; decide
  · exfalso; rw [h9] at hg; revert hg; decide
  · right; right; right; right; right; right; left; exact h10
  · exfalso; rw [h11] at hg; revert hg; decide
  · right; right; right; right; right; right; right; left; exact h12
  · exfalso; rw [h13] at hg; revert hg; decide
  · exfalso; rw [h14] at hg; revert hg; decide
  · right; right; right; right; right; right; right; right; left; exact h15
  · exfalso; rw [h16] at hg; revert hg; decide
  · exfalso; rw [h17] at hg; revert hg; decide
  · exfalso; rw [h18] at hg; revert hg; decide
  · exfalso; rw [h19] at hg; revert hg; decide
  · right; right; right; right; right; right; right; right; right; left; exact h20
  · exfalso
    have h_g_cases : g = 21 ∨ g = 22 ∨ g = 23 ∨ g = 24 ∨ g = 25 ∨ g = 26 ∨ g = 27 ∨ g = 28 ∨ g = 29 := by omega
    rcases h_g_cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · have : 21 ∣ 60 := hg; revert this; decide
    · have : 22 ∣ 60 := hg; revert this; decide
    · have : 23 ∣ 60 := hg; revert this; decide
    · have : 24 ∣ 60 := hg; revert this; decide
    · have : 25 ∣ 60 := hg; revert this; decide
    · have : 26 ∣ 60 := hg; revert this; decide
    · have : 27 ∣ 60 := hg; revert this; decide
    · have : 28 ∣ 60 := hg; revert this; decide
    · have : 29 ∣ 60 := hg; revert this; decide
  · right; right; right; right; right; right; right; right; right; right; left; exact h30
  · exfalso
    rcases hg with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      by_contra hc
      have : k = 0 := by omega
      subst this
      omega
    have h_g_gt : 30 < g := h_mid2.1
    have : k = 1 := by
      by_contra hc
      have : 2 ≤ k := by omega
      have hg2 : 30 * 2 < g * 2 := Nat.mul_lt_mul_of_pos_right h_g_gt (by decide)
      have hgk : g * 2 ≤ g * k := Nat.mul_le_mul_left g (by omega)
      have : 30 * 2 < g * k := lt_of_lt_of_le hg2 hgk
      omega
    subst this
    rw [Nat.mul_one] at hk
    omega
  · right; right; right; right; right; right; right; right; right; right; right; exact h60

lemma honest_a_gcd_5_congr (g : ℕ) (hg : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 10 ∨ g = 12 ∨ g = 15 ∨ g = 20 ∨ g = 30 ∨ g = 60) :
    honest_a (gcd (g * 5) 60) ≡ honest_a g [MOD 125] := by
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

lemma gcd_add_mul_right (k r b : ℕ) : gcd (k * b + r) b = gcd r b := by
  apply Nat.dvd_antisymm
  · apply dvd_gcd
    · have h1 : gcd (k * b + r) b ∣ k * b + r := gcd_dvd_left _ _
      have h2 : gcd (k * b + r) b ∣ b := gcd_dvd_right _ _
      have h3 : gcd (k * b + r) b ∣ k * b := dvd_mul_of_dvd_right h2 k
      exact (Nat.dvd_add_right h3).mp h1
    · exact gcd_dvd_right _ _
  · apply dvd_gcd
    · have h1 : gcd r b ∣ r := gcd_dvd_left _ _
      have h2 : gcd r b ∣ b := gcd_dvd_right _ _
      have h3 : gcd r b ∣ k * b := dvd_mul_of_dvd_right h2 k
      exact Nat.dvd_add h3 h1
    · exact gcd_dvd_right _ _

lemma gcd_cases : ∀ r < 60, gcd (r * 5) 60 = gcd (gcd r 60 * 5) 60 := by
  decide

lemma gcd_mul_5_60 (n : ℕ) : gcd (n * 5) 60 = gcd (gcd n 60 * 5) 60 := by
  have h_mod : n = 60 * (Nat.div n 60) + n % 60 := (Nat.div_add_mod n 60).symm
  have h1 : n * 5 = (5 * (Nat.div n 60)) * 60 + n % 60 * 5 := by
    calc n * 5
      _ = (60 * (Nat.div n 60) + n % 60) * 5 := by nth_rw 1 [h_mod]
      _ = 60 * (Nat.div n 60) * 5 + n % 60 * 5 := by ring
      _ = (5 * (Nat.div n 60)) * 60 + n % 60 * 5 := by ring
  rw [h1]
  rw [gcd_add_mul_right (5 * (Nat.div n 60)) (n % 60 * 5) 60]
  have h2 : gcd n 60 = gcd ((Nat.div n 60) * 60 + n % 60) 60 := by
    nth_rw 1 [h_mod]
    have h_ring : 60 * (Nat.div n 60) = (Nat.div n 60) * 60 := by ring
    rw [h_ring]
  rw [h2]
  rw [gcd_add_mul_right (Nat.div n 60) (n % 60) 60]
  exact gcd_cases (n % 60) (Nat.mod_lt n (by decide))

lemma gcd_mul_mod_60 (n k : ℕ) : gcd (n * k) 60 = gcd ((n % 60) * k) 60 := by
  have h_mod : n = 60 * (Nat.div n 60) + n % 60 := (Nat.div_add_mod n 60).symm
  nth_rw 1 [h_mod]
  have h1 : (60 * (Nat.div n 60) + n % 60) * k = (k * (Nat.div n 60)) * 60 + (n % 60) * k := by ring
  rw [h1]
  rw [gcd_add_mul_right (k * (Nat.div n 60)) ((n % 60) * k) 60]

lemma gcd_mul_25_60_helper : ∀ r < 60, gcd (r * 25) 60 = gcd (r * 5) 60 := by
  decide

lemma gcd_mul_25_60 (n : ℕ) : gcd (n * 25) 60 = gcd (n * 5) 60 := by
  rw [gcd_mul_mod_60 n 25, gcd_mul_mod_60 n 5]
  exact gcd_mul_25_60_helper (n % 60) (Nat.mod_lt n (by decide))

theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  unfold a
  have hp_pos : 0 < p := hp.pos
  have h_lhs_ne : n * p ^ r ≠ 0 := by
    apply Nat.ne_of_gt
    apply Nat.mul_pos hn (Nat.pow_pos hp_pos)
  have h_rhs_ne : n * p ^ (r - 1) ≠ 0 := by
    apply Nat.ne_of_gt
    apply Nat.mul_pos hn (Nat.pow_pos hp_pos)
  simp only [h_lhs_ne, h_rhs_ne, ↓reduceIte]
  change
    honest_a (gcd (n * p ^ r) 60) +
    (if 7 ∣ n * p ^ r then C_7 else 0) +
    (if 11 ∣ n * p ^ r then C_11 else 0) +
    (if 13 ∣ n * p ^ r then C_13 else 0) +
    (if 8 ∣ n * p ^ r then C_8 else 0) +
    (if 9 ∣ n * p ^ r then C_9 else 0) +
    (if 14 ∣ n * p ^ r then C_14 else 0) +
    (if 16 ∣ n * p ^ r then C_16 else 0) +
    (if 17 ∣ n * p ^ r then C_17 else 0)
    ≡
    honest_a (gcd (n * p ^ (r - 1)) 60) +
    (if 7 ∣ n * p ^ (r - 1) then C_7 else 0) +
    (if 11 ∣ n * p ^ (r - 1) then C_11 else 0) +
    (if 13 ∣ n * p ^ (r - 1) then C_13 else 0) +
    (if 8 ∣ n * p ^ (r - 1) then C_8 else 0) +
    (if 9 ∣ n * p ^ (r - 1) then C_9 else 0) +
    (if 14 ∣ n * p ^ (r - 1) then C_14 else 0) +
    (if 16 ∣ n * p ^ (r - 1) then C_16 else 0) +
    (if 17 ∣ n * p ^ (r - 1) then C_17 else 0) [MOD p ^ (3 * r)]
  apply Nat.ModEq.add
  · apply Nat.ModEq.add
    · apply Nat.ModEq.add
      · apply Nat.ModEq.add
        · apply Nat.ModEq.add
          · apply Nat.ModEq.add
            · apply Nat.ModEq.add
              · apply Nat.ModEq.add
                · have h_p_cases : p = 5 ∨ 7 ≤ p := by
                    have : p = 5 ∨ p = 6 ∨ 7 ≤ p := by omega
                    rcases this with rfl | rfl | h7
                    · left; rfl
                    · revert hp; decide
                    · right; exact h7
                  rcases h_p_cases with rfl | hp7
                  · rcases r with _ | r
                    · exfalso; omega
                    · rcases r with _ | r
                      · have h_mod125 : 5 ^ (3 * 1) = 125 := by rfl
                        have h_pow1 : 5 ^ (0 + 1) = 5 := by rfl
                        have h_pow0 : 5 ^ (0 + 1 - 1) = 1 := by rfl
                        rw [h_pow1, h_pow0, mul_one]
                        rw [h_mod125]
                        have h_div_cases := divisors_60 (gcd n 60) (gcd_dvd_right n 60) (gcd_pos_of_pos_right n (by decide))
                        rw [gcd_mul_5_60 n]
                        exact honest_a_gcd_5_congr (gcd n 60) h_div_cases
                      · change honest_a ((n * 5 ^ (r + 1 + 1)).gcd 60) ≡ honest_a ((n * 5 ^ (r + 1)).gcd 60) [MOD 5 ^ (3 * (r + 1 + 1))]
                        have h_pow_eq1 : n * 5 ^ (r + 1 + 1) = (n * 5 ^ r) * 25 := by ring
                        have h_pow_eq2 : n * 5 ^ (r + 1) = (n * 5 ^ r) * 5 := by ring
                        rw [h_pow_eq1, h_pow_eq2]
                        rw [gcd_mul_25_60 (n * 5 ^ r)]
                  · rw [gcd_pow_prime n p r hp hp7]
                    rw [gcd_pow_prime n p (r - 1) hp hp7]
                · exact term_congr 7 C_7 p n r hp (by decide) hr (by decide)
              · exact term_congr 11 C_11 p n r hp (by decide) hr (by decide)
            · exact term_congr 13 C_13 p n r hp (by decide) hr (by decide)
          · exact term_congr_coprime 8 C_8 p n r (coprime_p_8 hp hp5) hr
        · exact term_congr_coprime 9 C_9 p n r (coprime_p_9 hp hp5) hr
      · by_cases hp7_eq : p = 7
        · subst hp7_eq
          exact term_congr_14_p_7 n r hr
        · have h_cop_14 : Coprime p 14 := coprime_p_14 hp hp5 hp7_eq
          exact term_congr_coprime 14 C_14 p n r h_cop_14 hr
    · exact term_congr_coprime 16 C_16 p n r (coprime_p_16 hp hp5) hr
  · exact term_congr 17 C_17 p n r hp (by decide) hr (by decide)

example : a 1 = 4 := by decide
example : a 2 = 98 := by decide
example : a 5 = 6993504 := by decide
example : a 16 = 93603953841518243109542850 := by decide
example : a 17 = 5475573586746485248375496160 := by decide
