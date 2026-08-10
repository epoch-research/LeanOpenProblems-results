/-Copyright 2026 The Formal Conjectures Authors.Licensed under the Apache License, Version 2.0 (the "License");you may not use this file except in compliance with the License.You may obtain a copy of the License at    https://www.apache.org/licenses/LICENSE-2.0Unless required by applicable law or agreed to in writing, softwaredistributed under the License is distributed on an "AS IS" BASIS,WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.See the License for the specific language governing permissions andlimitations under the License.-/import FormalConjectures.Util.ProblemImportsset_option warningAsError falsenamespace Submission.Specopen Natopen Classical/--A272479: $a(n)$ is the smallest $k$ different from $n$ such that $(n, k)$ is a Harshad amicable pair.Let $D(n)$ be the sum of digits of $n$.$m$ and $k$ are Harshad amicable if they are distinct integers such that $D(m) \mid k$ and $D(k) \mid m$.For any $n$ with no Harshad amicable partner, $a(n)=0$ (Conjecture: the sequence contains no zeros.)-/noncomputable def a (n : ℕ) : ℕ :=  let dsum (m : ℕ) : ℕ := (digits 10 m).sum  let partners : Set ℕ := {k | k > 0 ∧ k ≠ n ∧ dsum n ∣ k ∧ dsum k ∣ n}  if partners.Nonempty then    sInf partners  else    0
intro n hn
def ten_pow_pos (p : ℕ) : 10^p > 0 := by
  induction p with
  | zero => simp
  | succ p ih =>
    have : 10^(p+1) = 10 * 10^p := by ring
    rw [this]
    omega

def ten_pow_gt (n : ℕ) : n < 10^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 10^(n+2) = 10 * 10^(n+1) := by ring
    rw [h1]
    have h2 : 10 * 10^(n+1) ≥ 10 * (n + 1) := Nat.mul_le_mul_left 10 ih
    omega

def dsum_pos (n : ℕ) (hn : n > 0) : (digits 10 n).sum > 0 := by
  have hb : 1 < 10 := by omega
  have h_ne : digits 10 n ≠ [] := digits_ne_nil_iff_ne_zero.mpr (_root_.ne_of_gt hn)
  have h_mem : (digits 10 n).getLast h_ne ∈ digits 10 n := List.getLast_mem h_ne
  have h_last_ne : (digits 10 n).getLast h_ne ≠ 0 := getLast_digit_ne_zero 10 (_root_.ne_of_gt hn)
  have h_last_pos : (digits 10 n).getLast h_ne > 0 := Nat.pos_of_ne_zero h_last_ne
  have h_sum_ge : (digits 10 n).sum ≥ (digits 10 n).getLast h_ne := by
    exact List.le_sum_of_mem h_mem
  omega

def sum_0_b (r b : ℕ) : ℕ :=
  Nat.recOn b
    0
    (fun _ ih => 1 + 10^r * ih)

def sum_ten_pow_shifted (a b r : ℕ) : ℕ :=
  Nat.recOn a
    (sum_0_b r b)
    (fun _ ih => 10 + 10^r * ih)

def sum_ten_pow_shifted_eq_0_0 (r : ℕ) : sum_ten_pow_shifted 0 0 r = 0 := rfl

def sum_ten_pow_shifted_eq_succ_a (a b r : ℕ) : sum_ten_pow_shifted (a + 1) b r = 10 + 10^r * sum_ten_pow_shifted a b r := rfl

def sum_ten_pow_shifted_eq_0_succ_b (b r : ℕ) : sum_ten_pow_shifted 0 (b + 1) r = 1 + 10^r * sum_ten_pow_shifted 0 b r := rfl

def sum_ten_pow_shifted_eq_0_1 (r : ℕ) : sum_ten_pow_shifted 0 1 r = 1 := by
  show sum_ten_pow_shifted 0 (0 + 1) r = 1
  rw [sum_ten_pow_shifted_eq_0_succ_b, sum_ten_pow_shifted_eq_0_0]
  simp

def sum_ten_pow_shifted_eq_1_0 (r : ℕ) : sum_ten_pow_shifted 1 0 r = 10 := by
  show sum_ten_pow_shifted (0 + 1) 0 r = 10
  rw [sum_ten_pow_shifted_eq_succ_a, sum_ten_pow_shifted_eq_0_0]
  simp

def d0_prime (d0 : ℕ) : ℕ := d0 / d0.gcd 9

def dsum_mul_pow_ten (d p : ℕ) (hd : d > 0) : (digits 10 (d * 10^p)).sum = (digits 10 d).sum := by
  have hb : 1 < 10 := by omega
  have hd_pos : 0 < d := hd
  have h_eq : d * 10^p = 0 + 10 ^ ((digits 10 0).length + p) * d := by
    simp
    ring
  rw [h_eq]
  rw [← digits_append_zeroes_append_digits hb hd_pos]
  simp

def dsum_le (n : ℕ) : (digits 10 n).sum ≤ n := by
  rcases n with _|n
  · simp
  · have hb2 : 2 ≤ 10 := by omega
    have h_eq : ofDigits 10 (digits 10 (n + 1)) = n + 1 := ofDigits_digits 10 (n + 1)
    have h_le_of : (digits 10 (n+1)).sum ≤ ofDigits 10 (digits 10 (n + 1)) := by
      induction (digits 10 (n+1)) with
      | nil => simp
      | cons x L ih =>
        simp [ofDigits]
        have h2 : ofDigits 10 L ≤ 10 * ofDigits 10 L := by
          have : 1 * ofDigits 10 L ≤ 10 * ofDigits 10 L := Nat.mul_le_mul_right (ofDigits 10 L) (by omega)
          simpa using this
        omega
    omega

def partners_nonempty_of_dsum_dvd_n (n : ℕ) (hn : n > 0) (h_div : (digits 10 n).sum ∣ n) :
    ( {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} : Set ℕ ).Nonempty := by
  use n * 10^(n+1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h10_pos := ten_pow_pos (n+1)
    exact Nat.mul_pos hn h10_pos
  · have h_gt : 10^(n+1) > n := ten_pow_gt n
    have h_mul_ge : n * 10^(n+1) ≥ 1 * 10^(n+1) :=
      Nat.mul_le_mul_right (10^(n+1)) hn
    omega
  · exact dvd_mul_of_dvd_left h_div _
  · rw [dsum_mul_pow_ten n (n+1) hn]
    exact h_div

def dsum_mod_nine (n : ℕ) : n ≡ (digits 10 n).sum [MOD 9] := by
  have h1 : 10 % 9 = 1 := by omega
  exact modEq_digits_sum 9 10 h1 n

def coprime_factorization (d : ℕ) (hd0 : d > 0) : ∃ d0 d1 : ℕ, d = d0 * d1 ∧ Coprime d0 10 ∧ d1 ∣ 10^d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases h2 : d % 2 = 0
    · have hd2 : d / 2 < d := Nat.div_lt_self hd0 (by omega)
      by_cases hd2_zero : d / 2 = 0
      · omega
      · have hd2_pos : d / 2 > 0 := Nat.pos_of_ne_zero hd2_zero
        rcases ih (d / 2) hd2 hd2_pos with ⟨d0, d1, heq, hcop, hd1_dvd⟩
        use d0, d1 * 2
        refine ⟨?_, hcop, ?_⟩
        · have h_eq_div : d = (d / 2) * 2 := (Nat.div_add_mod d 2).symm.trans (by omega)
          rw [h_eq_div, heq]
          ring
        · have h_eq_div : d = (d / 2) + (d - d / 2) := by omega
          rw [h_eq_div, Nat.pow_add]
          have h2_dvd : 2 ∣ 10^(d - d / 2) := by
            have : d - d / 2 ≥ 1 := by omega
            have : 10^(d - d/2) = 10 * 10^(d - d/2 - 1) := by
              have h_eq_pow : d - d / 2 = 1 + (d - d / 2 - 1) := by omega
              rw [h_eq_pow, Nat.pow_add]
              simp
            rw [this]
            exact dvd_mul_of_dvd_left (by decide) _
          exact mul_dvd_mul hd1_dvd h2_dvd
    · by_cases h5 : d % 5 = 0
      · have hd5 : d / 5 < d := Nat.div_lt_self hd0 (by omega)
        by_cases hd5_zero : d / 5 = 0
        · omega
        · have hd5_pos : d / 5 > 0 := Nat.pos_of_ne_zero hd5_zero
          rcases ih (d / 5) hd5 hd5_pos with ⟨d0, d1, heq, hcop, hd1_dvd⟩
          use d0, d1 * 5
          refine ⟨?_, hcop, ?_⟩
          · have h_eq_div : d = (d / 5) * 5 := (Nat.div_add_mod d 5).symm.trans (by omega)
            rw [h_eq_div, heq]
            ring
          · have h_eq_div : d = (d / 5) + (d - d / 5) := by omega
            rw [h_eq_div, Nat.pow_add]
            have h5_dvd : 5 ∣ 10^(d - d / 5) := by
              have : d - d / 5 ≥ 1 := by omega
              have : 10^(d - d/5) = 10 * 10^(d - d/5 - 1) := by
                have h_eq_pow : d - d / 5 = 1 + (d - d / 5 - 1) := by omega
                rw [h_eq_pow, Nat.pow_add]
                simp
              rw [this]
              exact dvd_mul_of_dvd_left (by decide) _
            exact mul_dvd_mul hd1_dvd h5_dvd
      · use d, 1
        refine ⟨?_, ?_, ?_⟩
        · ring
        · have h_gcd2 : d.gcd 2 = 1 := by
            have : ¬ 2 ∣ d := by
              intro h_dvd
              have : d % 2 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
              contradiction
            have h1 : d.gcd 2 ∣ 2 := d.gcd_dvd_right 2
            have h2_dvd : d.gcd 2 ∣ d := d.gcd_dvd_left 2
            have h3 : d.gcd 2 > 0 := Nat.gcd_pos_of_pos_right d (by decide)
            have h4 : d.gcd 2 ≤ 2 := Nat.le_of_dvd (by decide) h1
            have h5 : d.gcd 2 ≠ 2 := by
              intro hc
              have : 2 ∣ d := hc ▸ h2_dvd
              contradiction
            omega
          have h_gcd5 : d.gcd 5 = 1 := by
            have : ¬ 5 ∣ d := by
              intro h_dvd
              have : d % 5 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
              contradiction
            have h1 : d.gcd 5 ∣ 5 := d.gcd_dvd_right 5
            have h5_dvd : d.gcd 5 ∣ d := d.gcd_dvd_left 5
            have h3 : d.gcd 5 > 0 := Nat.gcd_pos_of_pos_right d (by decide)
            have h4 : d.gcd 5 ≤ 5 := Nat.le_of_dvd (by decide) h1
            have h5 : d.gcd 5 ≠ 5 := by
              intro hc
              have : 5 ∣ d := hc ▸ h5_dvd
              contradiction
            have h_ne2 : d.gcd 5 ≠ 2 := by
              intro hc
              have : 2 ∣ 5 := hc ▸ h1
              contradiction
            have h_ne3 : d.gcd 5 ≠ 3 := by
              intro hc
              have : 3 ∣ 5 := hc ▸ h1
              contradiction
            have h_ne4 : d.gcd 5 ≠ 4 := by
              intro hc
              have : 4 ∣ 5 := hc ▸ h1
              contradiction
            omega
          have h_gcd10 : d.gcd 10 = 1 := by
            have h10 : (10 : ℕ) = 2 * 5 := by decide
            rw [h10]
            exact Coprime.mul_right h_gcd2 h_gcd5
          exact h_gcd10
        · simp

noncomputable def exists_pow_ten_mod_eq_one (d : ℕ) (hd : d > 0) (h_cop : Coprime d 10) :
    ∃ r : ℕ, r > 0 ∧ 10^r ≡ 1 [MOD d] := by
  have h_pigeonhole : ∃ x y : Fin (d + 1), x < y ∧ (10^(x : ℕ)) % d = (10^(y : ℕ)) % d := by
    have h_card : Fintype.card (Fin d) < Fintype.card (Fin (d + 1)) := by simp
    rcases Fintype.exists_ne_map_eq_of_card_lt (fun (i : Fin (d + 1)) => (⟨(10^(i : ℕ)) % d, Nat.mod_lt _ hd⟩ : Fin d)) h_card with ⟨x, y, h_ne, h_eq⟩
    simp at h_eq
    rcases lt_trichotomy (x : ℕ) (y : ℕ) with h_lt | h_eq_val | h_gt
    · use x, y
      refine ⟨h_lt, h_eq⟩
    · exfalso
      exact h_ne (Fin.ext h_eq_val)
    · use y, x
      refine ⟨h_gt, h_eq.symm⟩
  rcases h_pigeonhole with ⟨x, y, h_lt, h_eq_val⟩
  use (y : ℕ) - (x : ℕ)
  have hr_pos : (y : ℕ) - (x : ℕ) > 0 := by omega
  refine ⟨hr_pos, ?_⟩
  by_cases hd1 : d = 1
  · subst hd1
    simp [Nat.ModEq, Nat.mod_one]
  · have hd_gt1 : d > 1 := by omega
    have h_eq_mul : 10^(y : ℕ) = 10^(x : ℕ) * 10^((y:ℕ) - (x:ℕ)) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have h_mod : (10^(x : ℕ) * 10^((y:ℕ) - (x:ℕ))) % d = 10^(x : ℕ) % d := by
      rw [← h_eq_mul]
      exact h_eq_val.symm
    have h_cop_pow : Coprime d (10^(x : ℕ)) := Coprime.pow_right (x : ℕ) h_cop
    have h_modeq : 10^(x : ℕ) * 10^((y:ℕ) - (x:ℕ)) ≡ 10^(x : ℕ) * 1 [MOD d] := by
      simp [Nat.ModEq]
      rw [h_mod]
    exact Nat.ModEq.cancel_left_of_coprime h_cop_pow h_modeq

noncomputable def exists_a_congruence (d0_prime_val n c : ℕ) (h_pos : d0_prime_val > 0) (h_cop : Coprime c d0_prime_val) :
    ∃ a, (a < d0_prime_val ∨ d0_prime_val = 1 ∧ a = 0) ∧ (c * a + n) % d0_prime_val = 0 := by
  by_cases h1 : d0_prime_val ≤ 1
  · use 0
    have : d0_prime_val = 1 := by omega
    subst this
    simp [Nat.mod_one]
  · have hgt : d0_prime_val > 1 := by omega
    have h_cop_symm : Coprime c d0_prime_val := h_cop
    rcases Nat.exists_mul_mod_eq_one_of_coprime h_cop_symm hgt with ⟨x, hx, h_inv⟩
    let val := (d0_prime_val - (n % d0_prime_val)) % d0_prime_val
    let a := (x * val) % d0_prime_val
    use a
    have ha_lt : a < d0_prime_val := Nat.mod_lt _ (by omega)
    refine ⟨Or.inl ha_lt, ?_⟩
    have h_mod : (c * a + n) % d0_prime_val = 0 := by
      have h_a_eq : a ≡ x * val [MOD d0_prime_val] := by
        simp [Nat.ModEq, a]
      have h_a : c * a ≡ c * (x * val) [MOD d0_prime_val] := Nat.ModEq.mul_left c h_a_eq
      have h_inv_modeq : c * x ≡ 1 [MOD d0_prime_val] := by
        simp [Nat.ModEq, h_inv, Nat.mod_eq_of_lt hgt]
      have h_inv_val : (c * x) * val ≡ 1 * val [MOD d0_prime_val] := Nat.ModEq.mul_right val h_inv_modeq
      have h_assoc : c * (x * val) = (c * x) * val := by ring
      have h_9a : c * a ≡ val [MOD d0_prime_val] := by
        have h_tmp : c * a ≡ (c * x) * val [MOD d0_prime_val] := by
          rw [← h_assoc]
          exact h_a
        have h_tmp2 : (c * x) * val ≡ val [MOD d0_prime_val] := by
          simp [Nat.ModEq] at h_inv_val ⊢
          exact h_inv_val
        exact Nat.ModEq.trans h_tmp h_tmp2
      have h_9a_add : c * a + n ≡ val + n [MOD d0_prime_val] := Nat.ModEq.add_right n h_9a
      have h_val_n : (val + n) % d0_prime_val = 0 := by
        have h_add : (d0_prime_val - n % d0_prime_val) % d0_prime_val + n ≡ (d0_prime_val - n % d0_prime_val) + n [MOD d0_prime_val] := by
          simp [Nat.ModEq]
        have h_eq_sub : (d0_prime_val - n % d0_prime_val) + n = d0_prime_val + (n - n % d0_prime_val) := by
          have hn_le : n % d0_prime_val ≤ n := Nat.mod_le n d0_prime_val
          have h_sub_le : n % d0_prime_val < d0_prime_val := Nat.mod_lt n (by omega)
          omega
        have h_mod_zero : (d0_prime_val + (n - n % d0_prime_val)) % d0_prime_val = 0 := by
          rw [Nat.add_mod]
          have h_eq_div_add : n = d0_prime_val * (n / d0_prime_val) + n % d0_prime_val := (Nat.div_add_mod n d0_prime_val).symm
          have h_mult : n - n % d0_prime_val = d0_prime_val * (n / d0_prime_val) := by omega
          rw [h_mult]
          simp
        have h_tmp : ((d0_prime_val - n % d0_prime_val) % d0_prime_val + n) % d0_prime_val = ((d0_prime_val - n % d0_prime_val) + n) % d0_prime_val := h_add
        rw [h_tmp, h_eq_sub, h_mod_zero]
      have h_val_n_modeq : val + n ≡ 0 [MOD d0_prime_val] := by
        simp [Nat.ModEq, h_val_n]
      exact Nat.ModEq.trans h_9a_add h_val_n_modeq
    exact h_mod

def dsum_add_mul_pow_ten (n m P k : ℕ) (hm : m > 0) (hp : P = (digits 10 n).length + k) :
    (digits 10 (n + 10^P * m)).sum = (digits 10 n).sum + (digits 10 m).sum := by
  have hb : 1 < 10 := by omega
  have h_eq : n + 10^P * m = n + 10^((digits 10 n).length + k) * m := by
    rw [hp]
  rw [h_eq]
  rw [← digits_append_zeroes_append_digits hb hm]
  simp

def sum_ten_pow_shifted_pos (a b r : ℕ) (h : a > 0 ∨ b > 0) : sum_ten_pow_shifted a b r > 0 := by
  rcases a with _|a
  · rcases b with _|b
    · omega
    · rw [sum_ten_pow_shifted_eq_0_succ_b]
      omega
  · rw [sum_ten_pow_shifted_eq_succ_a]
    omega

def sum_ten_pow_shifted_dsum (a b r : ℕ) (hr : r ≥ 2) :
    (digits 10 (sum_ten_pow_shifted a b r)).sum = a + b := by
  induction a generalizing b with
  | zero =>
    induction b with
    | zero =>
      rw [sum_ten_pow_shifted_eq_0_0]
      simp
    | succ b ih =>
      by_cases hb0 : b = 0
      · simp [hb0]
        rw [sum_ten_pow_shifted_eq_0_1]
        simp
      · have h_pos : sum_ten_pow_shifted 0 b r > 0 := sum_ten_pow_shifted_pos 0 b r (Or.inr (by omega))
        have h_len : (digits 10 1).length = 1 := by simp
        have hp : r = (digits 10 1).length + (r - 1) := by omega
        rw [sum_ten_pow_shifted_eq_0_succ_b]
        rw [dsum_add_mul_pow_ten 1 (sum_ten_pow_shifted 0 b r) r (r - 1) h_pos hp]
        simp
        rw [ih]
        omega
  | succ a ih =>
    by_cases hab0 : a = 0 ∧ b = 0
    · simp [hab0]
      rw [sum_ten_pow_shifted_eq_1_0]
      simp
    · have h_pos : sum_ten_pow_shifted a b r > 0 := sum_ten_pow_shifted_pos a b r (by omega)
      have h_len : (digits 10 10).length = 2 := by simp
      have hp : r = (digits 10 10).length + (r - 2) := by omega
      rw [sum_ten_pow_shifted_eq_succ_a]
      rw [dsum_add_mul_pow_ten 10 (sum_ten_pow_shifted a b r) r (r - 2) h_pos hp]
      simp
      rw [ih b]
      omega

def sum_ten_pow_shifted_mod (a b r d0 : ℕ) (h_inv : 10^r ≡ 1 [MOD d0]) :
    sum_ten_pow_shifted a b r ≡ 10 * a + b [MOD d0] := by
  induction a generalizing b with
  | zero =>
    induction b with
    | zero =>
      rw [sum_ten_pow_shifted_eq_0_0]
    | succ b ih =>
      by_cases hb0 : b = 0
      · subst hb0
        change sum_ten_pow_shifted 0 1 r ≡ 10 * 0 + 1 [MOD d0]
        rw [sum_ten_pow_shifted_eq_0_1]
      · rw [sum_ten_pow_shifted_eq_0_succ_b]
        have h_add : 1 + 10^r * sum_ten_pow_shifted 0 b r ≡ 1 + 1 * sum_ten_pow_shifted 0 b r [MOD d0] := by
          simp [Nat.ModEq] at h_inv ⊢
          rw [Nat.add_mod, Nat.mul_mod, h_inv]
          simp
        have h_sub : 1 + 1 * sum_ten_pow_shifted 0 b r = 1 + sum_ten_pow_shifted 0 b r := by ring
        rw [h_sub] at h_add
        have h_final : 1 + sum_ten_pow_shifted 0 b r ≡ 0 * 10 + (b + 1) [MOD d0] := by
          have h_eq_arith : 0 * 10 + (b + 1) = 1 + b := by ring
          rw [h_eq_arith]
          have ih_b : sum_ten_pow_shifted 0 b r ≡ b [MOD d0] := by
            have : 0 * 10 + b = b := by ring
            rw [this] at ih
            exact ih
          exact Nat.ModEq.add_left 1 ih_b
        exact Nat.ModEq.trans h_add h_final
  | succ a ih =>
    by_cases hab0 : a = 0 ∧ b = 0
    · rcases hab0 with ⟨rfl, rfl⟩
      change sum_ten_pow_shifted 1 0 r ≡ 10 * 1 + 0 [MOD d0]
      rw [sum_ten_pow_shifted_eq_1_0]
    · rw [sum_ten_pow_shifted_eq_succ_a]
      have h_add : 10 + 10^r * sum_ten_pow_shifted a b r ≡ 10 + 1 * sum_ten_pow_shifted a b r [MOD d0] := by
        simp [Nat.ModEq] at h_inv ⊢
        rw [Nat.add_mod, Nat.mul_mod, h_inv]
        simp
      have h_sub : 10 + 1 * sum_ten_pow_shifted a b r = 10 + sum_ten_pow_shifted a b r := by ring
      rw [h_sub] at h_add
      have h_final : 10 + sum_ten_pow_shifted a b r ≡ 10 * (a + 1) + b [MOD d0] := by
        have h_eq_arith : 10 * (a + 1) + b = 10 + (10 * a + b) := by ring
        rw [h_eq_arith]
        exact Nat.ModEq.add_left 10 (ih b)
      exact Nat.ModEq.trans h_add h_final

def d0_prime_dvd (d0 : ℕ) : d0_prime d0 ∣ d0 := by
  show (d0 / d0.gcd 9) ∣ d0
  exact div_dvd_of_dvd (Nat.gcd_dvd_left d0 9)

def dvd_of_dvd_div (a n d0 : ℕ) (hg : d0.gcd 9 ∣ n) (hdvd : (d0 / d0.gcd 9) ∣ (9 / d0.gcd 9) * a + (n / d0.gcd 9)) :
    d0 ∣ 9 * a + n := by
  let g := d0.gcd 9
  let nine_prime := 9 / g
  let d0_prime_val := d0 / g
  let n_prime := n / g
  rcases hdvd with ⟨k, hk⟩
  have h_mul : g * (nine_prime * a + n_prime) = g * (d0_prime_val * k) := by rw [hk]
  have h_dist : g * (nine_prime * a + n_prime) = (g * nine_prime) * a + g * n_prime := by
    ring
  rw [h_dist] at h_mul
  have h_g_nine : g * nine_prime = 9 := by
    unfold nine_prime
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right d0 9)
  have h_g_n : g * n_prime = n := by
    unfold n_prime
    exact Nat.mul_div_cancel' hg
  have h_g_d0 : g * d0_prime_val = d0 := by
    unfold d0_prime_val
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left d0 9)
  rw [h_g_nine, h_g_n] at h_mul
  have h_right : g * (d0_prime_val * k) = d0 * k := by
    calc g * (d0_prime_val * k) = (g * d0_prime_val) * k := by ring
    _ = d0 * k := by rw [h_g_d0]
  rw [h_right] at h_mul
  exact ⟨k, h_mul⟩

def dvd_of_modeq_nine (n g d0 d1 : ℕ) (hd : (digits 10 n).sum = d0 * d1) (hg : g = d0.gcd 9) : g ∣ n := by
  have h_modeq := dsum_mod_nine n
  have h_g_dvd_9 : g ∣ 9 := by
    rw [hg]
    exact Nat.gcd_dvd_right d0 9
  have h_modeq_g : n ≡ (digits 10 n).sum [MOD g] := Nat.ModEq.of_dvd h_g_dvd_9 h_modeq
  have h_g_dvd_d : g ∣ (digits 10 n).sum := by
    rw [hd]
    have : g ∣ d0 := by
      rw [hg]
      exact Nat.gcd_dvd_left d0 9
    exact dvd_mul_of_dvd_left this d1
  have h_mod_g : (digits 10 n).sum % g = 0 := Nat.mod_eq_zero_of_dvd h_g_dvd_d
  have h_n_mod_g : n % g = (digits 10 n).sum % g := h_modeq_g
  have h_n_mod : n % g = 0 := h_n_mod_g.trans h_mod_g
  exact Nat.dvd_of_mod_eq_zero h_n_mod

noncomputable def partners_nonempty (n : ℕ) (hn : n > 0) :
    ( {k | k > 0 ∧ k ≠ n ∧ (digits 10 n).sum ∣ k ∧ (digits 10 k).sum ∣ n} : Set ℕ ).Nonempty := by
  by_cases hn10 : n < 10
  · have h_dsum : (digits 10 n).sum = n := by
      have : n ≠ 0 := by omega
      rw [Nat.digits_of_lt 10 n this (by omega)]
      simp
    apply partners_nonempty_of_dsum_dvd_n n hn
    rw [h_dsum]
  · have hn10_le : n ≥ 10 := by omega
    let d := (digits 10 n).sum
    have hd0 : d > 0 := dsum_pos n hn
    rcases coprime_factorization d hd0 with ⟨d0, d1, h_eq, h_cop, hd1_dvd⟩
    have hd0_pos : d0 > 0 := by
      rcases d0 with _|d0
      · rcases d1 with _|d1
        · rw [h_eq] at hd0; contradiction
        · rw [h_eq] at hd0; contradiction
      · omega
    have h_d0_prime_pos : d0_prime d0 > 0 := by
      change d0 / d0.gcd 9 > 0
      have h0 : d0.gcd 9 > 0 := Nat.gcd_pos_of_pos_right d0 (by decide)
      have hd : d0.gcd 9 ∣ d0 := Nat.gcd_dvd_left d0 9
      exact Nat.div_pos (Nat.le_of_dvd hd0_pos hd) h0
    have h_cop_nine_prime : Coprime (9 / d0.gcd 9) (d0_prime d0) := by
      have h_gcd_pos : d0.gcd 9 > 0 := Nat.gcd_pos_of_pos_right d0 (by decide)
      have h_cop_div := Nat.coprime_div_gcd_div_gcd h_gcd_pos
      change Coprime (9 / d0.gcd 9) (d0 / d0.gcd 9)
      exact h_cop_div.symm
    let g := d0.gcd 9
    let nine_prime := 9 / g
    let n_prime := n / g
    rcases exists_a_congruence (d0_prime d0) n_prime nine_prime h_d0_prime_pos h_cop_nine_prime with ⟨a, h_cases_a, h_congruence⟩
    have ha_lt_n : a < n := by
      rcases h_cases_a with ha_lt | h_d1
      · have hd0_prime_le_d0 : d0_prime d0 ≤ d0 := by
          have : d0_prime d0 ∣ d0 := d0_prime_dvd d0
          exact Nat.le_of_dvd hd0_pos this
        have hd0_le_d : d0 ≤ d := by
          rcases d1 with _|d1
          · rw [h_eq] at hd0; contradiction
          · rw [h_eq]
            exact Nat.le_mul_of_pos_right d0 (by omega)
        have hd_le_n : d ≤ n := dsum_le n
        omega
      · rcases h_d1 with ⟨_, rfl⟩
        omega
    let b := n - a
    have hb_pos : b > 0 := by omega
    have hab_or : a > 0 ∨ b > 0 := Or.inr hb_pos
    rcases exists_pow_ten_mod_eq_one d0 hd0_pos h_cop with ⟨r', hr'_pos, hr'⟩
    let r := 2 * r'
    have hr_ge2 : r ≥ 2 := by omega
    have h_inv : 10^r ≡ 1 [MOD d0] := by
      have : 10^r = (10^r')^2 := by ring
      rw [this]
      have h1 : (10^r')^2 ≡ 1^2 [MOD d0] := Nat.ModEq.pow 2 hr'
      simp at h1
      exact h1
    let K := sum_ten_pow_shifted a b r
    have h_K_pos : K > 0 := sum_ten_pow_shifted_pos a b r hab_or
    have h_K_dsum : (digits 10 K).sum = n := by
      have : (digits 10 K).sum = a + b := sum_ten_pow_shifted_dsum a b r hr_ge2
      rw [this]
      omega
    have h_K_mod : K ≡ 10 * a + b [MOD d0] := sum_ten_pow_shifted_mod a b r d0 h_inv
    have h_arith : 10 * a + b = 9 * a + n := by omega
    rw [h_arith] at h_K_mod
    have hg_dvd_n : d0.gcd 9 ∣ n := dvd_of_modeq_nine n (d0.gcd 9) d0 d1 h_eq rfl
    have hd0_dvd_val : d0 ∣ 9 * a + n := by
      have h_div_val : d0_prime d0 ∣ (9 / d0.gcd 9) * a + (n / d0.gcd 9) := Nat.dvd_of_mod_eq_zero h_congruence
      exact dvd_of_dvd_div a n d0 hg_dvd_n h_div_val
    have h_K_mod_zero : K ≡ 0 [MOD d0] := by
      have : (9 * a + n) ≡ 0 [MOD d0] := Nat.modEq_zero_iff_dvd.mpr hd0_dvd_val
      exact h_K_mod.trans this
    have hd0_dvd_K : d0 ∣ K := Nat.modEq_zero_iff_dvd.mp h_K_mod_zero
    use K * 10^(n+1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : 10^(n+1) > 0 := ten_pow_pos (n+1)
      exact Nat.mul_pos h_K_pos this
    · have : K * 10^(n+1) ≥ 1 * 10^(n+1) := Nat.mul_le_mul_right (10^(n+1)) h_K_pos
      have h_gt : 10^(n+1) > n := ten_pow_gt n
      omega
    · have h_cop_d0_d1 : Coprime d0 d1 := by
        have h_cop_d0_10d : Coprime d0 (10^d) := Coprime.pow_right d h_cop
        exact Nat.Coprime.of_dvd_right hd1_dvd h_cop_d0_10d
      have hd0_dvd_k : d0 ∣ K * 10^(n+1) := dvd_mul_of_dvd_left hd0_dvd_K _
      have hd1_dvd_k : d1 ∣ K * 10^(n+1) := by
        have hd1_dvd_pow : d1 ∣ 10^(n+1) := by
          have hd_le_n1 : d ≤ n + 1 := by
            have : d ≤ n := dsum_le n
            omega
          have h_pow_dvd : 10^d ∣ 10^(n+1) := by
            have : n + 1 = d + (n + 1 - d) := by omega
            rw [this, Nat.pow_add]
            exact dvd_mul_of_dvd_left (dvd_rfl) _
          exact dvd_trans hd1_dvd h_pow_dvd
        exact dvd_mul_of_dvd_right hd1_dvd_pow _
      change d ∣ K * 10^(n+1)
      rw [h_eq]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h_cop_d0_d1 hd0_dvd_k hd1_dvd_k
    · rw [dsum_mul_pow_ten K (n+1) h_K_pos, h_K_dsum]

/-- A272479 Conjecture: the sequence contains no zeros. -/
@[category research open, AMS 11]
theorem oeis_272479_conjecture_0 : ∀ n : ℕ, n > 0 → a n ≠ 0 := by
  intro n hn
  unfold a
  dsimp
  split_ifs with h
  · have h_mem := Nat.sInf_mem h
    exact _root_.ne_of_gt h_mem.1
  · exfalso
    exact h (partners_nonempty n hn)

end Submission.Spec
