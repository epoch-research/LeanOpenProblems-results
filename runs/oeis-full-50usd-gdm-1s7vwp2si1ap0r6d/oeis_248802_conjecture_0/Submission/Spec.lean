import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/--
A248802: Smallest prime factor of ^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

-- General Helper Lemmas
lemma periodic_induction (P : ℕ → Prop) (T : ℕ) (hT : 0 < T)
    (base : ∀ n < T, P n) (step : ∀ n, P n → P (n + T)) (n : ℕ) : P n := by
  have hE : n = T * (n / T) + n % T := (Nat.div_add_mod n T).symm
  rw [hE]
  have hr : n % T < T := Nat.mod_lt n hT
  generalize h_div : n / T = q
  generalize h_mod : n % T = r
  rw [h_mod] at hr
  clear hE h_div h_mod
  induction q with
  | zero =>
    simp only [Nat.mul_zero, zero_add]
    exact base r hr
  | succ q ih =>
    have h_step : T * (q + 1) + r = (T * q + r) + T := by ring
    rw [h_step]
    exact step (T * q + r) ih

lemma pow_modEq_pow_mod (a d p E : ℕ) (h : a ^ d ≡ 1 [MOD p]) : a ^ E ≡ a ^ (E % d) [MOD p] := by
  have hE : E = d * (E / d) + E % d := (Nat.div_add_mod E d).symm
  nth_rw 1 [hE]
  rw [pow_add, pow_mul]
  have h1 : (a ^ d) ^ (E / d) ≡ 1 ^ (E / d) [MOD p] := Nat.ModEq.pow (E / d) h
  rw [one_pow] at h1
  have h2 : (a ^ d) ^ (E / d) * a ^ (E % d) ≡ 1 * a ^ (E % d) [MOD p] := Nat.ModEq.mul h1 (Nat.ModEq.refl _)
  rw [one_mul] at h2
  exact h2

def pow2_mod (d : ℕ) : ℕ → ℕ
  | 0 => 1 % d
  | i + 1 => (pow2_mod d i * 2) % d

lemma pow2_mod_eq (d i : ℕ) : 2 ^ i ≡ pow2_mod d i [MOD d] := by
  induction i with
  | zero =>
    simp [pow2_mod]
    exact (Nat.mod_modEq 1 d).symm
  | succ i ih =>
    simp [pow2_mod]
    have h1 : 2 ^ (i + 1) = 2 ^ i * 2 := rfl
    rw [h1]
    have h2 : 2 ^ i * 2 ≡ pow2_mod d i * 2 [MOD d] := Nat.ModEq.mul_right 2 ih
    have h3 : pow2_mod d i * 2 ≡ (pow2_mod d i * 2) % d [MOD d] := (Nat.mod_modEq _ d).symm
    exact h2.trans h3

lemma base_case_helper (p d c : ℕ) (h2d : 2 ^ d ≡ 1 [MOD p]) :
    2 ^ (2 ^ (10 * c + 2) + 2) + 3 ≡ 2 ^ ((pow2_mod d (10 * c + 2) + 2) % d) + 3 [MOD p] := by
  have h1 := pow2_mod_eq d (10 * c + 2)
  have h2 := Nat.ModEq.add_right 2 h1
  have h3 : (2 ^ (10 * c + 2) + 2) % d = (pow2_mod d (10 * c + 2) + 2) % d := h2
  have h4 := pow_modEq_pow_mod 2 d p (2 ^ (10 * c + 2) + 2) h2d
  rw [h3] at h4
  exact Nat.ModEq.add_right 3 h4

lemma exp_congruence_helper (d T : ℕ) (h_base : 2 ^ (10 * T + 2) ≡ 2 ^ 2 [MOD d])
    (h_step : 2 ^ (10 * T) * 2 ^ 12 ≡ 2 ^ 12 [MOD d]) (n : ℕ) :
    2 ^ (10 * (n + T) + 2) ≡ 2 ^ (10 * n + 2) [MOD d] := by
  induction n with
  | zero =>
    simp only [Nat.mul_zero, zero_add] at h_base ⊢
    exact h_base
  | succ n ih =>
    have h_add1 : 10 * (n + 1 + T) + 2 = 10 * (n + T) + 12 := by omega
    have h_add2 : 10 * (n + 1) + 2 = 10 * n + 12 := by omega
    rw [h_add1, h_add2]
    have h_add3 : 10 * (n + T) + 12 = 10 * T + 10 * n + 12 := by omega
    rw [h_add3]
    have h_add5 : 10 * T + 10 * n + 12 = 10 * n + (10 * T + 12) := by omega
    rw [h_add5, pow_add]
    rw [pow_add]
    rw [pow_add]
    have h_mul : 2 ^ (10 * n) * (2 ^ (10 * T) * 2 ^ 12) ≡ 2 ^ (10 * n) * 2 ^ 12 [MOD d] := by
      exact Nat.ModEq.mul (Nat.ModEq.refl _) h_step
    exact h_mul

lemma hE_proof_general (d T : ℕ) (h_base : 2 ^ (10 * T + 2) ≡ 2 ^ 2 [MOD d])
    (h_step : 2 ^ (10 * T) * 2 ^ 12 ≡ 2 ^ 12 [MOD d]) (n : ℕ) :
    (2 ^ (10 * (n + T) + 2) + 2) % d = (2 ^ (10 * n + 2) + 2) % d :=
  Nat.ModEq.add_right 2 (exp_congruence_helper d T h_base h_step n)

lemma step_mod (p d T : ℕ) (h2d : 2 ^ d ≡ 1 [MOD p])
    (hE : ∀ n, (2 ^ (10 * (n + T) + 2) + 2) % d = (2 ^ (10 * n + 2) + 2) % d) (n : ℕ) :
    2 ^ (2 ^ (10 * (n + T) + 2) + 2) ≡ 2 ^ (2 ^ (10 * n + 2) + 2) [MOD p] := by
  have h1 := pow_modEq_pow_mod 2 d p (2 ^ (10 * (n + T) + 2) + 2) h2d
  have h2 := pow_modEq_pow_mod 2 d p (2 ^ (10 * n + 2) + 2) h2d
  rw [hE n] at h1
  exact h1.trans h2.symm

lemma step_dvd_general (p d T : ℕ) (h2d : 2 ^ d ≡ 1 [MOD p])
    (hE : ∀ n, (2 ^ (10 * (n + T) + 2) + 2) % d = (2 ^ (10 * n + 2) + 2) % d) (n : ℕ)
    (h : ¬ p ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) : ¬ p ∣ 2 ^ (2 ^ (10 * (n + T) + 2) + 2) + 3 := by
  have h_eq := step_mod p d T h2d hE n
  have h_eq_add := Nat.ModEq.add_right 3 h_eq
  have h_dvd : p ∣ 2 ^ (2 ^ (10 * (n + T) + 2) + 2) + 3 ↔ p ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 :=
    Nat.ModEq.dvd_iff h_eq_add (dvd_refl p)
  tauto

theorem not_dvd_2 (n : ℕ) : ¬ 2 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have hE : 2 ^ (10 * n + 2) + 2 = (2 ^ (10 * n + 2) + 1) + 1 := by omega
  rw [hE, pow_succ]
  omega

theorem not_dvd_3 (E : ℕ) : ¬ 3 ∣ 2 ^ E + 3 := by
  have h2d : 2 ^ 2 ≡ 1 [MOD 3] := by
    have h := pow2_mod_eq 3 2
    have h_val : pow2_mod 3 2 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_eq := pow_modEq_pow_mod 2 2 3 E h2d
  have h_eq_add := Nat.ModEq.add_right 3 h_eq
  have h_dvd : 3 ∣ 2 ^ E + 3 ↔ 3 ∣ 2 ^ (E % 2) + 3 := Nat.ModEq.dvd_iff h_eq_add (dvd_refl 3)
  rw [h_dvd]
  have hr : E % 2 < 2 := Nat.mod_lt E (by decide)
  interval_cases E % 2 <;> decide

theorem not_dvd_17 (E : ℕ) : ¬ 17 ∣ 2 ^ E + 3 := by
  have h2d : 2 ^ 8 ≡ 1 [MOD 17] := by
    have h := pow2_mod_eq 17 8
    have h_val : pow2_mod 17 8 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_eq := pow_modEq_pow_mod 2 8 17 E h2d
  have h_eq_add := Nat.ModEq.add_right 3 h_eq
  have h_dvd : 17 ∣ 2 ^ E + 3 ↔ 17 ∣ 2 ^ (E % 8) + 3 := Nat.ModEq.dvd_iff h_eq_add (dvd_refl 17)
  rw [h_dvd]
  have hr : E % 8 < 8 := Nat.mod_lt E (by decide)
  interval_cases E % 8 <;> decide

theorem not_dvd_23 (E : ℕ) : ¬ 23 ∣ 2 ^ E + 3 := by
  have h2d : 2 ^ 11 ≡ 1 [MOD 23] := by
    have h := pow2_mod_eq 23 11
    have h_val : pow2_mod 23 11 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_eq := pow_modEq_pow_mod 2 11 23 E h2d
  have h_eq_add := Nat.ModEq.add_right 3 h_eq
  have h_dvd : 23 ∣ 2 ^ E + 3 ↔ 23 ∣ 2 ^ (E % 11) + 3 := Nat.ModEq.dvd_iff h_eq_add (dvd_refl 23)
  rw [h_dvd]
  have hr : E % 11 < 11 := Nat.mod_lt E (by decide)
  interval_cases E % 11 <;> decide

theorem not_dvd_31 (E : ℕ) : ¬ 31 ∣ 2 ^ E + 3 := by
  have h2d : 2 ^ 5 ≡ 1 [MOD 31] := by
    have h := pow2_mod_eq 31 5
    have h_val : pow2_mod 31 5 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_eq := pow_modEq_pow_mod 2 5 31 E h2d
  have h_eq_add := Nat.ModEq.add_right 3 h_eq
  have h_dvd : 31 ∣ 2 ^ E + 3 ↔ 31 ∣ 2 ^ (E % 5) + 3 := Nat.ModEq.dvd_iff h_eq_add (dvd_refl 31)
  rw [h_dvd]
  have hr : E % 5 < 5 := Nat.mod_lt E (by decide)
  interval_cases E % 5 <;> decide

theorem not_dvd_41 (E : ℕ) : ¬ 41 ∣ 2 ^ E + 3 := by
  have h2d : 2 ^ 20 ≡ 1 [MOD 41] := by
    have h := pow2_mod_eq 41 20
    have h_val : pow2_mod 41 20 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_eq := pow_modEq_pow_mod 2 20 41 E h2d
  have h_eq_add := Nat.ModEq.add_right 3 h_eq
  have h_dvd : 41 ∣ 2 ^ E + 3 ↔ 41 ∣ 2 ^ (E % 20) + 3 := Nat.ModEq.dvd_iff h_eq_add (dvd_refl 41)
  rw [h_dvd]
  have hr : E % 20 < 20 := Nat.mod_lt E (by decide)
  interval_cases E % 20 <;> decide

theorem not_dvd_43 (E : ℕ) : ¬ 43 ∣ 2 ^ E + 3 := by
  have h2d : 2 ^ 14 ≡ 1 [MOD 43] := by
    have h := pow2_mod_eq 43 14
    have h_val : pow2_mod 43 14 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_eq := pow_modEq_pow_mod 2 14 43 E h2d
  have h_eq_add := Nat.ModEq.add_right 3 h_eq
  have h_dvd : 43 ∣ 2 ^ E + 3 ↔ 43 ∣ 2 ^ (E % 14) + 3 := Nat.ModEq.dvd_iff h_eq_add (dvd_refl 43)
  rw [h_dvd]
  have hr : E % 14 < 14 := Nat.mod_lt E (by decide)
  interval_cases E % 14 <;> decide

theorem not_dvd_47 (E : ℕ) : ¬ 47 ∣ 2 ^ E + 3 := by
  have h2d : 2 ^ 23 ≡ 1 [MOD 47] := by
    have h := pow2_mod_eq 47 23
    have h_val : pow2_mod 47 23 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_eq := pow_modEq_pow_mod 2 23 47 E h2d
  have h_eq_add := Nat.ModEq.add_right 3 h_eq
  have h_dvd : 47 ∣ 2 ^ E + 3 ↔ 47 ∣ 2 ^ (E % 23) + 3 := Nat.ModEq.dvd_iff h_eq_add (dvd_refl 47)
  rw [h_dvd]
  have hr : E % 23 < 23 := Nat.mod_lt E (by decide)
  interval_cases E % 23 <;> decide

theorem not_dvd_5 (n : ℕ) : ¬ 5 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 4 ≡ 1 [MOD 5] := by
    have h := pow2_mod_eq 5 4
    have h_val : pow2_mod 5 4 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_base : 2 ^ (10 * 1 + 2) ≡ 2 ^ 2 [MOD 4] := by decide
  have h_step : 2 ^ (10 * 1) * 2 ^ 12 ≡ 2 ^ 12 [MOD 4] := by decide
  have hE := hE_proof_general 4 1 h_base h_step
  apply periodic_induction (fun n => ¬ 5 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) 1 (by decide)
  · intro n hn
    interval_cases n
    · have h_eq := base_case_helper 5 4 0 h2d
      have h_dvd : 5 ∣ 2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 ↔ 5 ∣ 2 ^ ((pow2_mod 4 (10 * 0 + 2) + 2) % 4) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
  · intro n hn
    exact step_dvd_general 5 4 1 h2d hE n hn

theorem not_dvd_7 (n : ℕ) : ¬ 7 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 3 ≡ 1 [MOD 7] := by
    have h := pow2_mod_eq 7 3
    have h_val : pow2_mod 7 3 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_base : 2 ^ (10 * 1 + 2) ≡ 2 ^ 2 [MOD 3] := by decide
  have h_step : 2 ^ (10 * 1) * 2 ^ 12 ≡ 2 ^ 12 [MOD 3] := by decide
  have hE := hE_proof_general 3 1 h_base h_step
  apply periodic_induction (fun n => ¬ 7 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) 1 (by decide)
  · intro n hn
    interval_cases n
    · have h_eq := base_case_helper 7 3 0 h2d
      have h_dvd : 7 ∣ 2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 ↔ 7 ∣ 2 ^ ((pow2_mod 3 (10 * 0 + 2) + 2) % 3) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
  · intro n hn
    exact step_dvd_general 7 3 1 h2d hE n hn

theorem not_dvd_11 (n : ℕ) : ¬ 11 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 10 ≡ 1 [MOD 11] := by
    have h := pow2_mod_eq 11 10
    have h_val : pow2_mod 11 10 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_base : 2 ^ (10 * 2 + 2) ≡ 2 ^ 2 [MOD 10] := by decide
  have h_step : 2 ^ (10 * 2) * 2 ^ 12 ≡ 2 ^ 12 [MOD 10] := by decide
  have hE := hE_proof_general 10 2 h_base h_step
  apply periodic_induction (fun n => ¬ 11 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) 2 (by decide)
  · intro n hn
    interval_cases n
    · have h_eq := base_case_helper 11 10 0 h2d
      have h_dvd : 11 ∣ 2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 ↔ 11 ∣ 2 ^ ((pow2_mod 10 (10 * 0 + 2) + 2) % 10) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 11 10 1 h2d
      have h_dvd : 11 ∣ 2 ^ (2 ^ (10 * 1 + 2) + 2) + 3 ↔ 11 ∣ 2 ^ ((pow2_mod 10 (10 * 1 + 2) + 2) % 10) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
  · intro n hn
    exact step_dvd_general 11 10 2 h2d hE n hn

theorem not_dvd_13 (n : ℕ) : ¬ 13 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 12 ≡ 1 [MOD 13] := by
    have h := pow2_mod_eq 13 12
    have h_val : pow2_mod 13 12 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_base : 2 ^ (10 * 1 + 2) ≡ 2 ^ 2 [MOD 12] := by decide
  have h_step : 2 ^ (10 * 1) * 2 ^ 12 ≡ 2 ^ 12 [MOD 12] := by decide
  have hE := hE_proof_general 12 1 h_base h_step
  apply periodic_induction (fun n => ¬ 13 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) 1 (by decide)
  · intro n hn
    interval_cases n
    · have h_eq := base_case_helper 13 12 0 h2d
      have h_dvd : 13 ∣ 2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 ↔ 13 ∣ 2 ^ ((pow2_mod 12 (10 * 0 + 2) + 2) % 12) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
  · intro n hn
    exact step_dvd_general 13 12 1 h2d hE n hn

theorem not_dvd_19 (n : ℕ) : ¬ 19 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 18 ≡ 1 [MOD 19] := by
    have h := pow2_mod_eq 19 18
    have h_val : pow2_mod 19 18 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_base : 2 ^ (10 * 3 + 2) ≡ 2 ^ 2 [MOD 18] := by decide
  have h_step : 2 ^ (10 * 3) * 2 ^ 12 ≡ 2 ^ 12 [MOD 18] := by decide
  have hE := hE_proof_general 18 3 h_base h_step
  apply periodic_induction (fun n => ¬ 19 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) 3 (by decide)
  · intro n hn
    interval_cases n
    · have h_eq := base_case_helper 19 18 0 h2d
      have h_dvd : 19 ∣ 2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 ↔ 19 ∣ 2 ^ ((pow2_mod 18 (10 * 0 + 2) + 2) % 18) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 19 18 1 h2d
      have h_dvd : 19 ∣ 2 ^ (2 ^ (10 * 1 + 2) + 2) + 3 ↔ 19 ∣ 2 ^ ((pow2_mod 18 (10 * 1 + 2) + 2) % 18) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 19 18 2 h2d
      have h_dvd : 19 ∣ 2 ^ (2 ^ (10 * 2 + 2) + 2) + 3 ↔ 19 ∣ 2 ^ ((pow2_mod 18 (10 * 2 + 2) + 2) % 18) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
  · intro n hn
    exact step_dvd_general 19 18 3 h2d hE n hn

theorem not_dvd_29 (n : ℕ) : ¬ 29 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 28 ≡ 1 [MOD 29] := by
    have h := pow2_mod_eq 29 28
    have h_val : pow2_mod 29 28 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_base : 2 ^ (10 * 3 + 2) ≡ 2 ^ 2 [MOD 28] := by decide
  have h_step : 2 ^ (10 * 3) * 2 ^ 12 ≡ 2 ^ 12 [MOD 28] := by decide
  have hE := hE_proof_general 28 3 h_base h_step
  apply periodic_induction (fun n => ¬ 29 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) 3 (by decide)
  · intro n hn
    interval_cases n
    · have h_eq := base_case_helper 29 28 0 h2d
      have h_dvd : 29 ∣ 2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 ↔ 29 ∣ 2 ^ ((pow2_mod 28 (10 * 0 + 2) + 2) % 28) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 29 28 1 h2d
      have h_dvd : 29 ∣ 2 ^ (2 ^ (10 * 1 + 2) + 2) + 3 ↔ 29 ∣ 2 ^ ((pow2_mod 28 (10 * 1 + 2) + 2) % 28) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 29 28 2 h2d
      have h_dvd : 29 ∣ 2 ^ (2 ^ (10 * 2 + 2) + 2) + 3 ↔ 29 ∣ 2 ^ ((pow2_mod 28 (10 * 2 + 2) + 2) % 28) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
  · intro n hn
    exact step_dvd_general 29 28 3 h2d hE n hn

theorem not_dvd_37 (n : ℕ) : ¬ 37 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 36 ≡ 1 [MOD 37] := by
    have h := pow2_mod_eq 37 36
    have h_val : pow2_mod 37 36 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_base : 2 ^ (10 * 3 + 2) ≡ 2 ^ 2 [MOD 36] := by decide
  have h_step : 2 ^ (10 * 3) * 2 ^ 12 ≡ 2 ^ 12 [MOD 36] := by decide
  have hE := hE_proof_general 36 3 h_base h_step
  apply periodic_induction (fun n => ¬ 37 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) 3 (by decide)
  · intro n hn
    interval_cases n
    · have h_eq := base_case_helper 37 36 0 h2d
      have h_dvd : 37 ∣ 2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 ↔ 37 ∣ 2 ^ ((pow2_mod 36 (10 * 0 + 2) + 2) % 36) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 37 36 1 h2d
      have h_dvd : 37 ∣ 2 ^ (2 ^ (10 * 1 + 2) + 2) + 3 ↔ 37 ∣ 2 ^ ((pow2_mod 36 (10 * 1 + 2) + 2) % 36) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 37 36 2 h2d
      have h_dvd : 37 ∣ 2 ^ (2 ^ (10 * 2 + 2) + 2) + 3 ↔ 37 ∣ 2 ^ ((pow2_mod 36 (10 * 2 + 2) + 2) % 36) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
  · intro n hn
    exact step_dvd_general 37 36 3 h2d hE n hn

theorem not_dvd_53 (n : ℕ) : ¬ 53 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 52 ≡ 1 [MOD 53] := by
    have h := pow2_mod_eq 53 52
    have h_val : pow2_mod 53 52 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_base : 2 ^ (10 * 6 + 2) ≡ 2 ^ 2 [MOD 52] := by decide
  have h_step : 2 ^ (10 * 6) * 2 ^ 12 ≡ 2 ^ 12 [MOD 52] := by decide
  have hE := hE_proof_general 52 6 h_base h_step
  apply periodic_induction (fun n => ¬ 53 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) 6 (by decide)
  · intro n hn
    interval_cases n
    · have h_eq := base_case_helper 53 52 0 h2d
      have h_dvd : 53 ∣ 2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 ↔ 53 ∣ 2 ^ ((pow2_mod 52 (10 * 0 + 2) + 2) % 52) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 53 52 1 h2d
      have h_dvd : 53 ∣ 2 ^ (2 ^ (10 * 1 + 2) + 2) + 3 ↔ 53 ∣ 2 ^ ((pow2_mod 52 (10 * 1 + 2) + 2) % 52) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 53 52 2 h2d
      have h_dvd : 53 ∣ 2 ^ (2 ^ (10 * 2 + 2) + 2) + 3 ↔ 53 ∣ 2 ^ ((pow2_mod 52 (10 * 2 + 2) + 2) % 52) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 53 52 3 h2d
      have h_dvd : 53 ∣ 2 ^ (2 ^ (10 * 3 + 2) + 2) + 3 ↔ 53 ∣ 2 ^ ((pow2_mod 52 (10 * 3 + 2) + 2) % 52) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 53 52 4 h2d
      have h_dvd : 53 ∣ 2 ^ (2 ^ (10 * 4 + 2) + 2) + 3 ↔ 53 ∣ 2 ^ ((pow2_mod 52 (10 * 4 + 2) + 2) % 52) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 53 52 5 h2d
      have h_dvd : 53 ∣ 2 ^ (2 ^ (10 * 5 + 2) + 2) + 3 ↔ 53 ∣ 2 ^ ((pow2_mod 52 (10 * 5 + 2) + 2) % 52) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
  · intro n hn
    exact step_dvd_general 53 52 6 h2d hE n hn

theorem not_dvd_59 (n : ℕ) : ¬ 59 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 58 ≡ 1 [MOD 59] := by
    have h := pow2_mod_eq 59 58
    have h_val : pow2_mod 59 58 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_base : 2 ^ (10 * 14 + 2) ≡ 2 ^ 2 [MOD 58] := by decide
  have h_step : 2 ^ (10 * 14) * 2 ^ 12 ≡ 2 ^ 12 [MOD 58] := by decide
  have hE := hE_proof_general 58 14 h_base h_step
  apply periodic_induction (fun n => ¬ 59 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) 14 (by decide)
  · intro n hn
    interval_cases n
    · have h_eq := base_case_helper 59 58 0 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 0 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 1 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 1 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 1 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 2 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 2 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 2 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 3 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 3 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 3 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 4 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 4 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 4 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 5 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 5 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 5 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 6 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 6 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 6 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 7 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 7 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 7 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 8 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 8 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 8 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 9 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 9 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 9 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 10 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 10 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 10 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 11 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 11 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 11 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 12 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 12 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 12 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 59 58 13 h2d
      have h_dvd : 59 ∣ 2 ^ (2 ^ (10 * 13 + 2) + 2) + 3 ↔ 59 ∣ 2 ^ ((pow2_mod 58 (10 * 13 + 2) + 2) % 58) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
  · intro n hn
    exact step_dvd_general 59 58 14 h2d hE n hn

theorem not_dvd_61 (n : ℕ) : ¬ 61 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 60 ≡ 1 [MOD 61] := by
    have h := pow2_mod_eq 61 60
    have h_val : pow2_mod 61 60 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_base : 2 ^ (10 * 2 + 2) ≡ 2 ^ 2 [MOD 60] := by decide
  have h_step : 2 ^ (10 * 2) * 2 ^ 12 ≡ 2 ^ 12 [MOD 60] := by decide
  have hE := hE_proof_general 60 2 h_base h_step
  apply periodic_induction (fun n => ¬ 61 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) 2 (by decide)
  · intro n hn
    interval_cases n
    · have h_eq := base_case_helper 61 60 0 h2d
      have h_dvd : 61 ∣ 2 ^ (2 ^ (10 * 0 + 2) + 2) + 3 ↔ 61 ∣ 2 ^ ((pow2_mod 60 (10 * 0 + 2) + 2) % 60) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
    · have h_eq := base_case_helper 61 60 1 h2d
      have h_dvd : 61 ∣ 2 ^ (2 ^ (10 * 1 + 2) + 2) + 3 ↔ 61 ∣ 2 ^ ((pow2_mod 60 (10 * 1 + 2) + 2) % 60) + 3 :=
        Nat.ModEq.dvd_iff h_eq (dvd_refl _)
      rw [h_dvd]
      decide
  · intro n hn
    exact step_dvd_general 61 60 2 h2d hE n hn

lemma exp_congruence_66 (n : ℕ) : 2 ^ (10 * n + 2) ≡ 4 [MOD 66] := by
  have h_base : 2 ^ (10 * 1 + 2) ≡ 2 ^ 2 [MOD 66] := by decide
  have h_step : 2 ^ (10 * 1) * 2 ^ 12 ≡ 2 ^ 12 [MOD 66] := by decide
  apply periodic_induction (fun n => 2 ^ (10 * n + 2) ≡ 4 [MOD 66]) 1 (by decide)
  · intro n hn
    interval_cases n <;> decide
  · intro n ih
    have h_step_eq := exp_congruence_helper 66 1 h_base h_step n
    exact h_step_eq.trans ih

theorem dvd_67 (n : ℕ) : 67 ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := by
  have h2d : 2 ^ 66 ≡ 1 [MOD 67] := by
    have h := pow2_mod_eq 67 66
    have h_val : pow2_mod 67 66 = 1 := by decide
    rw [h_val] at h
    exact h
  have h_exp_67 := exp_congruence_66 n
  have h_exp_add_67 := Nat.ModEq.add_right 2 h_exp_67
  have h_eq := pow_modEq_pow_mod 2 66 67 (2 ^ (10 * n + 2) + 2) h2d
  have h_mod : (2 ^ (10 * n + 2) + 2) % 66 = 6 := h_exp_add_67
  rw [h_mod] at h_eq
  have h_eq_add := Nat.ModEq.add_right 3 h_eq
  have h_zero : 2 ^ 6 + 3 ≡ 0 [MOD 67] := rfl
  have h_final := h_eq_add.trans h_zero
  exact Nat.modEq_zero_iff_dvd.mp h_final

lemma prime_bound (p : ℕ) (hp : p.Prime) (hdp : p ∣ 2 ^ (2 ^ (10 * n + 2) + 2) + 3) : 67 ≤ p := by
  by_contra h_lt
  have h_lt : p < 67 := by omega
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases p
  · exact not_dvd_2 n hdp
  · exact not_dvd_3 (2 ^ (10 * n + 2) + 2) hdp
  · have h_prime : ¬ Nat.Prime 4 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_5 n hdp
  · have h_prime : ¬ Nat.Prime 6 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_7 n hdp
  · have h_prime : ¬ Nat.Prime 8 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 9 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 10 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_11 n hdp
  · have h_prime : ¬ Nat.Prime 12 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_13 n hdp
  · have h_prime : ¬ Nat.Prime 14 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 15 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 16 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_17 (2 ^ (10 * n + 2) + 2) hdp
  · have h_prime : ¬ Nat.Prime 18 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_19 n hdp
  · have h_prime : ¬ Nat.Prime 20 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 21 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 22 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_23 (2 ^ (10 * n + 2) + 2) hdp
  · have h_prime : ¬ Nat.Prime 24 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 25 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 26 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 27 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 28 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_29 n hdp
  · have h_prime : ¬ Nat.Prime 30 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_31 (2 ^ (10 * n + 2) + 2) hdp
  · have h_prime : ¬ Nat.Prime 32 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 33 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 34 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 35 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 36 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_37 n hdp
  · have h_prime : ¬ Nat.Prime 38 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 39 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 40 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_41 (2 ^ (10 * n + 2) + 2) hdp
  · have h_prime : ¬ Nat.Prime 42 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_43 (2 ^ (10 * n + 2) + 2) hdp
  · have h_prime : ¬ Nat.Prime 44 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 45 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 46 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_47 (2 ^ (10 * n + 2) + 2) hdp
  · have h_prime : ¬ Nat.Prime 48 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 49 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 50 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 51 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 52 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_53 n hdp
  · have h_prime : ¬ Nat.Prime 54 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 55 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 56 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 57 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 58 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_59 n hdp
  · have h_prime : ¬ Nat.Prime 60 := by decide
    exact (h_prime hp).elim
  · exact not_dvd_61 n hdp
  · have h_prime : ¬ Nat.Prime 62 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 63 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 64 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 65 := by decide
    exact (h_prime hp).elim
  · have h_prime : ¬ Nat.Prime 66 := by decide
    exact (h_prime hp).elim

/-- OEIS A248802 Conjecture 1: a(10n+2) = 67 for n >= 0. -/
theorem oeis_248802_conjecture_0 (n : ℕ) : a (10 * n + 2) = 67 := by
  unfold a
  have h1 : 2 ^ (2 ^ (10 * n + 2) + 2) + 3 ≠ 1 := by
    have h2 : 3 ≤ 2 ^ (2 ^ (10 * n + 2) + 2) + 3 := Nat.le_add_left 3 _
    omega
  apply Nat.le_antisymm
  · exact Nat.minFac_le_of_dvd (by decide) (dvd_67 n)
  · have hp := Nat.minFac_prime h1
    have hdp := Nat.minFac_dvd (2 ^ (2 ^ (10 * n + 2) + 2) + 3)
    exact prime_bound (Nat.minFac (2 ^ (2 ^ (10 * n + 2) + 2) + 3)) hp hdp
