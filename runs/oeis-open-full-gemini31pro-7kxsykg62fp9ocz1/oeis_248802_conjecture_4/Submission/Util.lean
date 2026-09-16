import Mathlib

def exp_seq (m : ℕ) (n : ℕ) : ℕ :=
  match n with
  | 0 => (2^26) % m
  | n + 1 => (exp_seq m n * (2^58 % m)) % m

def val_mod_p (p n : ℕ) : ℕ := ( (2 ^ (exp_seq (p-1) n) % p) * 4 + 3 ) % p

lemma zmod_pow_mod_m (p m : ℕ) (h : (2^m) % p = 1) (X : ℕ) :
  ((2 : ℕ) : ZMod p) ^ X = ((2 : ℕ) : ZMod p) ^ (X % m) := by
  have h1 : X = m * (X / m) + X % m := (Nat.div_add_mod X m).symm
  nth_rw 1 [h1]
  rw [pow_add, pow_mul]
  have h2 : (((2^m : ℕ) : ZMod p)) = 1 := by
    rw [← ZMod.natCast_mod, h, Nat.cast_one]
  have h3 : ((2 : ℕ) : ZMod p) ^ m = 1 := by
    calc ((2 : ℕ) : ZMod p) ^ m = ((2^m : ℕ) : ZMod p) := by rw [Nat.cast_pow]
      _ = 1 := h2
  rw [h3, one_pow, one_mul]

lemma val_mod_p_correct (p n : ℕ) (h : (2^(p-1)) % p = 1) (h_eq : exp_seq (p-1) n = (2^(58*n+26)) % (p-1)) :
  ( (2^(2^(58*n+26)+2) + 3 : ℕ) : ZMod p ) = (val_mod_p p n : ZMod p) := by
  dsimp [val_mod_p]
  have h1 : ((2:ℕ):ZMod p)^(2^(58*n+26)) = ((2:ℕ):ZMod p)^((2^(58*n+26)) % (p-1)) := zmod_pow_mod_m p (p-1) h (2^(58*n+26))
  have h2 : 2 ^ (2 ^ (58 * n + 26) + 2) = 2 ^ (2 ^ (58 * n + 26)) * 4 := by
    have : 2 ^ (2 ^ (58 * n + 26) + 2) = 2 ^ (2 ^ (58 * n + 26)) * 2^2 := by rw [pow_add]
    rw [this]
    rfl
  calc ((2 ^ (2 ^ (58 * n + 26) + 2) + 3 : ℕ) : ZMod p) 
    _ = ((2 ^ (2 ^ (58 * n + 26)) * 4 + 3 : ℕ) : ZMod p) := by rw [h2]
    _ = ((2:ℕ):ZMod p)^(2^(58*n+26)) * 4 + 3 := by push_cast; rfl
    _ = ((2:ℕ):ZMod p)^((2^(58*n+26)) % (p-1)) * 4 + 3 := by rw [h1]
    _ = ((2:ℕ):ZMod p)^(exp_seq (p-1) n) * 4 + 3 := by rw [h_eq]
    _ = ( ((2 ^ (exp_seq (p-1) n) % p) * 4 + 3 : ℕ) : ZMod p ) := by
      push_cast
      have h4 : (((2 ^ exp_seq (p - 1) n % p : ℕ) : ZMod p)) = ((2:ℕ):ZMod p)^(exp_seq (p - 1) n) := by
        rw [ZMod.natCast_mod]
        push_cast
        rfl
      rw [h4]
      rfl
    _ = ( ((2 ^ (exp_seq (p-1) n) % p) * 4 + 3 : ℕ) % p : ZMod p) := by rw [ZMod.natCast_mod]

lemma mod_p_eq_zero_iff (a p : ℕ) : a % p = 0 ↔ (a : ZMod p) = 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, ZMod.natCast_eq_zero_iff]

lemma not_dvd_of_val_mod_p (p n : ℕ) (hp : p.Prime) (h : (2^(p-1)) % p = 1) (h_eq : exp_seq (p-1) n = (2^(58*n+26)) % (p-1)) 
  (h_val : val_mod_p p n ≠ 0) : ¬ p ∣ (2^(2^(58*n+26)+2) + 3) := by
  intro H
  have H1 : ( (2^(2^(58*n+26)+2) + 3 : ℕ) : ZMod p ) = 0 := by
    rw [← mod_p_eq_zero_iff]
    exact Nat.dvd_iff_mod_eq_zero.mp H
  have H2 := val_mod_p_correct p n h h_eq
  rw [H1] at H2
  have H3 : val_mod_p p n % p = 0 := by
    rw [mod_p_eq_zero_iff]
    exact H2.symm
  have H4 : val_mod_p p n < p := by
    dsimp [val_mod_p]
    exact Nat.mod_lt _ (Nat.Prime.pos hp)
  rw [Nat.mod_eq_of_lt H4] at H3
  exact h_val H3

lemma exp_seq_add_one (m n : ℕ) : exp_seq m (n + 1) = (exp_seq m n * (2^58 % m)) % m := rfl

lemma exp_seq_period (m P n : ℕ) (h : exp_seq m P = exp_seq m 0) :
  exp_seq m (n + P) = exp_seq m n := by
  induction n with
  | zero => rw [Nat.zero_add]; exact h
  | succ n ih =>
    have h1 : n + 1 + P = n + P + 1 := by omega
    rw [h1, exp_seq_add_one, exp_seq_add_one, ih]

lemma exp_seq_mul_period (m P q n : ℕ) (h : exp_seq m P = exp_seq m 0) :
  exp_seq m (n + q * P) = exp_seq m n := by
  induction q with
  | zero => rw [Nat.zero_mul, Nat.add_zero]
  | succ q ih =>
    have h1 : n + (q + 1) * P = n + q * P + P := by ring
    rw [h1, exp_seq_period m P _ h, ih]

lemma exp_seq_mod (m P n : ℕ) (h : exp_seq m P = exp_seq m 0) :
  exp_seq m n = exp_seq m (n % P) := by
  have H : n = n % P + (n / P) * P := by
    calc n = P * (n / P) + n % P := (Nat.div_add_mod n P).symm
      _ = n % P + (n / P) * P := by ring
  nth_rw 1 [H]
  rw [exp_seq_mul_period m P (n / P) (n % P) h]

lemma val_mod_p_mod (p P n : ℕ) (h : exp_seq (p-1) P = exp_seq (p-1) 0) :
  val_mod_p p n = val_mod_p p (n % P) := by
  dsimp [val_mod_p]
  rw [exp_seq_mod (p-1) P n h]

def check_prime_period_cond (p P : ℕ) (cond : ℕ → Bool) : Bool :=
  (List.range P).all (fun i => cond i || val_mod_p p i != 0)

lemma val_mod_p_not_zero_of_cond (p P : ℕ) (cond : ℕ → Bool) (h : check_prime_period_cond p P cond = true) (i : ℕ) (hi : i < P) (hcond : cond i = false) : val_mod_p p i ≠ 0 := by
  have h1 : ∀ x ∈ List.range P, (cond x || val_mod_p p x != 0) = true := by
    exact List.all_eq_true.mp h
  have h2 := h1 i (List.mem_range.mpr hi)
  rw [hcond, Bool.false_or] at h2
  intro H
  have H2 : (val_mod_p p i == 0) = true := by rw [H]; rfl
  change (!(val_mod_p p i == 0)) = true at h2
  rw [H2] at h2
  contradiction

lemma exp_seq_eq (m : ℕ) (n : ℕ) : exp_seq m n = (2^(58*n+26)) % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (exp_seq m n * (2^58 % m)) % m = _
    rw [ih]
    have h : 58 * (n + 1) + 26 = 58 * n + 26 + 58 := by omega
    rw [h]
    have H : ((2 ^ (58 * n + 26)) % m * (2 ^ 58 % m)) % m = (2 ^ (58 * n + 26) * 2 ^ 58) % m :=
      (Nat.mul_mod (2 ^ (58 * n + 26)) (2 ^ 58) m).symm
    rw [H]
    have H2 : 2 ^ (58 * n + 26) * 2 ^ 58 = 2 ^ (58 * n + 26 + 58) := (pow_add 2 (58 * n + 26) 58).symm
    rw [H2]

def cond_67 (n : ℕ) : Bool := (n == 2)
def cond_271 (n : ℕ) : Bool := (n == 11)
def cond_523 (n : ℕ) : Bool := (n == 26)

lemma cond_67_imp (n : ℕ) (h : cond_67 (n % 5) = true) : n % 5 = 2 := by
  dsimp [cond_67] at h
  exact beq_iff_eq.mp h

lemma cond_271_imp (n : ℕ) (h : cond_271 (n % 18) = true) : n % 18 = 11 := by
  dsimp [cond_271] at h
  exact beq_iff_eq.mp h

lemma cond_523_imp (n : ℕ) (h : cond_523 (n % 42) = true) : n % 42 = 26 := by
  dsimp [cond_523] at h
  exact beq_iff_eq.mp h

def covered_by_C1 (k : ℕ) : Prop := ∃ m : ℕ, k = 10 * m + 2
def covered_by_C2 (k : ℕ) : Prop := ∃ m : ℕ, k = 36 * m + 16 ∧ m % 5 ≠ 1
def covered_by_C3 (k : ℕ) : Prop := ∃ m : ℕ, k = 84 * m + 22 ∧ m % 5 ≠ 0

lemma C1_of_mod_5_eq_2 (n : ℕ) (h : n % 5 = 2) : covered_by_C1 (58 * n + 26) := by
  have H : n = 5 * (n / 5) + n % 5 := (Nat.div_add_mod n 5).symm
  rw [h] at H
  use 29 * (n / 5) + 14
  calc 58 * n + 26 = 58 * (5 * (n / 5) + 2) + 26 := by nth_rw 1 [H]
    _ = 10 * (29 * (n / 5) + 14) + 2 := by ring

lemma C2_or_C1_of_mod_18_eq_11 (n : ℕ) (h : n % 18 = 11) : 
  covered_by_C1 (58 * n + 26) ∨ covered_by_C2 (58 * n + 26) := by
  have H : n = 18 * (n / 18) + n % 18 := (Nat.div_add_mod n 18).symm
  rw [h] at H
  let m := 29 * (n / 18) + 18
  have hk : 58 * n + 26 = 36 * m + 16 := by
    calc 58 * n + 26 = 58 * (18 * (n / 18) + 11) + 26 := by nth_rw 1 [H]
      _ = 36 * (29 * (n / 18) + 18) + 16 := by ring
  by_cases hm : m % 5 = 1
  · left
    have Hm : m = 5 * (m / 5) + 1 := by omega
    use 18 * (m / 5) + 5
    calc 58 * n + 26 = 36 * m + 16 := hk
      _ = 36 * (5 * (m / 5) + 1) + 16 := by nth_rw 1 [Hm]
      _ = 10 * (18 * (m / 5) + 5) + 2 := by ring
  · right
    use m

lemma C3_or_C1_of_mod_42_eq_26 (n : ℕ) (h : n % 42 = 26) : 
  covered_by_C1 (58 * n + 26) ∨ covered_by_C3 (58 * n + 26) := by
  have H : n = 42 * (n / 42) + n % 42 := (Nat.div_add_mod n 42).symm
  rw [h] at H
  let m := 29 * (n / 42) + 18
  have hk : 58 * n + 26 = 84 * m + 22 := by
    calc 58 * n + 26 = 58 * (42 * (n / 42) + 26) + 26 := by nth_rw 1 [H]
      _ = 84 * (29 * (n / 42) + 18) + 22 := by ring
  by_cases hm : m % 5 = 0
  · left
    have Hm : m = 5 * (m / 5) := by omega
    use 42 * (m / 5) + 2
    calc 58 * n + 26 = 84 * m + 22 := hk
      _ = 84 * (5 * (m / 5)) + 22 := by nth_rw 1 [Hm]
      _ = 10 * (42 * (m / 5) + 2) + 2 := by ring
  · right
    use m

lemma minFac_ge (N : ℕ) (H1 : 1 < N) (H2 : ∀ p < 1399, p.Prime → ¬ p ∣ N) : 1399 ≤ N.minFac := by
  by_contra h
  push_neg at h
  have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : N.minFac ∣ N := Nat.minFac_dvd N
  exact H2 N.minFac h hp hdvd

lemma two_pow_2_pow_k_mod_1399 (k : ℕ) (hk : (2^k) % 233 = 204) :
  (2^(2^k + 2) + 3) % 1399 = 0 := by
  have h1 : 2^k = 233 * (2^k / 233) + 204 := by
    have h2 := Nat.div_add_mod (2^k) 233
    omega
  have h2 : 2^(2^k) = (2^233)^(2^k / 233) * (2^204) := by
    calc 2^(2^k) = 2^(233 * (2^k / 233) + 204) := by nth_rw 1 [h1]
      _ = 2^(233 * (2^k / 233)) * 2^204 := by rw [pow_add]
      _ = (2^233)^(2^k / 233) * 2^204 := by rw [pow_mul]
  have h3 : 2^(2^k + 2) = 2^(2^k) * 4 := by
    rw [pow_add]
    rfl
  rw [h3, h2]
  rw [mod_p_eq_zero_iff]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
  have h4 : ((2^233 : ℕ) : ZMod 1399) = 1 := by
    have h5 : (2^233 : ℕ) % 1399 = 1 := by norm_num
    rw [← ZMod.natCast_mod (2^233) 1399, h5]
    rfl
  rw [h4, one_pow, one_mul]
  have h6 : ((2^204 * 4 + 3 : ℕ) : ZMod 1399) = 0 := by decide
  push_cast at h6
  exact h6

lemma two_pow_k_mod_233 (n : ℕ) : (2^(58 * n + 26)) % 233 = 204 := by
  induction' n with n ih
  · rfl
  · have h1 : 58 * (n + 1) + 26 = 58 * n + 26 + 58 := by omega
    rw [h1, pow_add]
    have H : (2 ^ (58 * n + 26) * 2 ^ 58) % 233 = (2 ^ (58 * n + 26) % 233 * (2 ^ 58 % 233)) % 233 :=
      Nat.mul_mod _ _ _
    rw [H, ih]
    rfl

lemma a_mod_1399 (n : ℕ) : (2^(2^(58 * n + 26) + 2) + 3) % 1399 = 0 := by
  apply two_pow_2_pow_k_mod_1399
  apply two_pow_k_mod_233

lemma not_dvd_2 (n : ℕ) (hC1 : ¬ covered_by_C1 (58 * n + 26)) (hC2 : ¬ covered_by_C2 (58 * n + 26)) (hC3 : ¬ covered_by_C3 (58 * n + 26)) : ¬ 2 ∣ (2^(2^(58*n+26)+2) + 3) := by
  intro h
  have H : (2^(2^(58*n+26)+2) + 3) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  have H2 : 2^(2^(58*n+26)+2) % 2 = 0 := by
    have h3 : 2^(2^(58*n+26)+2) = 2 * 2^(2^(58*n+26)+1) := by
      have h4 : 2^(58*n+26)+2 = 1 + (2^(58*n+26)+1) := by omega
      rw [h4, pow_add, pow_one, mul_comm]
    rw [h3, Nat.mul_mod_right]
  have H3 : (2^(2^(58*n+26)+2) + 3) % 2 = (2^(2^(58*n+26)+2) % 2 + 3 % 2) % 2 := Nat.add_mod _ _ 2
  rw [H2] at H3
  have H4 : 3 % 2 = 1 := by rfl
  rw [H4] at H3
  rw [H3] at H
  revert H
  decide
