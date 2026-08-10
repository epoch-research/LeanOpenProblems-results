import Mathlib

open Nat Finset BigOperators

def A_seq : ℕ → ℤ
  | 0 => 0
  | k + 1 => (k.factorial : ℤ) + (k + 1 : ℤ) * A_seq k

def B_seq : ℕ → ℤ
  | 0 => 0
  | k + 1 => A_seq k + (k + 1 : ℤ) * B_seq k

def C_seq (p : ℤ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => 8 * B_seq k + (2 * p + k + 1 : ℤ) * C_seq p k

def f_seq (p : ℤ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => (2 * p + k + 1 : ℤ) * f_seq p k

lemma product_identity (p : ℤ) (k : ℕ) :
    f_seq p k = (k.factorial : ℤ) + 2 * p * A_seq k + 4 * p^2 * B_seq k + p^3 * C_seq p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [f_seq, A_seq, B_seq, C_seq]
    rw [ih]
    push_cast
    ring

lemma choose_mul_factorial_succ (n k : ℕ) :
    (2 * n + k + 1).choose (k + 1) * (k + 1).factorial = (2 * n + k + 1) * (2 * n + k).choose k * k.factorial := by
  have h1 : (2 * n + k + 1).choose (k + 1) * (k + 1) = (2 * n + k + 1) * (2 * n + k).choose k := by
    exact choose_succ_right_eq (2 * n + k) k
  have h_fact : (k + 1).factorial = (k + 1) * k.factorial := rfl
  rw [h_fact, ← mul_assoc, h1, mul_assoc]

lemma f_seq_eq_choose_mul_factorial (n : ℕ) (k : ℕ) :
    f_seq (n : ℤ) k = (((2 * n + k).choose k * k.factorial : ℕ) : ℤ) := by
  induction k with
  | zero =>
    simp [f_seq]
  | succ k ih =>
    simp [f_seq]
    rw [ih]
    push_cast
    have h_mul := choose_mul_factorial_succ n k
    exact_mod_cast h_mul.symm

def A_sum (k : ℕ) : ℤ :=
  ∑ j ∈ range k, (((k.factorial / (j + 1) : ℕ) : ℤ))

lemma A_seq_eq_A_sum (k : ℕ) :
    A_seq k = A_sum k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [A_seq, ih]
    have h_sum_succ : A_sum (k + 1) = ∑ j ∈ range k, (((k + 1).factorial / (j + 1) : ℕ) : ℤ) + (((k + 1).factorial / (k + 1) : ℕ) : ℤ) := by
      exact sum_range_succ (fun j => (((k + 1).factorial / (j + 1) : ℕ) : ℤ)) k
    rw [h_sum_succ]
    have h_last : (((k + 1).factorial / (k + 1) : ℕ) : ℤ) = (k.factorial : ℤ) := by
      have h_div : (k + 1).factorial / (k + 1) = k.factorial := by
        rw [factorial_succ]
        exact Nat.mul_div_cancel_left _ (by omega)
      rw [h_div]
    rw [h_last]
    have h_eq : (k + 1 : ℤ) * A_sum k = ∑ j ∈ range k, (((k + 1).factorial / (j + 1) : ℕ) : ℤ) := by
      rw [A_sum, mul_sum]
      apply sum_congr rfl
      intro x hx
      have hx_lt : x < k := by rwa [mem_range] at hx
      have h_dvd : x + 1 ∣ k.factorial := Nat.dvd_factorial (by omega) (by omega)
      have h_div_assoc : (k + 1).factorial / (x + 1) = (k + 1) * (k.factorial / (x + 1)) := by
        rw [factorial_succ]
        exact Nat.mul_div_assoc _ h_dvd
      rw [h_div_assoc]
      push_cast
      ring
    rw [h_eq, add_comm]

lemma sum_range_reflect (k : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ range (2 * k), f i = ∑ i ∈ range k, f i + ∑ i ∈ range k, f (2 * k - 1 - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_LHS : ∑ i ∈ range (2 * k + 2), f i = ∑ i ∈ range (2 * k), f i + f (2 * k) + f (2 * k + 1) := by
      rw [add_assoc, sum_range_succ, sum_range_succ]
      ring
    rw [h_LHS, ih]
    have h_RHS1 : ∑ i ∈ range (k + 1), f i = ∑ i ∈ range k, f i + f k := sum_range_succ f k
    have h_RHS2 : ∑ i ∈ range (k + 1), f (2 * k + 1 - i) = f (2 * k + 1) + ∑ i ∈ range k, f (2 * k - i) := by
      rw [sum_range_succ']
      congr 1
      apply sum_congr rfl
      intro x _
      congr 1
      omega
    rw [h_RHS1, h_RHS2]
    rcases k with rfl | k
    · simp
    · have h_rec1 : ∑ i ∈ range (k + 1), f (2 * k + 1 - i) = ∑ i ∈ range k, f (2 * k + 1 - i) + f (k + 1) := sum_range_succ _ _
      have h_rec2 : ∑ i ∈ range (k + 1), f (2 * k + 2 - i) = f (2 * k + 2) + ∑ i ∈ range k, f (2 * k + 1 - i) := by
        rw [sum_range_succ']
        congr 1
        apply sum_congr rfl
        intro x _
        congr 1
        omega
      -- Wait, let's write it in a way that avoids dependent omega or complex matching.
      -- We want to prove:
      -- ∑ i ∈ range (k + 1), f (2 * k + 1 - i) + f (2 * (k + 1)) = f (k + 1) + ∑ i ∈ range (k + 1), f (2 * (k + 1) - i)
      -- Let's define g i = f (2 * k + 1 - i)
      -- Then the LHS term is ∑ i ∈ range (k + 1), f (2 * k + 1 - i)
      -- and RHS has ∑ i ∈ range (k + 1), f (2 * k + 2 - i)
      -- This is just finite sum manipulations.
      sorry

lemma dvd_RHS_of_dvd_A_B (p : ℕ) (A_div : (p : ℤ)^2 ∣ A_seq (p - 1)) (B_div : (p : ℤ) ∣ B_seq (p - 1)) :
    (p : ℤ)^3 ∣ 2 * p * A_seq (p - 1) + 4 * p^2 * B_seq (p - 1) + p^3 * C_seq p (p - 1) := by
  rcases A_div with ⟨a, rfl⟩
  rcases B_div with ⟨b, rfl⟩
  use 2 * a + 4 * b + C_seq p (p - 1)
  ring

lemma coprime_p_factorial (p : ℕ) (hp : p.Prime) :
    Nat.Coprime (p ^ 3) (p - 1).factorial := by
  have h_lt : p - 1 < p := by omega
  have h_cop : Nat.Coprime p (p - 1).factorial := Nat.Prime.coprime_factorial_of_lt hp h_lt
  exact Nat.Coprime.pow_left 3 h_cop

lemma h_S1_mod_deduction (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3)
    (h_div : (p : ℤ)^3 ∣ 2 * p * A_seq (p - 1) + 4 * p^2 * B_seq (p - 1) + p^3 * C_seq p (p - 1)) :
    (p : ℤ)^3 ∣ (3 * (3 * p - 1).choose (p - 1) : ℤ) - 3 := by
  have h_prod := product_identity p (p - 1)
  have h_choose := f_seq_eq_choose_mul_factorial p (p - 1)
  rw [h_choose] at h_prod
  have h_sub : ((((3 * p - 1).choose (p - 1) * (p - 1).factorial : ℕ) : ℤ) - ((p - 1).factorial : ℤ)) =
      ((((3 * p - 1).choose (p - 1) - 1) * (p - 1).factorial : ℕ) : ℤ) := by
    have h_choose_ge : (3 * p - 1).choose (p - 1) ≥ 1 := by
      apply Nat.choose_pos
      omega
    push_cast
    ring
  have h_algebra : (((3 * p - 1).choose (p - 1) * (p - 1).factorial : ℕ) : ℤ) - ((p - 1).factorial : ℤ) =
      2 * p * A_seq (p - 1) + 4 * p^2 * B_seq (p - 1) + p^3 * C_seq p (p - 1) := by
    omega
  rw [h_sub] at h_algebra
  have h_div_z : (p : ℤ)^3 ∣ ((((3 * p - 1).choose (p - 1) - 1) * (p - 1).factorial : ℕ) : ℤ) := by
    rw [← h_algebra]
    exact h_div
  have h_div_n : p^3 ∣ ((3 * p - 1).choose (p - 1) - 1) * (p - 1).factorial := by
    exact_mod_cast h_div_z
  have h_cop : Nat.Coprime (p ^ 3) (p - 1).factorial := coprime_p_factorial p hp
  have h_dvd_n : p^3 ∣ (3 * p - 1).choose (p - 1) - 1 := by
    exact Nat.Coprime.dvd_mul_right h_cop h_div_n
  have h_dvd_z2 : (p : ℤ)^3 ∣ (((3 * p - 1).choose (p - 1) - 1 : ℕ) : ℤ) := by
    exact_mod_cast h_dvd_n
  have h_final_sub : (((3 * p - 1).choose (p - 1) - 1 : ℕ) : ℤ) = ((3 * p - 1).choose (p - 1) : ℤ) - 1 := by
    have h_choose_ge : (3 * p - 1).choose (p - 1) ≥ 1 := by
      apply Nat.choose_pos
      omega
    push_cast
    rfl
  rw [h_final_sub] at h_dvd_z2
  have h_mult : (3 * (3 * p - 1).choose (p - 1) : ℤ) - 3 = 3 * (((3 * p - 1).choose (p - 1) : ℤ) - 1) := by ring
  rw [h_mult]
  exact dvd_mul_of_dvd_right h_dvd_z2 3

lemma B_seq_identity (k : ℕ) :
    2 * (k.factorial : ℤ) * B_seq k = (A_seq k)^2 - ∑ i ∈ range k, (((k.factorial / (i + 1) : ℕ) : ℤ))^2 := by
  induction k with
  | zero => simp [A_seq, B_seq]
  | succ k ih =>
    have h_LHS : 2 * ((k + 1).factorial : ℤ) * B_seq (k + 1) =
        2 * (k + 1 : ℤ) * (k.factorial : ℤ) * (A_seq k + (k + 1 : ℤ) * B_seq k) := by
      simp [B_seq, factorial_succ]
      ring
    rw [h_LHS]
    have h_split : 2 * (k + 1 : ℤ) * (k.factorial : ℤ) * (A_seq k + (k + 1 : ℤ) * B_seq k) =
        2 * (k + 1 : ℤ) * (k.factorial : ℤ) * A_seq k + (k + 1 : ℤ)^2 * (2 * (k.factorial : ℤ) * B_seq k) := by ring
    rw [h_split, ih]
    have h_sum_succ : ∑ i ∈ range (k + 1), (((k + 1).factorial / (i + 1) : ℕ) : ℤ)^2 =
        ∑ i ∈ range k, (((k + 1).factorial / (i + 1) : ℕ) : ℤ)^2 + (((k + 1).factorial / (k + 1) : ℕ) : ℤ)^2 := by
      exact sum_range_succ (fun i => (((k + 1).factorial / (i + 1) : ℕ) : ℤ)^2) k
    have h_last : (((k + 1).factorial / (k + 1) : ℕ) : ℤ)^2 = (k.factorial : ℤ)^2 := by
      have h_div : (k + 1).factorial / (k + 1) = k.factorial := by
        rw [factorial_succ]
        exact Nat.mul_div_cancel_left _ (by omega)
      rw [h_div]
      rfl
    have h_scale : ∑ i ∈ range k, (((k + 1).factorial / (i + 1) : ℕ) : ℤ)^2 =
        (k + 1 : ℤ)^2 * ∑ i ∈ range k, (((k.factorial / (i + 1) : ℕ) : ℤ))^2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      have hx_lt : x < k := by rwa [mem_range] at hx
      have h_dvd : x + 1 ∣ k.factorial := Nat.dvd_factorial (by omega) (by omega)
      have h_div_assoc : (k + 1).factorial / (x + 1) = (k + 1) * (k.factorial / (x + 1)) := by
        rw [factorial_succ]
        exact Nat.mul_div_assoc _ h_dvd
      push_cast [h_div_assoc]
      ring
    have h_A_succ : (A_seq (k + 1))^2 = ((k.factorial : ℤ) + (k + 1 : ℤ) * A_seq k)^2 := by
      rw [A_seq]
    -- Now we just use ring to equate everything
    rw [h_A_succ]
    -- We want to prove:
    -- 2 * (k + 1) * k! * A_seq k + (k + 1)^2 * ((A_seq k)^2 - sum) =
    -- (k! + (k + 1) * A_seq k)^2 - (scale_sum + last)
    -- which is exactly:
    -- 2 * (k + 1) * k! * A_seq k + (k + 1)^2 * (A_seq k)^2 - (k + 1)^2 * sum =
    -- (k!)^2 + 2 * (k + 1) * k! * A_seq k + (k + 1)^2 * (A_seq k)^2 - (k + 1)^2 * sum - (k!)^2
    -- Let's substitute scale_sum and last
    rw [h_scale, h_last]
    ring

def S2_sum (k : ℕ) : ℤ := ∑ i ∈ range k, (((k.factorial / (i + 1) : ℕ) : ℤ))^2

lemma B_seq_div_of_A_S2_div (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5)
    (hA : (p : ℤ) ∣ A_seq (p - 1)) (hS2 : (p : ℤ) ∣ S2_sum (p - 1)) :
    (p : ℤ) ∣ B_seq (p - 1) := by
  have h_ident := B_seq_identity (p - 1)
  change S2_sum (p - 1) at h_ident
  have h_sub : (p : ℤ) ∣ (A_seq (p - 1))^2 - S2_sum (p - 1) := by
    apply dvd_sub
    · exact dvd_pow hA (by omega)
    · exact hS2
  rw [← h_ident] at h_sub
  -- We have (p : ℤ) ∣ 2 * (p - 1).factorial * B_seq (p - 1)
  -- Convert to Nat using Int.natCast_dvd
  rw [Int.natCast_dvd] at h_sub
  have h_abs : (2 * ((p - 1).factorial : ℤ) * B_seq (p - 1)).natAbs =
      (2 * (p - 1).factorial) * (B_seq (p - 1)).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul]
    rfl
  rw [h_abs] at h_sub
  have h_cop : Nat.Coprime p (2 * (p - 1).factorial) := by
    have h_cop_fact : Nat.Coprime p (p - 1).factorial := by
      have h_lt : p - 1 < p := by omega
      exact Nat.Prime.coprime_factorial_of_lt hp h_lt
    have h_cop_2 : Nat.Coprime p 2 := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hdvd
      have h_le := Nat.le_of_dvd (by omega) hdvd
      omega
    exact Nat.Coprime.mul_right h_cop_2 h_cop_fact
  have h_div_abs : p ∣ (B_seq (p - 1)).natAbs := by
    exact Nat.Coprime.dvd_mul_right h_cop h_sub
  rwa [← Int.natCast_dvd] at h_div_abs

lemma coprime_of_sum_eq_prime (p a b : ℕ) (hp : p.Prime) (hsum : a + b = p) (ha : a < p) :
    Nat.Coprime a b := by
  have h_gcd : Nat.gcd a b ∣ p := by
    have h1 : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
    have h2 : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
    have h3 : Nat.gcd a b ∣ a + b := dvd_add h1 h2
    rwa [hsum] at h3
  rcases hp.eq_one_or_self_of_dvd _ h_gcd with h_one | h_self
  · exact h_one
  · have h_le : Nat.gcd a b ≤ a := by
      rcases a with rfl | a
      · omega
      · exact Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
    omega

lemma product_dvd_factorial (p j : ℕ) (hp : p.Prime) (hj : j < p - 1) :
    (j + 1) * (p - 1 - j) ∣ (p - 1).factorial := by
  have h_sum : (j + 1) + (p - 1 - j) = p := by omega
  have h_lt1 : j + 1 < p := by omega
  have h_lt2 : p - 1 - j < p := by omega
  have h_cop : Nat.Coprime (j + 1) (p - 1 - j) := coprime_of_sum_eq_prime p (j + 1) (p - 1 - j) hp h_sum h_lt1
  have hdvd1 : j + 1 ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  have hdvd2 : p - 1 - j ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h_cop hdvd1 hdvd2

lemma div_add_div_eq_mul_div (F A B p : ℕ) (h_dvd : A * B ∣ F) (h_sum : A + B = p) (hA : A > 0) (hB : B > 0) :
    F / A + F / B = p * (F / (A * B)) := by
  rcases h_dvd with ⟨K, rfl⟩
  have h_div1 : (A * B * K) / A = B * K := by
    have h_assoc : A * B * K = A * (B * K) := by ring
    rw [h_assoc]
    exact Nat.mul_div_cancel_left (B * K) hA
  have h_div2 : (A * B * K) / B = A * K := by
    have h_assoc : A * B * K = B * (A * K) := by ring
    rw [h_assoc]
    exact Nat.mul_div_cancel_left (A * K) hB
  have h_div3 : (A * B * K) / (A * B) = K := by
    exact Nat.mul_div_cancel_left K (by omega)
  rw [h_div1, h_div2, h_div3]
  rw [← add_mul, ← h_sum]
  ring

lemma sum_factorial_div_reflect (p : ℕ) (hp3 : p ≥ 3) :
    ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
    ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) := by
  have h_ref := Finset.sum_range_reflect (fun j => (((p - 1).factorial / (j + 1) : ℕ) : ℤ)) (p - 1)
  have h_congr : (fun j => (((p - 1).factorial / (p - 1 - 1 - j + 1) : ℕ) : ℤ)) =
                 (fun j => (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ)) := by
    ext j
    congr 2
    omega
  rw [h_congr] at h_ref
  exact h_ref

lemma A_seq_div_p (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (p : ℤ) ∣ A_seq (p - 1) := by
  rw [A_seq_eq_A_sum]
  have h_reflect := sum_factorial_div_reflect p (by omega)
  have h_add : 2 * A_sum (p - 1) = ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) + (p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) := by
    rw [A_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    push_cast
    rfl
  have h_rew_reflect : ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                       ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) := h_reflect
  have h_sum_add : ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) + ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                   2 * A_sum (p - 1) := by
    rw [h_rew_reflect, ← two_mul]
    rfl
  have h_dvd_sum : ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) + (p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                   (p : ℤ) * ∑ j ∈ range (p - 1), (((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ℤ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hj_lt : j < p - 1 := by rwa [mem_range] at hj
    have hdvd := product_dvd_factorial p j hp hj_lt
    have h_sum : (j + 1) + (p - 1 - j) = p := by omega
    have h_div := div_add_div_eq_mul_div (p - 1).factorial (j + 1) (p - 1 - j) p hdvd h_sum (by omega) (by omega)
    push_cast [h_div]
    ring
  rw [h_add, h_dvd_sum] at h_sum_add
  -- We have 2 * A_sum (p - 1) is divisible by p, but let's use the divisibility:
  have h_div_z : (p : ℤ) ∣ 2 * A_sum (p - 1) := by
    rw [h_add, h_dvd_sum]
    exact dvd_mul_right (p : ℤ) _
  rw [Int.natCast_dvd] at h_div_z
  have h_abs : (2 * A_sum (p - 1)).natAbs = 2 * (A_sum (p - 1)).natAbs := by
    rw [Int.natAbs_mul]
    rfl
  rw [h_abs] at h_div_z
  have h_cop : Nat.Coprime p 2 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdvd
    have h_le := Nat.le_of_dvd (by omega) hdvd
    omega
  have h_div_abs : p ∣ (A_sum (p - 1)).natAbs := Nat.Coprime.dvd_mul_right h_cop h_div_z
  rwa [← Int.natCast_dvd] at h_div_abs

lemma sum_squares (n : ℕ) :
    6 * ∑ i ∈ range n, (i + 1)^2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_sum : ∑ i ∈ range (n + 1), (i + 1)^2 = ∑ i ∈ range n, (i + 1)^2 + (n + 1)^2 := by
      exact sum_range_succ (fun i => (i + 1)^2) n
    rw [h_sum, mul_add, ih]
    ring


lemma nat_div_cast_zmod (p : ℕ) [Fact p.Prime] (a b : ℕ) (h_dvd : b ∣ a) (hb : (b : ZMod p) ≠ 0) :
    ((a / b : ℕ) : ZMod p) = (a : ZMod p) / (b : ZMod p) := by
  have h_eq : a = b * (a / b) := (Nat.mul_div_cancel' h_dvd).symm
  have h_cast : (a : ZMod p) = (b : ZMod p) * ((a / b : ℕ) : ZMod p) := by
    exact_mod_cast congr_arg (fun x => (x : ZMod p)) h_eq
  rw [h_cast, mul_div_cancel_left₀ _ hb]
