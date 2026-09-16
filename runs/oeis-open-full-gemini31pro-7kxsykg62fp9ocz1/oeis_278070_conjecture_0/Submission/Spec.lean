import FormalConjectures.Util.ProblemImports

open Nat Finset

def A278070 (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    (n.choose k) * ((n + k).pred.choose k) * (k.factorial)

-- Lemma 1: descFactorial_add
lemma descFactorial_add (X A B : ℕ) :
    X.descFactorial (A + B) = X.descFactorial A * (X - A).descFactorial B := by
  induction B with
  | zero => simp
  | succ B ih =>
    have h0 : A + (B + 1) = A + B + 1 := by omega
    rw [h0]
    have h1 : X.descFactorial (A + B + 1) = (X - (A + B)) * X.descFactorial (A + B) := rfl
    have h2 : (X - A).descFactorial (B + 1) = (X - A - B) * (X - A).descFactorial B := rfl
    rw [h1, h2, ih]
    have : X - (A + B) = X - A - B := by omega
    rw [this]
    ring

-- Lemma 2: descFactorial_succ_eq
lemma descFactorial_succ_eq (n m : ℕ) :
    n * (n - 1).descFactorial m = n.descFactorial (m + 1) := by
  induction m with
  | zero => simp [descFactorial]
  | succ m ih =>
    have h1 : n.descFactorial (m + 2) = (n - (m + 1)) * n.descFactorial (m + 1) := rfl
    have h2 : (n - 1).descFactorial (m + 1) = (n - 1 - m) * (n - 1).descFactorial m := rfl
    rw [h1, h2, ← ih]
    have h3 : n - 1 - m = n - (m + 1) := by omega
    rw [h3]
    ring

-- Lemma 3: L_eq_R
lemma L_eq_R (n k : ℕ) (hk : 1 ≤ k) :
    k.factorial * k.factorial * n.choose k * (n + k - 1).choose k = n * (2 * k - 1).factorial * (n + k - 1).choose (2 * k - 1) := by
  have h1 : k.factorial * n.choose k = n.descFactorial k := descFactorial_eq_factorial_mul_choose n k |>.symm
  have h2 : k.factorial * (n + k - 1).choose k = (n + k - 1).descFactorial k := descFactorial_eq_factorial_mul_choose (n+k-1) k |>.symm
  have hL : k.factorial * k.factorial * n.choose k * (n + k - 1).choose k = n.descFactorial k * (n + k - 1).descFactorial k := by
    calc
      k.factorial * k.factorial * n.choose k * (n + k - 1).choose k = (k.factorial * n.choose k) * (k.factorial * (n + k - 1).choose k) := by ring
      _ = n.descFactorial k * (n + k - 1).descFactorial k := by rw [h1, h2]

  have h3 : (2 * k - 1).factorial * (n + k - 1).choose (2 * k - 1) = (n + k - 1).descFactorial (2 * k - 1) := descFactorial_eq_factorial_mul_choose (n+k-1) (2*k-1) |>.symm
  have hR : n * (2 * k - 1).factorial * (n + k - 1).choose (2 * k - 1) = n * (n + k - 1).descFactorial (2 * k - 1) := by
    calc
      n * (2 * k - 1).factorial * (n + k - 1).choose (2 * k - 1) = n * ((2 * k - 1).factorial * (n + k - 1).choose (2 * k - 1)) := by ring
      _ = n * (n + k - 1).descFactorial (2 * k - 1) := by rw [h3]

  rw [hL, hR]
  have h4 : 2 * k - 1 = k + (k - 1) := by omega
  rw [h4, descFactorial_add]
  have h5 : n + k - 1 - k = n - 1 := by omega
  rw [h5]
  have h6 : k = (k - 1) + 1 := by omega
  conv_lhs =>
    lhs
    rw [h6, ← descFactorial_succ_eq n (k-1)]
  ring

-- Lemma 4: mul_choose_eq
lemma mul_choose_eq (X m : ℕ) :
    (m + 1) * X.choose (m + 1) = (X - m) * X.choose m := by
  have h1 : m.factorial * ((m + 1) * X.choose (m + 1)) = m.factorial * ((X - m) * X.choose m) := by
    calc
      m.factorial * ((m + 1) * X.choose (m + 1)) = ((m + 1) * m.factorial) * X.choose (m + 1) := by ring
      _ = (m + 1).factorial * X.choose (m + 1) := by rfl
      _ = X.descFactorial (m + 1) := by rw [← descFactorial_eq_factorial_mul_choose]
      _ = (X - m) * X.descFactorial m := by rfl
      _ = (X - m) * (m.factorial * X.choose m) := by rw [← descFactorial_eq_factorial_mul_choose]
      _ = m.factorial * ((X - m) * X.choose m) := by ring
  exact Nat.eq_of_mul_eq_mul_left (factorial_pos m) h1

-- Lemma 5: n_mul_choose_eq
lemma n_mul_choose_eq (n k : ℕ) (hk : 1 ≤ k) :
    n * (n + k - 1).choose (2 * k - 1) = k * (n + k - 1).choose (2 * k - 1) + 2 * k * (n + k - 1).choose (2 * k) := by
  have hX : 2 * k = (2 * k - 1) + 1 := by omega
  have h1 := mul_choose_eq (n + k - 1) (2 * k - 1)
  rw [← hX] at h1
  by_cases hn : k ≤ n
  · have h2 : n + k - 1 - (2 * k - 1) = n - k := by omega
    rw [h2] at h1
    have h3 : n = k + (n - k) := by omega
    calc
      n * (n + k - 1).choose (2 * k - 1) = (k + (n - k)) * (n + k - 1).choose (2 * k - 1) := by nth_rw 1 [h3]
      _ = k * (n + k - 1).choose (2 * k - 1) + (n - k) * (n + k - 1).choose (2 * k - 1) := by ring
      _ = k * (n + k - 1).choose (2 * k - 1) + 2 * k * (n + k - 1).choose (2 * k) := by rw [← h1]
  · have h_lt : n < k := by omega
    have h3 : n + k - 1 < 2 * k - 1 := by omega
    have h4 : (n + k - 1).choose (2 * k - 1) = 0 := choose_eq_zero_of_lt h3
    have h5 : n + k - 1 < 2 * k := by omega
    have h6 : (n + k - 1).choose (2 * k) = 0 := choose_eq_zero_of_lt h5
    rw [h4, h6]
    ring

-- Lemma 6: descFactorial_mul_factorial
lemma descFactorial_mul_factorial_eq (n k : ℕ) (h : k ≤ n) :
    n.descFactorial k * (n - k).factorial = n.factorial := by
  have h1 : n.choose k * k.factorial * (n - k).factorial = n.factorial := choose_mul_factorial_mul_factorial h
  have h2 : n.descFactorial k = n.choose k * k.factorial := by
    rw [descFactorial_eq_factorial_mul_choose, mul_comm]
  rw [h2]
  exact h1

-- Lemma 7: fact_mul_Ak
lemma fact_mul_Ak (k : ℕ) (hk : 1 ≤ k) :
    k.factorial * (2 * k - 1).descFactorial k = k * (2 * k - 1).factorial := by
  have h1 : k.factorial = k * (k - 1).factorial := by
    cases k with
    | zero => omega
    | succ k => rfl
  rw [h1]
  have h2 : (2 * k - 1).descFactorial k * (2 * k - 1 - k).factorial = (2 * k - 1).factorial := by
    apply descFactorial_mul_factorial_eq
    omega
  have h3 : 2 * k - 1 - k = k - 1 := by omega
  rw [h3] at h2
  calc
    k * (k - 1).factorial * (2 * k - 1).descFactorial k = k * ((2 * k - 1).descFactorial k * (k - 1).factorial) := by ring
    _ = k * (2 * k - 1).factorial := by rw [h2]

-- Lemma 8: P_eq_A_B
lemma P_eq_A_B (n k : ℕ) (hk : 1 ≤ k) :
    n.choose k * (n + k - 1).choose k * k.factorial =
      (2 * k - 1).descFactorial k * (n + k - 1).choose (2 * k - 1) +
      2 * (2 * k - 1).descFactorial k * (n + k - 1).choose (2 * k) := by
  have H1 := L_eq_R n k hk
  have H2 := n_mul_choose_eq n k hk
  have H3 := fact_mul_Ak k hk
  have h_mul : k.factorial * (n.choose k * (n + k - 1).choose k * k.factorial) =
    k.factorial * ((2 * k - 1).descFactorial k * (n + k - 1).choose (2 * k - 1) +
      2 * (2 * k - 1).descFactorial k * (n + k - 1).choose (2 * k)) := by
    calc
      k.factorial * (n.choose k * (n + k - 1).choose k * k.factorial) =
        k.factorial * k.factorial * n.choose k * (n + k - 1).choose k := by ring
      _ = n * (2 * k - 1).factorial * (n + k - 1).choose (2 * k - 1) := H1
      _ = (2 * k - 1).factorial * (n * (n + k - 1).choose (2 * k - 1)) := by ring
      _ = (2 * k - 1).factorial * (k * (n + k - 1).choose (2 * k - 1) + 2 * k * (n + k - 1).choose (2 * k)) := by rw [H2]
      _ = (k * (2 * k - 1).factorial) * (n + k - 1).choose (2 * k - 1) +
          2 * (k * (2 * k - 1).factorial) * (n + k - 1).choose (2 * k) := by ring
      _ = (k.factorial * (2 * k - 1).descFactorial k) * (n + k - 1).choose (2 * k - 1) +
          2 * (k.factorial * (2 * k - 1).descFactorial k) * (n + k - 1).choose (2 * k) := by rw [← H3]
      _ = k.factorial * ((2 * k - 1).descFactorial k * (n + k - 1).choose (2 * k - 1) +
          2 * (2 * k - 1).descFactorial k * (n + k - 1).choose (2 * k)) := by ring
  exact Nat.eq_of_mul_eq_mul_left (factorial_pos k) h_mul

lemma C_mul_choose_mod_K (m : ℕ) (C : ℕ) (hC : ∀ i, 1 ≤ i → i ≤ m → i ∣ C) (X K : ℕ) :
    C * (X + K).choose m ≡ C * X.choose m [MOD K] := by
  induction m generalizing X with
  | zero =>
    simp only [choose_zero_right, mul_one, ModEq.rfl]
  | succ m ih_m =>
    induction X with
    | zero =>
      simp only [zero_add, choose_zero_succ, mul_zero]
      cases K with
      | zero => rfl
      | succ K' =>
        have h1 : m + 1 ∣ C := hC (m + 1) (by omega) (by omega)
        rcases h1 with ⟨D, hD⟩
        have h2 : C * (K' + 1).choose (m + 1) = (K' + 1) * (D * K'.choose m) := by
          have h3 := Nat.add_one_mul_choose_eq K' m
          calc
            C * (K' + 1).choose (m + 1) = D * ((K' + 1).choose (m + 1) * (m + 1)) := by
              rw [hD]; ring
            _ = D * ((K' + 1) * K'.choose m) := by rw [← h3]
            _ = (K' + 1) * (D * K'.choose m) := by ring
        rw [h2]
        change ((K' + 1) * (D * K'.choose m)) % (K' + 1) = 0 % (K' + 1)
        rw [Nat.mul_mod_right, Nat.zero_mod]
    | succ X ih_X =>
      have h3 : (X + 1 + K).choose (m + 1) = (X + K).choose (m + 1) + (X + K).choose m := by
        have : X + 1 + K = X + K + 1 := by omega
        rw [this, choose_succ_succ', add_comm]
      have h4 : (X + 1).choose (m + 1) = X.choose (m + 1) + X.choose m := by
        rw [choose_succ_succ', add_comm]
      rw [h3, h4, mul_add, mul_add]
      have h5 : ∀ i, 1 ≤ i → i ≤ m → i ∣ C := fun i h1 h2 => hC i h1 (by omega)
      exact ModEq.add ih_X (ih_m h5 X)

lemma factor_dvd_descFactorial (n m i : ℕ) (h1 : n - m < i) (h2 : i ≤ n) :
    i ∣ n.descFactorial m := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : i = n - m
    · rw [h]
      have : n.descFactorial (m + 1) = (n - m) * n.descFactorial m := rfl
      rw [this]
      exact dvd_mul_right (n - m) (n.descFactorial m)
    · have h3 : n - m < i := by omega
      have : n.descFactorial (m + 1) = (n - m) * n.descFactorial m := rfl
      rw [this]
      exact dvd_mul_of_dvd_right (ih h3) (n - m)

lemma dvd_factorial_of_le (i m : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ m) :
    i ∣ m.factorial := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : i = m + 1
    · rw [h]
      exact dvd_mul_right (m + 1) m.factorial
    · have h3 : i ≤ m := by omega
      exact dvd_mul_of_dvd_right (ih h3) (m + 1)

lemma i_dvd_Ak (k i : ℕ) (hk : 1 ≤ k) (h1 : 1 ≤ i) (h2 : i ≤ 2 * k - 1) :
    i ∣ (2 * k - 1).descFactorial k := by
  by_cases h : i ≤ k
  · have h3 : i ∣ k.factorial := dvd_factorial_of_le i k h1 h
    have h4 : k.factorial ∣ (2 * k - 1).descFactorial k := by
      rw [descFactorial_eq_factorial_mul_choose]
      exact dvd_mul_right k.factorial _
    exact dvd_trans h3 h4
  · have h4 : 2 * k - 1 - k = k - 1 := by omega
    have h5 : 2 * k - 1 - k < i := by omega
    exact factor_dvd_descFactorial (2 * k - 1) k i h5 h2

lemma i_dvd_Bk (k i : ℕ) (hk : 1 ≤ k) (h1 : 1 ≤ i) (h2 : i ≤ 2 * k) :
    i ∣ 2 * (2 * k - 1).descFactorial k := by
  by_cases h : i ≤ 2 * k - 1
  · have h3 : i ∣ (2 * k - 1).descFactorial k := i_dvd_Ak k i hk h1 h
    exact dvd_mul_of_dvd_right h3 2
  · have h3 : i = 2 * k := by omega
    rw [h3]
    have h4 : k ∣ (2 * k - 1).descFactorial k := i_dvd_Ak k k hk hk (by omega)
    rcases h4 with ⟨D, hD⟩
    rw [hD]
    have : 2 * (k * D) = (2 * k) * D := by ring
    rw [this]
    exact dvd_mul_right (2 * k) D

lemma Pk_mod_K (n K k : ℕ) :
    (n + K).choose k * (n + K + k - 1).choose k * k.factorial ≡
    n.choose k * (n + k - 1).choose k * k.factorial [MOD K] := by
  by_cases hk : 1 ≤ k
  · have eq_nK := P_eq_A_B (n + K) k hk
    have eq_n := P_eq_A_B n k hk
    rw [eq_nK, eq_n]
    have h1 : ∀ i, 1 ≤ i → i ≤ 2 * k - 1 → i ∣ (2 * k - 1).descFactorial k := fun i h1 h2 => i_dvd_Ak k i hk h1 h2
    have H1 := C_mul_choose_mod_K (2 * k - 1) ((2 * k - 1).descFactorial k) h1 (n + k - 1) K
    have hX : n + K + k - 1 = n + k - 1 + K := by omega
    have hY : n + K + k - 1 = n + k - 1 + K := by omega
    have H1' : (2 * k - 1).descFactorial k * (n + K + k - 1).choose (2 * k - 1) ≡
               (2 * k - 1).descFactorial k * (n + k - 1).choose (2 * k - 1) [MOD K] := by
      rw [hX]
      exact H1
    have h2 : ∀ i, 1 ≤ i → i ≤ 2 * k → i ∣ 2 * (2 * k - 1).descFactorial k := fun i h1 h2 => i_dvd_Bk k i hk h1 h2
    have H2 := C_mul_choose_mod_K (2 * k) (2 * (2 * k - 1).descFactorial k) h2 (n + k - 1) K
    have H2' : 2 * (2 * k - 1).descFactorial k * (n + K + k - 1).choose (2 * k) ≡
               2 * (2 * k - 1).descFactorial k * (n + k - 1).choose (2 * k) [MOD K] := by
      rw [hY]
      exact H2
    exact ModEq.add H1' H2'
  · have hk0 : k = 0 := by omega
    subst hk0
    simp
    exact ModEq.refl 1

lemma sum_Pk_mod_K (n K : ℕ) :
    ((Finset.range (n + K + 1)).sum fun k => (n + K).choose k * (n + K + k - 1).choose k * k.factorial) ≡
    ((Finset.range (n + K + 1)).sum fun k => n.choose k * (n + k - 1).choose k * k.factorial) [MOD K] := by
  apply ModEq.sum
  intro k _
  exact Pk_mod_K n K k

lemma sum_Pk_eq_A (n K : ℕ) :
    (Finset.range (n + 1)).sum (fun k => n.choose k * (n + k - 1).choose k * k.factorial) =
    (Finset.range (n + K + 1)).sum (fun k => n.choose k * (n + k - 1).choose k * k.factorial) := by
  apply sum_subset
  · intro x
    simp only [mem_range]
    intro hx
    omega
  · intro x _ hnx
    simp only [mem_range, not_lt] at hnx
    have h1 : n < x := by omega
    have h2 : n.choose x = 0 := choose_eq_zero_of_lt h1
    rw [h2]
    ring

theorem oeis_278070_conjecture_0 : ∀ (n k : ℕ), Nat.ModEq k (A278070 (n + k)) (A278070 n) := by
  intro n K
  have h1 : A278070 (n + K) = (Finset.range (n + K + 1)).sum (fun k => (n + K).choose k * (n + K + k - 1).choose k * k.factorial) := rfl
  have h2 : A278070 n = (Finset.range (n + 1)).sum (fun k => n.choose k * (n + k - 1).choose k * k.factorial) := rfl
  rw [h1, h2]
  have h3 := sum_Pk_mod_K n K
  have h4 := sum_Pk_eq_A n K
  rw [h4]
  exact h3

theorem oeis_278070_conjecture_0.disproof : ¬ (type_of% @oeis_278070_conjecture_0) := sorry
