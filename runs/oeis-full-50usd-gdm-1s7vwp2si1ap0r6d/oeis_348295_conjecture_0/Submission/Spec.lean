import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 2000000


lemma Nat.sqrt_eq_of_le_and_lt {a b : ℕ} (h1 : a ^ 2 ≤ b) (h2 : b < (a + 1) ^ 2) : Nat.sqrt b = a := by
  have h_le : a ≤ Nat.sqrt b := by
    rw [Nat.le_sqrt]
    have h_sq : a ^ 2 = a * a := by ring
    rw [← h_sq]
    exact h1
  have h_lt : Nat.sqrt b < a + 1 := by
    rw [Nat.sqrt_lt]
    have h_sq : (a + 1) ^ 2 = (a + 1) * (a + 1) := by ring
    rw [← h_sq]
    exact h2
  omega

/--
A348295: The sequence $a(n) = \sum_{k=1}^n (-1)^{\lfloor k(\sqrt{2}-1) \rfloor}.$
-/
noncomputable def a (n : ℕ) : ℤ :=
  Finset.sum (Finset.Ioc 0 n) fun k : ℕ =>
    let k_real : ℝ := k
    let exponent_real : ℝ := k_real * (Real.sqrt 2 - 1)
    let exponent_int : ℤ := Int.floor exponent_real
    -- The exponent $\lfloor k(\sqrt{2}-1) \rfloor$ is non-negative for $k \ge 1$.
    (-1 : ℤ) ^ exponent_int.toNat

lemma floor_eq_sqrt (k : ℕ) :
    Int.floor ((k : ℝ) * (Real.sqrt 2 - 1)) = (Nat.sqrt (2 * k ^ 2) : ℤ) - (k : ℤ) := by
  rw [Int.floor_eq_iff]
  have h_sqrt2_ge : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h_sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hS_le : (Nat.sqrt (2 * k ^ 2) : ℝ) ^ 2 ≤ 2 * (k : ℝ) ^ 2 := by
    have h1 := Nat.sqrt_le (2 * k ^ 2)
    have h2 : ((Nat.sqrt (2 * k ^ 2) * Nat.sqrt (2 * k ^ 2) : ℕ) : ℝ) ≤ ((2 * k ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    ring_nf at h2 ⊢
    exact h2
  have hS_lt : 2 * (k : ℝ) ^ 2 < ((Nat.sqrt (2 * k ^ 2) : ℝ) + 1) ^ 2 := by
    have h1 := Nat.lt_succ_sqrt (2 * k ^ 2)
    have h2 : ((2 * k ^ 2 : ℕ) : ℝ) < (((Nat.sqrt (2 * k ^ 2) + 1) * (Nat.sqrt (2 * k ^ 2) + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    ring_nf at h2 ⊢
    exact h2
  constructor
  · push_cast
    have h_pos : 0 ≤ (Nat.sqrt (2 * k ^ 2) : ℝ) := by positivity
    have h_pos2 : 0 ≤ (k : ℝ) * Real.sqrt 2 := by positivity
    have h_sq : (Nat.sqrt (2 * k ^ 2) : ℝ) ≤ (k : ℝ) * Real.sqrt 2 := by
      rw [← sq_le_sq₀ h_pos h_pos2]
      rw [mul_pow, h_sqrt2_sq]
      ring_nf at hS_le ⊢
      exact hS_le
    linarith
  · push_cast
    have h_pos1 : 0 ≤ (k : ℝ) * Real.sqrt 2 := by positivity
    have h_pos2 : 0 ≤ (Nat.sqrt (2 * k ^ 2) : ℝ) + 1 := by positivity
    have h_sq : (k : ℝ) * Real.sqrt 2 < (Nat.sqrt (2 * k ^ 2) : ℝ) + 1 := by
      rw [← sq_lt_sq₀ h_pos1 h_pos2]
      rw [mul_pow, h_sqrt2_sq]
      ring_nf at hS_lt ⊢
      exact hS_lt
    linarith

lemma le_sqrt_two_k_sq (k : ℕ) : k ≤ Nat.sqrt (2 * k ^ 2) := by
  rw [Nat.le_sqrt]
  ring_nf
  omega

lemma a_term_eq_computable (k : ℕ) :
    (-1 : ℤ) ^ (Int.floor ((k : ℝ) * (Real.sqrt 2 - 1))).toNat = (-1 : ℤ) ^ (Nat.sqrt (2 * k ^ 2) - k) := by
  rw [floor_eq_sqrt]
  have hk : k ≤ Nat.sqrt (2 * k ^ 2) := le_sqrt_two_k_sq k
  have h_toNat : ((Nat.sqrt (2 * k ^ 2) : ℤ) - (k : ℤ)).toNat = Nat.sqrt (2 * k ^ 2) - k := by
    omega
  rw [h_toNat]

def a_comp (n : ℕ) : ℤ :=
  Finset.sum (Finset.Ioc 0 n) fun k : ℕ => (-1 : ℤ) ^ (Nat.sqrt (2 * k ^ 2) - k)

lemma a_eq_a_comp (n : ℕ) : a n = a_comp n := by
  dsimp [a, a_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact a_term_eq_computable k

unseal Nat.sqrt.iter in
lemma a_comp_2_eq : a_comp 2 = 2 := by decide

unseal Nat.sqrt.iter in
lemma a_comp_12_eq : a_comp 12 = 4 := by decide

unseal Nat.sqrt.iter in
lemma a_comp_70_eq : a_comp 70 = 6 := by decide

set_option maxRecDepth 1000000
unseal Nat.sqrt.iter in
lemma a_comp_408_eq : a_comp 408 = 8 := by decide


/--
Conjecture (1) for A348295: The sequence is unbounded from above.
-/

theorem sqrt_two_irrational_helper (j k : ℕ) (h : 2 * j^2 = k^2) : j = 0 := by
  if hj : j = 0 then
    exact hj
  else
    have h_dvd : 2 ∣ k^2 := ⟨j^2, by omega⟩
    have h_k_even : 2 ∣ k := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_dvd
    rcases h_k_even with ⟨m, rfl⟩
    have h_sq_expand : (2 * m)^2 = 2 * (2 * m^2) := by ring
    rw [h_sq_expand] at h
    have h_j_sq : j^2 = 2 * m^2 := by omega
    have h_j_dvd : 2 ∣ j^2 := ⟨m^2, by omega⟩
    have h_j_even : 2 ∣ j := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_j_dvd
    rcases h_j_even with ⟨r, rfl⟩
    have h_sq_expand2 : (2 * r)^2 = 2 * (2 * r^2) := by ring
    rw [h_sq_expand2] at h_j_sq
    have h_r_sq : 2 * r^2 = m^2 := by omega
    have hr : r < 2 * r := by omega
    have hr_zero : r = 0 := sqrt_two_irrational_helper r m h_r_sq
    omega
termination_by j

lemma sqrt_two_irrational (j k : ℕ) (hj : j ≥ 1) : 2 * j^2 ≠ k^2 := by
  intro h
  have hj0 : j = 0 := sqrt_two_irrational_helper j k h
  omega

lemma real_bound (j k : ℕ) (hj : j ≥ 1) :
    |(j : ℝ) * Real.sqrt 2 - (k : ℝ)| ≥ 1 / ((j : ℝ) * Real.sqrt 2 + (k : ℝ)) := by
  have h_pos : 0 < (j : ℝ) * Real.sqrt 2 + (k : ℝ) := by
    have h_sqrt2_pos : 0 < Real.sqrt 2 := by
      have h2 : (0 : ℝ) < 2 := by norm_num
      exact Real.sqrt_pos.mpr h2
    have h_j_pos : 0 < (j : ℝ) := by positivity
    positivity
  rw [ge_iff_le]
  rw [div_le_iff₀ h_pos]
  have h_mul : |(j : ℝ) * Real.sqrt 2 - (k : ℝ)| * ((j : ℝ) * Real.sqrt 2 + (k : ℝ)) = |((j : ℝ) * Real.sqrt 2 - (k : ℝ)) * ((j : ℝ) * Real.sqrt 2 + (k : ℝ))| := by
    have hY : (j : ℝ) * Real.sqrt 2 + (k : ℝ) = |(j : ℝ) * Real.sqrt 2 + (k : ℝ)| := by
      exact (abs_eq_self.mpr (by linarith [h_pos])).symm
    calc |(j : ℝ) * Real.sqrt 2 - (k : ℝ)| * ((j : ℝ) * Real.sqrt 2 + (k : ℝ))
      _ = |(j : ℝ) * Real.sqrt 2 - (k : ℝ)| * |(j : ℝ) * Real.sqrt 2 + (k : ℝ)| := congr_arg (fun y => |(j : ℝ) * Real.sqrt 2 - (k : ℝ)| * y) hY
      _ = |((j : ℝ) * Real.sqrt 2 - (k : ℝ)) * ((j : ℝ) * Real.sqrt 2 + (k : ℝ))| := by rw [← abs_mul]
  rw [h_mul]
  have h_prod : ((j : ℝ) * Real.sqrt 2 - (k : ℝ)) * ((j : ℝ) * Real.sqrt 2 + (k : ℝ)) = 2 * (j : ℝ)^2 - (k : ℝ)^2 := by
    have h_sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc ((j : ℝ) * Real.sqrt 2 - (k : ℝ)) * ((j : ℝ) * Real.sqrt 2 + (k : ℝ))
      _ = (j : ℝ)^2 * (Real.sqrt 2)^2 - (k : ℝ)^2 := by ring
      _ = 2 * (j : ℝ)^2 - (k : ℝ)^2 := by rw [h_sqrt2_sq]; ring
  rw [h_prod]
  have h_cast : 2 * (j : ℝ)^2 - (k : ℝ)^2 = (((2 * (j : ℤ)^2 - (k : ℤ)^2 : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [h_cast]
  rw [← Int.cast_abs]
  have h_irr : (2 * (j : ℤ)^2 - (k : ℤ)^2 : ℤ) ≠ 0 := by
    intro h_zero
    have h_eq : 2 * (j : ℤ)^2 = (k : ℤ)^2 := by omega
    have h_nat : 2 * j^2 = k^2 := by
      -- we can cast this back to nat
      have h_j_sq : (j : ℤ)^2 = ((j^2 : ℕ) : ℤ) := by push_cast; rfl
      have h_k_sq : (k : ℤ)^2 = ((k^2 : ℕ) : ℤ) := by push_cast; rfl
      rw [h_j_sq, h_k_sq] at h_eq
      have h_eq2 : (((2 * j^2 : ℕ) : ℤ)) = (((k^2 : ℕ) : ℤ)) := by
        push_cast
        omega
      exact_mod_cast h_eq2
    exact sqrt_two_irrational j k hj h_nat
  generalize h_X : (2 * (j : ℤ)^2 - (k : ℤ)^2 : ℤ) = X at h_irr ⊢
  have h_abs_ge : |X| ≥ 1 := by
    rcases lt_trichotomy X 0 with hLt | rfl | hGt
    · have h_abs : |X| = -X := abs_of_neg hLt
      rw [h_abs]
      omega
    · contradiction
    · have h_abs : |X| = X := abs_of_pos hGt
      rw [h_abs]
      omega
  exact_mod_cast h_abs_ge

def PQ : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 =>
    let (p, q) := PQ n
    (p + q, 2 * p + q)

def P (n : ℕ) : ℕ := (PQ n).1
def Q (n : ℕ) : ℕ := (PQ n).2

lemma P_zero : P 0 = 0 := rfl
lemma Q_zero : Q 0 = 1 := rfl

lemma P_succ (n : ℕ) : P (n + 1) = P n + Q n := by
  dsimp [P, PQ]
  rfl

lemma Q_succ (n : ℕ) : Q (n + 1) = 2 * P n + Q n := by
  dsimp [Q, PQ]
  rfl

lemma Pell_identity (n : ℕ) : (Q n : ℤ)^2 - 2 * (P n : ℤ)^2 = (-1 : ℤ)^n := by
  induction n with
  | zero =>
    rw [P_zero, Q_zero]
    ring
  | succ n ih =>
    rw [P_succ, Q_succ]
    push_cast
    have h_ring : ((2 * (P n : ℤ) + (Q n : ℤ))^2 - 2 * ((P n : ℤ) + (Q n : ℤ))^2) = - ((Q n : ℤ)^2 - 2 * (P n : ℤ)^2) := by ring
    rw [h_ring, ih]
    ring

lemma Q_ge_one (n : ℕ) : Q n ≥ 1 := by
  induction n with
  | zero =>
    rw [Q_zero]
  | succ n ih =>
    rw [Q_succ]
    omega

lemma Pell_identity_real (n : ℕ) : (Q n : ℝ)^2 - 2 * (P n : ℝ)^2 = (-1 : ℝ)^n := by
  have h := Pell_identity n
  have h_cast : (((Q n : ℤ)^2 - 2 * (P n : ℤ)^2 : ℤ) : ℝ) = (((-1 : ℤ)^n : ℤ) : ℝ) := congrArg Int.cast h
  push_cast at h_cast
  exact h_cast

lemma a_comp_succ (n : ℕ) : a_comp (n + 1) = a_comp n + (-1 : ℤ) ^ (Nat.sqrt (2 * (n + 1)^2) - (n + 1)) := by
  dsimp [a_comp]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]

lemma P_le_Q (n : ℕ) : P n ≤ Q n := by
  induction n with
  | zero =>
    rw [P_zero, Q_zero]
    omega
  | succ n ih =>
    rw [P_succ, Q_succ]
    omega

lemma P_ge_one (n : ℕ) : P (n + 1) ≥ 1 := by
  rw [P_succ]
  have h := Q_ge_one n
  omega

lemma P_ge_two_of_ge_two (n : ℕ) (h : n ≥ 2) : P n ≥ 2 := by
  rcases n with _ | _ | n
  · omega
  · omega
  · rw [P_succ]
    have h1 := P_ge_one n
    have h2 := Q_ge_one (n + 1)
    omega

lemma Q_ge_three_of_ge_two (n : ℕ) (h : n ≥ 2) : Q n ≥ 3 := by
  rcases n with _ | _ | n
  · omega
  · omega
  · rw [Q_succ]
    have h1 := P_ge_one n
    have h2 := Q_ge_one (n + 1)
    omega

lemma sqrt_two_P_sq_odd (m : ℕ) (h_pell : (Q m : ℤ)^2 - 2 * (P m : ℤ)^2 = -1) :
    Nat.sqrt (2 * P m ^ 2) = Q m := by
  have h1 : Q m ^ 2 ≤ 2 * P m ^ 2 := by
    have hp : 2 * (P m : ℤ)^2 = (Q m : ℤ)^2 + 1 := by omega
    have hp3 : (Q m : ℤ)^2 ≤ 2 * (P m : ℤ)^2 := by linarith
    exact_mod_cast hp3
  have h2 : 2 * P m ^ 2 < (Q m + 1) ^ 2 := by
    have hp : 2 * (P m : ℤ)^2 = (Q m : ℤ)^2 + 1 := by omega
    have hq_pos := Q_ge_one m
    have hp3 : 2 * (P m : ℤ)^2 < ((Q m : ℤ) + 1)^2 := by
      calc 2 * (P m : ℤ)^2 = (Q m : ℤ)^2 + 1 := hp
      _ < (Q m : ℤ)^2 + 2 * (Q m : ℤ) + 1 := by omega
      _ = ((Q m : ℤ) + 1)^2 := by ring
    exact_mod_cast hp3
  have h3 : Q m ≤ Nat.sqrt (2 * P m ^ 2) := by
    rw [Nat.le_sqrt, ← sq]
    exact h1
  have h4 : Nat.sqrt (2 * P m ^ 2) < Q m + 1 := by
    rw [Nat.sqrt_lt, ← sq]
    exact h2
  omega

lemma sqrt_two_P_sq_even (m : ℕ) (hm : m ≥ 2) (h_pell : (Q m : ℤ)^2 - 2 * (P m : ℤ)^2 = 1) :
    Nat.sqrt (2 * P m ^ 2) = Q m - 1 := by
  have h_sub : ((Q m - 1 : ℕ) : ℤ) = (Q m : ℤ) - 1 := by
    rw [Nat.cast_sub (by have := Q_ge_one m; omega)]
    rfl
  have h1 : (Q m - 1) ^ 2 ≤ 2 * P m ^ 2 := by
    have hp : 2 * (P m : ℤ)^2 = (Q m : ℤ)^2 - 1 := by omega
    have hq_pos := Q_ge_three_of_ge_two m hm
    have hp3 : (((Q m - 1 : ℕ) : ℤ)) ^ 2 ≤ 2 * (P m : ℤ)^2 := by
      rw [h_sub]
      calc ((Q m : ℤ) - 1)^2 = (Q m : ℤ)^2 - 2 * (Q m : ℤ) + 1 := by ring
      _ ≤ (Q m : ℤ)^2 - 1 := by omega
      _ = 2 * (P m : ℤ)^2 := hp.symm
    exact_mod_cast hp3
  have h2 : 2 * P m ^ 2 < Q m ^ 2 := by
    have hp : 2 * (P m : ℤ)^2 = (Q m : ℤ)^2 - 1 := by omega
    have hp3 : 2 * (P m : ℤ)^2 < (Q m : ℤ)^2 := by linarith
    exact_mod_cast hp3
  have h3 : Q m - 1 ≤ Nat.sqrt (2 * P m ^ 2) := by
    rw [Nat.le_sqrt, ← sq]
    exact h1
  have h4 : Nat.sqrt (2 * P m ^ 2) < Q m := by
    rw [Nat.sqrt_lt, ← sq]
    exact h2
  omega

lemma sqrt_two_Q_sq_odd (n : ℕ) (h_pell : (Q n : ℤ)^2 - 2 * (P n : ℤ)^2 = -1) :
    Nat.sqrt (2 * Q n ^ 2) = 2 * P n - 1 := by
  have hn_pos : n ≥ 1 := by
    by_contra hc
    have h_zero : n = 0 := by omega
    subst h_zero
    rw [P_zero, Q_zero] at h_pell
    omega
  have h_p_pos : (P n : ℤ) ≥ 1 := by
    rcases n with _ | k
    · contradiction
    · have h := P_ge_one k
      exact_mod_cast h
  have h_sub : ((2 * P n - 1 : ℕ) : ℤ) = 2 * (P n : ℤ) - 1 := by
    rw [Nat.cast_sub (by have := h_p_pos; omega)]
    push_cast
    rfl
  have h1 : (2 * P n - 1) ^ 2 ≤ 2 * Q n ^ 2 := by
    have hp : 2 * (Q n : ℤ)^2 = 4 * (P n : ℤ)^2 - 2 := by linarith
    have hp3 : (((2 * P n - 1 : ℕ) : ℤ)) ^ 2 ≤ 2 * (Q n : ℤ)^2 := by
      rw [h_sub]
      calc (2 * (P n : ℤ) - 1)^2 = 4 * (P n : ℤ)^2 - 4 * (P n : ℤ) + 1 := by ring
      _ ≤ 4 * (P n : ℤ)^2 - 2 := by omega
      _ = 2 * (Q n : ℤ)^2 := hp.symm
    exact_mod_cast hp3
  have h2 : 2 * Q n ^ 2 < (2 * P n) ^ 2 := by
    have hp : 2 * (Q n : ℤ)^2 = 4 * (P n : ℤ)^2 - 2 := by linarith
    have hp3 : 2 * (Q n : ℤ)^2 < (2 * (P n : ℤ))^2 := by linarith
    exact_mod_cast hp3
  have h3 : 2 * P n - 1 ≤ Nat.sqrt (2 * Q n ^ 2) := by
    rw [Nat.le_sqrt, ← sq]
    exact h1
  have h4 : Nat.sqrt (2 * Q n ^ 2) < 2 * P n := by
    rw [Nat.sqrt_lt, ← sq]
    exact h2
  omega

lemma sqrt_two_Q_sq_even (n : ℕ) (hn : n ≥ 2) (h_pell : (Q n : ℤ)^2 - 2 * (P n : ℤ)^2 = 1) :
    Nat.sqrt (2 * Q n ^ 2) = 2 * P n := by
  have h1 : (2 * P n) ^ 2 ≤ 2 * Q n ^ 2 := by
    have hp : (Q n : ℤ)^2 = 2 * (P n : ℤ)^2 + 1 := by omega
    have hp2 : 2 * (Q n : ℤ)^2 = 4 * (P n : ℤ)^2 + 2 := by linarith
    have hp3 : (2 * (P n : ℤ)) ^ 2 ≤ 2 * (Q n : ℤ)^2 := by
      calc (2 * (P n : ℤ)) ^ 2 = 4 * (P n : ℤ)^2 := by ring
      _ ≤ 2 * (Q n : ℤ)^2 := by linarith
    exact_mod_cast hp3
  have h2 : 2 * Q n ^ 2 < (2 * P n + 1) ^ 2 := by
    have hp : (Q n : ℤ)^2 = 2 * (P n : ℤ)^2 + 1 := by omega
    have hp2 : 2 * (Q n : ℤ)^2 = 4 * (P n : ℤ)^2 + 2 := by linarith
    have h_p_pos : P n ≥ 2 := P_ge_two_of_ge_two n hn
    have hp3 : 2 * (Q n : ℤ)^2 < (2 * (P n : ℤ) + 1)^2 := by
      calc 2 * (Q n : ℤ)^2 = 4 * (P n : ℤ)^2 + 2 := hp2
      _ < 4 * (P n : ℤ)^2 + 4 * (P n : ℤ) + 1 := by omega
      _ = (2 * (P n : ℤ) + 1)^2 := by ring
    exact_mod_cast hp3
  have h3 : 2 * P n ≤ Nat.sqrt (2 * Q n ^ 2) := by
    rw [Nat.le_sqrt, ← sq]
    exact h1
  have h4 : Nat.sqrt (2 * Q n ^ 2) < 2 * P n + 1 := by
    rw [Nat.sqrt_lt, ← sq]
    exact h2
  omega

lemma neg_one_pow_even (n : ℕ) (hn : n % 2 = 0) : (-1 : ℤ)^n = 1 := by
  have h_eq : n = 2 * (n / 2) := by omega
  rw [h_eq, pow_mul]
  ring

lemma neg_one_pow_odd (n : ℕ) (hn : n % 2 = 1) : (-1 : ℤ)^n = -1 := by
  have h_eq : n = 2 * (n / 2) + 1 := by omega
  rw [h_eq, pow_add, pow_mul]
  ring

lemma neg_one_pow_cases (n : ℕ) : (-1 : ℝ)^n = 1 ∨ (-1 : ℝ)^n = -1 := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    rcases ih with h | h
    · right
      rw [pow_succ, h]
      ring
    · left
      rw [pow_succ, h]
      ring

lemma j_le_half_Q_of_pell (n : ℕ) (hn : n ≥ 2) (h_pell_even : (Q n : ℤ)^2 - 2 * (P n : ℤ)^2 = 1)
    (j S : ℕ) (h_pell_j : (S : ℤ)^2 - 2 * (j : ℤ)^2 = -1) (hj_lt : j < Q n) :
    2 * j ≤ Q n := by
  by_contra h_gt
  push_neg at h_gt
  have h_QP : (Q n : ℤ) < 2 * (P n : ℤ) := by
    have h_P_ge : (P n : ℤ) ≥ 2 := by
      have h := P_ge_two_of_ge_two n hn
      exact_mod_cast h
    have h_prod : (2 * (P n : ℤ) - (Q n : ℤ)) * (2 * (P n : ℤ) + (Q n : ℤ)) > 0 := by
      calc (2 * (P n : ℤ) - (Q n : ℤ)) * (2 * (P n : ℤ) + (Q n : ℤ))
        _ = 4 * (P n : ℤ)^2 - (Q n : ℤ)^2 := by ring
        _ = 2 * (P n : ℤ)^2 - 1 := by omega
        _ > 0 := by nlinarith
    have h_sum_pos : 2 * (P n : ℤ) + (Q n : ℤ) > 0 := by
      have hQ := Q_ge_one n
      omega
    have h_diff_pos : 2 * (P n : ℤ) - (Q n : ℤ) > 0 := by
      nlinarith [h_prod, h_sum_pos]
    omega
  have h_lower : (Q n : ℤ) - (P n : ℤ) < (j : ℤ) := by
    have h_2j : 2 * (j : ℤ) ≥ (Q n : ℤ) + 1 := by omega
    linarith
  have h_upper : (j : ℤ) < (Q n : ℤ) + (P n : ℤ) := by
    have h_P_ge : (P n : ℤ) ≥ 2 := by
      have h := P_ge_two_of_ge_two n hn
      exact_mod_cast h
    omega
  have h_quad : (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 + 1 < 0 := by
    have h_id : (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 + 1 = ((j : ℤ) - (Q n : ℤ))^2 - (P n : ℤ)^2 := by
      calc (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 + 1
        _ = (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (Q n : ℤ)^2 - ((Q n : ℤ)^2 - 2 * (P n : ℤ)^2 - 1) - (P n : ℤ)^2 := by ring
        _ = ((j : ℤ) - (Q n : ℤ))^2 - (P n : ℤ)^2 := by rw [h_pell_even]; ring
    rw [h_id]
    have h_bound1 : (j : ℤ) - (Q n : ℤ) < (P n : ℤ) := by omega
    have h_bound2 : (j : ℤ) - (Q n : ℤ) > - (P n : ℤ) := by omega
    have h_pos1 : (P n : ℤ) - ((j : ℤ) - (Q n : ℤ)) > 0 := by linarith
    have h_pos2 : (P n : ℤ) + ((j : ℤ) - (Q n : ℤ)) > 0 := by linarith
    have h_prod : ((P n : ℤ) - ((j : ℤ) - (Q n : ℤ))) * ((P n : ℤ) + ((j : ℤ) - (Q n : ℤ))) > 0 := mul_pos h_pos1 h_pos2
    have h_alg : ((P n : ℤ) - ((j : ℤ) - (Q n : ℤ))) * ((P n : ℤ) + ((j : ℤ) - (Q n : ℤ))) = (P n : ℤ)^2 - ((j : ℤ) - (Q n : ℤ))^2 := by ring
    rw [h_alg] at h_prod
    linarith
  have h_pell_j_Z : (S : ℤ)^2 = 2 * (j : ℤ)^2 - 1 := by omega
  have h_S_pos : (S : ℤ) ≥ 0 := by omega
  have h_P_pos : (P n : ℤ) ≥ 0 := by omega
  have h_ineq1 : ((Q n : ℤ) * (j : ℤ) - 1)^2 < (P n : ℤ)^2 * (S : ℤ)^2 := by
    have h_Q2 : (Q n : ℤ)^2 = 2 * (P n : ℤ)^2 + 1 := by omega
    have h_diff : (P n : ℤ)^2 * (S : ℤ)^2 - ((Q n : ℤ) * (j : ℤ) - 1)^2 = - ((j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 + 1) := by
      calc (P n : ℤ)^2 * (S : ℤ)^2 - ((Q n : ℤ) * (j : ℤ) - 1)^2
        _ = (P n : ℤ)^2 * (2 * (j : ℤ)^2 - 1) - ((Q n : ℤ) * (j : ℤ) - 1)^2 := by rw [h_pell_j_Z]
        _ = 2 * (P n : ℤ)^2 * (j : ℤ)^2 - (P n : ℤ)^2 - ((Q n : ℤ)^2 * (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) * 1 + 1) := by ring
        _ = 2 * (P n : ℤ)^2 * (j : ℤ)^2 - (P n : ℤ)^2 - ((2 * (P n : ℤ)^2 + 1) * (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) * 1 + 1) := by rw [h_Q2]
        _ = - ((j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 + 1) := by ring
    linarith [h_quad, h_diff]
  have h_ineq2 : ((Q n : ℤ) * (j : ℤ) + 1)^2 > (P n : ℤ)^2 * (S : ℤ)^2 := by
    have h_Q2 : (Q n : ℤ)^2 = 2 * (P n : ℤ)^2 + 1 := by omega
    have h_diff : ((Q n : ℤ) * (j : ℤ) + 1)^2 - (P n : ℤ)^2 * (S : ℤ)^2 = (j : ℤ)^2 + 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 + 1 := by
      calc ((Q n : ℤ) * (j : ℤ) + 1)^2 - (P n : ℤ)^2 * (S : ℤ)^2
        _ = ((Q n : ℤ) * (j : ℤ) + 1)^2 - (P n : ℤ)^2 * (2 * (j : ℤ)^2 - 1) := by rw [h_pell_j_Z]
        _ = ((Q n : ℤ)^2 * (j : ℤ)^2 + 2 * (Q n : ℤ) * (j : ℤ) * 1 + 1) - 2 * (P n : ℤ)^2 * (j : ℤ)^2 + (P n : ℤ)^2 := by ring
        _ = ((2 * (P n : ℤ)^2 + 1) * (j : ℤ)^2 + 2 * (Q n : ℤ) * (j : ℤ) * 1 + 1) - 2 * (P n : ℤ)^2 * (j : ℤ)^2 + (P n : ℤ)^2 := by rw [h_Q2]
        _ = (j : ℤ)^2 + 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 + 1 := by ring
    have h_pos : (j : ℤ)^2 + 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 + 1 > 0 := by
      have hj : (j : ℤ) > 0 := by omega
      have hQ : (Q n : ℤ) > 0 := by omega
      have hP : (P n : ℤ) > 0 := by omega
      nlinarith
    linarith [h_diff, h_pos]
  have h_PS_pos : (P n : ℤ) * (S : ℤ) ≥ 0 := mul_nonneg h_P_pos h_S_pos
  have h_A_lt_B : (Q n : ℤ) * (j : ℤ) - 1 < (P n : ℤ) * (S : ℤ) := by
    by_contra! h_le
    have h_sq : ((Q n : ℤ) * (j : ℤ) - 1)^2 ≥ ((P n : ℤ) * (S : ℤ))^2 := by
      have h1 : (Q n : ℤ) * (j : ℤ) - 1 ≥ 0 := by
        have hj : (j : ℤ) ≥ 1 := by omega
        have hQ : (Q n : ℤ) ≥ 1 := by
          have h := Q_ge_one n
          exact_mod_cast h
        nlinarith
      nlinarith
    linarith
  have h_B_lt_C : (P n : ℤ) * (S : ℤ) < (Q n : ℤ) * (j : ℤ) + 1 := by
    by_contra! h_le
    have h_sq : ((P n : ℤ) * (S : ℤ))^2 ≥ ((Q n : ℤ) * (j : ℤ) + 1)^2 := by
      have h1 : (Q n : ℤ) * (j : ℤ) + 1 ≥ 0 := by
        have hj : (j : ℤ) ≥ 1 := by omega
        have hQ : (Q n : ℤ) ≥ 1 := by
          have h := Q_ge_one n
          exact_mod_cast h
        nlinarith
      nlinarith
    linarith
  have h_eq : (Q n : ℤ) * (j : ℤ) = (P n : ℤ) * (S : ℤ) := by omega
  have h_sq_eq : (Q n : ℤ)^2 * (j : ℤ)^2 = (P n : ℤ)^2 * (S : ℤ)^2 := by
    calc (Q n : ℤ)^2 * (j : ℤ)^2 = ((Q n : ℤ) * (j : ℤ))^2 := by ring
    _ = ((P n : ℤ) * (S : ℤ))^2 := by rw [h_eq]
    _ = (P n : ℤ)^2 * (S : ℤ)^2 := by ring
  have h_contra : (j : ℤ)^2 = - (P n : ℤ)^2 := by
    have h_subst : (P n : ℤ)^2 * (S : ℤ)^2 = (P n : ℤ)^2 * (2 * (j : ℤ)^2 - 1) := by rw [h_pell_j_Z]
    have h_expand : (Q n : ℤ)^2 * (j : ℤ)^2 = (2 * (P n : ℤ)^2 + 1) * (j : ℤ)^2 := by
      have h_Q2 : (Q n : ℤ)^2 = 2 * (P n : ℤ)^2 + 1 := by omega
      rw [h_Q2]
    rw [h_subst, h_expand] at h_sq_eq
    ring_nf at h_sq_eq
    omega
  have h_j_sq_pos : (j : ℤ)^2 > 0 := by
    have hj0 : (j : ℤ) ≥ 1 := by omega
    nlinarith
  have hPn_sq_neg : - (P n : ℤ)^2 < 0 := by
    have hP : (P n : ℤ) ≥ 2 := by
      have h := P_ge_two_of_ge_two n hn
      exact_mod_cast h
    nlinarith
  linarith

lemma j_le_half_Q_of_pell_odd (n : ℕ) (hn : n ≥ 3) (h_pell_odd : (Q n : ℤ)^2 - 2 * (P n : ℤ)^2 = -1)
    (j S : ℕ) (h_pell_j : (S + 1 : ℤ)^2 - 2 * (j : ℤ)^2 = 1) (hj_lt : j < Q n) :
    2 * j ≤ Q n := by
  by_contra h_gt
  push_neg at h_gt
  have h_QP : (Q n : ℤ) < 2 * (P n : ℤ) := by
    have h_P_ge : (P n : ℤ) ≥ 1 := by
      rcases n with _ | k
      · omega
      · have h := P_ge_one k
        exact_mod_cast h
    have h_prod : (2 * (P n : ℤ) - (Q n : ℤ)) * (2 * (P n : ℤ) + (Q n : ℤ)) > 0 := by
      calc (2 * (P n : ℤ) - (Q n : ℤ)) * (2 * (P n : ℤ) + (Q n : ℤ))
        _ = 4 * (P n : ℤ)^2 - (Q n : ℤ)^2 := by ring
        _ = 2 * (P n : ℤ)^2 + 1 := by omega
        _ > 0 := by nlinarith
    have h_sum_pos : 2 * (P n : ℤ) + (Q n : ℤ) > 0 := by
      have hQ := Q_ge_one n
      omega
    have h_diff_pos : 2 * (P n : ℤ) - (Q n : ℤ) > 0 := by
      nlinarith [h_prod, h_sum_pos]
    omega
  have h_lower : (Q n : ℤ) - (P n : ℤ) < (j : ℤ) := by
    have h_2j : 2 * (j : ℤ) ≥ (Q n : ℤ) + 1 := by omega
    linarith
  have h_upper : (j : ℤ) < (Q n : ℤ) + (P n : ℤ) := by
    have h_P_ge : (P n : ℤ) ≥ 2 := by
      have h := P_ge_two_of_ge_two n (by omega)
      exact_mod_cast h
    omega
  have h_quad : (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 - 1 < 0 := by
    have h_id : (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 - 1 = ((j : ℤ) - (Q n : ℤ))^2 - (P n : ℤ)^2 := by
      calc (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 - 1
        _ = (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (Q n : ℤ)^2 - ((Q n : ℤ)^2 - 2 * (P n : ℤ)^2 + 1) - (P n : ℤ)^2 := by ring
        _ = ((j : ℤ) - (Q n : ℤ))^2 - (P n : ℤ)^2 := by rw [h_pell_odd]; ring
    rw [h_id]
    have h_bound1 : (j : ℤ) - (Q n : ℤ) < (P n : ℤ) := by omega
    have h_bound2 : (j : ℤ) - (Q n : ℤ) > - (P n : ℤ) := by omega
    have h_pos1 : (P n : ℤ) - ((j : ℤ) - (Q n : ℤ)) > 0 := by linarith
    have h_pos2 : (P n : ℤ) + ((j : ℤ) - (Q n : ℤ)) > 0 := by linarith
    have h_prod : ((P n : ℤ) - ((j : ℤ) - (Q n : ℤ))) * ((P n : ℤ) + ((j : ℤ) - (Q n : ℤ))) > 0 := mul_pos h_pos1 h_pos2
    have h_alg : ((P n : ℤ) - ((j : ℤ) - (Q n : ℤ))) * ((P n : ℤ) + ((j : ℤ) - (Q n : ℤ))) = (P n : ℤ)^2 - ((j : ℤ) - (Q n : ℤ))^2 := by ring
    rw [h_alg] at h_prod
    linarith
  have h_pell_j_Z : (S + 1 : ℤ)^2 = 2 * (j : ℤ)^2 + 1 := by omega
  have h_S1_pos : (S + 1 : ℤ) ≥ 0 := by omega
  have h_P_pos : (P n : ℤ) ≥ 0 := by omega
  have h_ineq1 : ((Q n : ℤ) * (j : ℤ) - 1)^2 < (P n : ℤ)^2 * (S + 1 : ℤ)^2 := by
    have h_Q2 : (Q n : ℤ)^2 = 2 * (P n : ℤ)^2 - 1 := by omega
    have h_diff : (P n : ℤ)^2 * (S + 1 : ℤ)^2 - ((Q n : ℤ) * (j : ℤ) - 1)^2 = (j : ℤ)^2 + 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 - 1 := by
      calc (P n : ℤ)^2 * (S + 1 : ℤ)^2 - ((Q n : ℤ) * (j : ℤ) - 1)^2
        _ = (P n : ℤ)^2 * (2 * (j : ℤ)^2 + 1) - ((Q n : ℤ) * (j : ℤ) - 1)^2 := by rw [h_pell_j_Z]
        _ = 2 * (P n : ℤ)^2 * (j : ℤ)^2 + (P n : ℤ)^2 - ((Q n : ℤ)^2 * (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) * 1 + 1) := by ring
        _ = 2 * (P n : ℤ)^2 * (j : ℤ)^2 + (P n : ℤ)^2 - ((2 * (P n : ℤ)^2 - 1) * (j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) * 1 + 1) := by rw [h_Q2]
        _ = (j : ℤ)^2 + 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 - 1 := by ring
    have h_pos : (j : ℤ)^2 + 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 - 1 > 0 := by
      have hj : (j : ℤ) > 0 := by omega
      have hQ : (Q n : ℤ) > 0 := by omega
      have hP : (P n : ℤ) > 0 := by omega
      nlinarith
    linarith [h_diff, h_pos]
  have h_ineq2 : ((Q n : ℤ) * (j : ℤ) + 1)^2 > (P n : ℤ)^2 * (S + 1 : ℤ)^2 := by
    have h_Q2 : (Q n : ℤ)^2 = 2 * (P n : ℤ)^2 - 1 := by omega
    have h_diff : ((Q n : ℤ) * (j : ℤ) + 1)^2 - (P n : ℤ)^2 * (S + 1 : ℤ)^2 = - ((j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 - 1) := by
      calc ((Q n : ℤ) * (j : ℤ) + 1)^2 - (P n : ℤ)^2 * (S + 1 : ℤ)^2
        _ = ((Q n : ℤ) * (j : ℤ) + 1)^2 - (P n : ℤ)^2 * (2 * (j : ℤ)^2 + 1) := by rw [h_pell_j_Z]
        _ = ((Q n : ℤ)^2 * (j : ℤ)^2 + 2 * (Q n : ℤ) * (j : ℤ) * 1 + 1) - 2 * (P n : ℤ)^2 * (j : ℤ)^2 - (P n : ℤ)^2 := by ring
        _ = ((2 * (P n : ℤ)^2 - 1) * (j : ℤ)^2 + 2 * (Q n : ℤ) * (j : ℤ) * 1 + 1) - 2 * (P n : ℤ)^2 * (j : ℤ)^2 - (P n : ℤ)^2 := by rw [h_Q2]
        _ = - ((j : ℤ)^2 - 2 * (Q n : ℤ) * (j : ℤ) + (P n : ℤ)^2 - 1) := by ring
    linarith [h_diff, h_quad]
  have h_PS1_pos : (P n : ℤ) * (S + 1 : ℤ) ≥ 0 := mul_nonneg h_P_pos h_S1_pos
  have h_A_lt_B : (Q n : ℤ) * (j : ℤ) - 1 < (P n : ℤ) * (S + 1 : ℤ) := by
    by_contra! h_le
    have h_sq : ((Q n : ℤ) * (j : ℤ) - 1)^2 ≥ ((P n : ℤ) * (S + 1 : ℤ))^2 := by
      have h1 : (Q n : ℤ) * (j : ℤ) - 1 ≥ 0 := by
        have hj : (j : ℤ) ≥ 1 := by omega
        have hQ : (Q n : ℤ) ≥ 1 := by
          have h := Q_ge_one n
          exact_mod_cast h
        nlinarith
      nlinarith
    linarith
  have h_B_lt_C : (P n : ℤ) * (S + 1 : ℤ) < (Q n : ℤ) * (j : ℤ) + 1 := by
    by_contra! h_le
    have h_sq : ((P n : ℤ) * (S + 1 : ℤ))^2 ≥ ((Q n : ℤ) * (j : ℤ) + 1)^2 := by
      have h1 : (Q n : ℤ) * (j : ℤ) + 1 ≥ 0 := by
        have hj : (j : ℤ) ≥ 1 := by omega
        have hQ : (Q n : ℤ) ≥ 1 := by
          have h := Q_ge_one n
          exact_mod_cast h
        nlinarith
      nlinarith
    linarith
  have h_eq : (Q n : ℤ) * (j : ℤ) = (P n : ℤ) * (S + 1 : ℤ) := by omega
  have h_sq_eq : (Q n : ℤ)^2 * (j : ℤ)^2 = (P n : ℤ)^2 * (S + 1 : ℤ)^2 := by
    calc (Q n : ℤ)^2 * (j : ℤ)^2 = ((Q n : ℤ) * (j : ℤ))^2 := by ring
    _ = ((P n : ℤ) * (S + 1 : ℤ))^2 := by rw [h_eq]
    _ = (P n : ℤ)^2 * (S + 1 : ℤ)^2 := by ring
  have h_contra : (j : ℤ)^2 = - (P n : ℤ)^2 := by
    have h_subst : (P n : ℤ)^2 * (S + 1 : ℤ)^2 = (P n : ℤ)^2 * (2 * (j : ℤ)^2 + 1) := by rw [h_pell_j_Z]
    have h_expand : (Q n : ℤ)^2 * (j : ℤ)^2 = (2 * (P n : ℤ)^2 - 1) * (j : ℤ)^2 := by
      have h_Q2 : (Q n : ℤ)^2 = 2 * (P n : ℤ)^2 - 1 := by omega
      rw [h_Q2]
    rw [h_subst, h_expand] at h_sq_eq
    ring_nf at h_sq_eq
    omega
  have h_j_sq_pos : (j : ℤ)^2 > 0 := by
    have hj0 : (j : ℤ) ≥ 1 := by omega
    nlinarith
  have hPn_sq_neg : - (P n : ℤ)^2 < 0 := by
    have hP : (P n : ℤ) ≥ 2 := by
      have h := P_ge_two_of_ge_two n (by omega)
      exact_mod_cast h
    nlinarith
  linarith

unseal Nat.sqrt.iter in
lemma S_P_add_j_eq_Q_add_S (n : ℕ) (hn : n ≥ 1) (j : ℕ) (hj_pos : j ≥ 1) (hj : j ≤ Q n) :
    Nat.sqrt (2 * (P n + j) ^ 2) = Q n + Nat.sqrt (2 * j ^ 2) := by
  by_cases hj_eq : j = Q n
  · subst hj_eq
    rw [← P_succ]
    by_cases hn_even : n % 2 = 0
    · have hn_ge_2 : n ≥ 2 := by omega
      have h_pell : (Q n : ℤ)^2 - 2 * (P n : ℤ)^2 = 1 := by
        have hp := Pell_identity n
        rw [neg_one_pow_even n hn_even] at hp
        exact hp
      have h_pell_succ : (Q (n+1) : ℤ)^2 - 2 * (P (n+1) : ℤ)^2 = -1 := by
        have hp := Pell_identity (n+1)
        have hn_odd : (n+1) % 2 = 1 := by omega
        rw [neg_one_pow_odd (n+1) hn_odd] at hp
        exact hp
      rw [sqrt_two_P_sq_odd (n+1) h_pell_succ]
      rw [sqrt_two_Q_sq_even n hn_ge_2 h_pell]
      rw [Q_succ]
      have hP : P n ≥ 1 := by
        rcases n with _ | k
        · contradiction
        · exact P_ge_one k
      omega
    · have hn_odd : n % 2 = 1 := by omega
      have h_pell : (Q n : ℤ)^2 - 2 * (P n : ℤ)^2 = -1 := by
        have hp := Pell_identity n
        rw [neg_one_pow_odd n hn_odd] at hp
        exact hp
      have h_pell_succ : (Q (n+1) : ℤ)^2 - 2 * (P (n+1) : ℤ)^2 = 1 := by
        have hp := Pell_identity (n+1)
        have hn_even_succ : (n+1) % 2 = 0 := by omega
        rw [neg_one_pow_even (n+1) hn_even_succ] at hp
        exact hp
      rw [sqrt_two_P_sq_even (n+1) (by omega) h_pell_succ]
      rw [sqrt_two_Q_sq_odd n h_pell]
      rw [Q_succ]
      have hP : P n ≥ 1 := by
        rcases n with _ | k
        · contradiction
        · exact P_ge_one k
      omega
  · have hj_lt : j ≤ Q n - 1 := by omega
    have h_sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h_sqrt2_pos : Real.sqrt 2 > 0 := by
      have h2 : (0 : ℝ) < 2 := by norm_num
      exact Real.sqrt_pos.mpr h2
    have h_sqrt2_lt : Real.sqrt 2 < 1.5 := by
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
    have h_sqrt2_gt : 1.4 < Real.sqrt 2 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have h_Q_pos : (Q n : ℝ) > 0 := by
      have h_q_nat := Q_ge_one n
      exact_mod_cast h_q_nat
    have h_P_pos : (P n : ℝ) > 0 := by
      have hP : P n ≥ 1 := by
        rcases n with _ | k
        · contradiction
        · exact P_ge_one k
      exact_mod_cast hP
    have h_sum_pos : (Q n : ℝ) + Real.sqrt 2 * (P n : ℝ) > 0 := by
      have hP : (P n : ℝ) ≥ 0 := by positivity
      have h_mul : Real.sqrt 2 * (P n : ℝ) ≥ 0 := mul_nonneg (Real.sqrt_nonneg 2) hP
      linarith
    have h_sum_pos2 : Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ) > 0 := by
      have hj_pos_real : (j : ℝ) > 0 := by exact_mod_cast hj_pos
      have h_mul_pos : Real.sqrt 2 * (j : ℝ) > 0 := mul_pos h_sqrt2_pos hj_pos_real
      have h_S_nonneg : (Nat.sqrt (2 * j ^ 2) : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le _
      linarith
    have h_S_le := Nat.sqrt_le (2 * j ^ 2)
    have h_S_lt := Nat.lt_succ_sqrt (2 * j ^ 2)
    have h_S_le_real : (Nat.sqrt (2 * j ^ 2) : ℝ) ^ 2 ≤ 2 * (j : ℝ) ^ 2 := by
      have h2 : ((Nat.sqrt (2 * j ^ 2) * Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) ≤ ((2 * j ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast h_S_le
      push_cast at h2
      ring_nf at h2 ⊢
      exact h2
    have h_S_lt_real : 2 * (j : ℝ) ^ 2 < ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1) ^ 2 := by
      have h2 : ((2 * j ^ 2 : ℕ) : ℝ) < (((Nat.sqrt (2 * j ^ 2) + 1) * (Nat.sqrt (2 * j ^ 2) + 1) : ℕ) : ℝ) := by
        exact_mod_cast h_S_lt
      push_cast at h2
      ring_nf at h2 ⊢
      exact h2
    have h_pos_S : 0 ≤ (Nat.sqrt (2 * j ^ 2) : ℝ) := by exact_mod_cast Nat.zero_le _
    have h_pos_j : 0 ≤ (j : ℝ) * Real.sqrt 2 := mul_nonneg (by exact_mod_cast Nat.zero_le j) (Real.sqrt_nonneg 2)
    have h_pos_S1 : 0 ≤ (Nat.sqrt (2 * j ^ 2) : ℝ) + 1 := by linarith
    have h_sq_le_j : (Nat.sqrt (2 * j ^ 2) : ℝ) ≤ (j : ℝ) * Real.sqrt 2 := by
      rw [← sq_le_sq₀ h_pos_S h_pos_j]
      rw [mul_pow, h_sqrt2_sq]
      ring_nf at h_S_le_real ⊢
      exact h_S_le_real
    have h_sq_lt_j : (j : ℝ) * Real.sqrt 2 < (Nat.sqrt (2 * j ^ 2) : ℝ) + 1 := by
      rw [← sq_lt_sq₀ h_pos_j h_pos_S1]
      rw [mul_pow, h_sqrt2_sq]
      ring_nf at h_S_lt_real ⊢
      exact h_S_lt_real
    have h_pell_bound2 : (Q n : ℝ) ≤ Real.sqrt 2 * (P n : ℝ) + 1 := by
      rcases neg_one_pow_cases n with hn_even_real | hn_odd_real
      · have h_sq : (Q n : ℝ) ^ 2 ≤ (Real.sqrt 2 * (P n : ℝ) + 1) ^ 2 := by
          rw [add_sq]
          rw [mul_pow, h_sqrt2_sq]
          have h_pos : 2 * Real.sqrt 2 * (P n : ℝ) ≥ 0 := mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) (by exact_mod_cast Nat.zero_le (P n))
          linarith [Pell_identity_real n]
        have h1 : 0 ≤ (Q n : ℝ) := by exact_mod_cast Nat.zero_le (Q n)
        have h2 : 0 ≤ Real.sqrt 2 * (P n : ℝ) + 1 := by linarith [mul_nonneg (Real.sqrt_nonneg 2) (by exact_mod_cast Nat.zero_le (P n) : (P n : ℝ) ≥ 0)]
        exact (sq_le_sq₀ h1 h2).mp h_sq
      · have h_sq : (Q n : ℝ) ^ 2 ≤ (Real.sqrt 2 * (P n : ℝ)) ^ 2 := by
          rw [mul_pow, h_sqrt2_sq]
          linarith [Pell_identity_real n]
        have h1 : 0 ≤ (Q n : ℝ) := by exact_mod_cast Nat.zero_le (Q n)
        have h2 : 0 ≤ Real.sqrt 2 * (P n : ℝ) := mul_nonneg (Real.sqrt_nonneg 2) (by exact_mod_cast Nat.zero_le (P n))
        have h_le : (Q n : ℝ) ≤ Real.sqrt 2 * (P n : ℝ) := (sq_le_sq₀ h1 h2).mp h_sq
        linarith
    have h_R_pos : (2 * j ^ 2 - (Nat.sqrt (2 * j ^ 2)) ^ 2 : ℤ) ≥ 1 := by
      have h1 : (Nat.sqrt (2 * j ^ 2)) ^ 2 ≤ 2 * j ^ 2 := by
        rw [sq]
        exact Nat.sqrt_le (2 * j ^ 2)
      have h2 : 2 * j ^ 2 ≠ (Nat.sqrt (2 * j ^ 2)) ^ 2 := by
        intro h
        exact sqrt_two_irrational j (Nat.sqrt (2 * j ^ 2)) hj_pos h
      have h3 : 2 * j ^ 2 - (Nat.sqrt (2 * j ^ 2)) ^ 2 ≥ 1 := by omega
      exact_mod_cast h3
    have h_Q_plus_S : (Q n : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ) ≤ Real.sqrt 2 * ((P n : ℝ) + (j : ℝ)) ∧
        Real.sqrt 2 * ((P n : ℝ) + (j : ℝ)) < (Q n : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ) + 1 := by
      by_cases hn_even : n % 2 = 0
      · have h_pell_even : (Q n : ℤ)^2 - 2 * (P n : ℤ)^2 = 1 := by
          have hp := Pell_identity n
          rw [neg_one_pow_even n hn_even] at hp
          exact hp
        have hc : (2 * j ^ 2 - (Nat.sqrt (2 * j ^ 2)) ^ 2 : ℤ) = 1 ∨ (2 * j ^ 2 - (Nat.sqrt (2 * j ^ 2)) ^ 2 : ℤ) ≥ 2 := by omega
        rcases hc with h_R_eq | h_R_ge_2
        · have hn_ge_2 : n ≥ 2 := by omega
          have h_pell_j : (Nat.sqrt (2 * j ^ 2) : ℤ)^2 - 2 * (j : ℤ)^2 = -1 := by omega
          have h_le_half : 2 * j ≤ Q n := j_le_half_Q_of_pell n hn_ge_2 h_pell_even j (Nat.sqrt (2 * j ^ 2)) h_pell_j (by omega)
          constructor
          · have h_j_real : (j : ℝ) ≤ (Q n : ℝ) / 2 := by
              have h_cast : (2 * j : ℝ) ≤ (Q n : ℝ) := by exact_mod_cast h_le_half
              push_cast at h_cast
              linarith
            have h_ineq : Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ) ≤ (Q n : ℝ) + Real.sqrt 2 * (P n : ℝ) := by
              have h_LHS : Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ) ≤ 2 * Real.sqrt 2 * (j : ℝ) := by linarith [h_sq_le_j]
              have h_j_bound : 2 * Real.sqrt 2 * (j : ℝ) ≤ Real.sqrt 2 * (Q n : ℝ) := by
                have h_pos : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
                have h_temp : 2 * (j : ℝ) ≤ (Q n : ℝ) := by linarith [h_j_real]
                have h_mul := mul_le_mul_of_nonneg_left h_temp h_pos
                calc 2 * Real.sqrt 2 * (j : ℝ) = Real.sqrt 2 * (2 * (j : ℝ)) := by ring
                _ ≤ Real.sqrt 2 * (Q n : ℝ) := h_mul
              have h_RHS : Real.sqrt 2 * (Q n : ℝ) ≤ (Q n : ℝ) + Real.sqrt 2 * (P n : ℝ) := by
                have h_Q : (Q n : ℝ) ≤ Real.sqrt 2 * (P n : ℝ) + 1 := h_pell_bound2
                have h_P_ge : (P n : ℝ) ≥ 1 := by
                  have h_nat := P_ge_two_of_ge_two n hn_ge_2
                  have h_ge1 : P n ≥ 1 := by omega
                  exact_mod_cast h_ge1
                have h_temp : Real.sqrt 2 * (Q n : ℝ) ≤ Real.sqrt 2 * (Real.sqrt 2 * (P n : ℝ) + 1) := by
                  have h_pos : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
                  exact mul_le_mul_of_nonneg_left h_Q h_pos
                have h_temp2 : Real.sqrt 2 * (Real.sqrt 2 * (P n : ℝ) + 1) = (Real.sqrt 2)^2 * (P n : ℝ) + Real.sqrt 2 := by ring
                rw [h_temp2, h_sqrt2_sq] at h_temp
                have h_Q_bound : (Q n : ℝ) ≤ 1.5 * (P n : ℝ) + 1 := by
                  have h_temp_prod : Real.sqrt 2 * (P n : ℝ) < 1.5 * (P n : ℝ) := mul_lt_mul_of_pos_right h_sqrt2_lt h_P_pos
                  linarith [h_Q, h_temp_prod]
                nlinarith [h_temp, h_sqrt2_lt, h_sqrt2_gt, h_P_ge, h_Q_bound]
              linarith [h_LHS, h_j_bound, h_RHS]
            have h_diff_eq : (Q n : ℝ) - Real.sqrt 2 * (P n : ℝ) = 1 / ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) := by
              have h_factor : ((Q n : ℝ) - Real.sqrt 2 * (P n : ℝ)) * ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) = 1 := by
                calc ((Q n : ℝ) - Real.sqrt 2 * (P n : ℝ)) * ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ))
                  _ = (Q n : ℝ) ^ 2 - (Real.sqrt 2 * (P n : ℝ)) ^ 2 := by ring
                  _ = (Q n : ℝ) ^ 2 - (Real.sqrt 2) ^ 2 * (P n : ℝ) ^ 2 := by ring
                  _ = (Q n : ℝ) ^ 2 - 2 * (P n : ℝ) ^ 2 := by rw [h_sqrt2_sq]
                  _ = 1 := by exact_mod_cast h_pell_even
              exact eq_div_of_mul_eq (by linarith) h_factor
            have h_S_bound : Real.sqrt 2 * (j : ℝ) - (Nat.sqrt (2 * j ^ 2) : ℝ) ≥ 1 / (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) := by
              have h_prod : (Real.sqrt 2 * (j : ℝ) - (Nat.sqrt (2 * j ^ 2) : ℝ)) * (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) ≥ 1 := by
                calc (Real.sqrt 2 * (j : ℝ) - (Nat.sqrt (2 * j ^ 2) : ℝ)) * (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ))
                  _ = (Real.sqrt 2 * (j : ℝ)) ^ 2 - (Nat.sqrt (2 * j ^ 2) : ℝ) ^ 2 := by ring
                  _ = (Real.sqrt 2) ^ 2 * (j : ℝ) ^ 2 - (Nat.sqrt (2 * j ^ 2) : ℝ) ^ 2 := by ring
                  _ = 2 * (j : ℝ) ^ 2 - (Nat.sqrt (2 * j ^ 2) : ℝ) ^ 2 := by rw [h_sqrt2_sq]
                  _ ≥ 1 := by exact_mod_cast h_R_pos
              exact div_le_iff₀ h_sum_pos2 |>.mpr h_prod
            have h_recip : 1 / (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) ≥ 1 / ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) := by
              rw [ge_iff_le]
              exact (one_div_le_one_div h_sum_pos h_sum_pos2).mpr h_ineq
            linarith
          · have h_pell_neg : Real.sqrt 2 * (P n : ℝ) - (Q n : ℝ) < 0 := by
              have h_pow_even : (-1 : ℝ)^n = 1 := by
                have h_int := neg_one_pow_even n hn_even
                have h_cast : (((-1 : ℤ)^n : ℤ) : ℝ) = (1 : ℝ) := by exact_mod_cast h_int
                push_cast at h_cast
                exact h_cast
              have h_pell_real := Pell_identity_real n
              rw [h_pow_even] at h_pell_real
              have h_Q_ge : (Q n : ℝ) > Real.sqrt 2 * (P n : ℝ) := by
                have h_sq : (Q n : ℝ) ^ 2 > (Real.sqrt 2 * (P n : ℝ)) ^ 2 := by
                  rw [mul_pow, h_sqrt2_sq]
                  linarith
                have h1 : 0 ≤ (Q n : ℝ) := by exact_mod_cast Nat.zero_le (Q n)
                have h2 : 0 ≤ Real.sqrt 2 * (P n : ℝ) := mul_nonneg (Real.sqrt_nonneg 2) (by exact_mod_cast Nat.zero_le (P n))
                exact (sq_lt_sq₀ h2 h1).mp h_sq
              linarith
            linarith
        · constructor
          · have h_diff_eq : (Q n : ℝ) - Real.sqrt 2 * (P n : ℝ) = 1 / ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) := by
              have h_factor : ((Q n : ℝ) - Real.sqrt 2 * (P n : ℝ)) * ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) = 1 := by
                calc ((Q n : ℝ) - Real.sqrt 2 * (P n : ℝ)) * ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ))
                  _ = (Q n : ℝ) ^ 2 - (Real.sqrt 2 * (P n : ℝ)) ^ 2 := by ring
                  _ = (Q n : ℝ) ^ 2 - (Real.sqrt 2) ^ 2 * (P n : ℝ) ^ 2 := by ring
                  _ = (Q n : ℝ) ^ 2 - 2 * (P n : ℝ) ^ 2 := by rw [h_sqrt2_sq]
                  _ = 1 := by exact_mod_cast h_pell_even
              exact eq_div_of_mul_eq (by linarith) h_factor
            have h_exact : Real.sqrt 2 * (j : ℝ) - (Nat.sqrt (2 * j ^ 2) : ℝ) = (2 * j ^ 2 - (Nat.sqrt (2 * j ^ 2)) ^ 2 : ℤ) / (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) := by
              have h_prod : (Real.sqrt 2 * (j : ℝ) - (Nat.sqrt (2 * j ^ 2) : ℝ)) * (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) = (2 * j ^ 2 - (Nat.sqrt (2 * j ^ 2)) ^ 2 : ℤ) := by
                have h_alg : (Real.sqrt 2 * (j : ℝ) - (Nat.sqrt (2 * j ^ 2) : ℝ)) * (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) = (Real.sqrt 2)^2 * (j : ℝ)^2 - (Nat.sqrt (2 * j ^ 2) : ℝ)^2 := by ring
                rw [h_alg, h_sqrt2_sq]
                push_cast
                ring
              exact eq_div_of_mul_eq (by linarith) h_prod
            have h_S_bound : Real.sqrt 2 * (j : ℝ) - (Nat.sqrt (2 * j ^ 2) : ℝ) ≥ 2 / (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) := by
              rw [h_exact]
              have h_R_real : 2 ≤ (((2 * j ^ 2 - (Nat.sqrt (2 * j ^ 2)) ^ 2 : ℤ) : ℝ)) := by exact_mod_cast h_R_ge_2
              exact div_le_div_of_nonneg_right h_R_real (by linarith)
            have h_j_bound : (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) / 2 ≤ (Q n : ℝ) + Real.sqrt 2 * (P n : ℝ) := by
              have h_LHS : Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ) ≤ 2 * Real.sqrt 2 * (j : ℝ) := by linarith [h_sq_le_j]
              have h_j_lt : (j : ℝ) ≤ (Q n : ℝ) - 1 := by
                have h_cast : (j : ℝ) ≤ ((Q n - 1 : ℕ) : ℝ) := by exact_mod_cast hj_lt
                have h_sub : ((Q n - 1 : ℕ) : ℝ) = (Q n : ℝ) - 1 := by
                  rw [Nat.cast_sub (Q_ge_one n)]
                  push_cast
                  rfl
                linarith
              have h_j_bound2 : Real.sqrt 2 * (j : ℝ) ≤ Real.sqrt 2 * ((Q n : ℝ) - 1) := by
                have h_pos : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
                exact mul_le_mul_of_nonneg_left h_j_lt h_pos
              have hn_ge_2 : n ≥ 2 := by omega
              have h_RHS : Real.sqrt 2 * ((Q n : ℝ) - 1) < (Q n : ℝ) + Real.sqrt 2 * (P n : ℝ) := by
                have h_Q : (Q n : ℝ) ≤ Real.sqrt 2 * (P n : ℝ) + 1 := h_pell_bound2
                have h_P_ge : (P n : ℝ) ≥ 2 := by
                  have h_nat := P_ge_two_of_ge_two n hn_ge_2
                  exact_mod_cast h_nat
                have hP : (P n : ℝ) > 0 := by
                  have h_p_real : (P n : ℝ) ≥ 2 := by exact_mod_cast h_P_ge
                  linarith
                have h_ineq : Real.sqrt 2 * (Q n : ℝ) < 1.5 * (Q n : ℝ) := mul_lt_mul_of_pos_right h_sqrt2_lt h_Q_pos
                have h_P_bound : 1.4 * (P n : ℝ) < Real.sqrt 2 * (P n : ℝ) := mul_lt_mul_of_pos_right h_sqrt2_gt hP
                have h_Q_bound : (Q n : ℝ) ≤ 1.5 * (P n : ℝ) + 1 := by
                  have h_temp : Real.sqrt 2 * (P n : ℝ) < 1.5 * (P n : ℝ) := mul_lt_mul_of_pos_right h_sqrt2_lt hP
                  linarith [h_Q, h_temp]
                linarith [h_ineq, h_P_bound, h_Q_bound]
              linarith [h_LHS, h_j_bound2, h_RHS]
            have h_recip : 2 / (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) ≥ 1 / ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) := by
              rw [ge_iff_le]
              have h_eq : 2 / (Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) = 1 / ((Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) / 2) := by
                field_simp
              rw [h_eq]
              have h_half_pos : ((Real.sqrt 2 * (j : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ)) / 2) > 0 := by linarith
              exact (one_div_le_one_div h_sum_pos h_half_pos).mpr h_j_bound
            linarith
          · have h_pell_neg : Real.sqrt 2 * (P n : ℝ) - (Q n : ℝ) < 0 := by
              have h_pow_even : (-1 : ℝ)^n = 1 := by
                have h_int := neg_one_pow_even n hn_even
                have h_cast : ((((-1 : ℤ)^n : ℤ) : ℝ)) = (1 : ℝ) := by exact_mod_cast h_int
                push_cast at h_cast
                exact h_cast
              have h_pell_real := Pell_identity_real n
              rw [h_pow_even] at h_pell_real
              have h_Q_ge : (Q n : ℝ) > Real.sqrt 2 * (P n : ℝ) := by
                have h_sq : (Q n : ℝ) ^ 2 > (Real.sqrt 2 * (P n : ℝ)) ^ 2 := by
                  rw [mul_pow, h_sqrt2_sq]
                  linarith
                have h1 : 0 ≤ (Q n : ℝ) := by exact_mod_cast Nat.zero_le (Q n)
                have h2 : 0 ≤ Real.sqrt 2 * (P n : ℝ) := mul_nonneg (Real.sqrt_nonneg 2) (by exact_mod_cast Nat.zero_le (P n))
                exact (sq_lt_sq₀ h2 h1).mp h_sq
              linarith
            linarith
      · have h_pell_odd : (Q n : ℤ)^2 - 2 * (P n : ℤ)^2 = -1 := by
          have hp := Pell_identity n
          have hn_odd : n % 2 = 1 := by omega
          rw [neg_one_pow_odd n hn_odd] at hp
          exact hp
        have h_pow_odd : (-1 : ℝ)^n = -1 := by
          have h_int := neg_one_pow_odd n (by omega)
          have h_cast : (((-1 : ℤ)^n : ℤ) : ℝ) = (-1 : ℝ) := by exact_mod_cast h_int
          push_cast at h_cast
          exact h_cast
        have h_pell_real_odd : (Q n : ℝ)^2 - 2 * (P n : ℝ)^2 = -1 := by
          have h := Pell_identity_real n
          rw [h_pow_odd] at h
          exact h
        have h_R_pos2 : (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ) : ℤ)^2 - 2 * (j : ℤ) ^ 2 : ℤ) ≥ 1 := by
          have h1 : 2 * j ^ 2 < (Nat.sqrt (2 * j ^ 2) + 1) ^ 2 := by
            have h_t := Nat.lt_succ_sqrt (2 * j ^ 2)
            repeat rw [Nat.succ_eq_add_one] at h_t
            rw [sq, sq]
            rw [sq] at h_t
            exact h_t
          have h1_z : 2 * (j : ℤ) ^ 2 < ((Nat.sqrt (2 * j ^ 2) : ℤ) + 1) ^ 2 := by exact_mod_cast h1
          have h_cast_eq : (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ) : ℤ)) = (Nat.sqrt (2 * j ^ 2) : ℤ) + 1 := by push_cast; rfl
          rw [h_cast_eq]
          omega
        have hc : (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ) : ℤ)^2 - 2 * (j : ℤ)^2 : ℤ) = 1 ∨ (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ) : ℤ)^2 - 2 * (j : ℤ)^2 : ℤ) ≥ 2 := by omega
        rcases hc with h_R_eq | h_R_ge_2
        · have hn_neq_1 : n ≠ 1 := by
            intro hn1
            subst hn1
            have hj1 : j = 1 := by
              have hQ1 : Q 1 = 1 := rfl
              omega
            subst hj1
            have h_R_eq_eval : (((Nat.sqrt (2 * 1 ^ 2) + 1 : ℕ) : ℤ)^2 - 2 * 1 ^ 2 : ℤ) = 2 := by decide
            omega
          have hn_ge_3 : n ≥ 3 := by omega
          have h_pell_j : (Nat.sqrt (2 * j ^ 2) + 1 : ℤ)^2 - 2 * (j : ℤ)^2 = 1 := h_R_eq
          have h_le_half : 2 * j ≤ Q n := j_le_half_Q_of_pell_odd n hn_ge_3 h_pell_odd j (Nat.sqrt (2 * j ^ 2)) h_pell_j (by omega)
          constructor
          · have h_pell_pos : Real.sqrt 2 * (P n : ℝ) - (Q n : ℝ) > 0 := by
              have h_Q_ge : (Q n : ℝ) < Real.sqrt 2 * (P n : ℝ) := by
                have h_sq : (Q n : ℝ) ^ 2 < (Real.sqrt 2 * (P n : ℝ)) ^ 2 := by
                  rw [mul_pow, h_sqrt2_sq]
                  linarith [h_pell_real_odd]
                have h1 : 0 ≤ (Q n : ℝ) := by exact_mod_cast Nat.zero_le (Q n)
                have h2 : 0 ≤ Real.sqrt 2 * (P n : ℝ) := mul_nonneg (Real.sqrt_nonneg 2) (by exact_mod_cast Nat.zero_le (P n))
                exact (sq_lt_sq₀ h1 h2).mp h_sq
              linarith
            linarith [h_pell_pos, h_sq_le_j]
          · have h_j_lt2 : (j : ℝ) ≤ (Q n : ℝ) / 2 := by
              have h_cast : (2 * j : ℝ) ≤ (Q n : ℝ) := by exact_mod_cast h_le_half
              push_cast at h_cast
              linarith
            have h_ineq4 : (Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ) < (Q n : ℝ) + Real.sqrt 2 * (P n : ℝ) := by
              have h_LHS : (Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ) ≤ 2 * Real.sqrt 2 * (j : ℝ) + 1 := by linarith [h_sq_lt_j]
              have h_j_bound : 2 * Real.sqrt 2 * (j : ℝ) + 1 ≤ Real.sqrt 2 * (Q n : ℝ) + 1 := by
                have h_pos : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
                have h_temp : 2 * (j : ℝ) ≤ (Q n : ℝ) := by linarith [h_j_lt2]
                have h_mul := mul_le_mul_of_nonneg_left h_temp h_pos
                calc 2 * Real.sqrt 2 * (j : ℝ) + 1 = Real.sqrt 2 * (2 * (j : ℝ)) + 1 := by ring
                _ ≤ Real.sqrt 2 * (Q n : ℝ) + 1 := by linarith [h_mul]
              have h_RHS : Real.sqrt 2 * (Q n : ℝ) + 1 < (Q n : ℝ) + Real.sqrt 2 * (P n : ℝ) := by
                have h_Q_lt : (Q n : ℝ) ≤ Real.sqrt 2 * (P n : ℝ) := by
                  have h_sq : (Q n : ℝ) ^ 2 ≤ (Real.sqrt 2 * (P n : ℝ)) ^ 2 := by
                    rw [mul_pow, h_sqrt2_sq]
                    linarith [h_pell_real_odd]
                  have h1 : 0 ≤ (Q n : ℝ) := by exact_mod_cast Nat.zero_le (Q n)
                  have h2 : 0 ≤ Real.sqrt 2 * (P n : ℝ) := mul_nonneg (Real.sqrt_nonneg 2) (by exact_mod_cast Nat.zero_le (P n))
                  exact (sq_le_sq₀ h1 h2).mp h_sq
                have h_P_ge : (P n : ℝ) ≥ 5 := by
                  have h_nat : P n ≥ 5 := by
                    rcases n with _ | _ | _ | k
                    · omega
                    · omega
                    · omega
                    · rw [P_succ (k + 2), P_succ (k + 1), Q_succ (k + 1)]
                      have h1 := P_ge_one k
                      have h2 := Q_ge_one (k + 1)
                      omega
                  exact_mod_cast h_nat
                have h_ineq : Real.sqrt 2 * (Q n : ℝ) < 1.5 * (Q n : ℝ) := mul_lt_mul_of_pos_right h_sqrt2_lt h_Q_pos
                have h_ineq2 : Real.sqrt 2 * (Q n : ℝ) + 1 < 1.5 * (Q n : ℝ) + 1 := by linarith
                have h_temp3 : 1.5 * (Q n : ℝ) + 1 ≤ (Q n : ℝ) + Real.sqrt 2 * (P n : ℝ) := by
                  have hP : (P n : ℝ) ≥ 5 := h_P_ge
                  have h_P_pos : (P n : ℝ) > 0 := by linarith
                  have h_P_bound : 1.4 * (P n : ℝ) < Real.sqrt 2 * (P n : ℝ) := mul_lt_mul_of_pos_right h_sqrt2_gt h_P_pos
                  have h_Q_bound : (Q n : ℝ) ≤ Real.sqrt 2 * (P n : ℝ) := h_Q_lt
                  nlinarith [hP, h_P_bound, h_Q_bound]
                linarith [h_ineq2, h_temp3]
              linarith [h_LHS, h_j_bound, h_RHS]
            have h_diff_eq : Real.sqrt 2 * (P n : ℝ) - (Q n : ℝ) = 1 / ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) := by
              have h_factor : (Real.sqrt 2 * (P n : ℝ) - (Q n : ℝ)) * ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) = 1 := by
                calc (Real.sqrt 2 * (P n : ℝ) - (Q n : ℝ)) * ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ))
                  _ = (Real.sqrt 2 * (P n : ℝ)) ^ 2 - (Q n : ℝ) ^ 2 := by ring
                  _ = (Real.sqrt 2) ^ 2 * (P n : ℝ) ^ 2 - (Q n : ℝ) ^ 2 := by ring
                  _ = 2 * (P n : ℝ) ^ 2 - (Q n : ℝ) ^ 2 := by rw [h_sqrt2_sq]
                  _ = 1 := by linarith [h_pell_real_odd]
              exact eq_div_of_mul_eq (by linarith) h_factor
            have h_exact : (Nat.sqrt (2 * j ^ 2) : ℝ) + 1 - Real.sqrt 2 * (j : ℝ) = 1 / ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) := by
              have h_prod : ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 - Real.sqrt 2 * (j : ℝ)) * ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) = 1 := by
                have h_alg : ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 - Real.sqrt 2 * (j : ℝ)) * ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) = ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1)^2 - (Real.sqrt 2)^2 * (j : ℝ)^2 := by ring
                rw [h_alg, h_sqrt2_sq]
                have h_cast : (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ)^2 - 2 * j ^ 2 : ℕ) : ℝ) = ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1)^2 - 2 * (j : ℝ)^2 := by
                  push_cast
                  have h_lt' : 2 * j ^ 2 ≤ (Nat.sqrt (2 * j ^ 2) + 1) ^ 2 := by
                    have h_t := Nat.lt_succ_sqrt (2 * j ^ 2)
                    simp only [Nat.succ_eq_add_one] at h_t
                    have h_sq : (Nat.sqrt (2 * j ^ 2) + 1) ^ 2 = (Nat.sqrt (2 * j ^ 2) + 1) * (Nat.sqrt (2 * j ^ 2) + 1) := by ring
                    omega
                  rw [Nat.cast_sub h_lt']
                  push_cast
                  ring
                have h_pell_j_real : (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ)^2 - 2 * j ^ 2 : ℕ) : ℝ) = 1 := by
                  have h_eq_cast : (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ)^2 - 2 * j ^ 2 : ℕ) : ℝ) = (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ)^2 : ℕ) : ℝ) - (2 * j ^ 2 : ℕ) := by
                    have h_le_sub : 2 * j ^ 2 ≤ (Nat.sqrt (2 * j ^ 2) + 1) ^ 2 := by
                      have h_t := Nat.lt_succ_sqrt (2 * j ^ 2)
                      simp only [Nat.succ_eq_add_one] at h_t
                      have h_sq : (Nat.sqrt (2 * j ^ 2) + 1) ^ 2 = (Nat.sqrt (2 * j ^ 2) + 1) * (Nat.sqrt (2 * j ^ 2) + 1) := by ring
                      omega
                    exact Nat.cast_sub h_le_sub
                  rw [h_eq_cast]
                  exact_mod_cast h_pell_j
                rw [← h_cast, h_pell_j_real]
              exact eq_div_of_mul_eq (by linarith) h_prod
            have h_recip : 1 / ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) > 1 / ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) := by
              exact (one_div_lt_one_div (by linarith) (by linarith)).mpr h_ineq4
            linarith [h_exact, h_recip, h_diff_eq]
        · have h_diff_eq : Real.sqrt 2 * (P n : ℝ) - (Q n : ℝ) = 1 / ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) := by
            have h_factor : (Real.sqrt 2 * (P n : ℝ) - (Q n : ℝ)) * ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) = 1 := by
              calc (Real.sqrt 2 * (P n : ℝ) - (Q n : ℝ)) * ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ))
                _ = (Real.sqrt 2 * (P n : ℝ)) ^ 2 - (Q n : ℝ) ^ 2 := by ring
                _ = (Real.sqrt 2) ^ 2 * (P n : ℝ) ^ 2 - (Q n : ℝ) ^ 2 := by ring
                _ = 2 * (P n : ℝ) ^ 2 - (Q n : ℝ) ^ 2 := by rw [h_sqrt2_sq]
                _ = 1 := by linarith [h_pell_real_odd]
            exact eq_div_of_mul_eq (by linarith) h_factor
          have h_exact : (Nat.sqrt (2 * j ^ 2) : ℝ) + 1 - Real.sqrt 2 * (j : ℝ) = (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ)^2 - 2 * j ^ 2 : ℕ) : ℝ) / ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) := by
            have h_prod : ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 - Real.sqrt 2 * (j : ℝ)) * ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) = (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ)^2 - 2 * j ^ 2 : ℕ) : ℝ) := by
              have h_alg : ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 - Real.sqrt 2 * (j : ℝ)) * ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) = ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1)^2 - (Real.sqrt 2)^2 * (j : ℝ)^2 := by ring
              rw [h_alg, h_sqrt2_sq]
              have h_lt : 2 * j ^ 2 < (Nat.sqrt (2 * j ^ 2) + 1) * (Nat.sqrt (2 * j ^ 2) + 1) := Nat.lt_succ_sqrt (2 * j ^ 2)
              have h_cast : (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ)^2 - 2 * j ^ 2 : ℕ) : ℝ) = ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1)^2 - 2 * (j : ℝ)^2 := by
                push_cast
                have h_lt' : 2 * j ^ 2 ≤ (Nat.sqrt (2 * j ^ 2) + 1) ^ 2 := by
                  have h_t := Nat.lt_succ_sqrt (2 * j ^ 2)
                  simp only [Nat.succ_eq_add_one] at h_t
                  have h_sq : (Nat.sqrt (2 * j ^ 2) + 1) ^ 2 = (Nat.sqrt (2 * j ^ 2) + 1) * (Nat.sqrt (2 * j ^ 2) + 1) := by ring
                  omega
                rw [Nat.cast_sub h_lt']
                push_cast
                ring
              rw [← h_cast]
            exact eq_div_of_mul_eq (by linarith) h_prod
          have h_S_bound : (Nat.sqrt (2 * j ^ 2) : ℝ) + 1 - Real.sqrt 2 * (j : ℝ) ≥ 2 / ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) := by
            rw [h_exact]
            have h_R_real : 2 ≤ (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ)^2 - 2 * j ^ 2 : ℕ) : ℝ) := by
              have h_eq_cast : (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ)^2 - 2 * j ^ 2 : ℕ) : ℝ) = (((Nat.sqrt (2 * j ^ 2) + 1 : ℕ)^2 : ℕ) : ℝ) - (2 * j ^ 2 : ℕ) := by
                have h_le_sub : 2 * j ^ 2 ≤ (Nat.sqrt (2 * j ^ 2) + 1) ^ 2 := by
                  have h_t := Nat.lt_succ_sqrt (2 * j ^ 2)
                  simp only [Nat.succ_eq_add_one] at h_t
                  have h_sq : (Nat.sqrt (2 * j ^ 2) + 1) ^ 2 = (Nat.sqrt (2 * j ^ 2) + 1) * (Nat.sqrt (2 * j ^ 2) + 1) := by ring
                  omega
                exact Nat.cast_sub h_le_sub
              rw [h_eq_cast]
              exact_mod_cast h_R_ge_2
            exact div_le_div_of_nonneg_right h_R_real (by linarith)
          have h_recip : 2 / ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) > 1 / ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) := by
            rw [gt_iff_lt]
            have h_eq : 2 / ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) = 1 / (((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) / 2) := by
              field_simp
            rw [h_eq]
            have h_sum_pos2 : (Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ) > 0 := by
              have hj_pos_real : (j : ℝ) > 0 := by exact_mod_cast hj_pos
              have h_mul_pos : Real.sqrt 2 * (j : ℝ) > 0 := mul_pos h_sqrt2_pos hj_pos_real
              have h_S_nonneg : (Nat.sqrt (2 * j ^ 2) : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le _
              linarith
            have h_half_pos : ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) / 2 > 0 := by linarith
            have h_half_lt : ((Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ)) / 2 < (Q n : ℝ) + Real.sqrt 2 * (P n : ℝ) := by
              have h_LHS : (Nat.sqrt (2 * j ^ 2) : ℝ) + 1 + Real.sqrt 2 * (j : ℝ) ≤ 2 * Real.sqrt 2 * (j : ℝ) + 1 := by linarith [h_sq_lt_j]
              have h_j_bound : 2 * Real.sqrt 2 * (j : ℝ) + 1 ≤ 2 * Real.sqrt 2 * ((Q n : ℝ) - 1) + 1 := by
                have h_pos : 2 * Real.sqrt 2 ≥ 0 := by positivity
                have h_j_lt2 : (j : ℝ) ≤ (Q n : ℝ) - 1 := by
                  have h_cast : (j : ℝ) ≤ ((Q n - 1 : ℕ) : ℝ) := by exact_mod_cast hj_lt
                  have h_sub : ((Q n - 1 : ℕ) : ℝ) = (Q n : ℝ) - 1 := by
                    rw [Nat.cast_sub (Q_ge_one n)]
                    push_cast
                    rfl
                  linarith
                have h_mul := mul_le_mul_of_nonneg_left h_j_lt2 h_pos
                linarith
              have h_RHS : 2 * Real.sqrt 2 * ((Q n : ℝ) - 1) + 1 < 2 * ((Q n : ℝ) + Real.sqrt 2 * (P n : ℝ)) := by
                have h_Q_lt : (Q n : ℝ) ≤ Real.sqrt 2 * (P n : ℝ) := by
                  have h_sq : (Q n : ℝ) ^ 2 ≤ (Real.sqrt 2 * (P n : ℝ)) ^ 2 := by
                    rw [mul_pow, h_sqrt2_sq]
                    linarith [h_pell_real_odd]
                  have h1 : 0 ≤ (Q n : ℝ) := by exact_mod_cast Nat.zero_le (Q n)
                  have h2 : 0 ≤ Real.sqrt 2 * (P n : ℝ) := mul_nonneg (Real.sqrt_nonneg 2) (by exact_mod_cast Nat.zero_le (P n))
                  exact (sq_le_sq₀ h1 h2).mp h_sq
                have h_sqrt2_lt2 : Real.sqrt 2 < 2 := by
                  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
                  norm_num
                have h_sqrt2_gt : 1.4 < Real.sqrt 2 := by
                  rw [Real.lt_sqrt (by norm_num)]
                  norm_num
                have h_sqrt2_ge1 : Real.sqrt 2 ≥ 1 := by linarith [h_sqrt2_gt]
                have h_ineq : Real.sqrt 2 * (Q n : ℝ) < 2 * (Q n : ℝ) := mul_lt_mul_of_pos_right h_sqrt2_lt2 h_Q_pos
                linarith [h_Q_lt, h_ineq, h_sqrt2_gt]
              linarith [h_LHS, h_j_bound, h_RHS]
            exact (one_div_lt_one_div h_sum_pos h_half_pos).mpr h_half_lt
          have h_pell_pos : Real.sqrt 2 * (P n : ℝ) - (Q n : ℝ) > 0 := by
            rw [h_diff_eq]
            have h_sum_pos' : (Q n : ℝ) + Real.sqrt 2 * (P n : ℝ) > 0 := h_sum_pos
            positivity
          constructor
          · linarith [h_pell_pos, h_sq_le_j]
          · linarith [h_S_bound, h_recip, h_diff_eq]
    have h_Y_le : ((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) ≤ Real.sqrt 2 * ((P n + j : ℕ) : ℝ) := by
      have h_eq1 : ((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) = (Q n : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ) := by push_cast; rfl
      have h_eq2 : ((P n + j : ℕ) : ℝ) = (P n : ℝ) + (j : ℝ) := by push_cast; rfl
      rw [h_eq1, h_eq2]
      exact h_Q_plus_S.left
    have h_lt_Y1 : Real.sqrt 2 * ((P n + j : ℕ) : ℝ) < ((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) + 1 := by
      have h_eq1 : ((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) = (Q n : ℝ) + (Nat.sqrt (2 * j ^ 2) : ℝ) := by push_cast; rfl
      have h_eq2 : ((P n + j : ℕ) : ℝ) = (P n : ℝ) + (j : ℝ) := by push_cast; rfl
      rw [h_eq1, h_eq2]
      exact h_Q_plus_S.right
    have h_Y_sq_le : ((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) ^ 2 ≤ 2 * ((P n + j : ℕ) : ℝ) ^ 2 := by
      have h_sq : ((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) ^ 2 ≤ (Real.sqrt 2 * ((P n + j : ℕ) : ℝ)) ^ 2 := by
        have h_pos1 : 0 ≤ ((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
        have h_pos2 : 0 ≤ Real.sqrt 2 * ((P n + j : ℕ) : ℝ) := mul_nonneg (Real.sqrt_nonneg 2) (by exact_mod_cast Nat.zero_le _)
        exact sq_le_sq₀ h_pos1 h_pos2 |>.mpr h_Y_le
      rw [mul_pow, h_sqrt2_sq] at h_sq
      exact h_sq
    have h_lt_Y1_sq : 2 * ((P n + j : ℕ) : ℝ) ^ 2 < (((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) + 1) ^ 2 := by
      have h_sq : (Real.sqrt 2 * ((P n + j : ℕ) : ℝ)) ^ 2 < (((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) + 1) ^ 2 := by
        have h_pos1 : 0 ≤ Real.sqrt 2 * ((P n + j : ℕ) : ℝ) := mul_nonneg (Real.sqrt_nonneg 2) (by exact_mod_cast Nat.zero_le _)
        have h_pos2 : 0 ≤ ((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) + 1 := by
          have h_pos3 : 0 ≤ ((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
          linarith
        exact sq_lt_sq₀ h_pos1 h_pos2 |>.mpr h_lt_Y1
      rw [mul_pow, h_sqrt2_sq] at h_sq
      exact h_sq
    have h_Y_sq_le_nat : (Q n + Nat.sqrt (2 * j ^ 2)) ^ 2 ≤ 2 * (P n + j) ^ 2 := by
      exact_mod_cast h_Y_sq_le
    have h_lt_Y1_sq_nat : 2 * (P n + j) ^ 2 < (Q n + Nat.sqrt (2 * j ^ 2) + 1) ^ 2 := by
      have h_cast_add_one : (((Q n + Nat.sqrt (2 * j ^ 2) : ℕ) : ℝ) + 1) = (((Q n + Nat.sqrt (2 * j ^ 2) + 1 : ℕ) : ℝ)) := by push_cast; rfl
      rw [h_cast_add_one] at h_lt_Y1_sq
      exact_mod_cast h_lt_Y1_sq
    exact Nat.sqrt_eq_of_le_and_lt h_Y_sq_le_nat h_lt_Y1_sq_nat
lemma S_P_add_j_sub_P_add_j (n : ℕ) (hn : n ≥ 1) (j : ℕ) (hj_pos : j ≥ 1) (hj : j ≤ Q n) :
    Nat.sqrt (2 * (P n + j) ^ 2) - (P n + j) = (Q n - P n) + (Nat.sqrt (2 * j ^ 2) - j) := by
  have h1 := S_P_add_j_eq_Q_add_S n hn j hj_pos hj
  have h2 : P n ≤ Q n := P_le_Q n
  have h3 : j ≤ Nat.sqrt (2 * j ^ 2) := le_sqrt_two_k_sq j
  omega

lemma sum_Ioc_split (A B : ℕ) (f : ℕ → ℤ) :
    Finset.sum (Finset.Ioc 0 (A + B)) f = Finset.sum (Finset.Ioc 0 A) f + Finset.sum (Finset.Ioc A (A + B)) f := by
  induction B with
  | zero =>
    have h_eq : A + 0 = A := by omega
    rw [h_eq]
    have h_empty : Finset.Ioc A A = ∅ := by simp
    rw [h_empty, Finset.sum_empty, add_zero]
  | succ B ih =>
    have h_eq1 : A + (B + 1) = A + B + 1 := by omega
    rw [h_eq1]
    rw [Finset.sum_Ioc_succ_top (by omega)]
    rw [ih]
    rw [Finset.sum_Ioc_succ_top (by omega)]
    ring

lemma sum_P_add_j_helper (n : ℕ) (hn : n ≥ 1) (m : ℕ) (hm : m ≤ Q n) :
    Finset.sum (Finset.Ioc (P n) (P n + m)) (fun k => (-1 : ℤ) ^ (Nat.sqrt (2 * k^2) - k)) =
    (-1 : ℤ)^(Q n - P n) * Finset.sum (Finset.Ioc 0 m) (fun k => (-1 : ℤ) ^ (Nat.sqrt (2 * k^2) - k)) := by
  induction m with
  | zero =>
    have h_eq1 : P n + 0 = P n := by omega
    rw [h_eq1]
    have h_empty1 : Finset.Ioc (P n) (P n) = ∅ := by simp
    have h_empty2 : Finset.Ioc 0 0 = ∅ := by simp
    rw [h_empty1, h_empty2]
    ring
  | succ m ih =>
    have hm_succ : m ≤ Q n := by omega
    have ih_inst := ih hm_succ
    have h_eq1 : P n + (m + 1) = P n + m + 1 := by omega
    rw [h_eq1]
    rw [Finset.sum_Ioc_succ_top (by omega)]
    rw [Finset.sum_Ioc_succ_top (by omega)]
    rw [ih_inst]
    have h_term : (-1 : ℤ) ^ (Nat.sqrt (2 * (P n + (m + 1))^2) - (P n + (m + 1))) =
        (-1 : ℤ)^(Q n - P n) * (-1 : ℤ) ^ (Nat.sqrt (2 * (m + 1)^2) - (m + 1)) := by
      rw [S_P_add_j_sub_P_add_j n hn (m + 1) (by omega) hm]
      rw [pow_add]
    rw [← h_eq1]
    rw [h_term]
    ring

lemma a_comp_P_succ (n : ℕ) (hn : n ≥ 1) :
    a_comp (P (n + 1)) = a_comp (P n) + (-1 : ℤ)^(Q n - P n) * a_comp (Q n) := by
  have h_split := sum_Ioc_split (P n) (Q n) (fun k => (-1 : ℤ) ^ (Nat.sqrt (2 * k^2) - k))
  have h_P_succ : P (n + 1) = P n + Q n := P_succ n
  rw [h_P_succ]
  dsimp [a_comp]
  rw [h_split]
  have h_shift := sum_P_add_j_helper n hn (Q n) (by omega)
  rw [h_shift]

lemma QP_sub_step (n : ℕ) : Q (n + 2) - P (n + 2) = 2 * (Q (n + 1) - P (n + 1)) + (Q n - P n) := by
  rw [P_succ (n+1), Q_succ (n+1)]
  rw [P_succ n, Q_succ n]
  have h1 : P n ≤ Q n := P_le_Q n
  have h2 : P (n+1) ≤ Q (n+1) := P_le_Q (n+1)
  omega

lemma QP_parity_step (n : ℕ) : (-1 : ℤ)^(Q (n + 2) - P (n + 2)) = (-1 : ℤ)^(Q n - P n) := by
  rw [QP_sub_step n]
  rw [pow_add]
  have h_even : (-1 : ℤ)^(2 * (Q (n + 1) - P (n + 1))) = 1 := by
    rw [pow_mul]
    have h_sq : (-1 : ℤ)^2 = 1 := by ring
    rw [h_sq]
    exact one_pow (Q (n + 1) - P (n + 1))
  rw [h_even, one_mul]

lemma QP_parity_odd (k : ℕ) : (-1 : ℤ)^(Q (2 * k + 1) - P (2 * k + 1)) = 1 := by
  induction k with
  | zero =>
    rw [P_succ, Q_succ, P_zero, Q_zero]
    ring
  | succ k ih =>
    have h_eq : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by omega
    rw [h_eq]
    rw [QP_parity_step (2 * k + 1)]
    exact ih

lemma QP_parity_even (k : ℕ) : (-1 : ℤ)^(Q (2 * k) - P (2 * k)) = -1 := by
  induction k with
  | zero =>
    rw [P_zero, Q_zero]
    ring
  | succ k ih =>
    have h_eq : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h_eq]
    rw [QP_parity_step (2 * k)]
    exact ih

lemma Q_eq_P_add_P (n : ℕ) : Q (n + 1) = P (n + 1) + P n := by
  rw [P_succ, Q_succ]
  omega

lemma sqrt_two_eq_one : Nat.sqrt 2 = 1 := by
  have h1 : 1 ≤ Nat.sqrt 2 := by
    rw [Nat.le_sqrt]
    omega
  have h2 : Nat.sqrt 2 < 2 := by
    rw [Nat.sqrt_lt]
    omega
  omega

lemma a_comp_P_odd_even (k : ℕ) : a_comp (P (2 * k + 1)) = 1 ∧ a_comp (P (2 * k)) = 2 * k := by
  induction k with
  | zero =>
    constructor
    · have hP1 : P 1 = 1 := by rw [P_succ, P_zero, Q_zero]
      rw [hP1]
      have h_succ : a_comp 1 = a_comp 0 + (-1 : ℤ)^(Nat.sqrt 2 - 1) := by
        have h_eq : 1 = 0 + 1 := by rfl
        rw [h_eq]
        have h_succ_zero := a_comp_succ 0
        have h_sqrt2 : Nat.sqrt (2 * (0 + 1)^2) = Nat.sqrt 2 := by rfl
        rw [h_sqrt2] at h_succ_zero
        exact h_succ_zero
      have h_sqrt : Nat.sqrt 2 = 1 := sqrt_two_eq_one
      rw [h_sqrt] at h_succ
      rw [h_succ]
      have h_a0 : a_comp 0 = 0 := rfl
      rw [h_a0]
      simp
    · rw [P_zero]
      dsimp [a_comp]
      rfl
  | succ k ih =>
    have ih_odd := ih.1
    have ih_even := ih.2
    have h_2k1_pos : 2 * k + 1 ≥ 1 := by omega
    have h_2k2_pos : 2 * k + 2 ≥ 1 := by omega
    
    -- First prove the even part: a_comp (P (2 * k + 2)) = 2 * (k + 1)
    have h_even_step : a_comp (P (2 * k + 2)) = 2 * k + 2 := by
      have h_rec := a_comp_P_succ (2 * k + 1) h_2k1_pos
      have h_eq : 2 * k + 1 + 1 = 2 * k + 2 := by omega
      rw [h_eq] at h_rec
      rw [h_rec]
      rw [ih_odd]
      have h_parity := QP_parity_odd k
      rw [h_parity]
      have h_Q_split : Q (2 * k + 1) = P (2 * k + 1) + P (2 * k) := Q_eq_P_add_P (2 * k)
      have h_split := sum_Ioc_split (P (2 * k + 1)) (P (2 * k)) (fun k => (-1 : ℤ) ^ (Nat.sqrt (2 * k^2) - k))
      have h_comp_split : a_comp (Q (2 * k + 1)) = a_comp (P (2 * k + 1)) + Finset.sum (Finset.Ioc (P (2 * k + 1)) (P (2 * k + 1) + P (2 * k))) (fun k => (-1 : ℤ) ^ (Nat.sqrt (2 * k^2) - k)) := by
        dsimp [a_comp]
        rw [h_Q_split]
        exact h_split
      rw [h_comp_split]
      have h_shift := sum_P_add_j_helper (2 * k + 1) h_2k1_pos (P (2 * k)) (by
        have h_le := P_le_Q (2 * k)
        have h_Q_eq := Q_eq_P_add_P (2 * k)
        omega)
      rw [h_shift]
      have h_parity2 := QP_parity_odd k
      rw [h_parity2]
      have h_fold : Finset.sum (Finset.Ioc 0 (P (2 * k))) (fun k => (-1 : ℤ) ^ (Nat.sqrt (2 * k^2) - k)) = a_comp (P (2 * k)) := rfl
      rw [h_fold]
      rw [ih_odd, ih_even]
      ring

    constructor
    · -- a_comp (P (2 * k + 3)) = 1
      have h_odd_step : a_comp (P (2 * k + 3)) = 1 := by
        have h_rec := a_comp_P_succ (2 * k + 2) h_2k2_pos
        have h_eq : 2 * k + 2 + 1 = 2 * k + 3 := by omega
        rw [h_eq] at h_rec
        rw [h_rec]
        rw [h_even_step]
        have h_parity := QP_parity_even (k + 1)
        have h_mul_eq : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [h_mul_eq] at h_parity
        rw [h_parity]
        have h_Q_split : Q (2 * k + 2) = P (2 * k + 2) + P (2 * k + 1) := Q_eq_P_add_P (2 * k + 1)
        have h_split := sum_Ioc_split (P (2 * k + 2)) (P (2 * k + 1)) (fun k => (-1 : ℤ) ^ (Nat.sqrt (2 * k^2) - k))
        have h_comp_split : a_comp (Q (2 * k + 2)) = a_comp (P (2 * k + 2)) + Finset.sum (Finset.Ioc (P (2 * k + 2)) (P (2 * k + 2) + P (2 * k + 1))) (fun k => (-1 : ℤ) ^ (Nat.sqrt (2 * k^2) - k)) := by
          dsimp [a_comp]
          rw [h_Q_split]
          exact h_split
        rw [h_comp_split]
        have h_shift := sum_P_add_j_helper (2 * k + 2) h_2k2_pos (P (2 * k + 1)) (by
          have h_le := P_le_Q (2 * k + 1)
          have h_Q_eq := Q_eq_P_add_P (2 * k + 1)
          omega)
        rw [h_shift]
        have h_parity2 := QP_parity_even (k + 1)
        rw [h_mul_eq] at h_parity2
        rw [h_parity2]
        have h_fold : Finset.sum (Finset.Ioc 0 (P (2 * k + 1))) (fun k => (-1 : ℤ) ^ (Nat.sqrt (2 * k^2) - k)) = a_comp (P (2 * k + 1)) := rfl
        rw [h_fold]
        rw [h_even_step, ih_odd]
        ring
      have h_eq : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [h_eq]
      exact h_odd_step
    · have h_eq : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [h_eq]
      exact h_even_step

theorem oeis_348295_conjecture_0 : ∀ (M : ℤ), ∃ (n : ℕ), a n > M := by
  intro M
  have h_exist : ∃ (k : ℕ), (2 * k : ℤ) > M := by
    rcases M with n | n
    · use n + 1
      change (2 * (n + 1) : ℤ) > (n : ℤ)
      omega
    · use 0
      change (2 * 0 : ℤ) > Int.negSucc n
      omega
  rcases h_exist with ⟨k, h_gt⟩
  use P (2 * k)
  rw [a_eq_a_comp]
  have h_even := (a_comp_P_odd_even k).2
  rw [h_even]
  exact h_gt
