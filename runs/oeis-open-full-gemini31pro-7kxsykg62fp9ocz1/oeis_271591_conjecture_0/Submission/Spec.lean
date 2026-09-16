import FormalConjectures.Util.ProblemImports
open Nat

def tribonacci (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => (tribonacci (n + 2)) + (tribonacci (n + 1)) + (tribonacci n)

def a (n : ℕ) : ℕ :=
  let T := tribonacci n
  if h : T ≤ 1 then 0
  else let j_smsb : ℕ := T.log2 - 1; if T.testBit j_smsb then 1 else 0

def is_maximal_run (v : ℕ) (n L : ℕ) : Prop :=
  n ≥ 2 ∧ L ≥ 1 ∧
  (∀ i : ℕ, i < L → a (n + i) = v) ∧
  (a (n + L) ≠ v) ∧
  (a (n - 1) ≠ v)

lemma a_zero_or_one (n : Nat) : a n = 0 ∨ a n = 1 := by
  dsimp [a]; split; left; rfl; split; right; rfl; left; rfl

lemma a_not_zero_eq_one (n : Nat) : a n ≠ 0 ↔ a n = 1 := by
  have := a_zero_or_one n; omega
lemma a_not_one_eq_zero (n : Nat) : a n ≠ 1 ↔ a n = 0 := by
  have := a_zero_or_one n; omega

lemma trib_ge_2 (n : Nat) (hn : n ≥ 12) : tribonacci n ≥ 2 := by
  induction n using Nat.strong_induction_on with
  | h k ih =>
    have : k = 12 ∨ k = 13 ∨ k = 14 ∨ k ≥ 15 := by omega
    rcases this with rfl | rfl | rfl | hk15
    · decide
    · decide
    · decide
    have h1 := ih (k-1) (by omega) (by omega)
    have h_eq : tribonacci k = tribonacci (k-1) + tribonacci (k-2) + tribonacci (k-3) := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩; rfl
    omega

lemma a_zero_iff (n : Nat) (hn : n ≥ 12) :
  a n = 0 ↔ (tribonacci n).testBit ((tribonacci n).log2 - 1) = false := by
  unfold a
  have hT2 : tribonacci n ≥ 2 := trib_ge_2 n hn
  have hT_not_le_1 : ¬ (tribonacci n ≤ 1) := by omega
  rw [dif_neg hT_not_le_1]
  dsimp
  split
  · next h => simp [h]
  · next h => simp [h]

lemma a_one_iff (n : Nat) (hn : n ≥ 12) :
  a n = 1 ↔ (tribonacci n).testBit ((tribonacci n).log2 - 1) = true := by
  unfold a
  have hT2 : tribonacci n ≥ 2 := trib_ge_2 n hn
  have hT_not_le_1 : ¬ (tribonacci n ≤ 1) := by omega
  rw [dif_neg hT_not_le_1]
  dsimp
  split
  · next h => simp [h]
  · next h => simp [h]

lemma T_div_pow_log2 (T : Nat) (hT : T ≥ 2) : T / (2 ^ T.log2) = 1 := by
  have h1 : 2 ^ T.log2 ≤ T := Nat.log2_self_le (by omega)
  have h2 : T < 2 ^ (T.log2 + 1) := Nat.lt_log2_self
  have h3 : 2 ^ (T.log2 + 1) = 2 * 2 ^ T.log2 := by omega
  rw [h3] at h2
  have h1' : 1 * 2 ^ T.log2 ≤ T := by omega
  exact Nat.div_eq_of_lt_le h1' h2

lemma div_mod_omega (T P : Nat) (hP : P > 0) (h1 : T / (2 * P) = 1) :
  ((T / P) % 2 = 0 → 2 * P ≤ T ∧ T < 3 * P) ∧
  ((T / P) % 2 = 1 → 3 * P ≤ T ∧ T < 4 * P) := by
  have h_div : T / (2 * P) = T / P / 2 := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [h_div] at h1
  have h2 : T / P = 2 ∨ T / P = 3 := by omega
  have h3 : T = P * (T / P) + T % P := Nat.div_add_mod T P |>.symm
  have h4 : T % P < P := Nat.mod_lt T hP
  rcases h2 with h2 | h2
  · constructor; intro _; rw [h2] at h3; omega; intro h; rw [h2] at h; contradiction
  · constructor; intro h; rw [h2] at h; contradiction; intro _; rw [h2] at h3; omega

lemma bool_cases (M : Nat) (h1 : M < 2) (h2 : decide (M = 1) = false) : M = 0 := by
  revert h2
  cases M with
  | zero => intro _; rfl
  | succ M =>
    cases M with
    | zero => intro h; contradiction
    | succ M => omega

lemma a_zero_one_bounds (n : Nat) (hn : n ≥ 12) :
  (a n = 0 → ∃ P > 0, 2 * P ≤ tribonacci n ∧ tribonacci n < 3 * P ∧ P = 2^((tribonacci n).log2 - 1)) ∧
  (a n = 1 → ∃ P > 0, 3 * P ≤ tribonacci n ∧ tribonacci n < 4 * P ∧ P = 2^((tribonacci n).log2 - 1)) := by
  have hT2 : tribonacci n ≥ 2 := trib_ge_2 n hn
  let T := tribonacci n
  let k := T.log2 - 1
  let P := 2^k
  have hP : P > 0 := by positivity
  have hk : T.log2 = k + 1 := by
    dsimp [k]
    have : T.log2 ≥ 1 := by apply Nat.le_log2 (by omega) |>.mpr; omega
    omega
  have h_div : T / (2 * P) = 1 := by
    have h_pow : 2 * P = 2 ^ T.log2 := by change 2 * 2 ^ k = 2 ^ T.log2; rw [← Nat.pow_succ', hk]
    rw [h_pow]
    exact T_div_pow_log2 T hT2
  have h_testBit : T.testBit k = decide ((T / P) % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  have bounds := div_mod_omega T P hP h_div
  constructor
  · intro h0
    have h_bool : T.testBit k = false := a_zero_iff n hn |>.mp h0
    have h_dec : decide ((T / P) % 2 = 1) = false := by rw [← h_testBit]; exact h_bool
    have h_mod2 : (T / P) % 2 < 2 := Nat.mod_lt (T / P) (by decide)
    have h_mod : (T / P) % 2 = 0 := bool_cases ((T / P) % 2) h_mod2 h_dec
    have b1 : 2 * P ≤ T ∧ T < 3 * P := bounds.1 h_mod
    exact ⟨P, hP, b1.1, b1.2, rfl⟩
  · intro h1
    have h_bool : T.testBit k = true := a_one_iff n hn |>.mp h1
    have h_dec : decide ((T / P) % 2 = 1) = true := by rw [← h_testBit]; exact h_bool
    have h_mod : (T / P) % 2 = 1 := of_decide_eq_true h_dec
    have b2 : 3 * P ≤ T ∧ T < 4 * P := bounds.2 h_mod
    exact ⟨P, hP, b2.1, b2.2, rfl⟩

lemma trib_bound (n : Nat) (hn : n ≥ 12) :
  1838 * tribonacci (n-1) ≤ 1000 * tribonacci n ∧
  1000 * tribonacci n ≤ 1841 * tribonacci (n-1) := by
  induction n using Nat.strong_induction_on with
  | h k ih =>
    have : k = 12 ∨ k = 13 ∨ k = 14 ∨ k ≥ 15 := by omega
    rcases this with rfl | rfl | rfl | hk15
    · decide
    · decide
    · decide
    have h1 := ih (k-1) (by omega) (by omega)
    have h2 := ih (k-2) (by omega) (by omega)
    have h3 := ih (k-3) (by omega) (by omega)
    have h_eq : tribonacci k = tribonacci (k-1) + tribonacci (k-2) + tribonacci (k-3) := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩; rfl
    have h_eq2 : tribonacci (k-1-1) = tribonacci (k-2) := congr_arg tribonacci (by omega)
    have h_eq3 : tribonacci (k-2-1) = tribonacci (k-3) := congr_arg tribonacci (by omega)
    have h_eq4 : tribonacci (k-3-1) = tribonacci (k-4) := congr_arg tribonacci (by omega)
    rw [h_eq2] at h1; rw [h_eq3] at h2; rw [h_eq4] at h3
    omega

lemma pow2_cases (k1 k2 P1 P2 : Nat) (e1 : P1 = 2^k1) (e2 : P2 = 2^k2)
  (h1 : P2 < 4 * P1) (h2 : 4 * P2 > 3 * P1) : P2 = P1 ∨ P2 = 2 * P1 := by
  subst e1 e2
  have hk : k1 ≤ k2 ∨ k2 < k1 := by omega
  rcases hk with h | h
  · have hk2 : k2 = k1 ∨ k2 = k1 + 1 ∨ k2 ≥ k1 + 2 := by omega
    rcases hk2 with rfl | rfl | h_gt
    · left; rfl
    · right; rw [Nat.pow_succ', Nat.mul_comm]
    · exfalso
      have : 2^(k1+2) ≤ 2^k2 := Nat.pow_le_pow_right (by decide) h_gt
      have : 4 * 2^k1 ≤ 2^k2 := by
        calc 4 * 2^k1 = 2^2 * 2^k1 := rfl
        _ = 2^(k1+2) := by rw [Nat.pow_add, Nat.mul_comm]
        _ ≤ 2^k2 := this
      omega
  · exfalso
    have : k2 + 1 ≤ k1 := by omega
    have : 2^(k2+1) ≤ 2^k1 := Nat.pow_le_pow_right (by decide) this
    have : 2 * 2^k2 ≤ 2^k1 := by
      calc 2 * 2^k2 = 2^(k2+1) := by rw [Nat.pow_succ', Nat.mul_comm]
      _ ≤ 2^k1 := this
    omega

lemma P_rel (T1 T2 P1 P2 k1 k2 : Nat) (hP1 : P1 > 0) (hP2 : P2 > 0)
  (h1 : 2 * P1 ≤ T1 ∧ T1 < 4 * P1) (h2 : 2 * P2 ≤ T2 ∧ T2 < 4 * P2)
  (b1 : 1838 * T1 ≤ 1000 * T2) (b2 : 1000 * T2 ≤ 1841 * T1)
  (P1_eq : P1 = 2^k1) (P2_eq : P2 = 2^k2) :
  P2 = P1 ∨ P2 = 2 * P1 := by
  have h_bound1 : P2 < 4 * P1 := by omega
  have h_bound2 : 4 * P2 > 3 * P1 := by omega
  exact pow2_cases k1 k2 P1 P2 P1_eq P2_eq h_bound1 h_bound2

lemma hT_eq (n : Nat) (hn : n ≥ 3) : tribonacci n = tribonacci (n-3) + tribonacci (n-2) + tribonacci (n-1) := by
  have : n = (n - 3) + 3 := by omega
  nth_rw 1 [this]
  change tribonacci (n-3+2) + tribonacci (n-3+1) + tribonacci (n-3) = _
  have e1 : n - 3 + 2 = n - 1 := by omega
  have e2 : n - 3 + 1 = n - 2 := by omega
  rw [e1, e2]
  omega

lemma no_max_0_run_1_small (n : Nat) (hn : n ≥ 2) (hn2 : n < 14) : ¬ (a (n-1) = 1 ∧ a (n+0) = 0 ∧ a (n+1) = 1) := by
  have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

lemma no_max_0_run_1_large (T0 T1 T2 T3 P0 P1 P2 : Nat)
  (h0 : 1838 * T0 ≤ 1000 * T1) (h0' : 1000 * T1 ≤ 1841 * T0)
  (h1 : 1838 * T1 ≤ 1000 * T2) (h1' : 1000 * T2 ≤ 1841 * T1)
  (h2 : 1838 * T2 ≤ 1000 * T3) (h2' : 1000 * T3 ≤ 1841 * T2)
  (hT3 : T3 = T0 + T1 + T2)
  (a0 : 3 * P0 ≤ T0 ∧ T0 < 4 * P0)
  (a1 : 2 * P1 ≤ T1 ∧ T1 < 3 * P1)
  (a2 : 3 * P2 ≤ T2 ∧ T2 < 4 * P2)
  (p1 : P1 = P0 ∨ P1 = 2 * P0)
  (p2 : P2 = P1 ∨ P2 = 2 * P1)
  (hp0 : P0 > 0) : False := by omega

lemma apply_no_max_0_run_1_large (n : Nat) (hn : n ≥ 14) (h : a (n-1) = 1 ∧ a (n+0) = 0 ∧ a (n+1) = 1) : False := by
  have h_a_0 : a (n - 1 + 0) = 1 := by
    have eq : n - 1 + 0 = n - 1 := by omega
    rw [eq]
    exact h.1
  have h_a_1 : a (n - 1 + 1) = 0 := by
    have eq : n - 1 + 1 = n := by omega
    rw [eq]
    exact h.2.1
  have h_a_2 : a (n - 1 + 2) = 1 := by
    have eq : n - 1 + 2 = n + 1 := by omega
    rw [eq]
    exact h.2.2
  have hT0 := trib_bound (n - 1 + 0) (by omega)
  have hT1 := trib_bound (n - 1 + 1) (by omega)
  have hT2 := trib_bound (n - 1 + 2) (by omega)
  have hT3 := trib_bound (n - 1 + 3) (by omega)
  have b0 := a_zero_one_bounds (n - 1 + 0) (by omega) |>.right h_a_0
  rcases b0 with ⟨P0, hP0, hP0a, hP0b, P0_eq⟩
  have hP0_bnd : 2 * P0 ≤ tribonacci (n - 1 + 0) ∧ tribonacci (n - 1 + 0) < 4 * P0 := ⟨by omega, by omega⟩
  have b1 := a_zero_one_bounds (n - 1 + 1) (by omega) |>.left h_a_1
  rcases b1 with ⟨P1, hP1, hP1a, hP1b, P1_eq⟩
  have hP1_bnd : 2 * P1 ≤ tribonacci (n - 1 + 1) ∧ tribonacci (n - 1 + 1) < 4 * P1 := ⟨by omega, by omega⟩
  have b2 := a_zero_one_bounds (n - 1 + 2) (by omega) |>.right h_a_2
  rcases b2 with ⟨P2, hP2, hP2a, hP2b, P2_eq⟩
  have hP2_bnd : 2 * P2 ≤ tribonacci (n - 1 + 2) ∧ tribonacci (n - 1 + 2) < 4 * P2 := ⟨by omega, by omega⟩
  have p1 := P_rel _ _ _ _ _ _ hP0 hP1 hP0_bnd hP1_bnd hT1.1 hT1.2 P0_eq P1_eq
  have p2 := P_rel _ _ _ _ _ _ hP1 hP2 hP1_bnd hP2_bnd hT2.1 hT2.2 P1_eq P2_eq
  have hTeq3 := hT_eq (n - 1 + 3) (by omega)
  exact no_max_0_run_1_large _ _ _ _ _ _ _ hT1.1 hT1.2 hT2.1 hT2.2 hT3.1 hT3.2 hTeq3 ⟨hP0a, hP0b⟩ ⟨hP1a, hP1b⟩ ⟨hP2a, hP2b⟩ p1 p2 hP0

lemma no_max_0_run_2_small (n : Nat) (hn : n ≥ 2) (hn2 : n < 14) : ¬ (a (n-1) = 1 ∧ a (n+0) = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 1) := by
  have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

lemma no_max_0_run_2_large (T0 T1 T2 T3 T4 P0 P1 P2 P3 : Nat)
  (h0 : 1838 * T0 ≤ 1000 * T1) (h0' : 1000 * T1 ≤ 1841 * T0)
  (h1 : 1838 * T1 ≤ 1000 * T2) (h1' : 1000 * T2 ≤ 1841 * T1)
  (h2 : 1838 * T2 ≤ 1000 * T3) (h2' : 1000 * T3 ≤ 1841 * T2)
  (h3 : 1838 * T3 ≤ 1000 * T4) (h3' : 1000 * T4 ≤ 1841 * T3)
  (hT3 : T3 = T0 + T1 + T2)
  (hT4 : T4 = T1 + T2 + T3)
  (a0 : 3 * P0 ≤ T0 ∧ T0 < 4 * P0)
  (a1 : 2 * P1 ≤ T1 ∧ T1 < 3 * P1)
  (a2 : 2 * P2 ≤ T2 ∧ T2 < 3 * P2)
  (a3 : 3 * P3 ≤ T3 ∧ T3 < 4 * P3)
  (p1 : P1 = P0 ∨ P1 = 2 * P0)
  (p2 : P2 = P1 ∨ P2 = 2 * P1)
  (p3 : P3 = P2 ∨ P3 = 2 * P2)
  (hp0 : P0 > 0) : False := by omega

lemma apply_no_max_0_run_2_large (n : Nat) (hn : n ≥ 14) (h : a (n-1) = 1 ∧ a (n+0) = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 1) : False := by
  have h_a_0 : a (n - 1 + 0) = 1 := by
    have eq : n - 1 + 0 = n - 1 := by omega
    rw [eq]
    exact h.1
  have h_a_1 : a (n - 1 + 1) = 0 := by
    have eq : n - 1 + 1 = n := by omega
    rw [eq]
    exact h.2.1
  have h_a_2 : a (n - 1 + 2) = 0 := by
    have eq : n - 1 + 2 = n + 1 := by omega
    rw [eq]
    exact h.2.2.1
  have h_a_3 : a (n - 1 + 3) = 1 := by
    have eq : n - 1 + 3 = n + 2 := by omega
    rw [eq]
    exact h.2.2.2
  have hT0 := trib_bound (n - 1 + 0) (by omega)
  have hT1 := trib_bound (n - 1 + 1) (by omega)
  have hT2 := trib_bound (n - 1 + 2) (by omega)
  have hT3 := trib_bound (n - 1 + 3) (by omega)
  have hT4 := trib_bound (n - 1 + 4) (by omega)
  have b0 := a_zero_one_bounds (n - 1 + 0) (by omega) |>.right h_a_0
  rcases b0 with ⟨P0, hP0, hP0a, hP0b, P0_eq⟩
  have hP0_bnd : 2 * P0 ≤ tribonacci (n - 1 + 0) ∧ tribonacci (n - 1 + 0) < 4 * P0 := ⟨by omega, by omega⟩
  have b1 := a_zero_one_bounds (n - 1 + 1) (by omega) |>.left h_a_1
  rcases b1 with ⟨P1, hP1, hP1a, hP1b, P1_eq⟩
  have hP1_bnd : 2 * P1 ≤ tribonacci (n - 1 + 1) ∧ tribonacci (n - 1 + 1) < 4 * P1 := ⟨by omega, by omega⟩
  have b2 := a_zero_one_bounds (n - 1 + 2) (by omega) |>.left h_a_2
  rcases b2 with ⟨P2, hP2, hP2a, hP2b, P2_eq⟩
  have hP2_bnd : 2 * P2 ≤ tribonacci (n - 1 + 2) ∧ tribonacci (n - 1 + 2) < 4 * P2 := ⟨by omega, by omega⟩
  have b3 := a_zero_one_bounds (n - 1 + 3) (by omega) |>.right h_a_3
  rcases b3 with ⟨P3, hP3, hP3a, hP3b, P3_eq⟩
  have hP3_bnd : 2 * P3 ≤ tribonacci (n - 1 + 3) ∧ tribonacci (n - 1 + 3) < 4 * P3 := ⟨by omega, by omega⟩
  have p1 := P_rel _ _ _ _ _ _ hP0 hP1 hP0_bnd hP1_bnd hT1.1 hT1.2 P0_eq P1_eq
  have p2 := P_rel _ _ _ _ _ _ hP1 hP2 hP1_bnd hP2_bnd hT2.1 hT2.2 P1_eq P2_eq
  have p3 := P_rel _ _ _ _ _ _ hP2 hP3 hP2_bnd hP3_bnd hT3.1 hT3.2 P2_eq P3_eq
  have hTeq3 := hT_eq (n - 1 + 3) (by omega)
  have hTeq4 := hT_eq (n - 1 + 4) (by omega)
  exact no_max_0_run_2_large _ _ _ _ _ _ _ _ _ hT1.1 hT1.2 hT2.1 hT2.2 hT3.1 hT3.2 hT4.1 hT4.2 hTeq3 hTeq4 ⟨hP0a, hP0b⟩ ⟨hP1a, hP1b⟩ ⟨hP2a, hP2b⟩ ⟨hP3a, hP3b⟩ p1 p2 p3 hP0

lemma no_max_0_run_3_small (n : Nat) (hn : n ≥ 2) (hn2 : n < 14) : ¬ (a (n-1) = 1 ∧ a (n+0) = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 0 ∧ a (n+3) = 1) := by
  have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

lemma no_max_0_run_3_large (T0 T1 T2 T3 T4 T5 P0 P1 P2 P3 P4 : Nat)
  (h0 : 1838 * T0 ≤ 1000 * T1) (h0' : 1000 * T1 ≤ 1841 * T0)
  (h1 : 1838 * T1 ≤ 1000 * T2) (h1' : 1000 * T2 ≤ 1841 * T1)
  (h2 : 1838 * T2 ≤ 1000 * T3) (h2' : 1000 * T3 ≤ 1841 * T2)
  (h3 : 1838 * T3 ≤ 1000 * T4) (h3' : 1000 * T4 ≤ 1841 * T3)
  (h4 : 1838 * T4 ≤ 1000 * T5) (h4' : 1000 * T5 ≤ 1841 * T4)
  (hT3 : T3 = T0 + T1 + T2)
  (hT4 : T4 = T1 + T2 + T3)
  (hT5 : T5 = T2 + T3 + T4)
  (a0 : 3 * P0 ≤ T0 ∧ T0 < 4 * P0)
  (a1 : 2 * P1 ≤ T1 ∧ T1 < 3 * P1)
  (a2 : 2 * P2 ≤ T2 ∧ T2 < 3 * P2)
  (a3 : 2 * P3 ≤ T3 ∧ T3 < 3 * P3)
  (a4 : 3 * P4 ≤ T4 ∧ T4 < 4 * P4)
  (p1 : P1 = P0 ∨ P1 = 2 * P0)
  (p2 : P2 = P1 ∨ P2 = 2 * P1)
  (p3 : P3 = P2 ∨ P3 = 2 * P2)
  (p4 : P4 = P3 ∨ P4 = 2 * P3)
  (hp0 : P0 > 0) : False := by omega

lemma apply_no_max_0_run_3_large (n : Nat) (hn : n ≥ 14) (h : a (n-1) = 1 ∧ a (n+0) = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 0 ∧ a (n+3) = 1) : False := by
  have h_a_0 : a (n - 1 + 0) = 1 := by
    have eq : n - 1 + 0 = n - 1 := by omega
    rw [eq]
    exact h.1
  have h_a_1 : a (n - 1 + 1) = 0 := by
    have eq : n - 1 + 1 = n := by omega
    rw [eq]
    exact h.2.1
  have h_a_2 : a (n - 1 + 2) = 0 := by
    have eq : n - 1 + 2 = n + 1 := by omega
    rw [eq]
    exact h.2.2.1
  have h_a_3 : a (n - 1 + 3) = 0 := by
    have eq : n - 1 + 3 = n + 2 := by omega
    rw [eq]
    exact h.2.2.2.1
  have h_a_4 : a (n - 1 + 4) = 1 := by
    have eq : n - 1 + 4 = n + 3 := by omega
    rw [eq]
    exact h.2.2.2.2
  have hT0 := trib_bound (n - 1 + 0) (by omega)
  have hT1 := trib_bound (n - 1 + 1) (by omega)
  have hT2 := trib_bound (n - 1 + 2) (by omega)
  have hT3 := trib_bound (n - 1 + 3) (by omega)
  have hT4 := trib_bound (n - 1 + 4) (by omega)
  have hT5 := trib_bound (n - 1 + 5) (by omega)
  have b0 := a_zero_one_bounds (n - 1 + 0) (by omega) |>.right h_a_0
  rcases b0 with ⟨P0, hP0, hP0a, hP0b, P0_eq⟩
  have hP0_bnd : 2 * P0 ≤ tribonacci (n - 1 + 0) ∧ tribonacci (n - 1 + 0) < 4 * P0 := ⟨by omega, by omega⟩
  have b1 := a_zero_one_bounds (n - 1 + 1) (by omega) |>.left h_a_1
  rcases b1 with ⟨P1, hP1, hP1a, hP1b, P1_eq⟩
  have hP1_bnd : 2 * P1 ≤ tribonacci (n - 1 + 1) ∧ tribonacci (n - 1 + 1) < 4 * P1 := ⟨by omega, by omega⟩
  have b2 := a_zero_one_bounds (n - 1 + 2) (by omega) |>.left h_a_2
  rcases b2 with ⟨P2, hP2, hP2a, hP2b, P2_eq⟩
  have hP2_bnd : 2 * P2 ≤ tribonacci (n - 1 + 2) ∧ tribonacci (n - 1 + 2) < 4 * P2 := ⟨by omega, by omega⟩
  have b3 := a_zero_one_bounds (n - 1 + 3) (by omega) |>.left h_a_3
  rcases b3 with ⟨P3, hP3, hP3a, hP3b, P3_eq⟩
  have hP3_bnd : 2 * P3 ≤ tribonacci (n - 1 + 3) ∧ tribonacci (n - 1 + 3) < 4 * P3 := ⟨by omega, by omega⟩
  have b4 := a_zero_one_bounds (n - 1 + 4) (by omega) |>.right h_a_4
  rcases b4 with ⟨P4, hP4, hP4a, hP4b, P4_eq⟩
  have hP4_bnd : 2 * P4 ≤ tribonacci (n - 1 + 4) ∧ tribonacci (n - 1 + 4) < 4 * P4 := ⟨by omega, by omega⟩
  have p1 := P_rel _ _ _ _ _ _ hP0 hP1 hP0_bnd hP1_bnd hT1.1 hT1.2 P0_eq P1_eq
  have p2 := P_rel _ _ _ _ _ _ hP1 hP2 hP1_bnd hP2_bnd hT2.1 hT2.2 P1_eq P2_eq
  have p3 := P_rel _ _ _ _ _ _ hP2 hP3 hP2_bnd hP3_bnd hT3.1 hT3.2 P2_eq P3_eq
  have p4 := P_rel _ _ _ _ _ _ hP3 hP4 hP3_bnd hP4_bnd hT4.1 hT4.2 P3_eq P4_eq
  have hTeq3 := hT_eq (n - 1 + 3) (by omega)
  have hTeq4 := hT_eq (n - 1 + 4) (by omega)
  have hTeq5 := hT_eq (n - 1 + 5) (by omega)
  exact no_max_0_run_3_large _ _ _ _ _ _ _ _ _ _ _ hT1.1 hT1.2 hT2.1 hT2.2 hT3.1 hT3.2 hT4.1 hT4.2 hT5.1 hT5.2 hTeq3 hTeq4 hTeq5 ⟨hP0a, hP0b⟩ ⟨hP1a, hP1b⟩ ⟨hP2a, hP2b⟩ ⟨hP3a, hP3b⟩ ⟨hP4a, hP4b⟩ p1 p2 p3 p4 hP0

lemma no_max_1_run_1_small (n : Nat) (hn : n ≥ 2) (hn2 : n < 14) : ¬ (a (n-1) = 0 ∧ a (n+0) = 1 ∧ a (n+1) = 0) := by
  have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

lemma no_max_1_run_1_large (T0 T1 T2 T3 P0 P1 P2 : Nat)
  (h0 : 1838 * T0 ≤ 1000 * T1) (h0' : 1000 * T1 ≤ 1841 * T0)
  (h1 : 1838 * T1 ≤ 1000 * T2) (h1' : 1000 * T2 ≤ 1841 * T1)
  (h2 : 1838 * T2 ≤ 1000 * T3) (h2' : 1000 * T3 ≤ 1841 * T2)
  (hT3 : T3 = T0 + T1 + T2)
  (a0 : 2 * P0 ≤ T0 ∧ T0 < 3 * P0)
  (a1 : 3 * P1 ≤ T1 ∧ T1 < 4 * P1)
  (a2 : 2 * P2 ≤ T2 ∧ T2 < 3 * P2)
  (p1 : P1 = P0 ∨ P1 = 2 * P0)
  (p2 : P2 = P1 ∨ P2 = 2 * P1)
  (hp0 : P0 > 0) : False := by omega

lemma apply_no_max_1_run_1_large (n : Nat) (hn : n ≥ 14) (h : a (n-1) = 0 ∧ a (n+0) = 1 ∧ a (n+1) = 0) : False := by
  have h_a_0 : a (n - 1 + 0) = 0 := by
    have eq : n - 1 + 0 = n - 1 := by omega
    rw [eq]
    exact h.1
  have h_a_1 : a (n - 1 + 1) = 1 := by
    have eq : n - 1 + 1 = n := by omega
    rw [eq]
    exact h.2.1
  have h_a_2 : a (n - 1 + 2) = 0 := by
    have eq : n - 1 + 2 = n + 1 := by omega
    rw [eq]
    exact h.2.2
  have hT0 := trib_bound (n - 1 + 0) (by omega)
  have hT1 := trib_bound (n - 1 + 1) (by omega)
  have hT2 := trib_bound (n - 1 + 2) (by omega)
  have hT3 := trib_bound (n - 1 + 3) (by omega)
  have b0 := a_zero_one_bounds (n - 1 + 0) (by omega) |>.left h_a_0
  rcases b0 with ⟨P0, hP0, hP0a, hP0b, P0_eq⟩
  have hP0_bnd : 2 * P0 ≤ tribonacci (n - 1 + 0) ∧ tribonacci (n - 1 + 0) < 4 * P0 := ⟨by omega, by omega⟩
  have b1 := a_zero_one_bounds (n - 1 + 1) (by omega) |>.right h_a_1
  rcases b1 with ⟨P1, hP1, hP1a, hP1b, P1_eq⟩
  have hP1_bnd : 2 * P1 ≤ tribonacci (n - 1 + 1) ∧ tribonacci (n - 1 + 1) < 4 * P1 := ⟨by omega, by omega⟩
  have b2 := a_zero_one_bounds (n - 1 + 2) (by omega) |>.left h_a_2
  rcases b2 with ⟨P2, hP2, hP2a, hP2b, P2_eq⟩
  have hP2_bnd : 2 * P2 ≤ tribonacci (n - 1 + 2) ∧ tribonacci (n - 1 + 2) < 4 * P2 := ⟨by omega, by omega⟩
  have p1 := P_rel _ _ _ _ _ _ hP0 hP1 hP0_bnd hP1_bnd hT1.1 hT1.2 P0_eq P1_eq
  have p2 := P_rel _ _ _ _ _ _ hP1 hP2 hP1_bnd hP2_bnd hT2.1 hT2.2 P1_eq P2_eq
  have hTeq3 := hT_eq (n - 1 + 3) (by omega)
  exact no_max_1_run_1_large _ _ _ _ _ _ _ hT1.1 hT1.2 hT2.1 hT2.2 hT3.1 hT3.2 hTeq3 ⟨hP0a, hP0b⟩ ⟨hP1a, hP1b⟩ ⟨hP2a, hP2b⟩ p1 p2 hP0

lemma no_max_1_run_2_small (n : Nat) (hn : n ≥ 2) (hn2 : n < 14) : ¬ (a (n-1) = 0 ∧ a (n+0) = 1 ∧ a (n+1) = 1 ∧ a (n+2) = 0) := by
  have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

lemma no_max_1_run_2_large (T0 T1 T2 T3 T4 P0 P1 P2 P3 : Nat)
  (h0 : 1838 * T0 ≤ 1000 * T1) (h0' : 1000 * T1 ≤ 1841 * T0)
  (h1 : 1838 * T1 ≤ 1000 * T2) (h1' : 1000 * T2 ≤ 1841 * T1)
  (h2 : 1838 * T2 ≤ 1000 * T3) (h2' : 1000 * T3 ≤ 1841 * T2)
  (h3 : 1838 * T3 ≤ 1000 * T4) (h3' : 1000 * T4 ≤ 1841 * T3)
  (hT3 : T3 = T0 + T1 + T2)
  (hT4 : T4 = T1 + T2 + T3)
  (a0 : 2 * P0 ≤ T0 ∧ T0 < 3 * P0)
  (a1 : 3 * P1 ≤ T1 ∧ T1 < 4 * P1)
  (a2 : 3 * P2 ≤ T2 ∧ T2 < 4 * P2)
  (a3 : 2 * P3 ≤ T3 ∧ T3 < 3 * P3)
  (p1 : P1 = P0 ∨ P1 = 2 * P0)
  (p2 : P2 = P1 ∨ P2 = 2 * P1)
  (p3 : P3 = P2 ∨ P3 = 2 * P2)
  (hp0 : P0 > 0) : False := by omega

lemma apply_no_max_1_run_2_large (n : Nat) (hn : n ≥ 14) (h : a (n-1) = 0 ∧ a (n+0) = 1 ∧ a (n+1) = 1 ∧ a (n+2) = 0) : False := by
  have h_a_0 : a (n - 1 + 0) = 0 := by
    have eq : n - 1 + 0 = n - 1 := by omega
    rw [eq]
    exact h.1
  have h_a_1 : a (n - 1 + 1) = 1 := by
    have eq : n - 1 + 1 = n := by omega
    rw [eq]
    exact h.2.1
  have h_a_2 : a (n - 1 + 2) = 1 := by
    have eq : n - 1 + 2 = n + 1 := by omega
    rw [eq]
    exact h.2.2.1
  have h_a_3 : a (n - 1 + 3) = 0 := by
    have eq : n - 1 + 3 = n + 2 := by omega
    rw [eq]
    exact h.2.2.2
  have hT0 := trib_bound (n - 1 + 0) (by omega)
  have hT1 := trib_bound (n - 1 + 1) (by omega)
  have hT2 := trib_bound (n - 1 + 2) (by omega)
  have hT3 := trib_bound (n - 1 + 3) (by omega)
  have hT4 := trib_bound (n - 1 + 4) (by omega)
  have b0 := a_zero_one_bounds (n - 1 + 0) (by omega) |>.left h_a_0
  rcases b0 with ⟨P0, hP0, hP0a, hP0b, P0_eq⟩
  have hP0_bnd : 2 * P0 ≤ tribonacci (n - 1 + 0) ∧ tribonacci (n - 1 + 0) < 4 * P0 := ⟨by omega, by omega⟩
  have b1 := a_zero_one_bounds (n - 1 + 1) (by omega) |>.right h_a_1
  rcases b1 with ⟨P1, hP1, hP1a, hP1b, P1_eq⟩
  have hP1_bnd : 2 * P1 ≤ tribonacci (n - 1 + 1) ∧ tribonacci (n - 1 + 1) < 4 * P1 := ⟨by omega, by omega⟩
  have b2 := a_zero_one_bounds (n - 1 + 2) (by omega) |>.right h_a_2
  rcases b2 with ⟨P2, hP2, hP2a, hP2b, P2_eq⟩
  have hP2_bnd : 2 * P2 ≤ tribonacci (n - 1 + 2) ∧ tribonacci (n - 1 + 2) < 4 * P2 := ⟨by omega, by omega⟩
  have b3 := a_zero_one_bounds (n - 1 + 3) (by omega) |>.left h_a_3
  rcases b3 with ⟨P3, hP3, hP3a, hP3b, P3_eq⟩
  have hP3_bnd : 2 * P3 ≤ tribonacci (n - 1 + 3) ∧ tribonacci (n - 1 + 3) < 4 * P3 := ⟨by omega, by omega⟩
  have p1 := P_rel _ _ _ _ _ _ hP0 hP1 hP0_bnd hP1_bnd hT1.1 hT1.2 P0_eq P1_eq
  have p2 := P_rel _ _ _ _ _ _ hP1 hP2 hP1_bnd hP2_bnd hT2.1 hT2.2 P1_eq P2_eq
  have p3 := P_rel _ _ _ _ _ _ hP2 hP3 hP2_bnd hP3_bnd hT3.1 hT3.2 P2_eq P3_eq
  have hTeq3 := hT_eq (n - 1 + 3) (by omega)
  have hTeq4 := hT_eq (n - 1 + 4) (by omega)
  exact no_max_1_run_2_large _ _ _ _ _ _ _ _ _ hT1.1 hT1.2 hT2.1 hT2.2 hT3.1 hT3.2 hT4.1 hT4.2 hTeq3 hTeq4 ⟨hP0a, hP0b⟩ ⟨hP1a, hP1b⟩ ⟨hP2a, hP2b⟩ ⟨hP3a, hP3b⟩ p1 p2 p3 hP0

lemma no_any_0_run_6_small (n : Nat) (hn : n ≥ 2) (hn2 : n < 14) : ¬ (a (n+0) = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 0 ∧ a (n+3) = 0 ∧ a (n+4) = 0 ∧ a (n+5) = 0) := by
  have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

lemma no_any_0_run_6_large (T0 T1 T2 T3 T4 T5 T6 P0 P1 P2 P3 P4 P5 : Nat)
  (h0 : 1838 * T0 ≤ 1000 * T1) (h0' : 1000 * T1 ≤ 1841 * T0)
  (h1 : 1838 * T1 ≤ 1000 * T2) (h1' : 1000 * T2 ≤ 1841 * T1)
  (h2 : 1838 * T2 ≤ 1000 * T3) (h2' : 1000 * T3 ≤ 1841 * T2)
  (h3 : 1838 * T3 ≤ 1000 * T4) (h3' : 1000 * T4 ≤ 1841 * T3)
  (h4 : 1838 * T4 ≤ 1000 * T5) (h4' : 1000 * T5 ≤ 1841 * T4)
  (h5 : 1838 * T5 ≤ 1000 * T6) (h5' : 1000 * T6 ≤ 1841 * T5)
  (hT3 : T3 = T0 + T1 + T2)
  (hT4 : T4 = T1 + T2 + T3)
  (hT5 : T5 = T2 + T3 + T4)
  (hT6 : T6 = T3 + T4 + T5)
  (a0 : 2 * P0 ≤ T0 ∧ T0 < 3 * P0)
  (a1 : 2 * P1 ≤ T1 ∧ T1 < 3 * P1)
  (a2 : 2 * P2 ≤ T2 ∧ T2 < 3 * P2)
  (a3 : 2 * P3 ≤ T3 ∧ T3 < 3 * P3)
  (a4 : 2 * P4 ≤ T4 ∧ T4 < 3 * P4)
  (a5 : 2 * P5 ≤ T5 ∧ T5 < 3 * P5)
  (p1 : P1 = P0 ∨ P1 = 2 * P0)
  (p2 : P2 = P1 ∨ P2 = 2 * P1)
  (p3 : P3 = P2 ∨ P3 = 2 * P2)
  (p4 : P4 = P3 ∨ P4 = 2 * P3)
  (p5 : P5 = P4 ∨ P5 = 2 * P4)
  (hp0 : P0 > 0) : False := by omega

lemma apply_no_any_0_run_6_large (n : Nat) (hn : n ≥ 14) (h : a (n+0) = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 0 ∧ a (n+3) = 0 ∧ a (n+4) = 0 ∧ a (n+5) = 0) : False := by
  have h_a_0 : a (n + 0) = 0 := h.1
  have h_a_1 : a (n + 1) = 0 := h.2.1
  have h_a_2 : a (n + 2) = 0 := h.2.2.1
  have h_a_3 : a (n + 3) = 0 := h.2.2.2.1
  have h_a_4 : a (n + 4) = 0 := h.2.2.2.2.1
  have h_a_5 : a (n + 5) = 0 := h.2.2.2.2.2
  have hT0 := trib_bound (n + 0) (by omega)
  have hT1 := trib_bound (n + 1) (by omega)
  have hT2 := trib_bound (n + 2) (by omega)
  have hT3 := trib_bound (n + 3) (by omega)
  have hT4 := trib_bound (n + 4) (by omega)
  have hT5 := trib_bound (n + 5) (by omega)
  have hT6 := trib_bound (n + 6) (by omega)
  have b0 := a_zero_one_bounds (n+0) (by omega) |>.left h_a_0
  rcases b0 with ⟨P0, hP0, hP0a, hP0b, P0_eq⟩
  have hP0_bnd : 2 * P0 ≤ tribonacci (n+0) ∧ tribonacci (n+0) < 4 * P0 := ⟨by omega, by omega⟩
  have b1 := a_zero_one_bounds (n+1) (by omega) |>.left h_a_1
  rcases b1 with ⟨P1, hP1, hP1a, hP1b, P1_eq⟩
  have hP1_bnd : 2 * P1 ≤ tribonacci (n+1) ∧ tribonacci (n+1) < 4 * P1 := ⟨by omega, by omega⟩
  have b2 := a_zero_one_bounds (n+2) (by omega) |>.left h_a_2
  rcases b2 with ⟨P2, hP2, hP2a, hP2b, P2_eq⟩
  have hP2_bnd : 2 * P2 ≤ tribonacci (n+2) ∧ tribonacci (n+2) < 4 * P2 := ⟨by omega, by omega⟩
  have b3 := a_zero_one_bounds (n+3) (by omega) |>.left h_a_3
  rcases b3 with ⟨P3, hP3, hP3a, hP3b, P3_eq⟩
  have hP3_bnd : 2 * P3 ≤ tribonacci (n+3) ∧ tribonacci (n+3) < 4 * P3 := ⟨by omega, by omega⟩
  have b4 := a_zero_one_bounds (n+4) (by omega) |>.left h_a_4
  rcases b4 with ⟨P4, hP4, hP4a, hP4b, P4_eq⟩
  have hP4_bnd : 2 * P4 ≤ tribonacci (n+4) ∧ tribonacci (n+4) < 4 * P4 := ⟨by omega, by omega⟩
  have b5 := a_zero_one_bounds (n+5) (by omega) |>.left h_a_5
  rcases b5 with ⟨P5, hP5, hP5a, hP5b, P5_eq⟩
  have hP5_bnd : 2 * P5 ≤ tribonacci (n+5) ∧ tribonacci (n+5) < 4 * P5 := ⟨by omega, by omega⟩
  have p1 := P_rel _ _ _ _ _ _ hP0 hP1 hP0_bnd hP1_bnd hT1.1 hT1.2 P0_eq P1_eq
  have p2 := P_rel _ _ _ _ _ _ hP1 hP2 hP1_bnd hP2_bnd hT2.1 hT2.2 P1_eq P2_eq
  have p3 := P_rel _ _ _ _ _ _ hP2 hP3 hP2_bnd hP3_bnd hT3.1 hT3.2 P2_eq P3_eq
  have p4 := P_rel _ _ _ _ _ _ hP3 hP4 hP3_bnd hP4_bnd hT4.1 hT4.2 P3_eq P4_eq
  have p5 := P_rel _ _ _ _ _ _ hP4 hP5 hP4_bnd hP5_bnd hT5.1 hT5.2 P4_eq P5_eq
  have hTeq3 := hT_eq (n+3) (by omega)
  have hTeq4 := hT_eq (n+4) (by omega)
  have hTeq5 := hT_eq (n+5) (by omega)
  have hTeq6 := hT_eq (n+6) (by omega)
  exact no_any_0_run_6_large _ _ _ _ _ _ _ _ _ _ _ _ _ hT1.1 hT1.2 hT2.1 hT2.2 hT3.1 hT3.2 hT4.1 hT4.2 hT5.1 hT5.2 hT6.1 hT6.2 hTeq3 hTeq4 hTeq5 hTeq6 ⟨hP0a, hP0b⟩ ⟨hP1a, hP1b⟩ ⟨hP2a, hP2b⟩ ⟨hP3a, hP3b⟩ ⟨hP4a, hP4b⟩ ⟨hP5a, hP5b⟩ p1 p2 p3 p4 p5 hP0

lemma no_any_1_run_5_small (n : Nat) (hn : n ≥ 2) (hn2 : n < 14) : ¬ (a (n+0) = 1 ∧ a (n+1) = 1 ∧ a (n+2) = 1 ∧ a (n+3) = 1 ∧ a (n+4) = 1) := by
  have : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

lemma no_any_1_run_5_large (T0 T1 T2 T3 T4 T5 P0 P1 P2 P3 P4 : Nat)
  (h0 : 1838 * T0 ≤ 1000 * T1) (h0' : 1000 * T1 ≤ 1841 * T0)
  (h1 : 1838 * T1 ≤ 1000 * T2) (h1' : 1000 * T2 ≤ 1841 * T1)
  (h2 : 1838 * T2 ≤ 1000 * T3) (h2' : 1000 * T3 ≤ 1841 * T2)
  (h3 : 1838 * T3 ≤ 1000 * T4) (h3' : 1000 * T4 ≤ 1841 * T3)
  (h4 : 1838 * T4 ≤ 1000 * T5) (h4' : 1000 * T5 ≤ 1841 * T4)
  (hT3 : T3 = T0 + T1 + T2)
  (hT4 : T4 = T1 + T2 + T3)
  (hT5 : T5 = T2 + T3 + T4)
  (a0 : 3 * P0 ≤ T0 ∧ T0 < 4 * P0)
  (a1 : 3 * P1 ≤ T1 ∧ T1 < 4 * P1)
  (a2 : 3 * P2 ≤ T2 ∧ T2 < 4 * P2)
  (a3 : 3 * P3 ≤ T3 ∧ T3 < 4 * P3)
  (a4 : 3 * P4 ≤ T4 ∧ T4 < 4 * P4)
  (p1 : P1 = P0 ∨ P1 = 2 * P0)
  (p2 : P2 = P1 ∨ P2 = 2 * P1)
  (p3 : P3 = P2 ∨ P3 = 2 * P2)
  (p4 : P4 = P3 ∨ P4 = 2 * P3)
  (hp0 : P0 > 0) : False := by omega

lemma apply_no_any_1_run_5_large (n : Nat) (hn : n ≥ 14) (h : a (n+0) = 1 ∧ a (n+1) = 1 ∧ a (n+2) = 1 ∧ a (n+3) = 1 ∧ a (n+4) = 1) : False := by
  have h_a_0 : a (n + 0) = 1 := h.1
  have h_a_1 : a (n + 1) = 1 := h.2.1
  have h_a_2 : a (n + 2) = 1 := h.2.2.1
  have h_a_3 : a (n + 3) = 1 := h.2.2.2.1
  have h_a_4 : a (n + 4) = 1 := h.2.2.2.2
  have hT0 := trib_bound (n + 0) (by omega)
  have hT1 := trib_bound (n + 1) (by omega)
  have hT2 := trib_bound (n + 2) (by omega)
  have hT3 := trib_bound (n + 3) (by omega)
  have hT4 := trib_bound (n + 4) (by omega)
  have hT5 := trib_bound (n + 5) (by omega)
  have b0 := a_zero_one_bounds (n+0) (by omega) |>.right h_a_0
  rcases b0 with ⟨P0, hP0, hP0a, hP0b, P0_eq⟩
  have hP0_bnd : 2 * P0 ≤ tribonacci (n+0) ∧ tribonacci (n+0) < 4 * P0 := ⟨by omega, by omega⟩
  have b1 := a_zero_one_bounds (n+1) (by omega) |>.right h_a_1
  rcases b1 with ⟨P1, hP1, hP1a, hP1b, P1_eq⟩
  have hP1_bnd : 2 * P1 ≤ tribonacci (n+1) ∧ tribonacci (n+1) < 4 * P1 := ⟨by omega, by omega⟩
  have b2 := a_zero_one_bounds (n+2) (by omega) |>.right h_a_2
  rcases b2 with ⟨P2, hP2, hP2a, hP2b, P2_eq⟩
  have hP2_bnd : 2 * P2 ≤ tribonacci (n+2) ∧ tribonacci (n+2) < 4 * P2 := ⟨by omega, by omega⟩
  have b3 := a_zero_one_bounds (n+3) (by omega) |>.right h_a_3
  rcases b3 with ⟨P3, hP3, hP3a, hP3b, P3_eq⟩
  have hP3_bnd : 2 * P3 ≤ tribonacci (n+3) ∧ tribonacci (n+3) < 4 * P3 := ⟨by omega, by omega⟩
  have b4 := a_zero_one_bounds (n+4) (by omega) |>.right h_a_4
  rcases b4 with ⟨P4, hP4, hP4a, hP4b, P4_eq⟩
  have hP4_bnd : 2 * P4 ≤ tribonacci (n+4) ∧ tribonacci (n+4) < 4 * P4 := ⟨by omega, by omega⟩
  have p1 := P_rel _ _ _ _ _ _ hP0 hP1 hP0_bnd hP1_bnd hT1.1 hT1.2 P0_eq P1_eq
  have p2 := P_rel _ _ _ _ _ _ hP1 hP2 hP1_bnd hP2_bnd hT2.1 hT2.2 P1_eq P2_eq
  have p3 := P_rel _ _ _ _ _ _ hP2 hP3 hP2_bnd hP3_bnd hT3.1 hT3.2 P2_eq P3_eq
  have p4 := P_rel _ _ _ _ _ _ hP3 hP4 hP3_bnd hP4_bnd hT4.1 hT4.2 P3_eq P4_eq
  have hTeq3 := hT_eq (n+3) (by omega)
  have hTeq4 := hT_eq (n+4) (by omega)
  have hTeq5 := hT_eq (n+5) (by omega)
  exact no_any_1_run_5_large _ _ _ _ _ _ _ _ _ _ _ hT1.1 hT1.2 hT2.1 hT2.2 hT3.1 hT3.2 hT4.1 hT4.2 hT5.1 hT5.2 hTeq3 hTeq4 hTeq5 ⟨hP0a, hP0b⟩ ⟨hP1a, hP1b⟩ ⟨hP2a, hP2b⟩ ⟨hP3a, hP3b⟩ ⟨hP4a, hP4b⟩ p1 p2 p3 p4 hP0

theorem oeis_271591_conjecture_0 :
  (∀ n L, is_maximal_run 0 n L → (L = 4 ∨ L = 5)) ∧
  (∀ n L, is_maximal_run 1 n L → (L = 3 ∨ L = 4)) := by
  constructor
  · intro n L h
    have hL_ge_1 : L ≥ 1 := h.2.1
    have h_cases : L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5 ∨ L ≥ 6 := by omega
    rcases h_cases with rfl | rfl | rfl | rfl | rfl | hL6
    · have h_unfold : a (n-1) = 1 ∧ a n = 0 ∧ a (n+1) = 1 := by
        rcases h with ⟨h2, _, hAll, hNext, hPrev⟩
        have a0 := hAll 0 (by decide); rw [Nat.add_zero] at a0
        have p0 := a_not_zero_eq_one (n-1) |>.mp hPrev
        have n0 := a_not_zero_eq_one (n+1) |>.mp hNext
        exact ⟨p0, a0, n0⟩
      have hn_cases : n < 14 ∨ n ≥ 14 := by omega
      rcases hn_cases with hn_small | hn_large
      · exfalso; exact no_max_0_run_1_small n h.1 hn_small h_unfold
      · exfalso; exact apply_no_max_0_run_1_large n hn_large h_unfold
    · have h_unfold : a (n-1) = 1 ∧ a n = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 1 := by
        rcases h with ⟨h2, _, hAll, hNext, hPrev⟩
        have a0 := hAll 0 (by decide); rw [Nat.add_zero] at a0
        have a1 := hAll 1 (by decide)
        have p0 := a_not_zero_eq_one (n-1) |>.mp hPrev
        have n0 := a_not_zero_eq_one (n+2) |>.mp hNext
        exact ⟨p0, a0, a1, n0⟩
      have hn_cases : n < 14 ∨ n ≥ 14 := by omega
      rcases hn_cases with hn_small | hn_large
      · exfalso; exact no_max_0_run_2_small n h.1 hn_small h_unfold
      · exfalso; exact apply_no_max_0_run_2_large n hn_large h_unfold
    · have h_unfold : a (n-1) = 1 ∧ a n = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 0 ∧ a (n+3) = 1 := by
        rcases h with ⟨h2, _, hAll, hNext, hPrev⟩
        have a0 := hAll 0 (by decide); rw [Nat.add_zero] at a0
        have a1 := hAll 1 (by decide)
        have a2 := hAll 2 (by decide)
        have p0 := a_not_zero_eq_one (n-1) |>.mp hPrev
        have n0 := a_not_zero_eq_one (n+3) |>.mp hNext
        exact ⟨p0, a0, a1, a2, n0⟩
      have hn_cases : n < 14 ∨ n ≥ 14 := by omega
      rcases hn_cases with hn_small | hn_large
      · exfalso; exact no_max_0_run_3_small n h.1 hn_small h_unfold
      · exfalso; exact apply_no_max_0_run_3_large n hn_large h_unfold
    · left; rfl
    · right; rfl
    · have h_unfold : a n = 0 ∧ a (n+1) = 0 ∧ a (n+2) = 0 ∧ a (n+3) = 0 ∧ a (n+4) = 0 ∧ a (n+5) = 0 := by
        rcases h with ⟨h2, _, hAll, _, _⟩
        have a0 := hAll 0 (by omega); rw [Nat.add_zero] at a0
        exact ⟨a0, hAll 1 (by omega), hAll 2 (by omega), hAll 3 (by omega), hAll 4 (by omega), hAll 5 (by omega)⟩
      have hn_cases : n < 14 ∨ n ≥ 14 := by omega
      rcases hn_cases with hn_small | hn_large
      · exfalso; exact no_any_0_run_6_small n h.1 hn_small h_unfold
      · exfalso; exact apply_no_any_0_run_6_large n hn_large h_unfold

  · intro n L h
    have hL_ge_1 : L ≥ 1 := h.2.1
    have h_cases : L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 ∨ L ≥ 5 := by omega
    rcases h_cases with rfl | rfl | rfl | rfl | hL5
    · have h_unfold : a (n-1) = 0 ∧ a n = 1 ∧ a (n+1) = 0 := by
        rcases h with ⟨h2, _, hAll, hNext, hPrev⟩
        have a0 := hAll 0 (by decide); rw [Nat.add_zero] at a0
        have p0 := a_not_one_eq_zero (n-1) |>.mp hPrev
        have n0 := a_not_one_eq_zero (n+1) |>.mp hNext
        exact ⟨p0, a0, n0⟩
      have hn_cases : n < 14 ∨ n ≥ 14 := by omega
      rcases hn_cases with hn_small | hn_large
      · exfalso; exact no_max_1_run_1_small n h.1 hn_small h_unfold
      · exfalso; exact apply_no_max_1_run_1_large n hn_large h_unfold
    · have h_unfold : a (n-1) = 0 ∧ a n = 1 ∧ a (n+1) = 1 ∧ a (n+2) = 0 := by
        rcases h with ⟨h2, _, hAll, hNext, hPrev⟩
        have a0 := hAll 0 (by decide); rw [Nat.add_zero] at a0
        have a1 := hAll 1 (by decide)
        have p0 := a_not_one_eq_zero (n-1) |>.mp hPrev
        have n0 := a_not_one_eq_zero (n+2) |>.mp hNext
        exact ⟨p0, a0, a1, n0⟩
      have hn_cases : n < 14 ∨ n ≥ 14 := by omega
      rcases hn_cases with hn_small | hn_large
      · exfalso; exact no_max_1_run_2_small n h.1 hn_small h_unfold
      · exfalso; exact apply_no_max_1_run_2_large n hn_large h_unfold
    · left; rfl
    · right; rfl
    · have h_unfold : a n = 1 ∧ a (n+1) = 1 ∧ a (n+2) = 1 ∧ a (n+3) = 1 ∧ a (n+4) = 1 := by
        rcases h with ⟨h2, _, hAll, _, _⟩
        have a0 := hAll 0 (by omega); rw [Nat.add_zero] at a0
        exact ⟨a0, hAll 1 (by omega), hAll 2 (by omega), hAll 3 (by omega), hAll 4 (by omega)⟩
      have hn_cases : n < 14 ∨ n ≥ 14 := by omega
      rcases hn_cases with hn_small | hn_large
      · exfalso; exact no_any_1_run_5_small n h.1 hn_small h_unfold
      · exfalso; exact apply_no_any_1_run_5_large n hn_large h_unfold

theorem oeis_271591_conjecture_0.disproof : ¬ (type_of% @oeis_271591_conjecture_0) := sorry
