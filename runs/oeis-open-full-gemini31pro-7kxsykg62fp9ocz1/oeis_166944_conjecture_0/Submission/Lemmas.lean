import Submission.Spec
import Mathlib

lemma a_val {n : ℕ} (hn : 1 ≤ n) : a (n + 1) =
  if (n + 1) % 2 = 0 then
    a n + Nat.gcd (n + 1) (a n)
  else
    a n + Nat.gcd (n - 1) (a n) := by
  cases n with
  | zero => contradiction
  | succ m => rfl

lemma a_ge_n : ∀ n, n ≤ a n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; decide
    · have h1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      rw [a_val h1]
      split_ifs with h_even
      · calc n + 1 ≤ a n + 1 := Nat.add_le_add_right ih 1
        _ ≤ a n + Nat.gcd (n + 1) (a n) := Nat.add_le_add_left (Nat.gcd_pos_of_pos_left (a n) (by omega)) _
      · have h_n_minus_1_pos : 0 < n - 1 := by omega
        calc n + 1 ≤ a n + 1 := Nat.add_le_add_right ih 1
        _ ≤ a n + Nat.gcd (n - 1) (a n) := Nat.add_le_add_left (Nat.gcd_pos_of_pos_left (a n) h_n_minus_1_pos) _

def C (n : ℕ) : ℕ := a n - n

lemma a_eq_C_add_n (n : ℕ) : a n = C n + n := by
  rw [C, Nat.sub_add_cancel (a_ge_n n)]

lemma C_val {n : ℕ} (hn : 1 ≤ n) : C (n + 1) =
  if (n + 1) % 2 = 0 then
    C n + Nat.gcd (n + 1) (a n) - 1
  else
    C n + Nat.gcd (n - 1) (a n) - 1 := by
  rw [C, a_val hn]
  split_ifs with h_even
  · have h_gcd_pos : 1 ≤ Nat.gcd (n + 1) (a n) := Nat.gcd_pos_of_pos_left (a n) (by omega)
    have h_a_ge_n : n ≤ a n := a_ge_n n
    have h_C : C n = a n - n := rfl
    omega
  · have h_n_minus_1_pos : 0 < n - 1 := by omega
    have h_gcd_pos : 1 ≤ Nat.gcd (n - 1) (a n) := Nat.gcd_pos_of_pos_left (a n) h_n_minus_1_pos
    have h_a_ge_n : n ≤ a n := a_ge_n n
    have h_C : C n = a n - n := rfl
    omega

lemma C_ge_one : ∀ n, 1 ≤ n → 1 ≤ C n := by
  intro n
  induction n with
  | zero => intro h; contradiction
  | succ n ih =>
    intro h
    by_cases hn : n = 0
    · subst hn; decide
    · have h1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have ih1 : 1 ≤ C n := ih h1
      rw [C_val h1]
      split_ifs with h_even
      · have h_gcd_pos : 1 ≤ Nat.gcd (n + 1) (a n) := Nat.gcd_pos_of_pos_left (a n) (by omega)
        omega
      · have h_n_minus_1_pos : 0 < n - 1 := by omega
        have h_gcd_pos : 1 ≤ Nat.gcd (n - 1) (a n) := Nat.gcd_pos_of_pos_left (a n) h_n_minus_1_pos
        omega

lemma gcd_even_step {n : ℕ} (hn : 1 ≤ n) : Nat.gcd (n + 1) (a n) = Nat.gcd (n + 1) (C n - 1) := by
  have h_C : 1 ≤ C n := C_ge_one n hn
  have h_a : a n = C n - 1 + (n + 1) := by
    have : a n = C n + n := a_eq_C_add_n n
    omega
  rw [h_a]
  rw [Nat.gcd_add_self_right]

lemma gcd_odd_step {n : ℕ} (hn : 1 ≤ n) (h_even : ¬ (n + 1) % 2 = 0) : Nat.gcd (n - 1) (a n) = Nat.gcd (n - 1) (C n + 1) := by
  have h_n : 1 ≤ n := hn
  have h_a : a n = C n + 1 + (n - 1) := by
    have : a n = C n + n := a_eq_C_add_n n
    have : 2 ≤ n := by omega
    omega
  rw [h_a]
  rw [Nat.gcd_add_self_right]

lemma C_rec {n : ℕ} (hn : 1 ≤ n) : C (n + 1) =
  if h : (n + 1) % 2 = 0 then
    C n + Nat.gcd (n + 1) (C n - 1) - 1
  else
    C n + Nat.gcd (n - 1) (C n + 1) - 1 := by
  rw [C_val hn]
  split_ifs with h_even
  · rw [gcd_even_step hn]
  · rw [gcd_odd_step hn h_even]

lemma d_val {n : ℕ} (hn : 1 ≤ n) : d (n + 1) =
  if (n + 1) % 2 = 0 then
    Nat.gcd (n + 1) (C n - 1)
  else
    Nat.gcd (n - 1) (C n + 1) := by
  have hd : d (n + 1) = a (n + 1) - a n := by
    unfold d
    have : n + 1 - 1 = n := rfl
    rw [this]
  rw [hd, a_eq_C_add_n (n + 1), a_eq_C_add_n n]
  have h_C1 : C (n + 1) =
    if h : (n + 1) % 2 = 0 then
      C n + Nat.gcd (n + 1) (C n - 1) - 1
    else
      C n + Nat.gcd (n - 1) (C n + 1) - 1 := C_rec hn
  split_ifs with h_even
  · rw [h_C1, dif_pos h_even]
    have : 1 ≤ Nat.gcd (n + 1) (C n - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
    omega
  · rw [h_C1, dif_neg h_even]
    have : 0 < n - 1 := by omega
    have : 1 ≤ Nat.gcd (n - 1) (C n + 1) := Nat.gcd_pos_of_pos_left _ this
    omega

lemma C_mono {n : ℕ} (hn : 1 ≤ n) : C n ≤ C (n + 1) := by
  have h_C1 : C (n + 1) =
    if h : (n + 1) % 2 = 0 then
      C n + Nat.gcd (n + 1) (C n - 1) - 1
    else
      C n + Nat.gcd (n - 1) (C n + 1) - 1 := C_rec hn
  split_ifs at h_C1 with h_even
  · rw [h_C1]
    have : 1 ≤ Nat.gcd (n + 1) (C n - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
    omega
  · rw [h_C1]
    have : 0 < n - 1 := by omega
    have : 1 ≤ Nat.gcd (n - 1) (C n + 1) := Nat.gcd_pos_of_pos_left _ this
    omega

lemma C_mono_le {n m : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ m) : C n ≤ C m := by
  induction m, h2 using Nat.le_induction with
  | base => exact le_refl _
  | succ k hk ih =>
    have : 1 ≤ k := by omega
    exact le_trans ih (C_mono this)
