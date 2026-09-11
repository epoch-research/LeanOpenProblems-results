import FormalConjectures.Util.ProblemImports

open Nat Classical

def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)
    if h_ex : ∃ k, P k then
      have HP : DecidablePred P := by infer_instance
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

@[simp] def S : List ℕ → ℕ
| [] => 0
| d :: ds => d + S ds

@[simp] def W : List ℕ → ℕ
| [] => 0
| _ :: ds => S ds + W ds

@[simp] def val : List ℕ → ℕ
| [] => 0
| d :: ds => d + 10 * val ds

@[simp] theorem S_append (A B : List ℕ) : S (A ++ B) = S A + S B := by
  induction A <;> simp [*]; omega

@[simp] theorem S_reverse (D : List ℕ) : S D.reverse = S D := by
  induction D <;> simp [*]; omega

@[simp] theorem W_append (A B : List ℕ) : W (A ++ B) = W A + W B + A.length * S B := by
  induction A with
  | nil => simp
  | cons a as ih => simp [ih]; ring

theorem W_reverse_add_W (D : List ℕ) (h : D ≠ []) : W D + W D.reverse = (D.length - 1) * S D := by
  induction D with
  | nil => contradiction
  | cons d ds ih =>
    by_cases hds : ds = []
    · simp [hds]
    · have := ih hds
      calc W (d :: ds) + W (d :: ds).reverse
        _ = S ds + W ds + W (ds.reverse ++ [d]) := by simp
        _ = S ds + W ds + (W ds.reverse + W [d] + ds.reverse.length * S [d]) := by rw [W_append]
        _ = S ds + W ds + (W ds.reverse + 0 + ds.length * d) := by simp
        _ = S ds + (W ds + W ds.reverse) + ds.length * d := by omega
        _ = S ds + (ds.length - 1) * S ds + ds.length * d := by rw [this]
        _ = ((d :: ds).length - 1) * S (d :: ds) := by
          have h1 : ds.length ≥ 1 := List.length_pos_of_ne_nil hds
          generalize hl : ds.length = L
          rcases L with _ | k
          · omega
          · have : (k + 1 - 1) = k := by rfl
            simp [hl, this]
            ring

theorem val_mod_81 (D : List ℕ) : val D ≡ S D + 9 * W D [MOD 81] := by
  induction D with
  | nil => rfl
  | cons d ds ih =>
    calc d + 10 * val ds
      _ ≡ d + 10 * (S ds + 9 * W ds) [MOD 81] := Nat.ModEq.add_left d (Nat.ModEq.mul_left 10 ih)
      _ = d + 10 * S ds + 90 * W ds := by ring
      _ = 81 * W ds + (d + S ds + 9 * (S ds + W ds)) := by ring
      _ ≡ d + S ds + 9 * (S ds + W ds) [MOD 81] := by
        change (81 * W ds + (d + S ds + 9 * (S ds + W ds))) % 81 = _
        rw [Nat.add_comm, Nat.add_mul_mod_self_left]

theorem val_reverse_mod_81 (D : List ℕ) (h : D ≠ []) : val D + val D.reverse ≡ (2 + 9 * (D.length - 1)) * S D [MOD 81] := by
  have h1 := val_mod_81 D
  have h2 := val_mod_81 D.reverse
  have h3 := Nat.ModEq.add h1 h2
  calc val D + val D.reverse
    _ ≡ S D + 9 * W D + (S D.reverse + 9 * W D.reverse) [MOD 81] := h3
    _ = 2 * S D + 9 * (W D + W D.reverse) := by simp; ring
    _ = 2 * S D + 9 * ((D.length - 1) * S D) := by rw [W_reverse_add_W D h]
    _ = (2 + 9 * (D.length - 1)) * S D := by ring


theorem val_mod_27 (D : List ℕ) : val D ≡ S D + 9 * W D [MOD 27] := by
  induction D with
  | nil => rfl
  | cons d ds ih =>
    calc d + 10 * val ds
      _ ≡ d + 10 * (S ds + 9 * W ds) [MOD 27] := Nat.ModEq.add_left d (Nat.ModEq.mul_left 10 ih)
      _ = d + 10 * S ds + 90 * W ds := by ring
      _ = 27 * (3 * W ds) + (d + S ds + 9 * (S ds + W ds)) := by ring
      _ ≡ d + S ds + 9 * (S ds + W ds) [MOD 27] := by
        change (27 * (3 * W ds) + (d + S ds + 9 * (S ds + W ds))) % 27 = _
        rw [Nat.add_comm, Nat.add_mul_mod_self_left]

theorem val_reverse_mod_27 (D : List ℕ) (h : D ≠ []) : val D + val D.reverse ≡ (2 + 9 * (D.length - 1)) * S D [MOD 27] := by
  have h1 := val_mod_27 D
  have h2 := val_mod_27 D.reverse
  have h3 := Nat.ModEq.add h1 h2
  calc val D + val D.reverse
    _ ≡ S D + 9 * W D + (S D.reverse + 9 * W D.reverse) [MOD 27] := h3
    _ = 2 * S D + 9 * (W D + W D.reverse) := by simp; ring
    _ = 2 * S D + 9 * ((D.length - 1) * S D) := by rw [W_reverse_add_W D h]
    _ = (2 + 9 * (D.length - 1)) * S D := by ring

theorem val_mod_9 (D : List ℕ) : val D ≡ S D + 9 * W D [MOD 9] := by
  induction D with
  | nil => rfl
  | cons d ds ih =>
    calc d + 10 * val ds
      _ ≡ d + 10 * (S ds + 9 * W ds) [MOD 9] := Nat.ModEq.add_left d (Nat.ModEq.mul_left 10 ih)
      _ = d + 10 * S ds + 90 * W ds := by ring
      _ = 9 * (9 * W ds) + (d + S ds + 9 * (S ds + W ds)) := by ring
      _ ≡ d + S ds + 9 * (S ds + W ds) [MOD 9] := by
        change (9 * (9 * W ds) + (d + S ds + 9 * (S ds + W ds))) % 9 = _
        rw [Nat.add_comm, Nat.add_mul_mod_self_left]

theorem val_reverse_mod_9 (D : List ℕ) (h : D ≠ []) : val D + val D.reverse ≡ (2 + 9 * (D.length - 1)) * S D [MOD 9] := by
  have h1 := val_mod_9 D
  have h2 := val_mod_9 D.reverse
  have h3 := Nat.ModEq.add h1 h2
  calc val D + val D.reverse
    _ ≡ S D + 9 * W D + (S D.reverse + 9 * W D.reverse) [MOD 9] := h3
    _ = 2 * S D + 9 * (W D + W D.reverse) := by simp; ring
    _ = 2 * S D + 9 * ((D.length - 1) * S D) := by rw [W_reverse_add_W D h]
    _ = (2 + 9 * (D.length - 1)) * S D := by ring


theorem gcd_2_plus_9_9 (L : ℕ) (h1 : 1 ≤ L) (h2 : L ≤ 1) : Nat.gcd (2 + 9 * (L - 1)) 9 = 1 := by
  match L with
  | 0 => omega
  | 1 => decide
  | L + 2 => omega

theorem gcd_2_plus_9_27 (L : ℕ) (h1 : 1 ≤ L) (h2 : L ≤ 3) : Nat.gcd (2 + 9 * (L - 1)) 27 = 1 := by
  match L with
  | 0 => omega
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | L + 4 => omega

theorem gcd_2_plus_9_81 (L : ℕ) (h1 : 1 ≤ L) (h2 : L ≤ 9) : Nat.gcd (2 + 9 * (L - 1)) 81 = 1 := by
  match L with
  | 0 => omega
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | L + 10 => omega


theorem S_le_9_len (D : List ℕ) (h_digits : ∀ d ∈ D, d ≤ 9) : S D ≤ 9 * D.length := by
  induction D with
  | nil => simp
  | cons d ds ih =>
    simp
    have hd : d ≤ 9 := h_digits d (List.Mem.head ds)
    have hds : ∀ x ∈ ds, x ≤ 9 := fun x hx => h_digits x (List.Mem.tail d hx)
    have ih' := ih hds
    omega

theorem val_eq_zero_of_S_eq_zero (D : List ℕ) : S D = 0 → val D = 0 := by
  induction D with
  | nil => simp
  | cons d ds ih =>
    intro h
    have h1 : d + S ds = 0 := h
    have hd : d = 0 := by omega
    have hds : S ds = 0 := by omega
    have ih' := ih hds
    simp [hd, ih']

theorem S_pos (D : List ℕ) (h_val : val D > 0) : S D > 0 := by
  contrapose! h_val
  have h_zero : S D = 0 := by omega
  exact le_of_eq (val_eq_zero_of_S_eq_zero D h_zero)

theorem val_eq_pow_sub_one (D : List ℕ) (h_digits : ∀ d ∈ D, d = 9) : val D + 1 = 10 ^ D.length := by
  induction D with
  | nil => rfl
  | cons d ds ih =>
    simp
    have hd : d = 9 := h_digits d (List.Mem.head ds)
    have hds : ∀ x ∈ ds, x = 9 := fun x hx => h_digits x (List.Mem.tail d hx)
    have ih' := ih hds
    rw [hd]
    calc 9 + 10 * val ds + 1 = 10 * (val ds + 1) := by ring
      _ = 10 * 10 ^ ds.length := by rw [ih']
      _ = 10 ^ (ds.length + 1) := by ring

theorem all_9_of_S_eq (D : List ℕ) (h_digits : ∀ d ∈ D, d ≤ 9) (h_eq : S D = 9 * D.length) : ∀ d ∈ D, d = 9 := by
  induction D with
  | nil =>
    intro d hd
    contradiction
  | cons d ds ih =>
    simp at h_eq
    have hd : d ≤ 9 := h_digits d (List.Mem.head ds)
    have hds : ∀ x ∈ ds, x ≤ 9 := fun x hx => h_digits x (List.Mem.tail d hx)
    have h_le := S_le_9_len ds hds
    have h1 : d = 9 := by omega
    have h2 : S ds = 9 * ds.length := by omega
    have ih' := ih hds h2
    intro x hx
    cases hx with
    | head _ => exact h1
    | tail _ hx_tail => exact ih' x hx_tail

theorem extract_9 (S L : ℕ) (h_dvd : 9 ∣ S) (h_pos : 0 < S) (h_le : S ≤ 9 * L) (h_L : L ≤ 1) : S = 9 ∧ L = 1 := by
  have h_mod : S % 9 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
  omega

theorem extract_27 (S L : ℕ) (h_dvd : 27 ∣ S) (h_pos : 0 < S) (h_le : S ≤ 9 * L) (h_L : L ≤ 3) : S = 27 ∧ L = 3 := by
  have h_mod : S % 27 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
  omega

theorem extract_81 (S L : ℕ) (h_dvd : 81 ∣ S) (h_pos : 0 < S) (h_le : S ≤ 9 * L) (h_L : L ≤ 9) : S = 81 ∧ L = 9 := by
  have h_mod : S % 81 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
  omega


theorem divides_S_9 (D : List ℕ) (h1 : 1 ≤ D.length) (h2 : D.length ≤ 1)
    (h_val : 9 ∣ val D) (h_val_rev : 9 ∣ val D.reverse) : 9 ∣ S D := by
  have h3 := val_reverse_mod_9 D (List.length_pos_iff_ne_nil.mp (by omega))
  have h_add : 9 ∣ val D + val D.reverse := Nat.dvd_add h_val h_val_rev
  have h_mod1 : (val D + val D.reverse) % 9 = 0 := Nat.mod_eq_zero_of_dvd h_add
  have h_mod2 : (val D + val D.reverse) % 9 = ((2 + 9 * (D.length - 1)) * S D) % 9 := h3
  have h_mod3 : ((2 + 9 * (D.length - 1)) * S D) % 9 = 0 := by omega
  have h_dvd : 9 ∣ (2 + 9 * (D.length - 1)) * S D := Nat.dvd_of_mod_eq_zero h_mod3
  have h_coprime : Nat.Coprime 9 (2 + 9 * (D.length - 1)) := by
    rw [Nat.Coprime, Nat.gcd_comm]
    exact gcd_2_plus_9_9 D.length h1 h2
  exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_dvd

theorem divides_S_27 (D : List ℕ) (h1 : 1 ≤ D.length) (h2 : D.length ≤ 3)
    (h_val : 27 ∣ val D) (h_val_rev : 27 ∣ val D.reverse) : 27 ∣ S D := by
  have h3 := val_reverse_mod_27 D (List.length_pos_iff_ne_nil.mp (by omega))
  have h_add : 27 ∣ val D + val D.reverse := Nat.dvd_add h_val h_val_rev
  have h_mod1 : (val D + val D.reverse) % 27 = 0 := Nat.mod_eq_zero_of_dvd h_add
  have h_mod2 : (val D + val D.reverse) % 27 = ((2 + 9 * (D.length - 1)) * S D) % 27 := h3
  have h_mod3 : ((2 + 9 * (D.length - 1)) * S D) % 27 = 0 := by omega
  have h_dvd : 27 ∣ (2 + 9 * (D.length - 1)) * S D := Nat.dvd_of_mod_eq_zero h_mod3
  have h_coprime : Nat.Coprime 27 (2 + 9 * (D.length - 1)) := by
    rw [Nat.Coprime, Nat.gcd_comm]
    exact gcd_2_plus_9_27 D.length h1 h2
  exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_dvd

theorem divides_S_81 (D : List ℕ) (h1 : 1 ≤ D.length) (h2 : D.length ≤ 9)
    (h_val : 81 ∣ val D) (h_val_rev : 81 ∣ val D.reverse) : 81 ∣ S D := by
  have h3 := val_reverse_mod_81 D (List.length_pos_iff_ne_nil.mp (by omega))
  have h_add : 81 ∣ val D + val D.reverse := Nat.dvd_add h_val h_val_rev
  have h_mod1 : (val D + val D.reverse) % 81 = 0 := Nat.mod_eq_zero_of_dvd h_add
  have h_mod2 : (val D + val D.reverse) % 81 = ((2 + 9 * (D.length - 1)) * S D) % 81 := h3
  have h_mod3 : ((2 + 9 * (D.length - 1)) * S D) % 81 = 0 := by omega
  have h_dvd : 81 ∣ (2 + 9 * (D.length - 1)) * S D := Nat.dvd_of_mod_eq_zero h_mod3
  have h_coprime : Nat.Coprime 81 (2 + 9 * (D.length - 1)) := by
    rw [Nat.Coprime, Nat.gcd_comm]
    exact gcd_2_plus_9_81 D.length h1 h2
  exact Nat.Coprime.dvd_of_dvd_mul_left h_coprime h_dvd

theorem val_append (A B : List ℕ) : val (A ++ B) = val A + val B * 10 ^ A.length := by
  induction A <;> simp [*]; ring

theorem val_replicate_zero (n : ℕ) : val (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate, val]; linarith

def D_seq : ℕ → List ℕ
| 0 => [7, 8, 9, 9, 9, 9, 9, 9, 8, 4]
| m + 1 =>
  let K := 3 ^ (m + 3)
  let zeros := List.replicate (K - (D_seq m).length) 0
  D_seq m ++ zeros ++ D_seq m ++ zeros ++ D_seq m

lemma D_seq_succ (m : ℕ) : D_seq (m + 1) = D_seq m ++ List.replicate (3 ^ (m + 3) - (D_seq m).length) 0 ++ D_seq m ++ List.replicate (3 ^ (m + 3) - (D_seq m).length) 0 ++ D_seq m := rfl

lemma D_seq_len (m : ℕ) : (D_seq m).length ≤ 3 ^ (m + 3) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [D_seq_succ]
    have H : (D_seq m).length ≤ 3 ^ (m + 3) := ih
    simp
    have H2 : 3 ^ (m + 1 + 3) = 3 * 3 ^ (m + 3) := by ring
    omega

lemma D_seq_rev_succ (m : ℕ) : (D_seq (m + 1)).reverse = (D_seq m).reverse ++ List.replicate (3 ^ (m + 3) - (D_seq m).length) 0 ++ (D_seq m).reverse ++ List.replicate (3 ^ (m + 3) - (D_seq m).length) 0 ++ (D_seq m).reverse := by
  rw [D_seq_succ]
  have h1 : (List.replicate (3 ^ (m + 3) - (D_seq m).length) 0).reverse = List.replicate (3 ^ (m + 3) - (D_seq m).length) 0 := by simp
  simp [List.reverse_append, h1]

lemma val_D_seq (m : ℕ) : val (D_seq (m + 1)) = val (D_seq m) * (1 + 10 ^ (3 ^ (m + 3)) + 10 ^ (2 * 3 ^ (m + 3))) := by
  rw [D_seq_succ]
  have H : (D_seq m).length ≤ 3 ^ (m + 3) := D_seq_len m
  have h_zeros : val (List.replicate (3 ^ (m + 3) - (D_seq m).length) 0) = 0 := val_replicate_zero _
  repeat rw [val_append]
  simp [h_zeros]
  have H1 : (D_seq m).length + (3 ^ (m + 3) - (D_seq m).length) = 3 ^ (m + 3) := by omega
  have H2 : (D_seq m).length + (3 ^ (m + 3) - (D_seq m).length + 3 ^ (m + 3)) = 2 * 3 ^ (m + 3) := by omega
  rw [H1, H2]
  ring

lemma val_D_seq_rev (m : ℕ) : val (D_seq (m + 1)).reverse = val (D_seq m).reverse * (1 + 10 ^ (3 ^ (m + 3)) + 10 ^ (2 * 3 ^ (m + 3))) := by
  rw [D_seq_rev_succ]
  have H : (D_seq m).length ≤ 3 ^ (m + 3) := D_seq_len m
  have h_zeros : val (List.replicate (3 ^ (m + 3) - (D_seq m).length) 0) = 0 := val_replicate_zero _
  repeat rw [val_append]
  simp [h_zeros]
  have H1 : (D_seq m).length + (3 ^ (m + 3) - (D_seq m).length) = 3 ^ (m + 3) := by omega
  have H2 : (D_seq m).length + (3 ^ (m + 3) - (D_seq m).length + 3 ^ (m + 3)) = 2 * 3 ^ (m + 3) := by omega
  rw [H1, H2]
  ring

lemma multiplier_div_3 (m : ℕ) : 3 ∣ 1 + 10 ^ (3 ^ (m + 3)) + 10 ^ (2 * 3 ^ (m + 3)) := by
  have H1 : 10 ≡ 1 [MOD 3] := by decide
  have H2 : 10 ^ (3 ^ (m + 3)) ≡ 1 ^ (3 ^ (m + 3)) [MOD 3] := Nat.ModEq.pow _ H1
  have H2' : 10 ^ (3 ^ (m + 3)) ≡ 1 [MOD 3] := by
    calc 10 ^ (3 ^ (m + 3)) ≡ 1 ^ (3 ^ (m + 3)) [MOD 3] := H2
      _ = 1 := by simp
  have H3 : 10 ^ (2 * 3 ^ (m + 3)) ≡ 1 ^ (2 * 3 ^ (m + 3)) [MOD 3] := Nat.ModEq.pow _ H1
  have H3' : 10 ^ (2 * 3 ^ (m + 3)) ≡ 1 [MOD 3] := by
    calc 10 ^ (2 * 3 ^ (m + 3)) ≡ 1 ^ (2 * 3 ^ (m + 3)) [MOD 3] := H3
      _ = 1 := by simp
  have H4 : 1 + 10 ^ (3 ^ (m + 3)) + 10 ^ (2 * 3 ^ (m + 3)) ≡ 1 + 1 + 1 [MOD 3] := by
    apply Nat.ModEq.add
    apply Nat.ModEq.add (Nat.ModEq.refl 1) H2'
    exact H3'
  have H5 : 1 + 1 + 1 ≡ 0 [MOD 3] := by decide
  have H6 : 1 + 10 ^ (3 ^ (m + 3)) + 10 ^ (2 * 3 ^ (m + 3)) ≡ 0 [MOD 3] := Nat.ModEq.trans H4 H5
  exact Nat.dvd_of_mod_eq_zero H6

lemma val_D_seq_div (m : ℕ) : 3 ^ (m + 5) ∣ val (D_seq m) := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [val_D_seq]
    have h_pow : 3 ^ (m + 1 + 5) = 3 ^ (m + 5) * 3 := by ring
    rw [h_pow]
    exact mul_dvd_mul ih (multiplier_div_3 m)

lemma val_D_seq_rev_div (m : ℕ) : 3 ^ (m + 5) ∣ val (D_seq m).reverse := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [val_D_seq_rev]
    have h_pow : 3 ^ (m + 1 + 5) = 3 ^ (m + 5) * 3 := by ring
    rw [h_pow]
    exact mul_dvd_mul ih (multiplier_div_3 m)




lemma val_D_seq_pos (m : ℕ) : val (D_seq m) > 0 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [val_D_seq]
    have h1 : 10 ^ (3 ^ (m + 3)) ≥ 1 := Nat.one_le_pow _ _ (by decide)
    have h2 : 10 ^ (2 * 3 ^ (m + 3)) ≥ 1 := Nat.one_le_pow _ _ (by decide)
    have H1 : 1 + 10 ^ (3 ^ (m + 3)) + 10 ^ (2 * 3 ^ (m + 3)) > 0 := by omega
    exact Nat.mul_pos ih H1


lemma lt_pow_cube (X V : ℕ) (h1 : X ≥ 10) (h2 : V ≤ X - 2) : V * (1 + X + X^2) < X^3 - 1 := by
  have H_cube : X^3 ≥ 1 := by
    calc X^3 ≥ 10^3 := by gcongr
      _ ≥ 1 := by norm_num
  have h3 : (X - 1) * (1 + X + X^2) = X^3 - 1 := by
    zify [show X ≥ 1 by omega, H_cube]
    ring
  calc V * (1 + X + X^2) ≤ (X - 2) * (1 + X + X^2) := Nat.mul_le_mul_right _ h2
    _ < (X - 1) * (1 + X + X^2) := by
      apply Nat.mul_lt_mul_of_pos_right
      · omega
      · omega
    _ = X^3 - 1 := h3

lemma val_D_seq_lt (m : ℕ) : val (D_seq m) < 10 ^ (3 ^ (m + 3)) - 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [val_D_seq]
    have H_pow : 10 ^ 1 ≤ 10 ^ (3 ^ (m + 3)) := by
      apply Nat.pow_le_pow_right (by decide)
      have h3 : 1 ≤ 3 ^ (m + 3) := Nat.one_le_pow _ _ (by decide)
      omega
    have H1 : 10 ^ (3 ^ (m + 3)) ≥ 10 := H_pow
    have H2 : val (D_seq m) ≤ 10 ^ (3 ^ (m + 3)) - 2 := by
      zify [H1] at ih ⊢
      omega
    have H3 := lt_pow_cube (10 ^ (3 ^ (m + 3))) (val (D_seq m)) H1 H2
    have h_pow2 : (10 ^ 3 ^ (m + 3)) ^ 3 = 10 ^ 3 ^ (m + 1 + 3) := by
      have : (10 ^ 3 ^ (m + 3)) ^ 3 = 10 ^ (3 * 3 ^ (m + 3)) := by ring
      rw [this]
      have h2 : 3 * 3 ^ (m + 3) = 3 ^ (m + 1 + 3) := by ring
      rw [h2]
    have h_sq : (10 ^ 3 ^ (m + 3)) ^ 2 = 10 ^ (2 * 3 ^ (m + 3)) := by ring
    rw [←h_pow2, ←h_sq]
    exact H3



lemma D_seq_lt_10 (m : ℕ) (d : ℕ) (hd : d ∈ D_seq m) : d < 10 := by
  induction m with
  | zero =>
    revert d hd
    decide
  | succ m ih =>
    rw [D_seq_succ] at hd
    simp at hd
    rcases hd with hd | ⟨_, rfl⟩ | hd | ⟨_, rfl⟩ | hd
    · exact ih hd
    · omega
    · exact ih hd
    · omega
    · exact ih hd

lemma D_seq_not_empty (m : ℕ) : D_seq m ≠ [] := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [D_seq_succ]
    intro h
    have h1 := (List.append_eq_nil_iff.mp h).2
    contradiction

lemma D_seq_last (m : ℕ) : (D_seq m).getLast (D_seq_not_empty m) = 4 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have H : (D_seq (m + 1)).getLast (D_seq_not_empty (m + 1)) = (D_seq m).getLast (D_seq_not_empty m) := by
      exact List.getLast_append_of_ne_nil _ _
    rw [H, ih]

theorem val_eq_ofDigits (D : List ℕ) : val D = Nat.ofDigits 10 D := by
  induction D with
  | nil => rfl
  | cons d ds ih =>
    simp [ih, Nat.ofDigits]

lemma digits_val_D_seq (m : ℕ) : Nat.digits 10 (val (D_seq m)) = D_seq m := by
  rw [val_eq_ofDigits]
  apply Nat.digits_ofDigits
  · decide
  · intro d hd
    exact D_seq_lt_10 m d hd
  · intro he
    have H1 := D_seq_last m
    have H2 : (D_seq m).getLast he ≠ 0 := by omega
    exact H2

lemma reverse_nat_val_D_seq (m : ℕ) : reverse_nat (val (D_seq m)) = val (D_seq m).reverse := by
  unfold reverse_nat
  rw [digits_val_D_seq m]
  rw [←val_eq_ofDigits]

theorem P_D_seq (m : ℕ) : val (D_seq m) > 0 ∧ 3 ^ (m + 5) ∣ reverse_nat (val (D_seq m)) := by
  constructor
  · exact val_D_seq_pos m
  · rw [reverse_nat_val_D_seq]
    exact val_D_seq_rev_div m

lemma length_digits_le (X L : ℕ) (h_pos : X > 0) (h_lt : X < 10 ^ L) : (Nat.digits 10 X).length ≤ L := by
  induction L generalizing X with
  | zero =>
    simp at h_lt
    omega
  | succ L ih =>
    rw [Nat.digits_def' (by decide) h_pos]
    simp
    have h_div : X / 10 < 10 ^ L := by omega
    by_cases h_div_pos : X / 10 = 0
    · rw [h_div_pos, Nat.digits_zero]
      simp
    · have h_div_pos' : X / 10 > 0 := by omega
      have ih' := ih (X / 10) h_div_pos' h_div
      omega

theorem val_digits (X : ℕ) : val (Nat.digits 10 X) = X := by
  rw [val_eq_ofDigits]
  exact Nat.ofDigits_digits 10 X

theorem val_reverse_digits (X : ℕ) : val (Nat.digits 10 X).reverse = reverse_nat X := by
  rw [val_eq_ofDigits, reverse_nat]

theorem ex_9 : reverse_nat 9 = 9 := by norm_num [reverse_nat, Nat.digits, Nat.digitsAux, Nat.ofDigits]
theorem ex_27 : reverse_nat 999 = 999 := by norm_num [reverse_nat, Nat.digits, Nat.digitsAux, Nat.ofDigits]
theorem ex_81 : reverse_nat 999999999 = 999999999 := by norm_num [reverse_nat, Nat.digits, Nat.digitsAux, Nat.ofDigits]

theorem no_smaller_9 (X : ℕ) (h_pos : X > 0) (h_lt : X < 9) (h_div : 9 ∣ X) (h_div_rev : 9 ∣ reverse_nat X) : False := by
  have h_len := length_digits_le X 1 h_pos (by omega)
  have hd_val : val (Nat.digits 10 X) = X := val_digits X
  have hd_rev : val (Nat.digits 10 X).reverse = reverse_nat X := val_reverse_digits X
  have h_div_val : 9 ∣ val (Nat.digits 10 X) := by rw [hd_val]; exact h_div
  have h_div_rev_val : 9 ∣ val (Nat.digits 10 X).reverse := by rw [hd_rev]; exact h_div_rev
  have h_len_pos : 1 ≤ (Nat.digits 10 X).length := by
    cases H : Nat.digits 10 X with
    | nil =>
      have : val [] = 0 := rfl
      rw [H, this] at hd_val
      omega
    | cons _ _ => simp
  have hS := divides_S_9 (Nat.digits 10 X) h_len_pos h_len h_div_val h_div_rev_val
  have h_le_S : S (Nat.digits 10 X) ≤ 9 * (Nat.digits 10 X).length := by
    apply S_le_9_len
    intro d hd
    have h_lt10 := Nat.digits_lt_base (by decide : 1 < 10) hd
    omega
  have h_S_pos : S (Nat.digits 10 X) > 0 := by
    apply S_pos
    omega
  have H : S (Nat.digits 10 X) = 9 ∧ (Nat.digits 10 X).length = 1 := extract_9 (S (Nat.digits 10 X)) _ hS h_S_pos h_le_S h_len
  have h_all := all_9_of_S_eq (Nat.digits 10 X) (fun d hd => by
    have h_lt10 := Nat.digits_lt_base (by decide : 1 < 10) hd
    omega) (by omega)
  have h_val := val_eq_pow_sub_one (Nat.digits 10 X) h_all
  rw [H.2] at h_val
  have : 10 ^ 1 = 10 := by rfl
  rw [this] at h_val
  omega

theorem no_smaller_27 (X : ℕ) (h_pos : X > 0) (h_lt : X < 999) (h_div : 27 ∣ X) (h_div_rev : 27 ∣ reverse_nat X) : False := by
  have h_len := length_digits_le X 3 h_pos (by omega)
  have hd_val : val (Nat.digits 10 X) = X := val_digits X
  have hd_rev : val (Nat.digits 10 X).reverse = reverse_nat X := val_reverse_digits X
  have h_div_val : 27 ∣ val (Nat.digits 10 X) := by rw [hd_val]; exact h_div
  have h_div_rev_val : 27 ∣ val (Nat.digits 10 X).reverse := by rw [hd_rev]; exact h_div_rev
  have h_len_pos : 1 ≤ (Nat.digits 10 X).length := by
    cases H : Nat.digits 10 X with
    | nil =>
      have : val [] = 0 := rfl
      rw [H, this] at hd_val
      omega
    | cons _ _ => simp
  have hS := divides_S_27 (Nat.digits 10 X) h_len_pos h_len h_div_val h_div_rev_val
  have h_le_S : S (Nat.digits 10 X) ≤ 9 * (Nat.digits 10 X).length := by
    apply S_le_9_len
    intro d hd
    have h_lt10 := Nat.digits_lt_base (by decide : 1 < 10) hd
    omega
  have h_S_pos : S (Nat.digits 10 X) > 0 := by
    apply S_pos
    omega
  have H : S (Nat.digits 10 X) = 27 ∧ (Nat.digits 10 X).length = 3 := extract_27 (S (Nat.digits 10 X)) _ hS h_S_pos h_le_S h_len
  have h_all := all_9_of_S_eq (Nat.digits 10 X) (fun d hd => by
    have h_lt10 := Nat.digits_lt_base (by decide : 1 < 10) hd
    omega) (by omega)
  have h_val := val_eq_pow_sub_one (Nat.digits 10 X) h_all
  rw [H.2] at h_val
  have : 10 ^ 3 = 1000 := by rfl
  rw [this] at h_val
  omega

theorem no_smaller_81 (X : ℕ) (h_pos : X > 0) (h_lt : X < 999999999) (h_div : 81 ∣ X) (h_div_rev : 81 ∣ reverse_nat X) : False := by
  have h_len := length_digits_le X 9 h_pos (by omega)
  have hd_val : val (Nat.digits 10 X) = X := val_digits X
  have hd_rev : val (Nat.digits 10 X).reverse = reverse_nat X := val_reverse_digits X
  have h_div_val : 81 ∣ val (Nat.digits 10 X) := by rw [hd_val]; exact h_div
  have h_div_rev_val : 81 ∣ val (Nat.digits 10 X).reverse := by rw [hd_rev]; exact h_div_rev
  have h_len_pos : 1 ≤ (Nat.digits 10 X).length := by
    cases H : Nat.digits 10 X with
    | nil =>
      have : val [] = 0 := rfl
      rw [H, this] at hd_val
      omega
    | cons _ _ => simp
  have hS := divides_S_81 (Nat.digits 10 X) h_len_pos h_len h_div_val h_div_rev_val
  have h_le_S : S (Nat.digits 10 X) ≤ 9 * (Nat.digits 10 X).length := by
    apply S_le_9_len
    intro d hd
    have h_lt10 := Nat.digits_lt_base (by decide : 1 < 10) hd
    omega
  have h_S_pos : S (Nat.digits 10 X) > 0 := by
    apply S_pos
    omega
  have H : S (Nat.digits 10 X) = 81 ∧ (Nat.digits 10 X).length = 9 := extract_81 (S (Nat.digits 10 X)) _ hS h_S_pos h_le_S h_len
  have h_all := all_9_of_S_eq (Nat.digits 10 X) (fun d hd => by
    have h_lt10 := Nat.digits_lt_base (by decide : 1 < 10) hd
    omega) (by omega)
  have h_val := val_eq_pow_sub_one (Nat.digits 10 X) h_all
  rw [H.2] at h_val
  have : 10 ^ 9 = 1000000000 := by rfl
  rw [this] at h_val
  omega

lemma min_9 (h_ex : ∃ k, k > 0 ∧ 9 ∣ reverse_nat (k * 9)) : Nat.find h_ex * 9 = 9 := by
  have P_1 : 1 > 0 ∧ 9 ∣ reverse_nat (1 * 9) := by
    constructor
    · omega
    · rw [ex_9]
  have H_le : Nat.find h_ex ≤ 1 := Nat.find_le P_1
  have H_pos : Nat.find h_ex > 0 := (Nat.find_spec h_ex).1
  have H_eq : Nat.find h_ex = 1 := by omega
  omega

lemma min_27 (h_ex : ∃ k, k > 0 ∧ 27 ∣ reverse_nat (k * 27)) : Nat.find h_ex * 27 = 999 := by
  have P_37 : 37 > 0 ∧ 27 ∣ reverse_nat (37 * 27) := by
    constructor
    · omega
    · have h : 37 * 27 = 999 := by rfl
      rw [h, ex_27]
      decide
  have H_le : Nat.find h_ex ≤ 37 := Nat.find_le P_37
  have H_pos : Nat.find h_ex > 0 := (Nat.find_spec h_ex).1
  by_cases h_eq : Nat.find h_ex = 37
  · rw [h_eq]
  · have h_lt : Nat.find h_ex < 37 := by omega
    have h_mul : Nat.find h_ex * 27 < 999 := by omega
    have P_find := Nat.find_spec h_ex
    have h_false := no_smaller_27 (Nat.find h_ex * 27) (by omega) h_mul (dvd_mul_left _ _) P_find.2
    contradiction

lemma min_81 (h_ex : ∃ k, k > 0 ∧ 81 ∣ reverse_nat (k * 81)) : Nat.find h_ex * 81 = 999999999 := by
  have P_12345679 : 12345679 > 0 ∧ 81 ∣ reverse_nat (12345679 * 81) := by
    constructor
    · omega
    · have h : 12345679 * 81 = 999999999 := by rfl
      rw [h, ex_81]
      decide
  have H_le : Nat.find h_ex ≤ 12345679 := Nat.find_le P_12345679
  have H_pos : Nat.find h_ex > 0 := (Nat.find_spec h_ex).1
  by_cases h_eq : Nat.find h_ex = 12345679
  · rw [h_eq]
  · have h_lt : Nat.find h_ex < 12345679 := by omega
    have h_mul : Nat.find h_ex * 81 < 999999999 := by omega
    have P_find := Nat.find_spec h_ex
    have h_false := no_smaller_81 (Nat.find h_ex * 81) (by omega) h_mul (dvd_mul_left _ _) P_find.2
    contradiction

theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) := by
  intro hn
  constructor
  · intro heq
    have h_cases : n = 2 ∨ n = 3 ∨ n = 4 ∨ n ≥ 5 := by omega
    rcases h_cases with rfl | rfl | rfl | hn5
    · left; rfl
    · right; left; rfl
    · right; right; rfl
    · exfalso
      have hm : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      rcases hm with ⟨m, rfl⟩
      have H_a : a (3 ^ (m + 5)) = 10 ^ (3 ^ (m + 3)) - 1 := heq
      -- from a(3^(m+5)), we know there is no smaller multiple.
      -- but we constructed val (D_seq m) which is smaller and valid.
      unfold a at H_a
      simp at H_a
      have P_m := P_D_seq m
      have div_D := val_D_seq_div m
      let P := fun k => k > 0 ∧ 3 ^ (m + 5) ∣ reverse_nat (k * 3 ^ (m + 5))
      have P_val : P (val (D_seq m) / 3 ^ (m + 5)) := by
        constructor
        · exact Nat.div_pos (Nat.le_of_dvd P_m.1 div_D) (by omega)
        · have h_eq : val (D_seq m) / 3 ^ (m + 5) * 3 ^ (m + 5) = val (D_seq m) := Nat.div_mul_cancel div_D
          rw [h_eq]
          exact P_m.2
      have P_ex : ∃ k, P k := ⟨_, P_val⟩
      have H_find : Nat.find P_ex ≤ val (D_seq m) / 3 ^ (m + 5) := Nat.find_le P_val
      have H_le : Nat.find P_ex * 3 ^ (m + 5) ≤ val (D_seq m) := by
        have h_eq : val (D_seq m) / 3 ^ (m + 5) * 3 ^ (m + 5) = val (D_seq m) := Nat.div_mul_cancel div_D
        calc Nat.find P_ex * 3 ^ (m + 5) ≤ (val (D_seq m) / 3 ^ (m + 5)) * 3 ^ (m + 5) := Nat.mul_le_mul_right _ H_find
          _ = val (D_seq m) := h_eq
      have H_lt : val (D_seq m) < 10 ^ (3 ^ (m + 3)) - 1 := val_D_seq_lt m
      have H_contra : Nat.find P_ex * 3 ^ (m + 5) < 10 ^ (3 ^ (m + 3)) - 1 := by omega
      rw [dif_pos P_ex] at H_a
      exact Nat.ne_of_lt H_contra H_a
  · intro H
    rcases H with (rfl | rfl | rfl)
    · have h1 : 3^2 = 9 := by rfl
      have h2 : 10 ^ (3 ^ (2 - 2)) - 1 = 9 := by rfl
      rw [h1, h2]
      unfold a
      simp
      have h_ex : ∃ k, k > 0 ∧ 9 ∣ reverse_nat (k * 9) := ⟨1, by decide, by have : 1 * 9 = 9 := rfl; rw [this, ex_9]⟩
      rw [dif_pos h_ex]
      exact min_9 h_ex
    · have h1 : 3^3 = 27 := by rfl
      have h2 : 10 ^ (3 ^ (3 - 2)) - 1 = 999 := by rfl
      rw [h1, h2]
      unfold a
      simp
      have h_ex : ∃ k, k > 0 ∧ 27 ∣ reverse_nat (k * 27) := ⟨37, by decide, by have : 37 * 27 = 999 := rfl; rw [this, ex_27]; decide⟩
      rw [dif_pos h_ex]
      exact min_27 h_ex
    · have h1 : 3^4 = 81 := by rfl
      have h2 : 10 ^ (3 ^ (4 - 2)) - 1 = 999999999 := by rfl
      rw [h1, h2]
      unfold a
      simp
      have h_ex : ∃ k, k > 0 ∧ 81 ∣ reverse_nat (k * 81) := ⟨12345679, by decide, by have : 12345679 * 81 = 999999999 := rfl; rw [this, ex_81]; decide⟩
      rw [dif_pos h_ex]
      exact min_81 h_ex

theorem oeis_62567_conjecture_0.disproof : ¬ (∀ n : ℕ, 2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4)) := by
  sorry
