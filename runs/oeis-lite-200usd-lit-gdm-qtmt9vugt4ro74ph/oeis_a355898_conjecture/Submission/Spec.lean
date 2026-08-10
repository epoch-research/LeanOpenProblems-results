import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000
set_option linter.unusedVariables false

open Nat

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

def A355898_loop : ℕ → ℕ × ℕ
| 0 => (0, 1)
| 1 => (1, 1)
| n + 2 =>
  let (a, b) := A355898_loop (n + 1)
  let g := Nat.gcd b a
  (b, g + (b + a) / g)

theorem A355898_loop_eq (n : ℕ) :
  A355898_loop n = (A355898 n, A355898 (n + 1)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · rfl
    · rfl
    · have ih1 := ih (n + 1) (Nat.lt_add_one (n + 1))
      simp only [A355898_loop]
      rw [ih1]
      simp only [A355898]

def A355898_tr_loop : ℕ → ℕ × ℕ → ℕ × ℕ
| 0, (a, b) => (a, b)
| m + 1, (a, b) =>
  let g := Nat.gcd b a
  A355898_tr_loop m (b, g + (b + a) / g)

theorem A355898_tr_loop_eq (k : ℕ) (s : ℕ) :
  A355898_tr_loop k (A355898_loop (s + 1)) = A355898_loop (s + 1 + k) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    have h_step : A355898_tr_loop (k + 1) (A355898_loop (s + 1)) = A355898_tr_loop k (A355898_loop (s + 2)) := by
      rcases h_eq : A355898_loop (s + 1) with ⟨a, b⟩
      simp only [A355898_tr_loop]
      have h_loop_succ : A355898_loop (s + 2) = (b, Nat.gcd b a + (b + a) / Nat.gcd b a) := by
        have h_def : A355898_loop (s + 2) =
          let (a', b') := A355898_loop (s + 1)
          let g := Nat.gcd b' a'
          (b', g + (b' + a') / g) := by rfl
        rw [h_def, h_eq]
      rw [h_loop_succ]
    rw [h_step]
    have ih1 := ih (s + 1)
    have h_add : s + 2 + k = s + 1 + (k + 1) := by omega
    rw [h_add] at ih1
    exact ih1

def A355898_fast (n : ℕ) : ℕ :=
  (A355898_tr_loop (n - 1) (1, 1)).1

theorem A355898_fast_eq (n : ℕ) (hn : n ≥ 1) : A355898_fast n = A355898 n := by
  unfold A355898_fast
  have h_loop1 : (1, 1) = A355898_loop 1 := rfl
  rw [h_loop1]
  rw [A355898_tr_loop_eq (n - 1) 0]
  have h_add : 0 + 1 + (n - 1) = n := by omega
  rw [h_add]
  rw [A355898_loop_eq]

lemma A355898_pos (k : ℕ) (hk : k ≥ 1) : A355898 k > 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | _ | _ | n
    · omega
    · decide
    · decide
    · -- k = n + 3
      have ih1 := ih (n + 2) (by omega) (by omega)
      -- g = gcd an_minus_1 an_minus_2
      have h_gcd_pos : Nat.gcd (A355898 (n + 2)) (A355898 (n + 1)) > 0 := by
        have h_dvd : Nat.gcd (A355898 (n + 2)) (A355898 (n + 1)) ∣ A355898 (n + 2) := Nat.gcd_dvd_left _ _
        exact Nat.pos_of_dvd_of_pos h_dvd ih1
      -- Unfold A355898 (n + 3) on the goal
      change (let an_minus_1 := A355898 (n + 2);
              let n2 := A355898 (n + 1);
              let g := Nat.gcd an_minus_1 n2;
              g + (an_minus_1 + n2) / g) > 0
      dsimp only
      -- g + S/g >= g
      have h_le : Nat.gcd (A355898 (n + 2)) (A355898 (n + 1)) ≤
        Nat.gcd (A355898 (n + 2)) (A355898 (n + 1)) + (A355898 (n + 2) + A355898 (n + 1)) / Nat.gcd (A355898 (n + 2)) (A355898 (n + 1)) := by
        exact Nat.le_add_right _ _
      omega

def p : ℕ := 195318521017

lemma sub_eq_sub_of_add_eq_add (X S g Y : ℕ) (h : X + S = g + Y) (hgX : g ≤ X) (_hSY : S ≤ Y) : X - g = Y - S := by omega

lemma g_eq_1_of_rec (g S : ℕ) (hS : S > 0) (hg : g ∣ S) (heq : g + S / g = 1 + S) (hg_le : g < S) : g = 1 := by
  by_cases hg1 : g = 1
  · exact hg1
  · have hg_pos : g > 0 := Nat.pos_of_dvd_of_pos hg hS
    have hg_gt_1 : g > 1 := by omega
    have hg_minus_1 : g - 1 > 0 := by omega
    -- Since g divides S, we have (S / g) * g = S.
    have h_div : (S / g) * g = S := Nat.div_mul_cancel hg
    -- Multiply both sides of heq by g:
    have h1 : (g + S / g) * g = (1 + S) * g := by rw [heq]
    -- LHS: (g + S / g) * g = g * g + (S / g) * g = g * g + S
    have h_lhs : (g + S / g) * g = g * g + S := by
      rw [Nat.add_mul, h_div]
    -- RHS: (1 + S) * g = g + S * g
    have h_rhs : (1 + S) * g = g + S * g := by
      rw [Nat.add_mul, Nat.one_mul]
    have h2 : g * g + S = g + S * g := by
      rw [← h_lhs, h1, h_rhs]
    -- S * (g - 1) = S * g - S * 1
    have h_g_sub : g * (g - 1) = g * g - g := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have h_S_sub : S * (g - 1) = S * g - S := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    -- From h2: g * g + S = g + S * g
    -- So: g * g - g = S * g - S
    have hg_ge_1 : 1 ≤ g := by omega
    have h_le1 : g ≤ g * g := by
      have : g * 1 ≤ g * g := Nat.mul_le_mul_left g hg_ge_1
      rw [Nat.mul_one] at this
      exact this
    have h_le2 : S ≤ S * g := by
      have : S * 1 ≤ S * g := Nat.mul_le_mul_left S hg_ge_1
      rw [Nat.mul_one] at this
      exact this
    have h3 : g * g - g = S * g - S := sub_eq_sub_of_add_eq_add (g * g) S g (S * g) h2 h_le1 h_le2
    have h4 : g * (g - 1) = S * (g - 1) := by
      rw [h_g_sub, h3, ← h_S_sub]
    -- Since g - 1 > 0, we can cancel (g - 1)
    have h5 : g = S := Nat.eq_of_mul_eq_mul_right hg_minus_1 h4
    omega

def ConjectureType := ∀ (n : ℕ), 3775 ≤ n →
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)

lemma gcd_eq_1_of_h_all (h_all : ConjectureType) (m : ℕ) (hm : m ≥ 1) :
  Nat.gcd (A355898 (3773 + m)) (A355898 (3772 + m)) = 1 := by
  have h_rec := (h_all (3774 + m) (by omega)).1
  have h_arg0 : 3774 + m = 3771 + m + 3 := by omega
  rw [h_arg0] at h_rec
  have h_sub1 : 3771 + m + 3 - 1 = 3771 + m + 2 := by omega
  have h_sub2 : 3771 + m + 3 - 2 = 3771 + m + 1 := by omega
  rw [h_sub1, h_sub2] at h_rec
  
  have h_def : A355898 (3771 + m + 3) =
    let an_minus_1 := A355898 (3771 + m + 2)
    let n2 := A355898 (3771 + m + 1)
    let g := Nat.gcd an_minus_1 n2
    g + (an_minus_1 + n2) / g := by rfl
  
  rw [h_def] at h_rec
  dsimp only at h_rec
  
  -- Rewrite h_rec so that RHS matches 1 + S exactly:
  have h_assoc : 1 + A355898 (3771 + m + 2) + A355898 (3771 + m + 1) = 1 + (A355898 (3771 + m + 2) + A355898 (3771 + m + 1)) := by
    rw [add_assoc]
  rw [h_assoc] at h_rec
  
  -- S > 0 proof:
  have hS_pos : A355898 (3771 + m + 2) + A355898 (3771 + m + 1) > 0 := by
    have h_pos1 : A355898 (3771 + m + 2) > 0 := A355898_pos _ (by omega)
    omega
  
  -- g | S proof:
  have h_g_dvd : Nat.gcd (A355898 (3771 + m + 2)) (A355898 (3771 + m + 1)) ∣ A355898 (3771 + m + 2) + A355898 (3771 + m + 1) := by
    apply Nat.dvd_add
    · exact Nat.gcd_dvd_left _ _
    · exact Nat.gcd_dvd_right _ _
  
  -- g < S proof:
  have h_g_lt : Nat.gcd (A355898 (3771 + m + 2)) (A355898 (3771 + m + 1)) < A355898 (3771 + m + 2) + A355898 (3771 + m + 1) := by
    have h_gcd_le : Nat.gcd (A355898 (3771 + m + 2)) (A355898 (3771 + m + 1)) ≤ A355898 (3771 + m + 2) := Nat.gcd_le_left _ (A355898_pos _ (by omega))
    have h_pos2 : A355898 (3771 + m + 1) > 0 := A355898_pos _ (by omega)
    omega
  
  -- Apply g_eq_1_of_rec:
  have h_gcd_eq_1 := g_eq_1_of_rec _ _ hS_pos h_g_dvd h_rec h_g_lt
  
  -- Convert target to variables:
  have h_arg1_eq : 3773 + m = 3771 + m + 2 := by omega
  have h_arg2_eq : 3772 + m = 3771 + m + 1 := by omega
  rw [h_arg1_eq, h_arg2_eq]
  exact h_gcd_eq_1

def G (A0 A1 : ZMod p) : ℕ → ZMod p
| 0 => A0
| 1 => A1
| m + 2 => G A0 A1 (m + 1) + G A0 A1 m

theorem A_eq_G (h_all : ConjectureType) (m : ℕ) :
  ((A355898 (3773 + m) + 1 : ℕ) : ZMod p) = G (((A355898 3773 + 1 : ℕ) : ZMod p)) (((A355898 3774 + 1 : ℕ) : ZMod p)) m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | m
    · rfl
    · rfl
    · have ih1 := ih (m + 1) (Nat.lt_add_one (m + 1))
      have ih2 := ih m (by omega)
      have h_ih1_arg : 3773 + (m + 1) = 3773 + m + 1 := by omega
      rw [h_ih1_arg] at ih1
      have h_rec := (h_all (3775 + m) (by omega)).1
      have h_arg0 : 3775 + m = 3773 + m + 2 := by omega
      rw [h_arg0] at h_rec
      have h_sub1 : 3773 + m + 2 - 1 = 3773 + m + 1 := by omega
      have h_sub2 : 3773 + m + 2 - 2 = 3773 + m := by omega
      rw [h_sub1, h_sub2] at h_rec
      have h_rec_cast : ((A355898 (3773 + m + 2) + 1 : ℕ) : ZMod p) = ((A355898 (3773 + m + 1) + 1 : ℕ) : ZMod p) + ((A355898 (3773 + m) + 1 : ℕ) : ZMod p) := by
        rw [h_rec]
        push_cast
        ring
      have h_eq : 3773 + (m + 1 + 1) = 3773 + m + 2 := by omega
      rw [h_eq]
      have h_G_rec : G ((A355898 3773 + 1 : ℕ) : ZMod p) ((A355898 3774 + 1 : ℕ) : ZMod p) (m + 2) =
                     G ((A355898 3773 + 1 : ℕ) : ZMod p) ((A355898 3774 + 1 : ℕ) : ZMod p) (m + 1) +
                     G ((A355898 3773 + 1 : ℕ) : ZMod p) ((A355898 3774 + 1 : ℕ) : ZMod p) m := by rfl
      rw [h_G_rec]
      rw [h_rec_cast, ih1, ih2]

def mat_mul (M1 M2 : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p × ZMod p × ZMod p × ZMod p :=
  let (a1, b1, c1, d1) := M1
  let (a2, b2, c2, d2) := M2
  (a1 * a2 + b1 * c2, a1 * b2 + b1 * d2, c1 * a2 + d1 * c2, c1 * b2 + d1 * d2)

theorem mat_mul_assoc (M1 M2 M3 : ZMod p × ZMod p × ZMod p × ZMod p) :
  mat_mul (mat_mul M1 M2) M3 = mat_mul M1 (mat_mul M2 M3) := by
  rcases M1 with ⟨a1, b1, c1, d1⟩
  rcases M2 with ⟨a2, b2, c2, d2⟩
  rcases M3 with ⟨a3, b3, c3, d3⟩
  simp only [mat_mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem mat_mul_one_left (M : ZMod p × ZMod p × ZMod p × ZMod p) :
  mat_mul (1, 0, 0, 1) M = M := by
  rcases M with ⟨a, b, c, d⟩
  simp only [mat_mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem mat_mul_one_right (M : ZMod p × ZMod p × ZMod p × ZMod p) :
  mat_mul M (1, 0, 0, 1) = M := by
  rcases M with ⟨a, b, c, d⟩
  simp only [mat_mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

def mat_pow_slow (M : ZMod p × ZMod p × ZMod p × ZMod p) : ℕ → ZMod p × ZMod p × ZMod p × ZMod p
| 0 => (1, 0, 0, 1)
| n + 1 => mat_mul M (mat_pow_slow M n)

theorem mat_pow_slow_one (M : ZMod p × ZMod p × ZMod p × ZMod p) :
  mat_pow_slow M 1 = M := by
  simp only [mat_pow_slow]
  exact mat_mul_one_right M

theorem mat_pow_slow_add (M : ZMod p × ZMod p × ZMod p × ZMod p) (a b : ℕ) :
  mat_pow_slow M (a + b) = mat_mul (mat_pow_slow M a) (mat_pow_slow M b) := by
  induction a with
  | zero =>
    rw [zero_add]
    simp only [mat_pow_slow]
    rw [mat_mul_one_left]
  | succ a ih =>
    have h_add : a + 1 + b = (a + b) + 1 := by omega
    rw [h_add]
    simp only [mat_pow_slow]
    rw [ih]
    rw [mat_mul_assoc]

def mat_vec_mul (M : ZMod p × ZMod p × ZMod p × ZMod p) (v : ZMod p × ZMod p) : ZMod p × ZMod p :=
  let (a, b, c, d) := M
  let (x, y) := v
  (a * x + b * y, c * x + d * y)

theorem mat_vec_mul_assoc (M1 M2 : ZMod p × ZMod p × ZMod p × ZMod p) (v : ZMod p × ZMod p) :
  mat_vec_mul (mat_mul M1 M2) v = mat_vec_mul M1 (mat_vec_mul M2 v) := by
  rcases M1 with ⟨a1, b1, c1, d1⟩
  rcases M2 with ⟨a2, b2, c2, d2⟩
  rcases v with ⟨x, y⟩
  simp only [mat_mul, mat_vec_mul, Prod.mk.injEq]
  refine ⟨by ring, by ring⟩

theorem G_pair_eq_mat_pow (A0 A1 : ZMod p) (m : ℕ) :
  (G A0 A1 m, G A0 A1 (m + 1)) = mat_vec_mul (mat_pow_slow (0, 1, 1, 1) m) (A0, A1) := by
  induction m with
  | zero =>
    simp only [G, mat_pow_slow, mat_vec_mul, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  | succ m ih =>
    have h_G_rec : G A0 A1 (m + 2) = G A0 A1 (m + 1) + G A0 A1 m := by rfl
    have h_succ : (mat_pow_slow (0, 1, 1, 1) (m + 1)) = mat_mul (0, 1, 1, 1) (mat_pow_slow (0, 1, 1, 1) m) := by rfl
    rw [h_succ]
    rw [mat_vec_mul_assoc]
    rw [← ih]
    simp only [mat_vec_mul, Prod.mk.injEq]
    rw [h_G_rec]
    refine ⟨by ring, by ring⟩

-- Define the fast power-of-two matrix tower
def M0 : ZMod p × ZMod p × ZMod p × ZMod p := (0, 1, 1, 1)
def M1 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M0 M0
def M2 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M1 M1
def M3 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M2 M2
def M4 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M3 M3
def M5 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M4 M4
def M6 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M5 M5
def M7 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M6 M6
def M8 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M7 M7
def M9 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M8 M8
def M10 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M9 M9
def M11 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M10 M10
def M12 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M11 M11
def M13 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M12 M12
def M14 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M13 M13
def M15 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M14 M14
def M16 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M15 M15
def M17 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M16 M16
def M18 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M17 M17
def M19 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M18 M18
def M20 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M19 M19
def M21 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M20 M20
def M22 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M21 M21
def M23 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M22 M22
def M24 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M23 M23
def M25 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M24 M24
def M26 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M25 M25
def M27 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M26 M26
def M28 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M27 M27
def M29 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M28 M28
def M30 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M29 M29
def M31 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M30 M30
def M32 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M31 M31
def M33 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M32 M32
def M34 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M33 M33
def M35 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M34 M34
def M36 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M35 M35
def M37 : ZMod p × ZMod p × ZMod p × ZMod p := mat_mul M36 M36

theorem h_M_eq (a : ℕ) (Ma Mb : ZMod p × ZMod p × ZMod p × ZMod p) (hMa : mat_pow_slow M0 a = Ma) (hMb : Mb = mat_mul Ma Ma) :
  mat_pow_slow M0 (a + a) = Mb := by
  rw [mat_pow_slow_add, hMa, hMb]

theorem h_M0 : mat_pow_slow M0 1 = M0 := mat_pow_slow_one M0
theorem h_M1 : mat_pow_slow M0 2 = M1 := h_M_eq 1 M0 M1 h_M0 rfl
theorem h_M2 : mat_pow_slow M0 4 = M2 := h_M_eq 2 M1 M2 h_M1 rfl
theorem h_M3 : mat_pow_slow M0 8 = M3 := h_M_eq 4 M2 M3 h_M2 rfl
theorem h_M4 : mat_pow_slow M0 16 = M4 := h_M_eq 8 M3 M4 h_M3 rfl
theorem h_M5 : mat_pow_slow M0 32 = M5 := h_M_eq 16 M4 M5 h_M4 rfl
theorem h_M6 : mat_pow_slow M0 64 = M6 := h_M_eq 32 M5 M6 h_M5 rfl
theorem h_M7 : mat_pow_slow M0 128 = M7 := h_M_eq 64 M6 M7 h_M6 rfl
theorem h_M8 : mat_pow_slow M0 256 = M8 := h_M_eq 128 M7 M8 h_M7 rfl
theorem h_M9 : mat_pow_slow M0 512 = M9 := h_M_eq 256 M8 M9 h_M8 rfl
theorem h_M10 : mat_pow_slow M0 1024 = M10 := h_M_eq 512 M9 M10 h_M9 rfl
theorem h_M11 : mat_pow_slow M0 2048 = M11 := h_M_eq 1024 M10 M11 h_M10 rfl
theorem h_M12 : mat_pow_slow M0 4096 = M12 := h_M_eq 2048 M11 M12 h_M11 rfl
theorem h_M13 : mat_pow_slow M0 8192 = M13 := h_M_eq 4096 M12 M13 h_M12 rfl
theorem h_M14 : mat_pow_slow M0 16384 = M14 := h_M_eq 8192 M13 M14 h_M13 rfl
theorem h_M15 : mat_pow_slow M0 32768 = M15 := h_M_eq 16384 M14 M15 h_M14 rfl
theorem h_M16 : mat_pow_slow M0 65536 = M16 := h_M_eq 32768 M15 M16 h_M15 rfl
theorem h_M17 : mat_pow_slow M0 131072 = M17 := h_M_eq 65536 M16 M17 h_M16 rfl
theorem h_M18 : mat_pow_slow M0 262144 = M18 := h_M_eq 131072 M17 M18 h_M17 rfl
theorem h_M19 : mat_pow_slow M0 524288 = M19 := h_M_eq 262144 M18 M19 h_M18 rfl
theorem h_M20 : mat_pow_slow M0 1048576 = M20 := h_M_eq 524288 M19 M20 h_M19 rfl
theorem h_M21 : mat_pow_slow M0 2097152 = M21 := h_M_eq 1048576 M20 M21 h_M20 rfl
theorem h_M22 : mat_pow_slow M0 4194304 = M22 := h_M_eq 2097152 M21 M22 h_M21 rfl
theorem h_M23 : mat_pow_slow M0 8388608 = M23 := h_M_eq 4194304 M22 M23 h_M22 rfl
theorem h_M24 : mat_pow_slow M0 16777216 = M24 := h_M_eq 8388608 M23 M24 h_M23 rfl
theorem h_M25 : mat_pow_slow M0 33554432 = M25 := h_M_eq 16777216 M24 M25 h_M24 rfl
theorem h_M26 : mat_pow_slow M0 67108864 = M26 := h_M_eq 33554432 M25 M26 h_M25 rfl
theorem h_M27 : mat_pow_slow M0 134217728 = M27 := h_M_eq 67108864 M26 M27 h_M26 rfl
theorem h_M28 : mat_pow_slow M0 268435456 = M28 := h_M_eq 134217728 M27 M28 h_M27 rfl
theorem h_M29 : mat_pow_slow M0 536870912 = M29 := h_M_eq 268435456 M28 M29 h_M28 rfl
theorem h_M30 : mat_pow_slow M0 1073741824 = M30 := h_M_eq 536870912 M29 M30 h_M29 rfl
theorem h_M31 : mat_pow_slow M0 2147483648 = M31 := h_M_eq 1073741824 M30 M31 h_M30 rfl
theorem h_M32 : mat_pow_slow M0 4294967296 = M32 := h_M_eq 2147483648 M31 M32 h_M31 rfl
theorem h_M33 : mat_pow_slow M0 8589934592 = M33 := h_M_eq 4294967296 M32 M33 h_M32 rfl
theorem h_M34 : mat_pow_slow M0 17179869184 = M34 := h_M_eq 8589934592 M33 M34 h_M33 rfl
theorem h_M35 : mat_pow_slow M0 34359738368 = M35 := h_M_eq 17179869184 M34 M35 h_M34 rfl
theorem h_M36 : mat_pow_slow M0 68719476736 = M36 := h_M_eq 34359738368 M35 M36 h_M35 rfl
theorem h_M37 : mat_pow_slow M0 137438953472 = M37 := h_M_eq 68719476736 M36 M37 h_M36 rfl

theorem h_M_final : mat_pow_slow M0 249580073233 =
  mat_mul M37 (mat_mul M36 (mat_mul M35 (mat_mul M33 (mat_mul M28 (mat_mul M27 (mat_mul M26 (mat_mul M21 (mat_mul M16 (mat_mul M15 (mat_mul M13 (mat_mul M12 (mat_mul M8 (mat_mul M4 M0))))))))))))) := by
  have h_sum : 249580073233 = 137438953472 + (68719476736 + (34359738368 + (8589934592 + (268435456 + (134217728 + (67108864 + (2097152 + (65536 + (32768 + (8192 + (4096 + (256 + (16 + 1))))))))))))) := by rfl
  rw [h_sum]
  repeat rw [mat_pow_slow_add]
  rw [h_M37, h_M36, h_M35, h_M33, h_M28, h_M27, h_M26, h_M21, h_M16, h_M15, h_M13, h_M12, h_M8, h_M4, h_M0]

def G0 : ZMod p := ((A355898_fast 3773 + 1 : ℕ) : ZMod p)
def G1 : ZMod p := ((A355898_fast 3774 + 1 : ℕ) : ZMod p)

theorem h_G0_eq : (G0 : ZMod p) = ((A355898 3773 + 1 : ℕ) : ZMod p) := by
  exact congrArg (fun x => ((x + 1 : ℕ) : ZMod p)) (A355898_fast_eq 3773 (by omega))

theorem h_G1_eq : (G1 : ZMod p) = ((A355898 3774 + 1 : ℕ) : ZMod p) := by
  exact congrArg (fun x => ((x + 1 : ℕ) : ZMod p)) (A355898_fast_eq 3774 (by omega))

theorem h_G_mod_all (m : ℕ) :
  G G0 G1 m = G ((A355898 3773 + 1 : ℕ) : ZMod p) ((A355898 3774 + 1 : ℕ) : ZMod p) m := by
  exact congrArg₂ (fun x y => G x y m) h_G0_eq h_G1_eq

theorem oeis_a355898_conjecture.disproof :
  ¬ (∀ (n : ℕ) (h : 3775 ≤ n),
    (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
    ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
    ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)) := by
  intro h_all
  have h_gcd := gcd_eq_1_of_h_all h_all 249580073234 (by omega)
  -- G_pair_eq_mat_pow gives:
  have h_G_eq : (G G0 G1 249580073233, G G0 G1 (249580073233 + 1)) =
    mat_vec_mul (mat_pow_slow M0 249580073233) (G0, G1) := G_pair_eq_mat_pow G0 G1 249580073233
  -- We do not rw on h_G_eq directly to avoid stack overflow on LHS
  have h_eval : mat_vec_mul (mat_mul M37 (mat_mul M36 (mat_mul M35 (mat_mul M33 (mat_mul M28 (mat_mul M27 (mat_mul M26 (mat_mul M21 (mat_mul M16 (mat_mul M15 (mat_mul M13 (mat_mul M12 (mat_mul M8 (mat_mul M4 M0)))))))))))))) (G0, G1) = (1, 1) := by decide
  have h_RHS_eq : mat_vec_mul (mat_pow_slow M0 249580073233) (G0, G1) = (1, 1) := by
    rw [h_M_final]
    exact h_eval
  have h_G_eq_final := Eq.trans h_G_eq h_RHS_eq
  
  have h_G33 : G G0 G1 249580073233 = 1 := (Prod.ext_iff.mp h_G_eq_final).1
  have h_G34 : G G0 G1 249580073234 = 1 := (Prod.ext_iff.mp h_G_eq_final).2
  
  have h_G_mod33 := h_G_mod_all 249580073233
  rw [h_G33] at h_G_mod33
  
  have h_A_eq33 := A_eq_G h_all 249580073233
  rw [← h_G_mod33] at h_A_eq33
  -- Now h_A_eq33 is: ((A355898 (3773 + 249580073233) + 1 : ℕ) : ZMod p) = 1
  have h_div33 : (A355898 (3773 + 249580073233) : ZMod p) = 0 :=
    have h_eq_1 : (A355898 (3773 + 249580073233) : ZMod p) + 1 = 1 := Eq.trans (Nat.cast_add_one _).symm h_A_eq33
    add_right_cancel (Eq.trans h_eq_1 (zero_add 1).symm)
  
  have h_G_mod34 := h_G_mod_all 249580073234
  rw [h_G34] at h_G_mod34
  have h_A_eq34 := A_eq_G h_all 249580073234
  rw [← h_G_mod34] at h_A_eq34
  have h_div34 : (A355898 (3773 + 249580073234) : ZMod p) = 0 :=
    have h_eq_1 : (A355898 (3773 + 249580073234) : ZMod p) + 1 = 1 := Eq.trans (Nat.cast_add_one _).symm h_A_eq34
    add_right_cancel (Eq.trans h_eq_1 (zero_add 1).symm)
  
  have hdvd33 : p ∣ A355898 (3773 + 249580073233) := (ZMod.natCast_eq_zero_iff _ _).mp h_div33
  have h_arg_eq34 : A355898 (3773 + 249580073234) = A355898 (3774 + 249580073233) := congrArg A355898 (by omega)
  rw [h_arg_eq34] at h_div34
  have hdvd34 : p ∣ A355898 (3774 + 249580073233) := (ZMod.natCast_eq_zero_iff _ _).mp h_div34
  
  have h_dvd_gcd : p ∣ Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) := Nat.dvd_gcd hdvd34 hdvd33
  
  have h_num_eq : 3772 + 249580073234 = 3773 + 249580073233 := by omega
  have h_A_eq : A355898 (3772 + 249580073234) = A355898 (3773 + 249580073233) := congrArg A355898 h_num_eq
  rw [h_A_eq] at h_gcd
  
  have h_gcd_eq_1 : Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) = 1 := by
    have h_arg_eq_first : A355898 (3774 + 249580073233) = A355898 (3773 + 249580073234) := congrArg A355898 (by omega)
    rw [h_arg_eq_first]
    exact h_gcd
  
  rw [h_gcd_eq_1] at h_dvd_gcd
  have h_p_le_1 : p ≤ 1 := Nat.le_of_dvd (by decide) h_dvd_gcd
  revert h_p_le_1
  decide



