import FormalConjectures.Util.ProblemImports

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

def A355898_fast_loop : ℕ → ℕ → ℕ → ℕ
| 0, a, _ => a
| 1, _, b => b
| n + 2, a, b =>
  let g := Nat.gcd b a
  A355898_fast_loop (n + 1) b (g + (b + a) / g)

theorem A355898_fast_loop_eq : ∀ (n k : ℕ),
  A355898_fast_loop n (A355898 (k + 1)) (A355898 (k + 2)) = A355898 (k + n + 1)
| 0, k => rfl
| 1, k => rfl
| n + 2, k => by
  have h_step : A355898_fast_loop (n + 2) (A355898 (k + 1)) (A355898 (k + 2)) =
                A355898_fast_loop (n + 1) (A355898 (k + 2)) (Nat.gcd (A355898 (k + 2)) (A355898 (k + 1)) +
                (A355898 (k + 2) + A355898 (k + 1)) / Nat.gcd (A355898 (k + 2)) (A355898 (k + 1))) := rfl
  rw [h_step]
  have h_eq : Nat.gcd (A355898 (k + 2)) (A355898 (k + 1)) +
              (A355898 (k + 2) + A355898 (k + 1)) / Nat.gcd (A355898 (k + 2)) (A355898 (k + 1)) =
              A355898 (k + 3) := rfl
  rw [h_eq]
  have h_arg : k + 1 + (n + 1) + 1 = k + (n + 2) + 1 := by omega
  rw [← h_arg]
  have ih := A355898_fast_loop_eq (n + 1) (k + 1)
  exact ih

def A355898_fast (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => A355898_fast_loop n 1 1

theorem A355898_eq_fast (n : ℕ) : A355898 n = A355898_fast n := by
  cases n with
  | zero => rfl
  | succ m =>
    dsimp [A355898_fast]
    have h_eq := A355898_fast_loop_eq m 0
    have h_idx : 0 + m + 1 = m + 1 := by omega
    rw [h_idx] at h_eq
    exact h_eq.symm

theorem test_mul_mod (a b p : ℕ) : ((a % p) * b) % p = (a * b) % p := by
  omega


def Y : ℕ → ℕ
| 0 => A355898_fast 3773 + 1
| 1 => A355898_fast 3774 + 1
| k + 2 => Y (k + 1) + Y k

theorem Y_ge_one (m : ℕ) : 1 ≤ Y m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      dsimp [Y]
      omega
    | succ m' =>
      cases m' with
      | zero =>
        dsimp [Y]
        omega
      | succ m'' =>
        have h_eq : Y (m'' + 2) = Y (m'' + 1) + Y m'' := rfl
        rw [h_eq]
        have ih1 := ih (m'' + 1) (by omega)
        have ih2 := ih m'' (by omega)
        omega

def a_prime (k : ℕ) : ℕ :=
  Y (k - 3773) - 1

theorem a_prime_step (k : ℕ) (hk : 3775 ≤ k) :
  a_prime k = 1 + a_prime (k - 1) + a_prime (k - 2) := by
  have h_sub : k - 3773 = (k - 3775) + 2 := by omega
  dsimp [a_prime]
  rw [h_sub]
  have h_Y : Y ((k - 3775) + 2) = Y ((k - 3775) + 1) + Y (k - 3775) := rfl
  rw [h_Y]
  have h1 : k - 1 - 3773 = (k - 3775) + 1 := by omega
  have h2 : k - 2 - 3773 = k - 3775 := by omega
  rw [h1, h2]
  have hY1 : 1 ≤ Y ((k - 3775) + 1) := Y_ge_one ((k - 3775) + 1)
  have hY2 : 1 ≤ Y (k - 3775) := Y_ge_one (k - 3775)
  omega


theorem A355898_eq_a_prime (h_rec : ∀ (n : ℕ) (h : 3775 ≤ n), A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  (k : ℕ) (hk : 3773 ≤ k) : A355898 k = a_prime k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases le_or_gt 3775 k with hk5 | hk5
    · -- k >= 3775
      have hk1 : 3773 ≤ k - 1 := by omega
      have hk2 : 3773 ≤ k - 2 := by omega
      have ih1 := ih (k - 1) (by omega) hk1
      have ih2 := ih (k - 2) (by omega) hk2
      rw [h_rec k hk5]
      rw [ih1, ih2]
      exact (a_prime_step k hk5).symm
    · -- k < 3775
      -- Since 3773 <= k and k < 3775, k can only be 3773 or 3774
      interval_cases k
      · dsimp [a_prime, Y]
        rw [A355898_eq_fast]
      · dsimp [a_prime, Y]
        rw [A355898_eq_fast]


def matrix_mul_mod (A B : (Nat × Nat) × (Nat × Nat)) (p : Nat) : (Nat × Nat) × (Nat × Nat) :=
  let ((a11, a12), (a21, a22)) := A
  let ((b11, b12), (b21, b22)) := B
  (((a11 * b11 + a12 * b21) % p, (a11 * b12 + a12 * b22) % p),
   ((a21 * b11 + a22 * b21) % p, (a21 * b12 + a22 * b22) % p))

def matrix_vector_mul_mod (M : (Nat × Nat) × (Nat × Nat)) (V : Nat × Nat) (p : Nat) : Nat × Nat :=
  let ((m11, m12), (m21, m22)) := M
  let (v1, v2) := V
  (((m11 * v1 + m12 * v2) % p, (m21 * v1 + m22 * v2) % p))

theorem matrix_vector_mul_assoc (M : (Nat × Nat) × (Nat × Nat)) (V : Nat × Nat) (p : Nat) :
  matrix_vector_mul_mod (matrix_mul_mod ((1, 1), (1, 0)) M p) V p =
  matrix_vector_mul_mod ((1, 1), (1, 0)) (matrix_vector_mul_mod M V p) p := by
  rcases M with ⟨⟨a11, a12⟩, ⟨a21, a22⟩⟩
  rcases V with ⟨v1, v2⟩
  dsimp [matrix_vector_mul_mod, matrix_mul_mod]
  ext
  · rw [← Nat.add_mod]
    congr 1
    ring
  · congr 1
    ring

