import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 100000

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

-- fast implementation of A355898
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

theorem A355898_step_sub (n : ℕ) (hn : 1 ≤ n) :
  A355898 (n + 2) = Nat.gcd (A355898 (n + 1)) (A355898 n) + (A355898 (n + 1) + A355898 n) / Nat.gcd (A355898 (n + 1)) (A355898 n) := by
  rcases n with _ | m
  · omega
  · rfl

def step_loop (v : ℕ × ℕ) : ℕ × ℕ :=
  (v.2, Nat.gcd v.2 v.1 + (v.2 + v.1) / Nat.gcd v.2 v.1)

def step_10 (v : ℕ × ℕ) : ℕ × ℕ :=
  step_loop (step_loop (step_loop (step_loop (step_loop (step_loop (step_loop (step_loop (step_loop (step_loop v)))))))))

def step_100 (v : ℕ × ℕ) : ℕ × ℕ :=
  step_10 (step_10 (step_10 (step_10 (step_10 (step_10 (step_10 (step_10 (step_10 (step_10 v)))))))))

def step_loop_n : ℕ → ℕ × ℕ → ℕ × ℕ
| 0, v => v
| k + 1, v => step_loop (step_loop_n k v)

def loop_super_fast : ℕ → ℕ × ℕ → ℕ × ℕ
| 0, v => v
| n + 1, v => step_100 (loop_super_fast n v)

theorem step_loop_n_add (a b : ℕ) (v : ℕ × ℕ) :
  step_loop_n (a + b) v = step_loop_n a (step_loop_n b v) := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ a ih =>
    have h_add : a + 1 + b = (a + b) + 1 := by omega
    rw [h_add]
    dsimp [step_loop_n]
    rw [ih]

theorem step_loop_n_100 (v : ℕ × ℕ) : step_loop_n 100 v = step_100 v := rfl

theorem loop_super_fast_eq (n : ℕ) (v : ℕ × ℕ) :
  loop_super_fast n v = step_loop_n (100 * n) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [loop_super_fast]
    rw [ih]
    rw [← step_loop_n_100]
    rw [← step_loop_n_add]
    congr 1
    omega

theorem A355898_fast_loop_eq_step_loop_n : ∀ (k : ℕ) (v : ℕ × ℕ),
  A355898_fast_loop (k + 1) v.1 v.2 = (step_loop_n k v).2
| 0, v => rfl
| 1, v => rfl
| k + 2, v => by
  have h_step : A355898_fast_loop (k + 3) v.1 v.2 = A355898_fast_loop (k + 2) (step_loop v).1 (step_loop v).2 := rfl
  rw [h_step]
  have ih := A355898_fast_loop_eq_step_loop_n (k + 1) (step_loop v)
  rw [ih]
  have h_add_lem := step_loop_n_add (k + 1) 1 v
  exact congrArg Prod.snd h_add_lem.symm

def p : ℕ := 195318521017
def j : ℕ := 249580073232
def T : (Nat × Nat) × (Nat × Nat) := ((1, 1), (1, 0))

def matrix_mul_mod (A B : (Nat × Nat) × (Nat × Nat)) (p : Nat) : (Nat × Nat) × (Nat × Nat) :=
  let ((a11, a12), (a21, a22)) := A
  let ((b11, b12), (b21, b22)) := B
  (((a11 * b11 + a12 * b21) % p, (a11 * b12 + a12 * b22) % p),
   ((a21 * b11 + a22 * b21) % p, (a21 * b12 + a22 * b22) % p))

theorem test_mul_mod (a b p : ℕ) : ((a % p) * b) % p = (a * b) % p := by
  rw [Nat.mul_mod (a % p) b p]
  rw [Nat.mod_mod]
  rw [← Nat.mul_mod a b p]

theorem test_mul_mod_right (a b p : ℕ) : (a * (b % p)) % p = (a * b) % p := by
  rw [Nat.mul_mod a (b % p) p]
  rw [Nat.mod_mod]
  rw [← Nat.mul_mod a b p]

theorem assoc_helper (x1 x2 y1 y2 p : ℕ) : (((x1 % p) * y1 + (x2 % p) * y2) % p) = (x1 * y1 + x2 * y2) % p := by
  rw [Nat.add_mod]
  rw [test_mul_mod x1 y1 p]
  rw [test_mul_mod x2 y2 p]
  rw [← Nat.add_mod]

theorem assoc_helper_right (x1 x2 y1 y2 p : ℕ) : ((x1 * (y1 % p) + x2 * (y2 % p)) % p) = (x1 * y1 + x2 * y2) % p := by
  rw [Nat.add_mod]
  rw [test_mul_mod_right x1 y1 p]
  rw [test_mul_mod_right x2 y2 p]
  rw [← Nat.add_mod]

theorem matrix_mul_assoc (A B C : (Nat × Nat) × (Nat × Nat)) (p : Nat) :
  matrix_mul_mod (matrix_mul_mod A B p) C p = matrix_mul_mod A (matrix_mul_mod B C p) p := by
  rcases A with ⟨⟨a11, a12⟩, ⟨a21, a22⟩⟩
  rcases B with ⟨⟨b11, b12⟩, ⟨b21, b22⟩⟩
  rcases C with ⟨⟨c11, c12⟩, ⟨c21, c22⟩⟩
  ext
  · dsimp [matrix_mul_mod]
    rw [assoc_helper (a11 * b11 + a12 * b21) (a11 * b12 + a12 * b22) c11 c21 p]
    rw [assoc_helper_right a11 a12 (b11 * c11 + b12 * c21) (b21 * c11 + b22 * c21) p]
    congr 1
    ring
  · dsimp [matrix_mul_mod]
    rw [assoc_helper (a11 * b11 + a12 * b21) (a11 * b12 + a12 * b22) c12 c22 p]
    rw [assoc_helper_right a11 a12 (b11 * c12 + b12 * c22) (b21 * c12 + b22 * c22) p]
    congr 1
    ring
  · dsimp [matrix_mul_mod]
    rw [assoc_helper (a21 * b11 + a22 * b21) (a21 * b12 + a22 * b22) c11 c21 p]
    rw [assoc_helper_right a21 a22 (b11 * c11 + b12 * c21) (b21 * c11 + b22 * c21) p]
    congr 1
    ring
  · dsimp [matrix_mul_mod]
    rw [assoc_helper (a21 * b11 + a22 * b21) (a21 * b12 + a22 * b22) c12 c22 p]
    rw [assoc_helper_right a21 a22 (b11 * c12 + b12 * c22) (b21 * c12 + b22 * c22) p]
    congr 1
    ring

theorem matrix_mul_id_left (M : (Nat × Nat) × (Nat × Nat)) (p : Nat) :
  matrix_mul_mod ((1, 0), (0, 1)) M p = (((M.1.1 % p, M.1.2 % p), (M.2.1 % p, M.2.2 % p))) := by
  rcases M with ⟨⟨m11, m12⟩, ⟨m21, m22⟩⟩
  dsimp [matrix_mul_mod]
  simp only [one_mul, zero_mul, add_zero, zero_add]

def matrix_pow_rec (A : (Nat × Nat) × (Nat × Nat)) (p : Nat) : Nat → (Nat × Nat) × (Nat × Nat)
| 0 => ((1, 0), (0, 1))
| k + 1 => matrix_mul_mod A (matrix_pow_rec A p k) p

theorem matrix_pow_rec_reduced (A : (Nat × Nat) × (Nat × Nat)) (p : Nat) (hp : 2 ≤ p) (b : ℕ) :
  (((matrix_pow_rec A p b).1.1 % p, (matrix_pow_rec A p b).1.2 % p),
   ((matrix_pow_rec A p b).2.1 % p, (matrix_pow_rec A p b).2.2 % p)) = matrix_pow_rec A p b := by
  cases b with
  | zero =>
    dsimp [matrix_pow_rec]
    have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
    ext <;> simp [h1]
  | succ m =>
    dsimp [matrix_pow_rec, matrix_mul_mod]
    simp only [Nat.mod_mod]

theorem matrix_pow_rec_add (A : (Nat × Nat) × (Nat × Nat)) (p : Nat) (hp : 2 ≤ p) (a b : ℕ) :
  matrix_pow_rec A p (a + b) = matrix_mul_mod (matrix_pow_rec A p a) (matrix_pow_rec A p b) p := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    dsimp [matrix_pow_rec]
    rw [matrix_mul_id_left]
    rw [matrix_pow_rec_reduced A p hp b]
  | succ a ih =>
    have h_add : a + 1 + b = a + b + 1 := by omega
    rw [h_add]
    dsimp [matrix_pow_rec]
    rw [ih]
    rw [matrix_mul_assoc]

def matrix_vector_mul_mod (M : (Nat × Nat) × (Nat × Nat)) (V : Nat × Nat) (p : Nat) : Nat × Nat :=
  let ((m11, m12), (m21, m22)) := M
  let (v1, v2) := V
  (((m11 * v1 + m12 * v2) % p, (m21 * v1 + m22 * v2) % p))

theorem matrix_vector_mul_assoc (M : (Nat × Nat) × (Nat × Nat)) (V : Nat × Nat) (p : Nat) :
  matrix_vector_mul_mod (matrix_mul_mod T M p) V p =
  matrix_vector_mul_mod T (matrix_vector_mul_mod M V p) p := by
  rcases M with ⟨⟨a11, a12⟩, ⟨a21, a22⟩⟩
  rcases V with ⟨v1, v2⟩
  dsimp [T, matrix_vector_mul_mod, matrix_mul_mod]
  ext
  · simp only [one_mul, zero_mul, add_zero]
    rw [Nat.add_mod, test_mul_mod (a11 + a21) v1 p, test_mul_mod (a12 + a22) v2 p, ← Nat.add_mod]
    rw [← Nat.add_mod]
    congr 1
    ring
  · simp only [one_mul, zero_mul, add_zero]
    rw [Nat.add_mod, test_mul_mod a11 v1 p, test_mul_mod a12 v2 p, ← Nat.add_mod]
    rw [Nat.mod_mod]

def Y : ℕ → ℕ
| 0 => A355898_fast 3773 + 1
| 1 => A355898_fast 3774 + 1
| k + 2 => Y (k + 1) + Y k

theorem Y_step (k : ℕ) : Y (k + 2) = Y (k + 1) + Y k := rfl

theorem Y_step_sub (k : ℕ) (hk : 1 ≤ k) : Y (k + 1) = Y k + Y (k - 1) := by
  rcases k with _ | m
  · omega
  · rfl

theorem Y_ge_one (m : ℕ) : 1 ≤ Y m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      dsimp [Y]
      exact Nat.succ_le_succ (Nat.zero_le _)
    | succ m' =>
      cases m' with
      | zero =>
        dsimp [Y]
        exact Nat.succ_le_succ (Nat.zero_le _)
      | succ m'' =>
        have h_eq : Y (m'' + 2) = Y (m'' + 1) + Y m'' := rfl
        rw [h_eq]
        have ih1 := ih (m'' + 1) (by omega)
        have ih2 := ih m'' (by omega)
        omega

theorem Y_step_pow (k p : ℕ) :
  (Y (k + 1) % p, Y k % p) = matrix_vector_mul_mod (matrix_pow_rec T p k) (Y 1 % p, Y 0 % p) p := by
  induction k with
  | zero =>
    dsimp [matrix_pow_rec, matrix_vector_mul_mod]
    simp only [one_mul, zero_mul, zero_add, add_zero, Nat.mod_mod]
  | succ k ih =>
    have h_Y : Y (k + 2) = Y (k + 1) + Y k := rfl
    dsimp [matrix_pow_rec]
    rw [matrix_vector_mul_assoc]
    rw [← ih]
    dsimp [T, matrix_vector_mul_mod]
    ext
    · simp only [one_mul, zero_mul, add_zero]
      rw [h_Y]
      rw [← Nat.add_mod]
    · simp only [one_mul, zero_mul, add_zero]
      rw [Nat.mod_mod]

theorem Y1_mod_p : Y 1 % p = 99768150822 := by
  have h_eq1 : Y 1 = (step_loop_n 72 (loop_super_fast 37 (1, 1))).2 + 1 := by
    dsimp [Y, A355898_fast]
    have h_num : 3773 = 3772 + 1 := rfl
    rw [h_num]
    rw [A355898_fast_loop_eq_step_loop_n 3772 (1, 1), loop_super_fast_eq]
    rw [← step_loop_n_add]
  rw [h_eq1]
  rfl

theorem Y0_mod_p : Y 0 % p = 77940394259 := by
  have h_eq0 : Y 0 = (step_loop_n 71 (loop_super_fast 37 (1, 1))).2 + 1 := by
    dsimp [Y, A355898_fast]
    have h_num : 3772 = 3771 + 1 := rfl
    rw [h_num]
    rw [A355898_fast_loop_eq_step_loop_n 3771 (1, 1), loop_super_fast_eq]
    rw [← step_loop_n_add]
  rw [h_eq0]
  rfl

theorem test_steps (hp : 2 ≤ p) : matrix_pow_rec T p j = ((21827756563, 117378126758), (117378126758, 99768150822)) := by
    have h_1 : matrix_pow_rec T p 1 = T := rfl
    have h_2 : matrix_pow_rec T p 2 = ((2, 1), (1, 1)) := by
      have h_add : 2 = 1 + 1 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 1]
      rw [h_1]
      rfl
    have h_3 : matrix_pow_rec T p 3 = ((3, 2), (2, 1)) := by
      have h_add : 3 = 1 + 2 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 2]
      rw [h_1, h_2]
      rfl
    have h_6 : matrix_pow_rec T p 6 = ((13, 8), (8, 5)) := by
      have h_add : 6 = 3 + 3 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 3 3]
      rw [h_3]
      rfl
    have h_7 : matrix_pow_rec T p 7 = ((21, 13), (13, 8)) := by
      have h_add : 7 = 1 + 6 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 6]
      rw [h_1, h_6]
      rfl
    have h_14 : matrix_pow_rec T p 14 = ((610, 377), (377, 233)) := by
      have h_add : 14 = 7 + 7 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 7 7]
      rw [h_7]
      rfl
    have h_28 : matrix_pow_rec T p 28 = ((514229, 317811), (317811, 196418)) := by
      have h_add : 28 = 14 + 14 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 14 14]
      rw [h_14]
      rfl
    have h_29 : matrix_pow_rec T p 29 = ((832040, 514229), (514229, 317811)) := by
      have h_add : 29 = 1 + 28 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 28]
      rw [h_1, h_28]
      rfl
    have h_58 : matrix_pow_rec T p 58 = ((175447941973, 5331166828), (5331166828, 170116775145)) := by
      have h_add : 58 = 29 + 29 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 29 29]
      rw [h_29]
      rfl
    have h_116 : matrix_pow_rec T p 116 = ((46896169886, 192440766623), (192440766623, 49773924280)) := by
      have h_add : 116 = 58 + 58 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 58 58]
      rw [h_58]
      rfl
    have h_232 : matrix_pow_rec T p 232 = ((154854891933, 194305937469), (194305937469, 155867475481)) := by
      have h_add : 232 = 116 + 116 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 116 116]
      rw [h_116]
      rfl
    have h_464 : matrix_pow_rec T p 464 = ((29385216473, 27770261298), (27770261298, 1614955175)) := by
      have h_add : 464 = 232 + 232 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 232 232]
      rw [h_232]
      rfl
    have h_928 : matrix_pow_rec T p 928 = ((86864070201, 96254381253), (96254381253, 185928209965)) := by
      have h_add : 928 = 464 + 464 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 464 464]
      rw [h_464]
      rfl
    have h_929 : matrix_pow_rec T p 929 = ((183118451454, 86864070201), (86864070201, 96254381253)) := by
      have h_add : 929 = 1 + 928 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 928]
      rw [h_1, h_928]
      rfl
    have h_1858 : matrix_pow_rec T p 1858 = ((161742261918, 38868090280), (38868090280, 122874171638)) := by
      have h_add : 1858 = 929 + 929 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 929 929]
      rw [h_929]
      rfl
    have h_1859 : matrix_pow_rec T p 1859 = ((5291831181, 161742261918), (161742261918, 38868090280)) := by
      have h_add : 1859 = 1 + 1858 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 1858]
      rw [h_1, h_1858]
      rfl
    have h_3718 : matrix_pow_rec T p 3718 = ((45733414097, 109362536927), (109362536927, 131689398187)) := by
      have h_add : 3718 = 1859 + 1859 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1859 1859]
      rw [h_1859]
      rfl
    have h_3719 : matrix_pow_rec T p 3719 = ((155095951024, 45733414097), (45733414097, 109362536927)) := by
      have h_add : 3719 = 1 + 3718 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 3718]
      rw [h_1, h_3718]
      rfl
    have h_7438 : matrix_pow_rec T p 7438 = ((79381895081, 91402293237), (91402293237, 183298122861)) := by
      have h_add : 7438 = 3719 + 3719 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 3719 3719]
      rw [h_3719]
      rfl
    have h_14876 : matrix_pow_rec T p 14876 = ((150503511699, 124511110930), (124511110930, 25992400769)) := by
      have h_add : 14876 = 7438 + 7438 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 7438 7438]
      rw [h_7438]
      rfl
    have h_29752 : matrix_pow_rec T p 29752 = ((113547008666, 131120349488), (131120349488, 177745180195)) := by
      have h_add : 29752 = 14876 + 14876 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 14876 14876]
      rw [h_14876]
      rfl
    have h_59504 : matrix_pow_rec T p 59504 = ((36774427091, 38091898265), (38091898265, 194001049843)) := by
      have h_add : 59504 = 29752 + 29752 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 29752 29752]
      rw [h_29752]
      rfl
    have h_119008 : matrix_pow_rec T p 119008 = ((154094075776, 127215937123), (127215937123, 26878138653)) := by
      have h_add : 119008 = 59504 + 59504 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 59504 59504]
      rw [h_59504]
      rfl
    have h_119009 : matrix_pow_rec T p 119009 = ((85991491882, 154094075776), (154094075776, 127215937123)) := by
      have h_add : 119009 = 1 + 119008 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 119008]
      rw [h_1, h_119008]
      rfl
    have h_238018 : matrix_pow_rec T p 238018 = ((140692518066, 77229582369), (77229582369, 63462935697)) := by
      have h_add : 238018 = 119009 + 119009 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 119009 119009]
      rw [h_119009]
      rfl
    have h_476036 : matrix_pow_rec T p 476036 = ((171354009733, 133112644149), (133112644149, 38241365584)) := by
      have h_add : 476036 = 238018 + 238018 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 238018 238018]
      rw [h_238018]
      rfl
    have h_952072 : matrix_pow_rec T p 952072 = ((55750958039, 112954738797), (112954738797, 138114740259)) := by
      have h_add : 952072 = 476036 + 476036 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 476036 476036]
      rw [h_476036]
      rfl
    have h_1904144 : matrix_pow_rec T p 1904144 = ((117534068978, 158795593120), (158795593120, 154056996875)) := by
      have h_add : 1904144 = 952072 + 952072 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 952072 952072]
      rw [h_952072]
      rfl
    have h_3808288 : matrix_pow_rec T p 3808288 = ((55730958665, 179877156576), (179877156576, 71172323106)) := by
      have h_add : 3808288 = 1904144 + 1904144 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1904144 1904144]
      rw [h_1904144]
      rfl
    have h_3808289 : matrix_pow_rec T p 3808289 = ((40289594224, 55730958665), (55730958665, 179877156576)) := by
      have h_add : 3808289 = 1 + 3808288 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 3808288]
      rw [h_1, h_3808288]
      rfl
    have h_7616578 : matrix_pow_rec T p 7616578 = ((13069814284, 158541234730), (158541234730, 49847100571)) := by
      have h_add : 7616578 = 3808289 + 3808289 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 3808289 3808289]
      rw [h_3808289]
      rfl
    have h_7616579 : matrix_pow_rec T p 7616579 = ((171611049014, 13069814284), (13069814284, 158541234730)) := by
      have h_add : 7616579 = 1 + 7616578 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 7616578]
      rw [h_1, h_7616578]
      rfl
    have h_15233158 : matrix_pow_rec T p 15233158 = ((13996030627, 38127008062), (38127008062, 171187543582)) := by
      have h_add : 15233158 = 7616579 + 7616579 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 7616579 7616579]
      rw [h_7616579]
      rfl
    have h_30466316 : matrix_pow_rec T p 30466316 = ((123761895008, 146193284997), (146193284997, 172887131028)) := by
      have h_add : 30466316 = 15233158 + 15233158 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 15233158 15233158]
      rw [h_15233158]
      rfl
    have h_30466317 : matrix_pow_rec T p 30466317 = ((74636658988, 123761895008), (123761895008, 146193284997)) := by
      have h_add : 30466317 = 1 + 30466316 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 30466316]
      rw [h_1, h_30466316]
      rfl
    have h_60932634 : matrix_pow_rec T p 60932634 = ((25816540105, 62910314271), (62910314271, 158224746851)) := by
      have h_add : 60932634 = 30466317 + 30466317 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 30466317 30466317]
      rw [h_30466317]
      rfl
    have h_60932635 : matrix_pow_rec T p 60932635 = ((88726854376, 25816540105), (25816540105, 62910314271)) := by
      have h_add : 60932635 = 1 + 60932634 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 60932634]
      rw [h_1, h_60932634]
      rfl
    have h_121865270 : matrix_pow_rec T p 121865270 = ((95903560321, 33068008935), (33068008935, 62835551386)) := by
      have h_add : 121865270 = 60932635 + 60932635 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 60932635 60932635]
      rw [h_60932635]
      rfl
    have h_243730540 : matrix_pow_rec T p 243730540 = ((121557274661, 176142473281), (176142473281, 140733322397)) := by
      have h_add : 243730540 = 121865270 + 121865270 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 121865270 121865270]
      rw [h_121865270]
      rfl
    have h_487461080 : matrix_pow_rec T p 487461080 = ((87559309127, 183150853626), (183150853626, 99726976518)) := by
      have h_add : 487461080 = 243730540 + 243730540 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 243730540 243730540]
      rw [h_243730540]
      rfl
    have h_974922160 : matrix_pow_rec T p 974922160 = ((181498976850, 144811362904), (144811362904, 36687613946)) := by
      have h_add : 974922160 = 487461080 + 487461080 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 487461080 487461080]
      rw [h_487461080]
      rfl
    have h_974922161 : matrix_pow_rec T p 974922161 = ((130991818737, 181498976850), (181498976850, 144811362904)) := by
      have h_add : 974922161 = 1 + 974922160 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 974922160]
      rw [h_1, h_974922160]
      rfl
    have h_1949844322 : matrix_pow_rec T p 1949844322 = ((107326271064, 194855280932), (194855280932, 107789511149)) := by
      have h_add : 1949844322 = 974922161 + 974922161 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 974922161 974922161]
      rw [h_974922161]
      rfl
    have h_3899688644 : matrix_pow_rec T p 3899688644 = ((132773265711, 92273131568), (92273131568, 40500134143)) := by
      have h_add : 3899688644 = 1949844322 + 1949844322 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1949844322 1949844322]
      rw [h_1949844322]
      rfl
    have h_7799377288 : matrix_pow_rec T p 7799377288 = ((97520643123, 16299744117), (16299744117, 81220899006)) := by
      have h_add : 7799377288 = 3899688644 + 3899688644 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 3899688644 3899688644]
      rw [h_3899688644]
      rfl
    have h_15598754576 : matrix_pow_rec T p 15598754576 = ((114245750984, 36811031866), (36811031866, 77434719118)) := by
      have h_add : 15598754576 = 7799377288 + 7799377288 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 7799377288 7799377288]
      rw [h_7799377288]
      rfl
    have h_15598754577 : matrix_pow_rec T p 15598754577 = ((151056782850, 114245750984), (114245750984, 36811031866)) := by
      have h_add : 15598754577 = 1 + 15598754576 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 1 15598754576]
      rw [h_1, h_15598754576]
      rfl
    have h_31197509154 : matrix_pow_rec T p 31197509154 = ((89381026484, 161884538056), (161884538056, 122815009445)) := by
      have h_add : 31197509154 = 15598754577 + 15598754577 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 15598754577 15598754577]
      rw [h_15598754577]
      rfl
    have h_62395018308 : matrix_pow_rec T p 62395018308 = ((112336186009, 124390278326), (124390278326, 183264428700)) := by
      have h_add : 62395018308 = 31197509154 + 31197509154 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 31197509154 31197509154]
      rw [h_31197509154]
      rfl
    have h_124790036616 : matrix_pow_rec T p 124790036616 = ((177541888520, 161398467405), (161398467405, 16143421115)) := by
      have h_add : 124790036616 = 62395018308 + 62395018308 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 62395018308 62395018308]
      rw [h_62395018308]
      rfl
    have h_249580073232 : matrix_pow_rec T p 249580073232 = ((21827756563, 117378126758), (117378126758, 99768150822)) := by
      have h_add : 249580073232 = 124790036616 + 124790036616 := by omega
      rw [h_add, matrix_pow_rec_add T p hp 124790036616 124790036616]
      rw [h_124790036616]
      rfl
    exact h_249580073232

theorem Y_j_mod_p : Y j % p = 0 ∧ Y (j + 1) % p = 1 := by
  have hp : 2 ≤ p := by decide
  have h_eq : (Y (j + 1) % p, Y j % p) = (1, 0) := by
    have h_pow := test_steps hp
    have h_vector := Y_step_pow j p
    rw [h_vector, h_pow, Y1_mod_p, Y0_mod_p]
    rfl
  injection h_eq with h_j1 h_j
  exact ⟨h_j, h_j1⟩

theorem Y_sub_one_step (k : ℕ) (hk : 3775 ≤ k) :
  Y (k - 3773) - 1 = 1 + (Y (k - 1 - 3773) - 1) + (Y (k - 2 - 3773) - 1) := by
  have h_sub : k - 3773 = (k - 3775) + 2 := by omega
  have h1 : k - 1 - 3773 = (k - 3775) + 1 := by omega
  have h2 : k - 2 - 3773 = k - 3775 := by omega
  rw [h_sub, h1, h2]
  have h_Y : Y ((k - 3775) + 2) = Y ((k - 3775) + 1) + Y (k - 3775) := rfl
  rw [h_Y]
  have hY1 : 1 ≤ Y ((k - 3775) + 1) := Y_ge_one ((k - 3775) + 1)
  have hY2 : 1 ≤ Y (k - 3775) := Y_ge_one (k - 3775)
  omega

theorem A355898_eq_Y_sub_one (h_rec : ∀ (n : ℕ) (h : 3775 ≤ n), A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  (k : ℕ) (hk : 3773 ≤ k) : A355898 k = Y (k - 3773) - 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases le_or_gt 3775 k with hk5 | hk5
    · have hk1 : 3773 ≤ k - 1 := by omega
      have hk2 : 3773 ≤ k - 2 := by omega
      have ih1 := ih (k - 1) (by omega) hk1
      have ih2 := ih (k - 2) (by omega) hk2
      rw [h_rec k hk5]
      rw [ih1, ih2]
      exact (Y_sub_one_step k hk5).symm
    · interval_cases k
      · dsimp [Y]
        rw [A355898_eq_fast]
      · dsimp [Y]
        rw [A355898_eq_fast]

theorem gcd_ineq (A B g : ℕ) (hA : 0 < A) (hB : 0 < B) (hg : g = Nat.gcd A B) (hg2 : 2 ≤ g) :
  g + (A + B) / g < 1 + A + B := by
  have hgA : g ∣ A := hg ▸ Nat.gcd_dvd_left A B
  have hgB : g ∣ B := hg ▸ Nat.gcd_dvd_right A B
  rcases hgA with ⟨a', rfl⟩
  rcases hgB with ⟨b', rfl⟩
  have ha' : 0 < a' := by
    cases a' with
    | zero => dsimp at hA; omega
    | succ a'' => omega
  have hb' : 0 < b' := by
    cases b' with
    | zero => dsimp at hB; omega
    | succ b'' => omega
  have h_sum : g * a' + g * b' = g * (a' + b') := by ring
  have h_div : (g * a' + g * b') / g = a' + b' := by
    rw [h_sum]
    rw [Nat.mul_div_cancel_left]
    omega
  have ha'_1 : 1 ≤ a' := ha'
  have hb'_1 : 1 ≤ b' := hb'
  have h_X1 : g ≤ g * a' := by
    have h_temp := Nat.mul_le_mul_left g ha'_1
    rw [Nat.mul_one] at h_temp
    exact h_temp
  have h_X2 : 2 * a' ≤ g * a' := Nat.mul_le_mul_right a' hg2
  have h_Y1 : g ≤ g * b' := by
    have h_temp := Nat.mul_le_mul_left g hb'_1
    rw [Nat.mul_one] at h_temp
    exact h_temp
  have h_Y2 : 2 * b' ≤ g * b' := Nat.mul_le_mul_right b' hg2
  rw [h_div]
  omega

def counter_n : ℕ := 3774 + j

theorem oeis_a355898_conjecture.disproof :
  ¬ ∀ (n : ℕ) (h : 3775 ≤ n),
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) := by
  intro h_all
  have h_rec : ∀ (n : ℕ) (h : 3775 ≤ n), A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2) := fun n hn => (h_all n hn).1
  have hp : 2 ≤ p := by decide
  have hj_pos : 1 ≤ j := by decide
  have h_counter_ge : 3775 ≤ counter_n := by
    dsimp [counter_n]
    omega
  have h_counter_ge1 : 3773 ≤ counter_n := by omega
  have h_counter_ge1_1 : 3773 ≤ counter_n + 1 := by omega
  have h_eq1 : A355898 counter_n = Y (counter_n - 3773) - 1 := A355898_eq_Y_sub_one h_rec counter_n h_counter_ge1
  have h_eq2 : A355898 (counter_n + 1) = Y (counter_n + 1 - 3773) - 1 := A355898_eq_Y_sub_one h_rec (counter_n + 1) h_counter_ge1_1
  have h_dvd_Yj : p ∣ Y j := Nat.dvd_of_mod_eq_zero (Y_j_mod_p).1
  have h_eq_Yj1 : Y (j + 1) = p * (Y (j + 1) / p) + 1 := by
    have h_div := Nat.div_add_mod (Y (j + 1)) p
    rw [(Y_j_mod_p).2] at h_div
    omega
  have hYj : Y j ≥ p := by
    have h_mod := (Y_j_mod_p).1
    have h_ge := Y_ge_one j
    have h_dvd : p ∣ Y j := Nat.dvd_of_mod_eq_zero h_mod
    exact Nat.le_of_dvd (by omega) h_dvd
  have hYj_ge : 2 ≤ Y j := Nat.le_trans hp hYj
  let B := A355898 counter_n
  let A := A355898 (counter_n + 1)
  have h_sub_B : counter_n - 3773 = j + 1 := by dsimp [counter_n]; omega
  have h_sub_A : counter_n + 1 - 3773 = j + 2 := by dsimp [counter_n]; omega
  rw [h_sub_B] at h_eq1
  have hB_eq : B = Y (j + 1) - 1 := h_eq1
  rw [h_sub_A] at h_eq2
  have hA_eq : A = Y (j + 2) - 1 := h_eq2
  have h_dvd_B : p ∣ B := by
    rw [hB_eq]
    rw [h_eq_Yj1]
    have h_sub : p * (Y (j + 1) / p) + 1 - 1 = p * (Y (j + 1) / p) := by omega
    rw [h_sub]
    exact dvd_mul_right p (Y (j + 1) / p)
  have h_dvd_A : p ∣ A := by
    rw [hA_eq]
    have h_A_split : Y (j + 2) - 1 = (Y (j + 1) - 1) + Y j := by
      have hY1_ge : 1 ≤ Y (j + 1) := Y_ge_one (j + 1)
      have hY2 : Y (j + 2) = Y (j + 1) + Y j := Y_step j
      omega
    rw [h_A_split]
    have h_dvd_B' : p ∣ Y (j + 1) - 1 := hB_eq ▸ h_dvd_B
    exact dvd_add h_dvd_B' h_dvd_Yj
  have h_counter_n_pos : 0 < B := by
    rw [hB_eq]
    have h_Y_add : Y (j + 1) = Y j + Y (j - 1) := Y_step_sub j hj_pos
    have h_Y_ge1 : 1 ≤ Y (j - 1) := Y_ge_one (j - 1)
    omega
  have h_counter_n1_pos : 0 < A := by
    rw [hA_eq]
    have hY2 : Y (j + 2) = Y (j + 1) + Y j := Y_step j
    have h_Y_ge1 : 1 ≤ Y (j + 1) := Y_ge_one (j + 1)
    omega
  let g := Nat.gcd A B
  have hg2 : 2 ≤ g := by
    have h_dvd_g : p ∣ g := Nat.dvd_gcd h_dvd_A h_dvd_B
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left B h_counter_n1_pos
    exact Nat.le_trans hp (Nat.le_of_dvd hg_pos h_dvd_g)
  have h_ineq := gcd_ineq A B g h_counter_n1_pos h_counter_n_pos rfl hg2
  have h_rec_def : A355898 (counter_n + 2) = g + (A + B) / g := A355898_step_sub counter_n (by omega)
  have h_conj_def : A355898 (counter_n + 2) = 1 + A + B := by
    have h_counter_ge2 : 3775 ≤ counter_n + 2 := by omega
    have h_eq := h_rec (counter_n + 2) h_counter_ge2
    have h_sub1 : counter_n + 2 - 1 = counter_n + 1 := by omega
    have h_sub2 : counter_n + 2 - 2 = counter_n := by omega
    rw [h_sub1, h_sub2] at h_eq
    exact h_eq
  rw [h_conj_def] at h_rec_def
  rw [h_rec_def] at h_ineq
  exact Nat.lt_irrefl (g + (A + B) / g) h_ineq

